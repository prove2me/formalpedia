-- Prove2me | solution 1 for Kyprianou.Ch03.momentFiniteBoundedGaussianJumpLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:02:46.354261+00:00
-- url     : https://prove2.me/submissions/1c55675a-f71e-4dcd-be25-9e82506c6959

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedJumpLawV1
import Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedMarkIdV1
import Theorems.Thm_Kyprianou_Ch03_momentFourierCharacterIntegrableV1
import Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedMarkExpV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ x ∂nu, |x| < 1) (d : Real) (v t : NNReal) :
    ∃ Q : ProbabilityMeasure Real,
      (∀ xi : Real, charFun (Q : Measure Real) xi =
        Complex.exp (((t : Real) : Complex) *
          (Complex.I * ((d * xi : Real) : Complex) -
          (((v : Real) * xi ^ 2 / 2 : Real) : Complex) +
          ∫ x, ProbabilityTheory.levyCompensatedIntegrand xi x ∂nu))) ∧
      (∀ b : Real, Integrable (fun x : Real => Real.exp (b*x)) (Q : Measure Real) ∧
        (∫ x, Real.exp (b*x) ∂(Q : Measure Real)) =
          Real.exp ((t : Real) * (d*b + (v : Real)*b^2/2 +
            ∫ x, (Real.exp (b*x)-1-b*x) ∂nu))) := by
  let C : ℝ := ∫ x : ℝ, x ∂nu
  let G := gaussianReal ((t : ℝ)*(d-C)) (t*v)
  obtain ⟨J, hchar, hreal⟩ := Kyprianou.Ch03.momentFiniteBoundedJumpLawV1 nu hnu t
  have hid := Kyprianou.Ch03.momentFiniteBoundedMarkIdV1 nu hnu
  refine ⟨⟨G.conv (J : Measure ℝ), inferInstance⟩, ?_, ?_⟩
  · intro xi
    let z := (xi : ℂ)*Complex.I
    let H (x : ℝ) := Complex.exp (Complex.I * (((xi*x : ℝ) : ℂ))) - 1
    have hH : Integrable H nu := by
      have hh := (Kyprianou.Ch03.momentFourierCharacterIntegrableV1 nu xi).sub (integrable_const 1)
      convert hh using 1
      funext x
      dsimp [H]
      push_cast
      congr 2
      ring
    have hcomp : (∫ x, levyCompensatedIntegrand xi x ∂nu) =
        (∫ x, H x ∂nu) - z * (C : ℂ) := by
      have he : levyCompensatedIntegrand xi =ᵐ[nu] fun x => H x - z*(x : ℂ) :=
        hnu.mono fun x hx => by
          simp [levyCompensatedIntegrand, hx, H, z, mul_comm, mul_left_comm, mul_assoc]
      rw [integral_congr_ae he, integral_sub hH
        (by simpa using (Complex.ofRealCLM.integrable_comp hid).const_mul z),
        integral_const_mul]
      have h : (∫ x : ℝ, (x : ℂ) ∂nu) = Complex.ofReal C :=
        integral_ofReal (𝕜 := ℂ) (μ := nu) (f := fun x : ℝ => x)
      rw [h]
    change charFun (G.conv (J : Measure ℝ)) xi = _
    rw [charFun_conv, charFun_gaussianReal, hchar, ← Complex.exp_add, hcomp]
    congr 1
    dsimp [G, C, z, H]
    push_cast
    ring
  · intro b
    let F (x : ℝ) := Real.exp (b*x)
    have hadd (x y : ℝ) : F (x+y) = F x*F y := by simp [F, mul_add, Real.exp_add]
    obtain ⟨hJ, hJe⟩ := hreal b
    have hG : Integrable F G := integrable_exp_mul_gaussianReal b
    have hi : Integrable F (G.conv (J : Measure ℝ)) := by
      change Integrable F ((G.prod (J : Measure ℝ)).map fun p => p.1+p.2)
      rw [integrable_map_measure (by fun_prop) (by fun_prop)]
      change Integrable (fun p : ℝ × ℝ => F (p.1+p.2)) (G.prod (J : Measure ℝ))
      simp_rw [hadd]
      exact hG.mul_prod hJ
    have hGe : (∫ x, F x ∂G) =
        Real.exp ((t : ℝ)*(d-C)*b + ((t*v : NNReal) : ℝ)*b^2/2) := by
      have hmap : G.map (id : ℝ → ℝ) = gaussianReal ((t : ℝ)*(d-C)) (t*v) := by simp [G]
      simpa only [mgf, id_eq, F] using mgf_gaussianReal hmap b
    have hν := Kyprianou.Ch03.momentFiniteBoundedMarkExpV1 nu hnu b
    refine ⟨hi, ?_⟩
    change (∫ x, F x ∂(G.conv (J : Measure ℝ))) = _
    rw [integral_conv hi]
    simp_rw [hadd, integral_const_mul]
    have hcomp : (∫ x, (Real.exp (b*x)-1-b*x) ∂nu) =
        (∫ x, (Real.exp (b*x)-1) ∂nu) - b*C := by
      have hsub : Integrable (fun x : ℝ => Real.exp (b*x)-1) nu := hν.sub (integrable_const 1)
      rw [integral_sub hsub (hid.const_mul b), integral_const_mul]
    rw [integral_mul_const, hGe, hJe, ← Real.exp_add, hcomp]
    congr 1
    dsimp [C]
    push_cast
    ring
