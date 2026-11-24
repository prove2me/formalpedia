-- Prove2me | solution 1 for Kyprianou.Ch03.momentFiniteBoundedJumpLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:02:37.099642+00:00
-- url     : https://prove2.me/submissions/de156988-9259-459c-8257-783871206e48

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_exponential_moment
import Theorems.Thm_Kyprianou_Ch03_momentCompoundPoissonCharFunV1
import Theorems.Thm_Kyprianou_Ch03_momentFiniteBoundedMarkExpV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ x ∂nu, |x| < 1) (t : NNReal) :
    ∃ J : ProbabilityMeasure Real,
      (∀ xi : Real, charFun (J : Measure Real) xi =
        Complex.exp (((t : Real) : Complex) *
          ∫ x, (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂nu)) ∧
      (∀ b : Real, Integrable (fun x : Real => Real.exp (b*x)) (J : Measure Real) ∧
        (∫ x, Real.exp (b*x) ∂(J : Measure Real)) =
          Real.exp ((t : Real) * ∫ x, (Real.exp (b*x)-1) ∂nu)) := by
  let rho : Measure ℝ := (t : ENNReal) • nu
  letI : IsFiniteMeasure rho := by dsimp [rho]; infer_instance
  let J := KSATSingleFlip.Connect.compoundPoisson rho
  letI : IsProbabilityMeasure J := ⟨KSATSingleFlip.Connect.compound_poisson_probability rho⟩
  refine ⟨⟨J, inferInstance⟩, ?_, ?_⟩
  · intro xi
    change charFun J xi = _
    rw [Kyprianou.Ch03.momentCompoundPoissonCharFunV1 rho xi]
    dsimp [rho]
    rw [integral_smul_nnreal_measure]
    congr 1
  · intro b
    let F (x : ℝ) := Real.exp (b*x)
    have hF : Integrable F nu := Kyprianou.Ch03.momentFiniteBoundedMarkExpV1 nu hnu b
    have hFr : Integrable F rho := by
      by_cases h : t = 0
      · simp [rho, h]
      · exact (integrable_smul_measure (by exact_mod_cast h) ENNReal.coe_ne_top).mpr hF
    have hnon (x : ℝ) : 0 ≤ F x := (Real.exp_pos _).le
    have hfin := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnon)).mp hFr.2
    have hcp := KSATSingleFlip.Connect.compound_poisson_exponential_moment rho b hfin.ne
    change (∫⁻ x, ENNReal.ofReal (F x) ∂J) = _ at hcp
    have hI : Integrable F J := ⟨by dsimp [F]; fun_prop,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnon)).mpr (hcp.trans_lt ENNReal.ofReal_lt_top)⟩
    refine ⟨hI, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hFr (Eventually.of_forall hnon),
      ENNReal.toReal_ofReal (integral_nonneg hnon),
      ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hnon)] at hcp
    have h := congrArg ENNReal.toReal hcp
    rw [ENNReal.toReal_ofReal (integral_nonneg hnon),
      ENNReal.toReal_ofReal (by positivity)] at h
    change (∫ x, F x ∂J) = _
    rw [h, ← Real.exp_add, integral_sub hF (integrable_const 1), integral_const]
    dsimp [rho]
    rw [integral_smul_nnreal_measure, ENNReal.toReal_mul]
    simp [Measure.real, smul_eq_mul]
    congr 1
    change -(↑t * (nu univ).toReal) + (t : ℝ) * (∫ x, F x ∂nu) = _
    ring
