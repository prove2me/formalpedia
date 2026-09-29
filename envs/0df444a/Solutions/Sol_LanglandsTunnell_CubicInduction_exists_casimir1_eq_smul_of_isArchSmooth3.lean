-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_casimir1_eq_smul_of_isArchSmooth3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/66c36d96-392c-50e0-b637-555e79a4a955

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

noncomputable section

namespace CF1Body48

theorem ofReal_mul' (r s : ℝ) :
    AutomorphicForm.StandardKernel.ofReal (r * s) =
      AutomorphicForm.StandardKernel.ofReal r * AutomorphicForm.StandardKernel.ofReal s := by
  funext v
  exact map_mul _ r s

theorem ofReal_zero' : AutomorphicForm.StandardKernel.ofReal 0 = 0 := by
  funext v
  exact map_zero _

theorem ofReal_one' : AutomorphicForm.StandardKernel.ofReal 1 = 1 := by
  funext v
  exact map_one _

theorem archRealMat3_diag (d : Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (fun i j => if i = j then d i else 0) =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun i => AutomorphicForm.StandardKernel.ofReal (d i)) := by
  unfold WhittakerBlock.archRealMat3
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [h, ofReal_zero']

theorem archMatrixInclN_diagonal_mul (x y : Fin 3 → InfiniteAdeleRing ℚ) :
    AutomorphicForm.archMatrixInclN (Fin 3) ℚ (Matrix.diagonal x) *
        AutomorphicForm.archMatrixInclN (Fin 3) ℚ (Matrix.diagonal y) =
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ (Matrix.diagonal fun i => x i * y i) := by
  rw [← AutomorphicForm.archMatrixInclN_mul, Matrix.diagonal_mul_diagonal]

theorem isUnit_archRealMat3_diag (d : Fin 3 → ℝ) (hd : ∀ i, d i ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 (fun i j => if i = j then d i else 0)) := by
  rw [archRealMat3_diag]
  have hmul : AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun i => AutomorphicForm.StandardKernel.ofReal (d i)) *
      AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun i => AutomorphicForm.StandardKernel.ofReal (d i)⁻¹) = 1 := by
    rw [archMatrixInclN_diagonal_mul]
    have hone : (fun i => AutomorphicForm.StandardKernel.ofReal (d i) *
        AutomorphicForm.StandardKernel.ofReal (d i)⁻¹) = fun _ => (1 : InfiniteAdeleRing ℚ) := by
      funext i
      rw [← ofReal_mul', mul_inv_cancel₀ (hd i), ofReal_one']
    rw [hone, Matrix.diagonal_one, AutomorphicForm.archMatrixInclN_one]
  exact ⟨⟨_, _, hmul, mul_eq_one_comm.mp hmul⟩, rfl⟩

theorem scalar_eq_archMatrixInclN_diagonal (c : ℝ) (hc : c ≠ 0) :
    ∃ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) =
        AutomorphicForm.archMatrixInclN (Fin 3) ℚ
          (Matrix.diagonal fun _ => AutomorphicForm.StandardKernel.ofReal c) := by
  have hval : ((AutomorphicForm.StandardKernel.ofReal c, 1) : AdeleRing (𝓞 ℚ) ℚ) *
      ((AutomorphicForm.StandardKernel.ofReal c⁻¹, 1) : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
    refine Prod.ext ?_ (one_mul 1)
    change AutomorphicForm.StandardKernel.ofReal c * AutomorphicForm.StandardKernel.ofReal c⁻¹ = 1
    rw [← ofReal_mul', mul_inv_cancel₀ hc, ofReal_one']
  have hval' : ((AutomorphicForm.StandardKernel.ofReal c⁻¹, 1) : AdeleRing (𝓞 ℚ) ℚ) *
      ((AutomorphicForm.StandardKernel.ofReal c, 1) : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
    refine Prod.ext ?_ (one_mul 1)
    change AutomorphicForm.StandardKernel.ofReal c⁻¹ * AutomorphicForm.StandardKernel.ofReal c = 1
    rw [← ofReal_mul', inv_mul_cancel₀ hc, ofReal_one']
  refine ⟨⟨_, _, hval, hval'⟩, ?_⟩
  ext i j
  refine Prod.ext ?_ ?_
  · change NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ (Matrix.scalar (Fin 3)
        ((AutomorphicForm.StandardKernel.ofReal c, 1) : AdeleRing (𝓞 ℚ) ℚ) i j) =
      NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ (AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun _ => AutomorphicForm.StandardKernel.ofReal c) i j)
    rw [AutomorphicForm.adeleArch_archMatrixInclN]
    by_cases h : i = j
    · subst h
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      rfl
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
      exact map_zero _
  · change NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ (Matrix.scalar (Fin 3)
        ((AutomorphicForm.StandardKernel.ofReal c, 1) : AdeleRing (𝓞 ℚ) ℚ) i j) =
      NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ (AutomorphicForm.archMatrixInclN (Fin 3) ℚ
        (Matrix.diagonal fun _ => AutomorphicForm.StandardKernel.ofReal c) i j)
    rw [AutomorphicForm.adeleFin_archMatrixInclN]
    by_cases h : i = j
    · subst h
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rfl
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      exact map_zero _

theorem exists_archRealLift3_scalar_eq_centralScalarGL (c : ℝ) (hc : c ≠ 0) :
    ∃ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      WhittakerBlock.archRealLift3 (fun i j => if i = j then c else 0) = centralScalarGL 3 (𝓞 ℚ) ℚ z := by
  obtain ⟨z, hz⟩ := scalar_eq_archMatrixInclN_diagonal c hc
  refine ⟨z, ?_⟩
  have hu : IsUnit (WhittakerBlock.archRealMat3 (fun i j : Fin 3 => if i = j then c else 0)) :=
    isUnit_archRealMat3_diag (fun _ => c) fun _ => hc
  rw [WhittakerBlock.archRealLift3, dif_pos hu]
  apply Units.ext
  rw [IsUnit.unit_spec]
  change WhittakerBlock.archRealMat3 (fun i j : Fin 3 => if i = j then c else 0) =
    Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ)
  rw [hz, archRealMat3_diag]

theorem mul_centralScalarGL_comm (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    h * centralScalarGL 3 (𝓞 ℚ) ℚ z = centralScalarGL 3 (𝓞 ℚ) ℚ z * h := by
  apply Units.ext
  simp only [Units.val_mul]
  show (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) =
    Matrix.scalar (Fin 3) (z : AdeleRing (𝓞 ℚ) ℚ) * (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 ℚ) ℚ) (fun r => mul_comm _ r) _).eq.symm

def I₃ : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then 1 else 0

def E₃ (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then 1 else 0

theorem sum_E₃_diag : ∑ i : Fin 3, E₃ i i = I₃ := by
  funext a b
  simp only [Finset.sum_apply, Fin.sum_univ_three, E₃, I₃]
  fin_cases a <;> fin_cases b <;> simp

theorem archDeriv_curve_eq (i j : Fin 3) (s : ℝ) :
    (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) = I₃ + s • E₃ i j := by
  funext a b
  simp only [Pi.add_apply, Pi.smul_apply, I₃, E₃, smul_eq_mul]
  split_ifs <;> simp

theorem exp_curve_eq (s : ℝ) :
    (fun a b : Fin 3 => if a = b then Real.exp s else 0) = Real.exp s • I₃ := by
  funext a b
  simp only [Pi.smul_apply, I₃, smul_eq_mul]
  split_ifs <;> simp

theorem det_of_I₃ : (Matrix.of I₃).det ≠ 0 := by
  have : Matrix.of I₃ = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext a b
    simp only [Matrix.of_apply, I₃, Matrix.one_apply]
  rw [this, Matrix.det_one]
  exact one_ne_zero

theorem isOpen_det_ne : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  have hc : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : Matrix (Fin 3) (Fin 3) ℝ => e).matrix_det
  exact isOpen_ne.preimage hc

theorem deriv_line {F : (Fin 3 → Fin 3 → ℝ) → ℂ} {x : Fin 3 → Fin 3 → ℝ} (hF : DifferentiableAt ℝ F x)
    (w : Fin 3 → Fin 3 → ℝ) :
    deriv (fun s : ℝ => F (x + s • w)) 0 = fderiv ℝ F x w := by
  have hγ : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hx : x + (0 : ℝ) • w = x := by simp
  have hF' : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • w) := by rw [hx]; exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) hγ).deriv

theorem deriv_exp_curve {F : (Fin 3 → Fin 3 → ℝ) → ℂ} (hF : DifferentiableAt ℝ F I₃) :
    deriv (fun s : ℝ => F (Real.exp s • I₃)) 0 = fderiv ℝ F I₃ I₃ := by
  have hγ : HasDerivAt (fun s : ℝ => Real.exp s • I₃) I₃ 0 := by
    simpa using (Real.hasDerivAt_exp 0).smul_const I₃
  have hx : Real.exp 0 • I₃ = I₃ := by simp
  have hF' : HasFDerivAt F (fderiv ℝ F I₃) (Real.exp 0 • I₃) := by rw [hx]; exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) hγ).deriv

theorem sum_deriv_diag_eq_deriv_exp {F : (Fin 3 → Fin 3 → ℝ) → ℂ} (hF : DifferentiableAt ℝ F I₃) :
    ∑ i : Fin 3, deriv (fun s : ℝ => F (I₃ + s • E₃ i i)) 0 = deriv (fun s : ℝ => F (Real.exp s • I₃)) 0 := by
  rw [deriv_exp_curve hF]
  simp_rw [deriv_line hF]
  rw [← map_sum, sum_E₃_diag]

theorem differentiableAt_of_isArchSmooth3 {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hsa : WhittakerBlock.IsArchSmooth3 u)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => u (g * WhittakerBlock.archRealLift3 e)) I₃ := by
  have h := (hsa g).contDiffAt (isOpen_det_ne.mem_nhds det_of_I₃)
  exact h.differentiableAt (by simp)

theorem casimir1_eq_deriv_exp {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hsa : WhittakerBlock.IsArchSmooth3 u)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.casimir1 u g =
      deriv (fun s : ℝ => u (g * WhittakerBlock.archRealLift3 (fun a b : Fin 3 => if a = b then Real.exp s else 0))) 0 := by
  simp only [WhittakerBlock.casimir1, WhittakerBlock.archDeriv]
  simp_rw [archDeriv_curve_eq, exp_curve_eq]
  exact sum_deriv_diag_eq_deriv_exp (F := fun e => u (g * WhittakerBlock.archRealLift3 e))
    (differentiableAt_of_isArchSmooth3 hsa g)

end CF1Body48

end

open CF1Body48 in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u) :
    ∃ c : ℂ, WhittakerBlock.casimir1 u = c • u := by
  classical

  have hz : ∀ s : ℝ, ∃ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      WhittakerBlock.archRealLift3 (fun i j : Fin 3 => if i = j then Real.exp s else 0) = centralScalarGL 3 (𝓞 ℚ) ℚ z :=
    fun s => exists_archRealLift3_scalar_eq_centralScalarGL (Real.exp s) (Real.exp_pos s).ne'
  choose z hz using hz

  have hcurve : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℝ),
      u (g * WhittakerBlock.archRealLift3 (fun a b : Fin 3 => if a = b then Real.exp s else 0)) = (ω (z s) : ℂ) * u g := by
    intro g s
    rw [hz s, mul_centralScalarGL_comm, hcen]
  refine ⟨deriv (fun s : ℝ => (ω (z s) : ℂ)) 0, ?_⟩
  funext g
  rw [Pi.smul_apply, smul_eq_mul, casimir1_eq_deriv_exp hsa g]
  simp_rw [hcurve g]
  by_cases hu : ∃ g₀ : AdelicGL 3 (𝓞 ℚ) ℚ, u g₀ ≠ 0
  · obtain ⟨g₀, hg₀⟩ := hu

    have hdiff : DifferentiableAt ℝ (fun s : ℝ => (ω (z s) : ℂ)) 0 := by
      have hF := differentiableAt_of_isArchSmooth3 hsa g₀
      have hcomp : DifferentiableAt ℝ
          (fun s : ℝ => u (g₀ * WhittakerBlock.archRealLift3 (fun a b : Fin 3 => if a = b then Real.exp s else 0))) 0 := by
        simp_rw [exp_curve_eq]
        have hx : Real.exp 0 • I₃ = I₃ := by simp
        have hF' : DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => u (g₀ * WhittakerBlock.archRealLift3 e))
            (Real.exp (0 : ℝ) • I₃) := by rw [hx]; exact hF
        show DifferentiableAt ℝ
          ((fun e : Fin 3 → Fin 3 → ℝ => u (g₀ * WhittakerBlock.archRealLift3 e)) ∘ (fun s : ℝ => Real.exp s • I₃)) 0
        exact hF'.comp (0 : ℝ) ((Real.differentiable_exp.differentiableAt).smul_const I₃)
      simp_rw [hcurve g₀] at hcomp
      have := hcomp.mul_const ((u g₀)⁻¹)
      simp_rw [mul_assoc, mul_inv_cancel₀ hg₀, mul_one] at this
      exact this
    exact (hdiff.hasDerivAt.mul_const (u g)).deriv
  · push Not at hu
    simp [hu]

end S_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_casimir1_eq_smul_of_isArchSmooth3 (solution)
