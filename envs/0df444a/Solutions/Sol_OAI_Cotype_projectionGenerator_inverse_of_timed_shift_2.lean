-- Prove2me | solution 2 for OAI.Cotype.projectionGenerator_inverse_of_timed_shift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:03:24.164322+00:00
-- url     : https://prove2.me/submissions/f6024e20-6270-46ba-8982-7f10cd5ed429

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionResolvent.lean:L106-L137
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.projectionGenerator_inverse_of_timed_shift. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Theorems.Thm_OAI_Cotype_exists_complex_shift_inverse_of_power_gap
import Theorems.Thm_OAI_Cotype_projectionGenerator_exp_shift

-- ---- from OAI.Analysis.Cotype.ProjectionProducts ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionProduct_norm_apply {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (h : ∀ i x, ‖P i x‖ ≤ ‖x‖) (x : X) : ‖projectionProduct P x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih => exact (h 0 _).trans (ih _ (fun i => h i.succ))

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionSemigroupBasics ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projectionSemigroup_factor_contracts (P : Y →L[ℝ] Y)
    (hP : ∀ y, ‖P y‖ ≤ ‖y‖) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (y : Y) :
    ‖(P + r • (1-P)) y‖ ≤ ‖y‖ := by
  have he : P + r • (1-P) = (1-r) • P + r • (1 : Y →L[ℝ] Y) := by module
  rw [he]
  change ‖(1-r) • P y + r • y‖ ≤ ‖y‖
  calc
    _ ≤ ‖(1-r) • P y‖ + ‖r • y‖ := norm_add_le _ _
    _ = (1-r)*‖P y‖ + r*‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hr1), abs_of_nonneg hr]
    _ ≤ (1-r)*‖y‖ + r*‖y‖ := by gcongr; exact hP y
    _ = ‖y‖ := by ring

theorem projectionSemigroup_contracts {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (y : Y) :
    ‖projectionSemigroup P r y‖ ≤ ‖y‖ :=
  projectionProduct_norm_apply _ (fun i => projectionSemigroup_factor_contracts (P i) (hP i) hr hr1) y

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ComplexProjectionPolynomial ----
namespace OAI

noncomputable section
namespace Cotype

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexProjectionProduct_lift {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    complexProjectionProduct (fun i => complexDualLift (P i)) =
      complexDualLift (projectionProduct P) := by
  induction m with
  | zero => simp [complexProjectionProduct, projectionProduct]
  | succ m ih => simp [complexProjectionProduct, projectionProduct, ih]

theorem complexProjectionPolynomial_real {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (r : ℝ) :
    complexProjectionPolynomial P (r : ℂ) = complexDualLift (projectionSemigroup P r) := by
  unfold complexProjectionPolynomial projectionSemigroup
  rw [← complexProjectionProduct_lift]
  congr 1
  funext i
  simp only [complexDualLift_add, complexDualLift_smul, complexDualLift_sub, complexDualLift_one]
  congr 1

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionGenerator ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexProjectionTime_real {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (t : ℝ) :
    complexProjectionTime P (t : ℂ) =
      complexDualLift (projectionSemigroup P (Real.exp (-t))) := by
  unfold complexProjectionTime
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, complexProjectionPolynomial_real]

theorem complexProjectionTime_real_norm_le {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖) {t : ℝ} (ht : 0 ≤ t) :
    ‖complexProjectionTime P (t : ℂ)‖ ≤ 1 := by
  rw [complexProjectionTime_real, complexDualLift_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simpa only [one_mul] using projectionSemigroup_contracts P hP
    (Real.exp_pos (-t)).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) y

theorem complexProjectionTime_real_power_gap {N : ℕ} {C : ℝ} (hC : 0 ≤ C)
    {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hgap : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
      ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖) {t : ℝ} (ht : 0 ≤ t) :
    ‖(1-complexProjectionTime P (t : ℂ))^N‖ ≤ C := by
  rw [complexProjectionTime_real]
  have h := ContinuousLinearMap.opNorm_le_bound _ hC
    (hgap (Real.exp (-t)) (Real.exp_pos (-t)).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)))
  simpa only [← complexDualLift_one, ← complexDualLift_sub, ← complexDualLift_pow,
    complexDualLift_norm] using h

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ExponentialIntegral ----
namespace OAI

noncomputable section
namespace Cotype
open MeasureTheory
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exponentialIntegral_mul (L : A) (t : ℝ) :
    exponentialIntegral L t * L = NormedSpace.exp (t • L) - 1 := by
  have hf := (differentiable_exp_smul_const ℝ L).continuous
  have hint := hf.intervalIntegrable (μ := volume) (0 : ℝ) t
  have hm := (ContinuousLinearMap.mulLeftRight ℝ A 1 L).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.mulLeftRight_apply, one_mul] at hm
  rw [exponentialIntegral, ← hm]
  simpa only [zero_smul, NormedSpace.exp_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_exp_smul_const L s)
      ((hf.mul continuous_const).intervalIntegrable (0 : ℝ) t)

theorem mul_exponentialIntegral (L : A) (t : ℝ) :
    L * exponentialIntegral L t = NormedSpace.exp (t • L) - 1 := by
  have hf := (differentiable_exp_smul_const ℝ L).continuous
  have hint := hf.intervalIntegrable (μ := volume) (0 : ℝ) t
  have hm := (ContinuousLinearMap.mulLeftRight ℝ A L 1).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.mulLeftRight_apply, mul_one] at hm
  rw [exponentialIntegral, ← hm]
  simpa only [zero_smul, NormedSpace.exp_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_exp_smul_const' L s)
      ((continuous_const.mul hf).intervalIntegrable (0 : ℝ) t)

omit [NormedAlgebra ℝ A] [CompleteSpace A] in

theorem exists_inverse_of_commuting_factorization (L V : A) (U : Aˣ)
    (hleft : L*V = (U : A)) (hright : V*L = (U : A)) :
    ∃ W : Aˣ, (W : A) = L ∧ ‖(↑W⁻¹ : A)‖ ≤ ‖V‖ * ‖(↑U⁻¹ : A)‖ := by
  have huv : (U : A) * (↑U⁻¹ : A) = 1 := U.val_inv
  have huiv : (↑U⁻¹ : A) * (U : A) = 1 := U.inv_val
  have hr : L * (V * (↑U⁻¹ : A)) = 1 := by rw [← mul_assoc, hleft, huv]
  have hl : ((↑U⁻¹ : A) * V) * L = 1 := by rw [mul_assoc, hright, huiv]
  have heq : (↑U⁻¹ : A) * V = V * (↑U⁻¹ : A) := by
    calc
      _ = ((↑U⁻¹ : A) * V) * (L * (V * (↑U⁻¹ : A))) := by rw [hr, mul_one]
      _ = V * (↑U⁻¹ : A) := by rw [← mul_assoc, hl, one_mul]
  refine ⟨⟨L, V * (↑U⁻¹ : A), hr, ?_⟩, rfl, norm_mul_le _ _⟩
  rw [← heq, hl]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionResolvent ----
namespace OAI

noncomputable section
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projectionShiftIntegral_factors {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (z : ℂ) (t : ℝ) :
    (z • 1 - projectionGenerator P) * projectionShiftIntegral P z t =
      complexProjectionTime P (t : ℂ) - Complex.exp (-(z * (t : ℂ))) • 1 ∧
    projectionShiftIntegral P z t * (z • 1 - projectionGenerator P) =
      complexProjectionTime P (t : ℂ) - Complex.exp (-(z * (t : ℂ))) • 1 := by
  have he : Complex.exp (-(z * (t : ℂ))) * Complex.exp (z * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hmul_smul (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)
      (scalar : ℂ) : left * (scalar • right) = scalar • (left * right) := by
    apply ContinuousLinearMap.ext
    intro vector
    exact left.map_smul scalar (right vector)
  have hsmul_mul (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)
      (scalar : ℂ) : (scalar • left) * right = scalar • (left * right) := by
    ext vector dual
    rfl
  have hsmul_sub (scalar : ℂ)
      (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) :
      scalar • (left - right) = scalar • left - scalar • right := by
    ext vector dual
    exact mul_sub scalar _ _
  constructor
  · rw [projectionShiftIntegral, hmul_smul, mul_exponentialIntegral,
      projectionGenerator_exp_shift P hp hc, hsmul_sub, smul_smul, he, one_smul]
  · rw [projectionShiftIntegral, hsmul_mul, exponentialIntegral_mul,
      projectionGenerator_exp_shift P hp hc, hsmul_sub, smul_smul, he, one_smul]

theorem projectionShiftIntegral_norm_le {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖) (z : ℂ) {t D : ℝ} (ht : 0 ≤ t)
    (hD : ∀ s ∈ Set.Icc 0 t, Real.exp (z.re * (s-t)) ≤ D) :
    ‖projectionShiftIntegral P z t‖ ≤ D*t := by
  rw [projectionShiftIntegral, exponentialIntegral, ← intervalIntegral.integral_smul]
  have he (s : ℝ) :
      Complex.exp (-(z*(t : ℂ))) •
        NormedSpace.exp (s • (z • 1 - projectionGenerator P)) =
      Complex.exp (z * ((s-t : ℝ) : ℂ)) • complexProjectionTime P (s : ℂ) := by
    rw [projectionGenerator_exp_shift P hp hc, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [he]
  have hn : ‖∫ s in (0 : ℝ)..t,
      Complex.exp (z * ((s-t : ℝ) : ℂ)) • complexProjectionTime P (s : ℂ)‖ ≤
      D * |t-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    rw [norm_smul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp (z.re * (s-t)) * 1 :=
        mul_le_mul_of_nonneg_left (complexProjectionTime_real_norm_le P hP hs0)
          (Real.exp_pos _).le
      _ ≤ D := by simpa using hD s ⟨hs0, hs.2⟩
  simpa [abs_of_nonneg ht] using hn

theorem projectionGenerator_inverse_of_timed_shift
    [Nontrivial (ComplexDualSpace Y)]
    {N : ℕ} {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ) (hgap : C < ρ^N)
    {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖)
    (hpower : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ y : Y,
      ‖((1-projectionSemigroup P r)^N) y‖ ≤ C*‖y‖)
    (z : ℂ) {t D : ℝ} (ht : 0 ≤ t)
    (hshift : ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖)
    (hD : ∀ s ∈ Set.Icc 0 t, Real.exp (z.re * (s-t)) ≤ D) :
    ∃ W : (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)ˣ,
      (W : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) = z • 1 - projectionGenerator P ∧
      ‖(↑W⁻¹ : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)‖ ≤
        D*t * (powerGapInverseBound N (2/ρ) (C/ρ^N) /
          ‖1-Complex.exp (-(z*(t : ℂ)))‖) := by
  obtain ⟨U, hU, hnU⟩ := exists_complex_shift_inverse_of_power_gap hC hρ hgap
    (complexProjectionTime P (t : ℂ)) (complexProjectionTime_real_norm_le P hP ht)
    (complexProjectionTime_real_power_gap hC P hpower ht)
    (1-Complex.exp (-(z*(t : ℂ)))) hshift
  have hv : (U : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) =
      complexProjectionTime P (t : ℂ) - Complex.exp (-(z*(t : ℂ))) • 1 := by
    rw [hU]
    module
  have hf := projectionShiftIntegral_factors P hp hc z t
  obtain ⟨W, hW, hnW⟩ := exists_inverse_of_commuting_factorization
    (z • 1 - projectionGenerator P) (projectionShiftIntegral P z t) U
    (hf.1.trans hv.symm) (hf.2.trans hv.symm)
  refine ⟨W, hW, hnW.trans ?_⟩
  have hD0 : 0 ≤ D := (Real.exp_pos _).le.trans (hD 0 ⟨le_rfl, ht⟩)
  exact mul_le_mul (projectionShiftIntegral_norm_le P hp hc hP z ht hD) hnU
    (norm_nonneg _) (mul_nonneg hD0 ht)

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.projectionGenerator_inverse_of_timed_shift := @_root_.OAI.Cotype.projectionGenerator_inverse_of_timed_shift
