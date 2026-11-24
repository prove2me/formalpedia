-- Prove2me | solution 1 for GlobalTheory.MinorInt.columns_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:18:48.712801+00:00
-- url     : https://prove2.me/submissions/60815319-e50d-4487-af81-88c3fefef5e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_star_dot_self_re
import Theorems.Thm_GlobalTheory_MinorInt_form_gram_re
import Theorems.Thm_GlobalTheory_MinorInt_volume_ellipsoid_le
import Theorems.Thm_GlobalTheory_MinorInt_near_one
import Theorems.Thm_GlobalTheory_MinorInt_det_ne_zero_of_form
import Theorems.Thm_GlobalTheory_MinorInt_lintegral_mul_right
import Theorems.Thm_GlobalTheory_MinorInt_weight_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (n : ℕ) (hn : 2 * (Fintype.card ι + Fintype.card κ) ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∫⁻ x : (ι → ι → ℂ) × (κ → ι → ℂ),
      {x : (ι → ι → ℂ) × (κ → ι → ℂ) | ∀ i j, ‖((Matrix.of x.1)ᵀᴴ * (Matrix.of x.1)ᵀ -
        (Matrix.of x.2)ᴴ * Matrix.of x.2 - 1 : Matrix ι ι ℂ) i j‖ < δ}.indicator
        (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ n)⁻¹) x < ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨δ, hδ, hδ1, hnear⟩ := near_one ι
  refine ⟨δ, hδ, ?_⟩
  set S := {x : (ι → ι → ℂ) × (κ → ι → ℂ) | ∀ i j, ‖((Matrix.of x.1)ᵀᴴ * (Matrix.of x.1)ᵀ -
        (Matrix.of x.2)ᴴ * Matrix.of x.2 - 1 : Matrix ι ι ℂ) i j‖ < δ} with hS
  have hSm : MeasurableSet S := by
    refine IsOpen.measurableSet ?_
    simp only [hS, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_lt ?_ continuous_const
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, transpose_apply, of_apply]
    fun_prop
  have hdetc : Continuous fun a : ι → ι → ℂ => ‖(Matrix.of a).det‖ :=
    (Continuous.matrix_det continuous_id).norm
  set F : (ι → ι → ℂ) × (κ → ι → ℂ) → ENNReal := S.indicator
    (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ (2 * (Fintype.card ι + Fintype.card κ) + k))⁻¹)
    with hF
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ hSm
    exact (((hdetc.measurable.comp measurable_fst).pow_const _).inv).ennreal_ofReal
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : κ → ι → ℂ) 1,
      ‖(1 - (Matrix.of z)ᴴ * Matrix.of z : Matrix ι ι ℂ).det‖ ≤ M := by
    refine (isCompact_closedBall _ _).exists_bound_of_continuousOn (Continuous.continuousOn ?_)
    refine Continuous.matrix_det (continuous_const.sub ?_)
    have : Continuous fun z : κ → ι → ℂ => Matrix.of z := continuous_id
    exact this.matrix_conjTranspose.matrix_mul this
  set V := volume (Metric.closedBall (0 : ι → ℂ) (Real.sqrt 2)) with hV
  set K : ENNReal := ENNReal.ofReal (2 ^ Fintype.card ι * (1 + 2 * M) ^ k) * V ^ Fintype.card ι
    with hK
  have hKt : K < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.pow_lt_top measure_closedBall_lt_top)
  set T : (ι → ι → ℂ) → (κ → ι → ℂ) → ENNReal := fun a z =>
    ENNReal.ofReal (‖(Matrix.of a)ᵀ.det‖ ^ (2 * Fintype.card κ)) *
      F (a, fun c => z c ᵥ* (Matrix.of a)ᵀ) with hT
  have hTm : Measurable (Function.uncurry T) := by
    refine Measurable.mul ?_ (hFm.comp (Continuous.measurable ?_))
    · simp only [det_transpose]
      exact ((hdetc.measurable.comp measurable_fst).pow_const _).ennreal_ofReal
    · refine continuous_fst.prodMk (continuous_pi fun c => continuous_pi fun i => ?_)
      simp only [vecMul, dotProduct, transpose_apply, of_apply]
      fun_prop
  have step1 : ∀ a, ∫⁻ c, F (a, c) ≤ ∫⁻ z, T a z := by
    intro a
    by_cases ha : (Matrix.of a)ᵀ.det = 0
    · have : ∀ c, F (a, c) = 0 := fun c => Set.indicator_of_notMem
        (fun h : (a, c) ∈ S => det_ne_zero_of_form _ _ (hnear _ h).2.2 ha) _
      simp [this]
    · exact (lintegral_mul_right _ ha (fun c => F (a, c))
        (hFm.comp measurable_prodMk_left)).le
  have step2 : ∀ z, ∫⁻ a, T a z ≤ (Metric.closedBall (0 : κ → ι → ℂ) 1).indicator (fun _ => K) z := by
    intro z
    set P : Matrix ι ι ℂ := 1 - (Matrix.of z)ᴴ * Matrix.of z with hP
    have hG : ∀ a : ι → ι → ℂ, (Matrix.of a)ᵀᴴ * (Matrix.of a)ᵀ -
        (Matrix.of fun c => z c ᵥ* (Matrix.of a)ᵀ)ᴴ * (Matrix.of fun c => z c ᵥ* (Matrix.of a)ᵀ) =
        (Matrix.of a)ᵀᴴ * P * (Matrix.of a)ᵀ := by
      intro a
      have : (Matrix.of fun c => z c ᵥ* (Matrix.of a)ᵀ) = Matrix.of z * (Matrix.of a)ᵀ := rfl
      rw [this, hP, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hdet : ∀ a : ι → ι → ℂ, (a, fun c => z c ᵥ* (Matrix.of a)ᵀ) ∈ S →
        1 / 2 ≤ ‖(Matrix.of a).det‖ ^ 2 * ‖P.det‖ := by
      intro a ha
      have := (hnear _ ha).1
      simp only [hG] at this
      rw [det_mul, det_mul, det_conjTranspose, det_transpose, norm_mul, norm_mul, norm_star] at this
      linarith
    by_cases hex : ∃ a : ι → ι → ℂ, (a, fun c => z c ᵥ* (Matrix.of a)ᵀ) ∈ S
    swap
    · have : ∀ a, T a z = 0 := fun a => by
        simp only [hT, hF]
        rw [Set.indicator_of_notMem (fun h => hex ⟨a, h⟩), mul_zero]
      simp [this]
    obtain ⟨a₀, ha₀⟩ := hex
    have hform := (hnear _ ha₀).2.2
    have hA₀ := det_ne_zero_of_form _ _ hform
    simp only [hG] at hform
    have hherm : P.IsHermitian := isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)
    have hre : ∀ v, 0 ≤ (star v ⬝ᵥ P *ᵥ v).re := by
      intro v
      obtain ⟨t, rfl⟩ : ∃ t, v = (Matrix.of a₀)ᵀ *ᵥ t := ⟨(Matrix.of a₀)ᵀ⁻¹ *ᵥ v, by
        rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hA₀), one_mulVec]⟩
      have := hform t
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec] at this
      exact le_trans (by positivity) this
    have hpsd : P.PosSemidef := PosSemidef.of_dotProduct_mulVec_nonneg hherm fun v =>
      Complex.nonneg_iff.2 ⟨hre v, (hherm.im_star_dotProduct_mulVec_self v).symm⟩
    have hPpos : 0 < ‖P.det‖ := by
      refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
      have := hdet a₀ ha₀
      rw [← h] at this; norm_num at this
    have hz : z ∈ Metric.closedBall (0 : κ → ι → ℂ) 1 := by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun c => ?_
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
      have h1 := hre (Pi.single j 1)
      rw [hP, sub_mulVec, dotProduct_sub, Complex.sub_re, form_gram_re, one_mulVec,
        star_dot_self_re] at h1
      have h2 : ∑ i, ‖(Pi.single j (1 : ℂ) : ι → ℂ) i‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single j] <;> simp +contextual
      have h3 := Finset.single_le_sum (f := fun c => ‖(Matrix.of z *ᵥ Pi.single j 1) c‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
      have h4 : (Matrix.of z *ᵥ Pi.single j 1) c = z c j := by simp
      simp only [h4] at h3
      have := norm_nonneg (z c j)
      nlinarith
    rw [Set.indicator_of_mem hz]
    have hMz : ‖P.det‖ ≤ M := hM z hz
    set E : Set (ι → ℂ) := {x | (star x ⬝ᵥ P *ᵥ x).re ≤ 2} with hE
    have hpt : ∀ a, T a z ≤ (Set.univ.pi fun _ : ι => E).indicator
        (fun _ => ENNReal.ofReal ((2 * ‖P.det‖) ^ Fintype.card ι * (1 + 2 * M) ^ k)) a := by
      intro a
      by_cases ha : (a, fun c => z c ᵥ* (Matrix.of a)ᵀ) ∈ S
      swap
      · simp only [hT, hF]
        rw [Set.indicator_of_notMem ha, mul_zero]; exact zero_le
      have hmem : a ∈ Set.univ.pi fun _ : ι => E := by
        intro j _
        have h1 := ha j j
        simp only [hG] at h1
        have h2 : ((Matrix.of a)ᵀᴴ * P * (Matrix.of a)ᵀ) j j = star (a j) ⬝ᵥ P *ᵥ a j := by
          rw [Matrix.mul_assoc]; rfl
        rw [Matrix.sub_apply, h2, one_apply_eq] at h1
        have h3 := Complex.re_le_norm (star (a j) ⬝ᵥ P *ᵥ a j - 1)
        rw [Complex.sub_re, Complex.one_re] at h3
        show _ ≤ (2 : ℝ)
        linarith
      simp only [hT, hF]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ha, ← ENNReal.ofReal_mul (by positivity),
        det_transpose]
      refine ENNReal.ofReal_le_ofReal (weight_le ?_ (hdet a ha) hMz _ _ _)
      have := det_ne_zero_of_form _ _ (hnear _ ha).2.2
      rw [det_transpose] at this
      exact norm_pos_iff.2 this
    refine (lintegral_mono hpt).trans ((lintegral_indicator_const_le _ _).trans ?_)
    rw [volume_pi_pi, Finset.prod_const, Finset.card_univ]
    have hvol := volume_ellipsoid_le 2 hpsd (norm_pos_iff.1 hPpos)
    have hM0 : 0 ≤ M := hPpos.le.trans hMz
    refine (mul_le_mul_right (pow_le_pow_left' hvol _) _).trans (le_of_eq ?_)
    rw [hK, mul_pow (ENNReal.ofReal _), ← mul_assoc, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [mul_pow, inv_pow]
    field_simp
  calc ∫⁻ x, F x = ∫⁻ a, ∫⁻ c, F (a, c) := lintegral_prod _ hFm.aemeasurable
    _ ≤ ∫⁻ a, ∫⁻ z, T a z := lintegral_mono step1
    _ = ∫⁻ z, ∫⁻ a, T a z := lintegral_lintegral_swap hTm.aemeasurable
    _ ≤ _ := lintegral_mono step2
    _ ≤ K * volume (Metric.closedBall (0 : κ → ι → ℂ) 1) := lintegral_indicator_const_le _ _
    _ < ⊤ := ENNReal.mul_lt_top hKt measure_closedBall_lt_top
end GlobalTheory.MinorInt
