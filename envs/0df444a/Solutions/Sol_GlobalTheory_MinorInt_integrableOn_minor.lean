-- Prove2me | solution 1 for GlobalTheory.MinorInt.integrableOn_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:51.851792+00:00
-- url     : https://prove2.me/submissions/ad20f7a6-f87c-46e9-ae7e-ec6c25863968

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
import Theorems.Thm_GlobalTheory_MinorInt_slice_volume
import Theorems.Thm_GlobalTheory_MinorInt_columns_integral
import Theorems.Thm_GlobalTheory_MinorInt_lintegral_cutEquiv

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
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ IntegrableOn
      (fun y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ => (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹)
      {y | ∀ a b, ‖((Matrix.of y)ᵀ * Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) *
        (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ)) a b‖
          < δ₀} volume := by
  obtain ⟨δ₁, hδ₁, K, hK, hslice⟩ := slice_volume ι κ
  obtain ⟨δ₂, hδ₂, hint⟩ := columns_integral ι κ n hn
  refine ⟨min (min δ₁ δ₂) 1, by positivity, ?_⟩
  set U := {y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ | ∀ a b, ‖((Matrix.of y)ᵀ *
    Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) *
        (Matrix.of y).map conj - Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ)) a b‖
          < min (min δ₁ δ₂) 1} with hU
  have hent : ∀ (y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ) r s, ((Matrix.of y)ᵀ *
      Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) * (Matrix.of y).map conj) r s =
      ∑ a, y (Sum.inl a) r * conj (y (Sum.inl a) s) -
        ∑ c, y (Sum.inr c) r * conj (y (Sum.inr c) s) := by
    intro y r s
    rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, one_apply, sub_eq_add_neg, neg_ite]
  have hUm : MeasurableSet U := by
    refine IsOpen.measurableSet ?_
    simp only [hU, Set.setOf_forall, Matrix.sub_apply, hent]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_lt ?_ continuous_const
    fun_prop
  have hfm : Measurable fun y : (ι ⊕ κ) → (ι ⊕ κ) → ℂ =>
      (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹ := by
    refine ((Continuous.measurable (Continuous.norm (Continuous.matrix_det ?_))).pow_const _).inv
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => by positivity),
    ← lintegral_indicator hUm]
  set S := {x : (ι → ι → ℂ) × (κ → ι → ℂ) | ∀ i j, ‖((Matrix.of x.1)ᵀᴴ * (Matrix.of x.1)ᵀ -
        (Matrix.of x.2)ᴴ * Matrix.of x.2 - 1 : Matrix ι ι ℂ) i j‖ < min δ₁ δ₂} with hS
  set B : (ι → ι → ℂ) × (κ → ι → ℂ) → Set (ι ⊕ κ → ℂ) := fun x =>
    {v | (∀ i, ‖((Matrix.of x.1)ᵀᴴ *ᵥ (v ∘ Sum.inl) - (Matrix.of x.2)ᴴ *ᵥ (v ∘ Sum.inr)) i‖ ≤ 1) ∧
        ∑ c, ‖v (Sum.inr c)‖ ^ 2 - ∑ a, ‖v (Sum.inl a)‖ ^ 2 ≤ 2} with hB
  set g : ((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ) → ENNReal := fun w =>
    (Set.univ.pi fun _ : κ => B w.1).indicator
      (fun _ => S.indicator (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ n)⁻¹) w.1) w.2 with hg
  let e := cutEquiv ι κ
  have hpt : ∀ y, U.indicator
      (fun y => ENNReal.ofReal (‖(Matrix.of y).toBlocks₁₁.det‖ ^ n)⁻¹) y ≤ g (e y) := by
    intro y
    by_cases hy : y ∈ U
    swap
    · rw [Set.indicator_of_notMem hy]; exact zero_le
    have hy' : ∀ r s, ‖∑ a, y (Sum.inl a) r * conj (y (Sum.inl a) s) -
        ∑ c, y (Sum.inr c) r * conj (y (Sum.inr c) s) -
        Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (-1 : Matrix κ κ ℂ) r s‖ < min (min δ₁ δ₂) 1 := by
      intro r s
      have := hy r s
      rwa [Matrix.sub_apply, hent] at this
    have h1 : (e y).1 ∈ S := by
      intro i j
      refine lt_of_eq_of_lt ?_ ((hy' (Sum.inl i) (Sum.inl j)).trans_le (min_le_left _ _))
      simp [e, cutEquiv, Matrix.mul_apply]
    have h2 : (e y).2 ∈ Set.univ.pi fun _ : κ => B (e y).1 := by
      intro c _
      refine ⟨fun i => ?_, ?_⟩
      · refine le_of_eq_of_le ?_ ((hy' (Sum.inl i) (Sum.inr c)).le.trans (min_le_right _ _))
        simp [e, cutEquiv, mulVec, dotProduct]
      · have h3 := (hy' (Sum.inr c) (Sum.inr c)).le.trans (min_le_right _ _)
        have h4 := (Complex.abs_re_le_norm _).trans h3
        simp only [Complex.mul_conj', fromBlocks_apply₂₂, Matrix.neg_apply, one_apply_eq,
          ← Complex.ofReal_pow, ← Complex.ofReal_sum, Complex.sub_re, Complex.ofReal_re,
          Complex.neg_re, Complex.one_re] at h4
        have h5 := (abs_le.1 h4).1
        have : ∀ r, ‖(e y).2 c r‖ = ‖y r (Sum.inr c)‖ := fun r => by simp [e, cutEquiv]
        simp only [this]
        linarith
    simp only [hg]
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem h2, Set.indicator_of_mem h1]
    have h6 : Matrix.of (e y).1.1 = (Matrix.of y).toBlocks₁₁ᴴ := by
      ext i j; simp [e, cutEquiv, toBlocks₁₁]
    rw [h6, det_conjTranspose, norm_star]
  obtain ⟨c, hc, hchg⟩ := lintegral_cutEquiv ι κ
  refine (lintegral_mono hpt).trans_lt ?_
  refine (hchg g).trans_lt (ENNReal.mul_lt_top hc ?_)
  refine (lintegral_prod_le g).trans_lt ?_
  have hKt : K ^ Fintype.card κ < ⊤ := ENNReal.pow_lt_top hK
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hint hKt)
  rw [← lintegral_mul_const' _ _ hKt.ne]
  refine lintegral_mono fun x => (lintegral_indicator_const_le (Set.univ.pi fun _ : κ => B x)
    (S.indicator (fun x => ENNReal.ofReal (‖(Matrix.of x.1).det‖ ^ n)⁻¹) x)).trans ?_
  by_cases hx : x ∈ S
  swap
  · simp only [Set.indicator_of_notMem hx, zero_mul]; exact zero_le
  rw [volume_pi_pi, Finset.prod_const, Finset.card_univ]
  refine mul_le_mul' ?_ (pow_le_pow_left'
    (hslice _ _ fun i j => (hx i j).trans_le (min_le_left _ _)) _)
  exact Set.indicator_le_indicator_of_subset
    (fun x hx i j => (hx i j).trans_le (min_le_right _ _)) (fun _ => zero_le) x
end GlobalTheory.MinorInt
