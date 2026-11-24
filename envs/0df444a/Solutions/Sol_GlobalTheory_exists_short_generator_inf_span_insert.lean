-- Prove2me | solution 1 for GlobalTheory.exists_short_generator_inf_span_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:44.306153+00:00
-- url     : https://prove2.me/submissions/40e9da8d-596b-4ac2-b194-374859b2d291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
import Theorems.Thm_GlobalTheory_exists_add_orthogonal_norm_sq_le
import Theorems.Thm_GlobalTheory_exists_mem_span_int_norm_sub_sq_le_sum
import Theorems.Thm_GlobalTheory_finite_mem_and_norm_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} (v : ι → E) (s : Finset ι) (hv : ∀ i ∈ s, v i ∈ L) {u : E} (huL : u ∈ L)
    (hu : u ∉ span ℝ (v '' s)) :
    ∃ b : E, L ⊓ (span ℝ (insert u (v '' s))).restrictScalars ℤ =
        span ℤ {b} ⊔ L ⊓ (span ℝ (v '' s)).restrictScalars ℤ ∧
      ‖b‖ ^ 2 ≤ ‖u‖ ^ 2 + (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  set W := span ℝ (v '' s) with hW
  set C := ‖u‖ ^ 2 + (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 with hC
  obtain ⟨p, hp, q, hq, hupq, hle⟩ := exists_add_orthogonal_norm_sq_le W u
  have hZ : span ℤ (v '' s) ≤ L := span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact hv i hi)

  have red : ∀ (t : ℝ) (y : E), y ∈ W → t • u + y ∈ L → 0 < t → t ≤ 1 →
      ∃ y' ∈ W, t • u + y' ∈ L ∧ ‖t • u + y'‖ ^ 2 ≤ C := by
    intro t y hy hL h0 h1
    have hy' : y + t • p ∈ W := add_mem hy (smul_mem _ _ hp)
    obtain ⟨w, hw, hwle⟩ := exists_mem_span_int_norm_sub_sq_le_sum v s hy'
    have hwR : w ∈ W := span_subset_span ℤ ℝ _ hw
    refine ⟨y - w, sub_mem hy hwR, by rw [← add_sub_assoc]; exact sub_mem hL (hZ hw), ?_⟩
    have he : t • u + (y - w) = (y + t • p - w) + t • q := by rw [hupq]; module
    rw [he, norm_add_sq_real,
      Submodule.inner_right_of_mem_orthogonal (sub_mem hy' hwR) (smul_mem _ _ hq),
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul h2 hle (sq_nonneg _) zero_le_one]

  have uniq : ∀ (t t' : ℝ) (y y' : E), y ∈ W → y' ∈ W → t • u + y = t' • u + y' → t = t' := by
    intro t t' y y' hy hy' h
    by_contra hne
    apply hu
    have : u = (t - t')⁻¹ • (y' - y) := by
      rw [eq_inv_smul_iff₀ (sub_ne_zero.2 hne), sub_smul, sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]; exact smul_mem _ _ (sub_mem hy' hy)
  let T : Set ℝ := {t | 0 < t ∧ t ≤ 1 ∧ ∃ y ∈ W, t • u + y ∈ L ∧ ‖t • u + y‖ ^ 2 ≤ C}
  have hT : T.Finite := by
    choose! f hfW hfL hfC using fun (t : ℝ) (ht : t ∈ T) => ht.2.2
    refine Set.Finite.of_injOn (f := fun t => t • u + f t) ?_ ?_ (finite_mem_and_norm_le L √C)
    · exact fun t ht => ⟨hfL t ht, Real.le_sqrt_of_sq_le (hfC t ht)⟩
    · exact fun t ht t' ht' h => uniq _ _ _ _ (hfW t ht) (hfW t' ht') h
  have hT1 : (1 : ℝ) ∈ T :=
    ⟨one_pos, le_rfl, red 1 0 (zero_mem _) (by simpa using huL) one_pos le_rfl⟩
  obtain ⟨t₀, ⟨h0, h1, y₀, hy₀, hbL, hbC⟩, hmin⟩ := Set.exists_min_image T id hT ⟨1, hT1⟩
  refine ⟨t₀ • u + y₀, le_antisymm ?_ (sup_le ?_ ?_), hbC⟩
  · rintro x ⟨hxL, hx⟩
    obtain ⟨t, y, hy, rfl⟩ := mem_span_insert.1 hx
    set k : ℤ := ⌊t / t₀⌋ with hk
    have hk1 : k * t₀ ≤ t := (le_div_iff₀ h0).1 (Int.floor_le _)
    have hk2 : t < (k + 1) * t₀ := (div_lt_iff₀ h0).1 (Int.lt_floor_add_one _)
    have he : t • u + y - k • (t₀ • u + y₀) = (t - k * t₀) • u + (y - (k : ℝ) • y₀) := by
      rw [← Int.cast_smul_eq_zsmul ℝ]; module
    have hyW : y - (k : ℝ) • y₀ ∈ W := sub_mem hy (smul_mem _ _ hy₀)
    have hL' : (t - k * t₀) • u + (y - (k : ℝ) • y₀) ∈ L := he ▸ sub_mem hxL (smul_mem _ _ hbL)
    have hz : t - k * t₀ = 0 := by
      by_contra hne
      have hpos : 0 < t - k * t₀ := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      have hlt : t - k * t₀ < t₀ := by linarith
      exact absurd (hmin _ ⟨hpos, by linarith, red _ _ hyW hL' hpos (by linarith)⟩) (not_le.2 hlt)
    rw [hz, zero_smul, zero_add] at he hL'
    rw [eq_add_of_sub_eq' he]
    exact add_mem (mem_sup_left (smul_mem _ _ (mem_span_singleton_self _)))
      (mem_sup_right ⟨hL', hyW⟩)
  · rw [span_singleton_le_iff_mem]
    exact ⟨hbL, mem_span_insert.2 ⟨_, _, hy₀, rfl⟩⟩
  · exact inf_le_inf_left _ fun x hx => span_mono (Set.subset_insert _ _) hx
end GlobalTheory
