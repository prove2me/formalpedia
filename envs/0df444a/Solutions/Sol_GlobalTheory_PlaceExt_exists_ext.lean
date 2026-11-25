-- Prove2me | solution 1 for GlobalTheory.PlaceExt.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:42:22.044777+00:00
-- url     : https://prove2.me/submissions/1c88bb40-ae6e-4af4-b367-f39ded61c7c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
import Theorems.Thm_GlobalTheory_PlaceExt_wt_eq_of_min
import Theorems.Thm_GlobalTheory_PlaceExt_wt_add_of_min
import Theorems.Thm_GlobalTheory_PlaceExt_wt_mul_of_min
import Theorems.Thm_GlobalTheory_PlaceExt_le_val_pow_mul
import Theorems.Thm_GlobalTheory_PlaceExt_min_eq_of_le_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PlaceExt
variable {L A : Type*} [Field L] [CommRing A]
variable (ι : L →+* A) (S : Subring A) (π : L) (w : AddValuation L (WithTop ℤ))
namespace GlobalTheory.PlaceExt
theorem _root_.solution (hπ0 : π ≠ 0) (hπS : ι π ∈ S) (hw : 1 ≤ w π)
    (hS : ∀ l, ι l ∈ S → 0 ≤ w l)
    (happ : ∀ (x : A) (m : ℕ), ∃ l, ∃ b ∈ S, x - ι l = ι π ^ m * b)
    (hden : ∀ x : A, ∃ n : ℕ, ι π ^ n * x ∈ S) :
    ∃ u : AddValuation A (WithTop ℤ), (∀ l, u (ι l) = w l) ∧ ∀ b ∈ S, 0 ≤ u b := by
  classical
  let C : A → ℕ → L → Prop := fun x m l => ∃ b ∈ S, x - ι l = ι π ^ m * b
  have hmono : ∀ x m m' l, m ≤ m' → C x m' l → C x m l := by
    rintro x m m' l hm ⟨b, hb, h⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact ⟨ι π ^ k * b, S.mul_mem (S.pow_mem hπS k) hb, by rw [h]; ring⟩
  have hcl : ∀ x m l l', C x m l → C x m l' → min (w l) (m : ℤ) = min (w l') (m : ℤ) := by
    rintro x m l l' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    apply min_eq_of_le_sub
    have hp : π ^ m ≠ 0 := pow_ne_zero _ hπ0
    have e1 : l - l' = π ^ m * ((π ^ m)⁻¹ * (l - l')) := by field_simp
    rw [e1]
    apply le_val_pow_mul w hw
    apply hS
    have e2 : ι ((π ^ m)⁻¹ * (l - l')) = b' - b := by
      have : ι (l - l') = ι (π ^ m) * (b' - b) := by
        rw [map_sub, map_pow]; linear_combination h' - h
      rw [map_mul, this, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hp, map_one, one_mul]
    rw [e2]
    exact S.sub_mem hb' hb
  let f : A → WithTop ℤ := fun x =>
    if h : ∃ ml : ℕ × L, C x ml.1 ml.2 ∧ w ml.2 < (ml.1 : ℤ) then w h.choose.2 else ⊤
  have hf : ∀ x m l, C x m l → min (f x) (m : ℤ) = min (w l) (m : ℤ) := by
    intro x m l hC
    by_cases h : ∃ ml : ℕ × L, C x ml.1 ml.2 ∧ w ml.2 < (ml.1 : ℤ)
    · have e : f x = w h.choose.2 := dif_pos h
      obtain ⟨h1, h2⟩ := h.choose_spec
      rw [e]
      generalize h.choose = ml at h1 h2
      obtain ⟨m', l'⟩ := ml
      rcases le_total m m' with hm | hm
      · exact hcl x m _ _ (hmono x m m' l' hm h1) hC
      · have h3 := hcl x m' _ _ h1 (hmono x m' m l hm hC)
        dsimp only at h2 ⊢
        have : w l' = w l := by grind
        rw [this]
    · have e : f x = ⊤ := dif_neg h
      have : ¬ w l < (m : ℤ) := fun h' => h ⟨(m, l), hC, h'⟩
      rw [e, min_eq_right le_top, min_eq_right (not_lt.1 this)]
  have hι : ∀ l, f (ι l) = w l := fun l =>
    wt_eq_of_min fun m => hf _ m l ⟨0, S.zero_mem, by simp⟩
  refine ⟨AddValuation.of f ?_ ?_ ?_ ?_, hι, ?_⟩
  · simpa using hι 0
  · simpa using hι 1
  · intro x y
    apply wt_add_of_min
    intro m
    obtain ⟨l, b, hb, h⟩ := happ x m
    obtain ⟨l', b', hb', h'⟩ := happ y m
    refine ⟨w l, w l', w (l + l'), hf x m l ⟨b, hb, h⟩, hf y m l' ⟨b', hb', h'⟩,
      hf _ m _ ⟨b + b', S.add_mem hb hb', ?_⟩, w.map_add _ _⟩
    rw [map_add]; linear_combination h + h'
  · intro x y
    obtain ⟨n1, hx⟩ := hden x
    obtain ⟨n2, hy⟩ := hden y
    apply wt_mul_of_min (n1 + n2)
    intro m
    obtain ⟨l, b, hb, h⟩ := happ x (m + (n1 + n2))
    obtain ⟨l', b', hb', h'⟩ := happ y (m + (n1 + n2))
    refine ⟨w l, w l', hf x _ l ⟨b, hb, h⟩, hf y _ l' ⟨b', hb', h'⟩, ?_⟩
    rw [← w.map_mul]
    refine hf _ m _ ⟨ι π ^ n1 * b * (ι π ^ n2 * y) + ι π ^ n2 * b' * (ι π ^ n1 * x)
      - ι π ^ (m + 2 * (n1 + n2)) * b * b', ?_, ?_⟩
    · exact S.sub_mem (S.add_mem (S.mul_mem (S.mul_mem (S.pow_mem hπS _) hb) hy)
        (S.mul_mem (S.mul_mem (S.pow_mem hπS _) hb') hx))
        (S.mul_mem (S.mul_mem (S.pow_mem hπS _) hb) hb')
    · have e1 : ι l = x - ι π ^ (m + (n1 + n2)) * b := by linear_combination -h
      have e2 : ι l' = y - ι π ^ (m + (n1 + n2)) * b' := by linear_combination -h'
      rw [map_mul, e1, e2]; ring
  · intro b hb
    have := hf b 0 0 ⟨b, hb, by simp⟩
    simp only [AddValuation.map_zero, le_top, min_eq_right, min_eq_right_iff] at this
    simpa using this
end GlobalTheory.PlaceExt
