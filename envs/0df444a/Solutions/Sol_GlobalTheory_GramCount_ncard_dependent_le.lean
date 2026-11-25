-- Prove2me | solution 1 for GlobalTheory.GramCount.ncard_dependent_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:12:23.539661+00:00
-- url     : https://prove2.me/submissions/d6f6986b-9d06-4266-8211-9c5731646e4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardDependentVectorsAffineGramLe
import Theorems.Thm_GlobalTheory_GramCount_depSet_subset_mul
import Theorems.Thm_GlobalTheory_GramCount_dep_unit_or_idem
import Theorems.Thm_GlobalTheory_GramCount_dep_idem_eq
import Theorems.Thm_GlobalTheory_GramCount_ncard_depSet_idem_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B]
namespace GlobalTheory.GramCount
theorem _root_.solution : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) →
    ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n →
    ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B),
    Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
      ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by
  intro B _ _ c hc ω hω hf q hq2 hq k n hkn x hx g
  by_cases hex : ∃ ε : B, ε + c ε = 1 ∧ ε * c ε = 0
  · obtain ⟨ε, h1, h2⟩ := hex
    have hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
        ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆
        depSet c x g ε ∪ depSet c x g (c ε) := by
      rintro y ⟨hy, a, ha, hs⟩
      have hy' : y ∈ depSet c x g a := ⟨hy, hs⟩
      rcases dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb1, hb2⟩
      · left
        have := depSet_subset_mul c x g a (ε * b) hy'
        rwa [mul_assoc, hb, mul_one] at this
      · have := depSet_subset_mul c x g a b hy'
        rcases dep_idem_eq c hc hω hf h1 h2 hb1 hb2 with h | h
        · left; rwa [h] at this
        · right; rwa [h] at this
    have hA := ncard_depSet_idem_le c hc hω hq x hx g h1 h2
    have hB := ncard_depSet_idem_le c hc hω hq x hx g (ε := c ε) (by rw [hc, add_comm, h1])
      (by rw [hc, mul_comm, h2])
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    omega
  · have hsub : {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧
        ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ⊆
        (fun s : Fin k → B => ∑ i, s i • x i) '' Set.univ := by
      rintro y ⟨hy, a, ha, hs⟩
      have hy' : y ∈ depSet c x g a := ⟨hy, hs⟩
      rcases dep_unit_or_idem c hc hω hf ha with ⟨b, hb⟩ | ⟨b, hb⟩
      · obtain ⟨-, s, hs⟩ := depSet_subset_mul c x g a b hy'
        rw [hb, one_smul] at hs
        exact ⟨s, trivial, hs.symm⟩
      · exact absurd ⟨_, hb⟩ hex
    have h1 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (Set.ncard_image_le (Set.toFinite _))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, hq, Fintype.card_fin,
      ← pow_mul] at h1
    have h2 : q ^ (2 * k) ≤ q ^ n := Nat.pow_le_pow_right (by omega) hkn
    omega
end GlobalTheory.GramCount
