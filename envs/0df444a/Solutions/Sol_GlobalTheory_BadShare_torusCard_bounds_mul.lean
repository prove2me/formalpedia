-- Prove2me | solution 1 for GlobalTheory.BadShare.torusCard_bounds_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:05:19.210669+00:00
-- url     : https://prove2.me/submissions/524369ea-ab5c-422f-82a1-dfe1c27c17df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusCardBoundsAndMul
import Theorems.Thm_GlobalTheory_BadShare_degType_pos
import Theorems.Thm_GlobalTheory_BadShare_degType_sum
import Theorems.Thm_GlobalTheory_BadShare_prod_pow_sub_one_le
import Theorems.Thm_GlobalTheory_BadShare_ne_zero_natDegree_of_mem_sqSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], (∀ (N : ℕ), ∀ f ∈ sqSet g N, 0 < torusCard g f ∧ torusCard g f ≤ g ^ N ∧ (degType g f).sum = N ∧ ∀ d ∈ degType g f, 0 < d) ∧ (∀ h f : (ZMod g)[X], h ≠ 0 → f ≠ 0 → degType g (h * f) = degType g h + degType g f ∧ torusCard g (h * f) = torusCard g h * torusCard g f) ∧ ∀ P : (ZMod g)[X], Irreducible P → degType g P = {P.natDegree} ∧ torusCard g P = g ^ P.natDegree - 1 := by
  intro g hg
  refine ⟨fun N f hf => ?_, fun h f hh hf => ?_, fun P hP => ?_⟩
  · obtain ⟨h0, hN⟩ := ne_zero_natDegree_of_mem_sqSet g N f hf
    have hs : (degType g f).sum = N := (degType_sum g f h0).trans hN
    refine ⟨?_, ?_, hs, degType_pos g f⟩
    · unfold torusCard
      apply Multiset.prod_pos
      intro a ha
      obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.1 ha
      exact Nat.sub_pos_of_lt (Nat.one_lt_pow (degType_pos g f d hd).ne' hg.out.one_lt)
    · rw [← hs]
      exact prod_pow_sub_one_le g _
  · have hd : degType g (h * f) = degType g h + degType g f := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hh hf, Multiset.map_add]
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_add, Multiset.prod_add]
  · have hd : degType g P = {P.natDegree} := by
      unfold degType
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP, Multiset.map_singleton]
      congr 1
      exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (normalize_associated P))
    refine ⟨hd, ?_⟩
    unfold torusCard
    rw [hd, Multiset.map_singleton, Multiset.prod_singleton]
end GlobalTheory.BadShare
