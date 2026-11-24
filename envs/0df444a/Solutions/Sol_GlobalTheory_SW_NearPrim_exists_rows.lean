-- Prove2me | solution 1 for GlobalTheory.SW.NearPrim.exists_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:44:31.722298+00:00
-- url     : https://prove2.me/submissions/1b38745b-caef-4fe8-b1d6-c218e8e14930

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_min

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.NearPrim
namespace GlobalTheory.SW.NearPrim
theorem _root_.solution {E : Type} [Field E] [NumberField E] {k : ℕ} (L : AddSubgroup (Fin k → E))
    (hO : ∀ s : Fin k → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L) (d : ℤ) (hd : d ≠ 0)
    (hL : ∀ s ∈ L, ∀ i, IsIntegral ℤ ((d : E) * s i)) (C : ℝ)
    (hC : ∀ x : E, ∃ y : E, IsIntegral ℤ y ∧ ‖canonicalEmbedding E (x - y)‖ ≤ C) (i : Fin k) :
    ∃ a ∈ L, (∀ j, i < j → a j = 0) ∧ a i ≠ 0 ∧ (∀ j, ‖canonicalEmbedding E (a j)‖ ≤ max 1 C) ∧
      ∀ s ∈ L, (∀ j, i < j → s j = 0) → s i ≠ 0 →
        ‖canonicalEmbedding E (a i)‖ ≤ ‖canonicalEmbedding E (s i)‖ := by
  classical
  obtain ⟨α, ⟨hα0, a, haL, ha0, rfl⟩, hα1, hmin⟩ := exists_min
    {x : E | x ≠ 0 ∧ ∃ s ∈ L, (∀ j, i < j → s j = 0) ∧ s i = x} d hd
    (by rintro _ ⟨-, s, hs, -, rfl⟩; exact hL s hs i)
    ⟨one_ne_zero, Pi.single i 1, hO _ (fun j => by
      by_cases h : j = i
      · subst h; simpa using isIntegral_one
      · simpa [h] using isIntegral_zero), fun j hj => by simp [hj.ne'], by simp⟩
  choose y hy hyC using hC
  refine ⟨a - fun j => if j < i then y (a j) else 0, L.sub_mem haL (hO _ fun j => ?_),
    fun j hj => ?_, ?_, fun j => ?_, fun s hs hs0 hsi => ?_⟩
  · split_ifs
    · exact hy _
    · exact isIntegral_zero
  · simp [ha0 j hj, not_lt.2 hj.le]
  · simpa using hα0
  · rcases lt_trichotomy j i with h | rfl | h
    · simp only [Pi.sub_apply, if_pos h]
      exact (hyC _).trans (le_max_right _ _)
    · simp only [Pi.sub_apply, lt_irrefl, if_false, sub_zero]
      exact hα1.trans (le_max_left _ _)
    · simp [ha0 j h, not_lt.2 h.le]
  · simp only [Pi.sub_apply, lt_irrefl, if_false, sub_zero]
    exact hmin _ ⟨hsi, s, hs, hs0, rfl⟩
end GlobalTheory.SW.NearPrim
