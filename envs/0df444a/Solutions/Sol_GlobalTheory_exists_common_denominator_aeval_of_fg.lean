-- Prove2me | solution 1 for GlobalTheory.exists_common_denominator_aeval_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:49.65805+00:00
-- url     : https://prove2.me/submissions/26d9b1ea-987d-4284-a164-5dc75f5a62e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommonDenominatorAevalOfFg
import Theorems.Thm_GlobalTheory_exists_denominator_aeval_elem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O E A : Type) [CommRing O] [IsDomain O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] (g : A) (h : ∀ x : A, ∃ p : E[X], aeval g p = x)
    (S : Submodule O A) (hS : S.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  classical
  obtain ⟨s, rfl⟩ := hS
  have key : ∃ c : O, c ≠ 0 ∧ ∀ x ∈ s, ∃ p : O[X], aeval g p = c • x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a s _ ih =>
      obtain ⟨c, hc, hs⟩ := ih
      obtain ⟨d, hd, p, hp⟩ := exists_denominator_aeval_elem O E A g h a
      refine ⟨c * d, mul_ne_zero hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨c • p, by rw [map_smul, hp, mul_smul]⟩
      · obtain ⟨q, hq⟩ := hs x hx
        exact ⟨d • q, by rw [map_smul, hq, mul_comm, mul_smul]⟩
  obtain ⟨c, hc, hs⟩ := key
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add, hp, hq, smul_add]⟩
  | smul a x _ hx =>
    obtain ⟨p, hp⟩ := hx
    exact ⟨a • p, by rw [map_smul, hp, smul_comm]⟩
end GlobalTheory
