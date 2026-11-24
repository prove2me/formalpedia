-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.finsum_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:32:56.462606+00:00
-- url     : https://prove2.me/submissions/57260537-6561-4192-86e3-4e9cad1759e8

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumTwoStageDescentUnipotent
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
open Classical
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution {X Y : Type} (f : X → ℂ) (Q : X → Prop) (R : Y → X → Prop)
    (hf : (Function.support f).Finite) (hQ : ∀ x, Q x ↔ ∃ y, R y x)
    (hu : ∀ x y y', R y x → R y' x → y = y') :
    (Function.support fun y => ∑ᶠ x, if R y x then f x else 0).Finite ∧
      (∑ᶠ x, if Q x then f x else 0) = ∑ᶠ y, ∑ᶠ x, if R y x then f x else 0 := by
  have hS : ∀ (T : X → Prop) [DecidablePred T],
      (∑ᶠ x, if T x then f x else 0) = ∑ x ∈ hf.toFinset, if T x then f x else 0 := by
    intro T _
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    exact hx (by simp [h0])
  have hfin : ∀ x, (Function.support fun y => if R y x then f x else 0).Finite := by
    intro x
    refine Set.Subsingleton.finite fun y hy y' hy' => hu x y y' ?_ ?_
    · by_contra h; exact hy (by simp [h])
    · by_contra h; exact hy' (by simp [h])
  simp only [hS]
  constructor
  · refine (hf.biUnion fun x _ => hfin x).subset fun y hy => ?_
    obtain ⟨x, hx, hx'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    exact Set.mem_biUnion (hf.mem_toFinset.1 hx) hx'
  · rw [finsum_sum_comm _ _ fun x _ => hfin x]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Q x
    · obtain ⟨y, hy⟩ := (hQ x).1 hx
      rw [finsum_eq_single _ y, if_pos hx, if_pos hy]
      intro y' hy'
      exact if_neg fun h => hy' (hu x y' y h hy)
    · rw [if_neg hx]
      symm
      exact finsum_eq_zero_of_forall_eq_zero fun y => if_neg fun h => hx ((hQ x).2 ⟨y, h⟩)
end GlobalTheory.SatakeWeyl
