-- Prove2me | solution 1 for GlobalTheory.exists_net_card_le_of_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:47.082842+00:00
-- url     : https://prove2.me/submissions/77622f3d-2056-4ee7-8a0c-27f73eb8e050

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNetCardLeOfSubsetClosedBall
import Theorems.Thm_GlobalTheory_finset_card_le_of_separated


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (S : Set E)
      (R δ : ℝ), 0 < δ → 0 ≤ R → S ⊆ closedBall 0 R →
      ∃ T : Finset E, (T : Set E) ⊆ S ∧ (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E ∧
        ∀ x ∈ S, ∃ t ∈ T, dist x t ≤ δ := by
  intro E _ _ _ S R δ hδ hR hS
  classical
  let P : Finset E → Prop := fun T =>
    (T : Set E) ⊆ S ∧ (T : Set E).Pairwise fun a b => δ ≤ dist a b
  have hb : ∀ T, P T → (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E := fun T hT =>
    finset_card_le_of_separated T hδ hR 0 (fun a ha => hS (hT.1 ha)) hT.2
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 + 2 * R / δ) ^ Module.finrank ℝ E)
  let Q : ℕ → Prop := fun n => ∃ T, P T ∧ T.card = n
  have hQ0 : Q 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨T, hT, hTc⟩ : Q (Nat.findGreatest Q N) := Nat.findGreatest_spec (Nat.zero_le N) hQ0
  refine ⟨T, hT.1, hb T hT, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxT : x ∉ T := fun h => by
    have := hcon x h
    rw [dist_self] at this
    linarith
  have hP : P (insert x T) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hT.1
    · rw [Finset.coe_insert]
      refine hT.2.insert fun b hb' _ => ⟨(hcon b hb').le, ?_⟩
      rw [dist_comm]
      exact (hcon b hb').le
  have hle : (insert x T).card ≤ N := by
    exact_mod_cast (hb _ hP).trans hN
  have := Nat.le_findGreatest (P := Q) hle ⟨_, hP, rfl⟩
  rw [Finset.card_insert_of_notMem hxT] at this
  omega
end GlobalTheory
