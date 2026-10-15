-- Prove2me | solution 1 for OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:27:52.341721+00:00
-- url     : https://prove2.me/submissions/2956543b-e4d5-4b9c-90a7-e1668a39898c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean:L51-L63
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Theorems.Thm_OAI_Paper320_Tournament_card_internalEdges

-- ---- from OAI.Combinatorics.Sensitivity.TournamentCounts ----
namespace OAI

/-! The exact internal edge count and the small gate-candidate bound. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

theorem sum_outdegree_eq (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter (T.Adj i)).card = (T.internalEdges I).card := by
  simp only [internalEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem card_le_three_of_outdegree_le_one (I : Finset (Fin k))
    (h : ∀ i ∈ I, (I.filter (T.Adj i)).card ≤ 1) : I.card ≤ 3 := by
  have hsum := Finset.sum_le_sum h
  have hc : I.card.choose 2 ≤ I.card := by
    rw [← T.card_internalEdges, ← T.sum_outdegree_eq]
    simpa only [Finset.sum_const_nat, mul_one] using hsum
  have hdouble : I.card * (I.card - 1) ≤ 2 * I.card + 1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have h4 : 4 ≤ I.card := by omega
  have ht : I.card - 1 + 1 = I.card := by omega
  nlinarith

end Paper320.Tournament

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical BigOperators
variable {k : ℕ} (T : Tournament k)

theorem solution (I : Finset (Fin k))
    (h : ∀ i ∈ I, (I.filter (T.Adj i)).card ≤ 1) : I.card ≤ 3 := by
  first
    | exact OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one I h
    | exact OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one T I h
    | exact OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one
    | (apply OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one <;> assumption)
    | (intros; apply OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one <;> assumption)
