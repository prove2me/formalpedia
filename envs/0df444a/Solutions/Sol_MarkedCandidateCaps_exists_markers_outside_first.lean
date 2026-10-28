-- Prove2me | solution 1 for MarkedCandidateCaps.exists_markers_outside_first
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:42:10.014436+00:00
-- url     : https://prove2.me/submissions/e38da9a0-a12e-42ed-99d7-ccf835185a87

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace CandidateCoherence
end CandidateCoherence
namespace GuardAugmentation
end GuardAugmentation
namespace ResidualCaps
end ResidualCaps
namespace TournamentHighRows
end TournamentHighRows
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace MarkedCandidateCaps
end MarkedCandidateCaps
open MarkedCandidateCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
variable {V X : Type} [Fintype V] [DecidableEq V]

/-- Select eligible markers outside T first. This proves the exact correction
    max(0,m-outside) used by the numerical prefix-cap formula. -/
theorem solution (T E : Finset V) (m : ℕ) (hm : m ≤ E.card) :
    ∃ M : Finset V, M ⊆ E ∧ M.card = m ∧ (T ∩ M).card ≤ m - (E \ T).card := by
  by_cases hout : m ≤ (E \ T).card
  · obtain ⟨M,hMO,hMc⟩ := Finset.exists_subset_card_eq hout
    refine ⟨M,hMO.trans Finset.sdiff_subset,hMc,?_⟩
    have hdis : Disjoint T M := by
      apply Finset.disjoint_left.mpr
      intro v hvT hvM
      exact (Finset.mem_sdiff.mp (hMO hvM)).2 hvT
    have hempty : T ∩ M = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdis
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · have houtle : (E \ T).card ≤ m := by omega
    have hsplit := Finset.card_sdiff_add_card_inter E T
    have hneed : m - (E \ T).card ≤ (E ∩ T).card := by omega
    obtain ⟨J,hJI,hJc⟩ := Finset.exists_subset_card_eq hneed
    let O := E \ T
    let M := O ∪ J
    have hME : M ⊆ E := by
      apply Finset.union_subset
      · exact Finset.sdiff_subset
      · exact hJI.trans Finset.inter_subset_left
    have hdis : Disjoint O J := by
      apply Finset.disjoint_left.mpr
      intro v hvO hvJ
      exact (Finset.mem_sdiff.mp hvO).2 (Finset.mem_inter.mp (hJI hvJ)).2
    have hMc : M.card = m := by
      have hc : M.card = O.card + J.card := Finset.card_union_of_disjoint hdis
      dsimp [O] at hc
      omega
    have hsub : T ∩ M ⊆ J := by
      intro v hv
      obtain ⟨hvT,hvM⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp hvM with hvO | hvJ
      · exact False.elim ((Finset.mem_sdiff.mp hvO).2 hvT)
      · exact hvJ
    refine ⟨M,hME,hMc,?_⟩
    exact (Finset.card_le_card hsub).trans (le_of_eq hJc)
end
