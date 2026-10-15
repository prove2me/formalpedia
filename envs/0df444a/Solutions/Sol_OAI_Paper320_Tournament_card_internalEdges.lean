-- Prove2me | solution 1 for OAI.Paper320.Tournament.card_internalEdges
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:26:44.122035+00:00
-- url     : https://prove2.me/submissions/01169cff-70fc-4a9b-beeb-8fe09eaa6258

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean:L19-L45
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.Tournament.card_internalEdges. The node keeps its source
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

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h

theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h

theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.TournamentCounts ----
namespace OAI

/-! The exact internal edge count and the small gate-candidate bound. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

theorem card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  let U := T.internalEdges I
  let V := (I ×ˢ I).filter fun p => T.Adj p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact T.not_adj_reverse (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,T.ne_of_adj h⟩
      · exact ⟨hi,hj,(T.ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      exact (T.adj_or_reverse hne).imp (fun h => ⟨⟨hi,hj⟩,h⟩) (fun h => ⟨⟨hi,hj⟩,h⟩)
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

end Paper320.Tournament

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical BigOperators
variable {k : ℕ} (T : Tournament k)

theorem solution (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  first
    | exact OAI.Paper320.Tournament.card_internalEdges I
    | exact OAI.Paper320.Tournament.card_internalEdges T I
    | exact OAI.Paper320.Tournament.card_internalEdges
    | (apply OAI.Paper320.Tournament.card_internalEdges <;> assumption)
    | (intros; apply OAI.Paper320.Tournament.card_internalEdges <;> assumption)
