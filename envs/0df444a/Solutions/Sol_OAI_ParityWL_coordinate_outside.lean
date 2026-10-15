-- Prove2me | solution 1 for OAI.ParityWL.coordinate_outside
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:29:38.821351+00:00
-- url     : https://prove2.me/submissions/d880d16a-b34d-44eb-8802-cc987b617fc8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Detection.lean:L52-L64
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.coordinate_outside. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection

-- ---- from OAI.Combinatorics.ParityLifts.Detection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section Detection

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

lemma coordinate_outside {k : ℕ} (hk : 4 ≤ k) (a b c : Fin k) :
    ∃ i : Fin k, i ≠ a ∧ i ≠ b ∧ i ≠ c := by
  have hc : ({a, b, c} : Finset (Fin k)).card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans (by
      have hh := Finset.card_insert_le b ({c} : Finset (Fin k))
      simp only [Finset.card_singleton] at hh
      omega)
  have hlt : ({a, b, c} : Finset (Fin k)).card < Fintype.card (Fin k) := by
    simpa only [Fintype.card_fin] using hc.trans_lt (by omega)
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (hlt.trans_eq (Finset.card_univ.symm))
  refine ⟨i, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hi

end Detection

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.coordinate_outside := @_root_.OAI.ParityWL.coordinate_outside
