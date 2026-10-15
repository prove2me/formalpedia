-- Prove2me | solution 1 for OAI.ParityWL.template_positive_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:28:26.876695+00:00
-- url     : https://prove2.me/submissions/b4f32ccb-a5fa-4b67-9207-dea16f9a2bb7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/TagSizes.lean:L69-L84
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.template_positive_degree. The node keeps its source
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

-- ---- from OAI.Combinatorics.ParityLifts.TagSizes ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section TagSizes

open scoped Classical

variable {I : Type} [Fintype I]

lemma template_positive_degree {t : ℕ} (ht : 2 ≤ t) (a : TemplateVertex t) :
    ((template t).neighborSet a).Nonempty := by
  cases a with
  | inl i =>
    by_cases hi : i.val = 0
    · refine ⟨.inl ⟨1, by omega⟩, ?_⟩
      change i ≠ ⟨1, by omega⟩
      intro h
      have hh := congrArg Fin.val h
      change i.val = 1 at hh
      omega
    · refine ⟨.inl ⟨0, by omega⟩, ?_⟩
      change i ≠ ⟨0, by omega⟩
      intro h
      exact hi (congrArg Fin.val h)
  | inr h => exact ⟨.inl h.1.1.1.1, Or.inl rfl⟩

end TagSizes

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.template_positive_degree := @_root_.OAI.ParityWL.template_positive_degree
