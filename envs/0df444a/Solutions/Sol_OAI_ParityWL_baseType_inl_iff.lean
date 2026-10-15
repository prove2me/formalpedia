-- Prove2me | solution 1 for OAI.ParityWL.baseType_inl_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:16:12.338997+00:00
-- url     : https://prove2.me/submissions/d2169ae5-7a6a-4102-8d0c-833e60576237

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/BaseLabels.lean:L15-L27
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.baseType_inl_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels

-- ---- from OAI.Combinatorics.ParityLifts.BaseLabels ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section BaseLabels

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t)

lemma baseType_inl_iff (v : BaseVertex C) (i : Fin t) :
    baseType v = .inl i ↔ ∃ d : C.Domain i, v = .inl ⟨i, d⟩ := by
  cases v with
  | inl x =>
    rcases x with ⟨j, d⟩
    constructor
    · intro h
      have hj : j = i := Sum.inl.inj h
      subst j
      exact ⟨d, rfl⟩
    · rintro ⟨e, he⟩
      exact congrArg baseType he
  | inr x => simp [baseType]

end BaseLabels

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.baseType_inl_iff := @_root_.OAI.ParityWL.baseType_inl_iff
