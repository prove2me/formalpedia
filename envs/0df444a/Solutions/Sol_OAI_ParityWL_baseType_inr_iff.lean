-- Prove2me | solution 1 for OAI.ParityWL.baseType_inr_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:17:28.913779+00:00
-- url     : https://prove2.me/submissions/85fc3fec-4b92-4547-9f91-3b90ea98f283

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/BaseLabels.lean:L29-L41
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.baseType_inr_iff. The node keeps its source
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

lemma baseType_inr_iff (v : BaseVertex C) (h : Helper t) :
    baseType v = .inr h ↔ ∃ q : C.Label h.1.1, v = .inr ⟨h, q⟩ := by
  cases v with
  | inr x =>
    rcases x with ⟨j, d⟩
    constructor
    · intro h'
      have hj : j = h := Sum.inr.inj h'
      subst j
      exact ⟨d, rfl⟩
    · rintro ⟨e, he⟩
      exact congrArg baseType he
  | inl x => simp [baseType]

end BaseLabels

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.baseType_inr_iff := @_root_.OAI.ParityWL.baseType_inr_iff
