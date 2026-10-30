-- Prove2me | solution 1 for OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_query
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:05:44.12935+00:00
-- url     : https://prove2.me/submissions/bc3d5943-0fdc-43f0-9a8c-bc48a443ab32

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_parameter_query

section
-- module Solutions.OAIQ5_T6.TypeSystem_Equivalence
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode.Formed

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem class_query_oai (t : Fin 3) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (B.query L.code KY.code KP.code (ChannelCode.classTag t) v)
      (B.propertyC L.code KY.code KP.code t v) := by
  fin_cases t
  · exact H.parameter_query KY KP 1 hv mv
  · exact H.parameter_query KY KP 2 hv mv
  · exact H.parameter_query KY KP 3 hv mv

end SpecializedCode.Formed

end PureTypeSystem.Labelled

end OAI
end

theorem solution.{u} : type_of% @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_query_oai.{u} := @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_query_oai.{u}
