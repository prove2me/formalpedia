-- Prove2me | solution 1 for OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_query
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:10:08.181666+00:00
-- url     : https://prove2.me/submissions/b13055ac-5204-4efb-a0be-36a3efbf2960

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

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem edge_query_oai (t : Bool) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (B.query L.code KY.code KP.code (ChannelCode.edgeTag t) v)
      (B.propertyE L.code KY.code KP.code (if t then 2 else 1) v) := by
  cases t
  · exact H.parameter_query KY KP 4 hv mv
  · exact H.parameter_query KY KP 5 hv mv
end

end SpecializedCode.Formed

end PureTypeSystem.Labelled

end OAI
end

theorem solution.{u} : type_of% @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_query_oai.{u} := @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_query_oai.{u}
