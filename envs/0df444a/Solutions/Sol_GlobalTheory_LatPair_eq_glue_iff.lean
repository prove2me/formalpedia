-- Prove2me | solution 1 for GlobalTheory.LatPair.eq_glue_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:03.64687+00:00
-- url     : https://prove2.me/submissions/825a55bb-63f0-464f-97c9-f9062a7095c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
variable {L L' : Submodule 𝒪[k] (n → k)} {e e' : n → k}
namespace GlobalTheory.LatPair
theorem _root_.solution (h : IsGlue L e) {P : Pair k n} : P = glue h ↔ P.ker = L ∧ P.HasVal e 1 :=
  ⟨fun hP => hP ▸ ⟨glue_ker h, glue_hasVal h⟩, fun hP => Pair.ext_ker (hP.1.trans (glue_ker h).symm) hP.2 (glue_hasVal h)⟩
end GlobalTheory.LatPair
