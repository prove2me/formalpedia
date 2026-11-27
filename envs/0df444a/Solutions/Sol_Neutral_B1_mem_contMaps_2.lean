-- Prove2me | solution 2 for Neutral.B1.mem_contMaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:56.421364+00:00
-- url     : https://prove2.me/submissions/16f30b58-7bd3-4320-b88f-1c6be85679e7

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (R M)
variable {R M}
namespace Neutral.B1
theorem _root_.solution {X : Type*} [TopologicalSpace X] (f : X → M) :
    f ∈ contMaps R M X ↔ Continuous f := Iff.rfl
end Neutral.B1
