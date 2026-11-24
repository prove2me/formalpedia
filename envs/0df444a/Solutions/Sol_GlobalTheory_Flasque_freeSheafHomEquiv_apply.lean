-- Prove2me | solution 1 for GlobalTheory.Flasque.freeSheafHomEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:53.503455+00:00
-- url     : https://prove2.me/submissions/20c47961-7ecd-4d33-8573-3037685ae190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
namespace GlobalTheory.Flasque
theorem _root_.solution (U : C) (F : Sheaf J AddCommGrpCat.{v}) (f : freeSheaf J U ⟶ F) :
    freeSheafHomEquiv U F f = f.hom.app (op U) (freeSheafGen J U) := rfl
end GlobalTheory.Flasque
