-- Prove2me | solution 1 for GlobalTheory.Flasque.freeSheafMap_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:08.804799+00:00
-- url     : https://prove2.me/submissions/49e35e5b-8e13-4b3a-9307-c36427d3f48a

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
theorem _root_.solution {V U : C} (i : V ⟶ U) :
    (freeSheafMap J i).hom.app (op V) (freeSheafGen J V) =
      (freeSheaf J U).obj.map i.op (freeSheafGen J U) := by
  have h1 := congr(($(toSheafify_naturality J
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)).app (op V)) (FreeAbelianGroup.of (𝟙 V)))
  have h2 := congr($((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).naturality i.op)
    (FreeAbelianGroup.of (𝟙 U)))
  refine h1.symm.trans (Eq.trans ?_ h2)
  change (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op V) (FreeAbelianGroup.of (𝟙 V ≫ i)) =
    (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op V) (FreeAbelianGroup.of (i ≫ 𝟙 U))
  simp
end GlobalTheory.Flasque
