-- Prove2me | solution 1 for GlobalTheory.Flasque.freeSheafHomEquiv_freeSheafMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:29:50.780799+00:00
-- url     : https://prove2.me/submissions/ca4ad733-e812-4d4e-b507-0875d16eceae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Theorems.Thm_GlobalTheory_Flasque_freeSheafHomEquiv_apply
import Theorems.Thm_GlobalTheory_Flasque_freeSheafMap_gen

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
theorem _root_.solution {V U : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (f : freeSheaf J U ⟶ F) :
    freeSheafHomEquiv V F (freeSheafMap J i ≫ f) = F.obj.map i.op (freeSheafHomEquiv U F f) := by
  rw [freeSheafHomEquiv_comp, freeSheafHomEquiv_apply, freeSheafMap_gen, freeSheafHomEquiv_apply]
  exact congr($(f.hom.naturality i.op) (freeSheafGen J U))
end GlobalTheory.Flasque
