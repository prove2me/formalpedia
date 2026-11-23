-- Prove2me | solution 1 for GlobalTheory.TopForm.dForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:55.580845+00:00
-- url     : https://prove2.me/submissions/78c26769-6f8b-4972-9ce0-b8ed8965c560

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
namespace GlobalTheory.TopForm
theorem _root_.solution (α : k →+* A) (f : Fin D → A) :
    dForm α f = exteriorPower.ιMulti A D fun i => dFun α (f i) := rfl
end GlobalTheory.TopForm
