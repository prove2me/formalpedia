-- Prove2me | solution 1 for GlobalTheory.Cube.restrictDeg_totalD_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:53:33.370088+00:00
-- url     : https://prove2.me/submissions/8a8dfced-efa1-4d77-a6aa-6f958002bbbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]
variable [LinearOrder ι]
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s) :
    restrictDeg A (p + 1) (totalD A x) = d A p (restrictDeg A p x) :=
  funext fun t => (d_apply_eq_totalD A (restrictDeg A p x) x (fun _ => rfl) t).symm
end GlobalTheory.Cube
