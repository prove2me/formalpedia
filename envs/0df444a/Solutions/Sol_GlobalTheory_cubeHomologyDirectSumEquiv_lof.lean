-- Prove2me | solution 1 for GlobalTheory.cubeHomologyDirectSumEquiv_lof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:58.494221+00:00
-- url     : https://prove2.me/submissions/2a867426-6009-432a-a822-04aec8b57da1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open DirectSum
variable {R : Type u} [Ring R] {κ : Type} [DecidableEq κ]
variable {ι : Type}
variable [LinearOrder ι]
variable [Finite ι]
namespace GlobalTheory
theorem _root_.solution (A : κ → Cube.{v} ι R) (p : ℕ) (k : κ)
    (x : (cubeComplex (A k)).homology p) :
    cubeHomologyDirectSumEquiv A p
        (DirectSum.lof R κ (fun k => (cubeComplex (A k)).homology p) k x) =
      (HomologicalComplex.homologyMap (cubeComplexMap (Cube.directSumIncl A k)) p).hom x :=
  DirectSum.toModule_lof (M := fun k => (cubeComplex (A k)).homology p) R k x
end GlobalTheory
