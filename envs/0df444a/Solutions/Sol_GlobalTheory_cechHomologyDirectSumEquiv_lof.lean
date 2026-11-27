-- Prove2me | solution 1 for GlobalTheory.cechHomologyDirectSumEquiv_lof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:57.724203+00:00
-- url     : https://prove2.me/submissions/ea2a5564-e08b-4b4d-9275-8343fb008254

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
    (x : (cechComplex (A k)).homology p) :
    cechHomologyDirectSumEquiv A p
        (DirectSum.lof R κ (fun k => (cechComplex (A k)).homology p) k x) =
      (HomologicalComplex.homologyMap (cechComplexMap (Cube.directSumIncl A k)) p).hom x :=
  DirectSum.toModule_lof (M := fun k => (cechComplex (A k)).homology p) R k x
end GlobalTheory
