-- Prove2me | solution 1 for GlobalTheory.isZero_cechComplex_homology
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:43.249362+00:00
-- url     : https://prove2.me/submissions/e3644d69-ed2b-4777-aff7-d729e8bd90bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_isZero_cechComplex_X

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution [Fintype ι] (A : Cube.{v} ι R) {p : ℕ}
    (h : Fintype.card ι ≤ p) : IsZero ((cechComplex A).homology p) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_cechComplex_X A h)
end GlobalTheory
