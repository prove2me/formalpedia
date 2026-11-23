-- Prove2me | solution 1 for GlobalTheory.isZero_cubeComplex_homology
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:59.45369+00:00
-- url     : https://prove2.me/submissions/3a848f30-54f8-402f-bdf9-3925c7053785

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_isZero_cubeComplex_X

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
    (h : Fintype.card ι < p) : IsZero ((cubeComplex A).homology p) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_cubeComplex_X A h)
end GlobalTheory
