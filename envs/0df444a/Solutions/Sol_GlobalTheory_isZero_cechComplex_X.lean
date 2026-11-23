-- Prove2me | solution 1 for GlobalTheory.isZero_cechComplex_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:32.114413+00:00
-- url     : https://prove2.me/submissions/c3db46ed-6e3f-47ef-ba6f-1e40066b1284

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
theorem _root_.solution [Fintype ι] (A : Cube.{v} ι R) {p : ℕ} (h : Fintype.card ι ≤ p) :
    IsZero ((cechComplex A).X p) :=
  isZero_cubeComplex_X A (Nat.lt_succ_of_le h)
end GlobalTheory
