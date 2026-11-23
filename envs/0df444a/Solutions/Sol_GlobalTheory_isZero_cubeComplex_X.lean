-- Prove2me | solution 1 for GlobalTheory.isZero_cubeComplex_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:59.620381+00:00
-- url     : https://prove2.me/submissions/6d1e593e-385c-44bb-a65c-3d644850c920

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution [Fintype ι] (A : Cube.{v} ι R) {p : ℕ} (h : Fintype.card ι < p) :
    IsZero ((cubeComplex A).X p) :=
  haveI := Cube.subsingleton_term A h
  ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Cube.Term A p))
end GlobalTheory
