-- Prove2me | solution 1 for GlobalTheory.cechCyclesIso_hom_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:24.028022+00:00
-- url     : https://prove2.me/submissions/e4670d61-1844-46c8-a7cc-7190dc38d0a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_cochainCyclesIsoKer_hom_subtype

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
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    (cechCyclesIso A p).hom ≫ ModuleCat.ofHom (LinearMap.ker (Cube.d A (p + 1))).subtype =
      (cechComplex A).iCycles p :=
  cochainCyclesIsoKer_hom_subtype (cechComplex A) p (Cube.d A (p + 1)) (cechComplex_d A p)
end GlobalTheory
