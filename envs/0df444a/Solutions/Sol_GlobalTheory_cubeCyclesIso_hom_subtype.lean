-- Prove2me | solution 1 for GlobalTheory.cubeCyclesIso_hom_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:04.460017+00:00
-- url     : https://prove2.me/submissions/40134048-1f82-4aa5-8176-8a9b456a3061

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
    (cubeCyclesIso A p).hom ≫ ModuleCat.ofHom (LinearMap.ker (Cube.d A p)).subtype =
      (cubeComplex A).iCycles p :=
  cochainCyclesIsoKer_hom_subtype (cubeComplex A) p (Cube.d A p) (cubeComplex_d A p)
end GlobalTheory
