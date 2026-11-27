-- Prove2me | solution 2 for GlobalTheory.cubeComplexMap_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:37:34.671671+00:00
-- url     : https://prove2.me/submissions/fc1538c9-e812-44be-bed2-65a75d13adda

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
theorem _root_.solution {A B : Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ) :
    (cubeComplexMap φ).f p = ModuleCat.ofHom (Cube.termMap φ p) := rfl
end GlobalTheory
