-- Prove2me | solution 2 for GlobalTheory.cechComplexMap_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:57.689989+00:00
-- url     : https://prove2.me/submissions/9b71ba79-1eea-446b-a6cc-a2a4fae50bdd

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
    (cechComplexMap φ).f p = ModuleCat.ofHom (Cube.termMap φ (p + 1)) := rfl
end GlobalTheory
