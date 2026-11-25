-- Prove2me | solution 1 for GlobalTheory.Cube.res_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:21.92284+00:00
-- url     : https://prove2.me/submissions/27b8b990-f981-411f-bd40-8f6f38b6e72d

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
open TensorProduct
variable {ι : Type} {R : Type u} [CommRing R]
variable (S : Type u') [CommRing S] [Algebra R S]
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : Cube.{v} ι R) {s t : Finset ι} (h : s ⊆ t) :
    Cube.res (Cube.baseChange S A) h = (Cube.res A h).baseChange S := rfl
end Cube
end GlobalTheory
