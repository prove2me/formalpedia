-- Prove2me | solution 1 for GlobalTheory.cubeFunctor_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:24.483784+00:00
-- url     : https://prove2.me/submissions/1dbfccfe-8b2d-4651-b3ed-33d18a90ee80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_Cube_term_shortExact

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
theorem _root_.solution (S : ShortComplex (Cube.{v} ι R))
    (hS : ∀ s : Finset ι, (S.map ((evaluation _ _).obj s)).ShortExact) :
    (S.map (cubeFunctor ι R)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p =>
    Cube.term_shortExact S p fun s _ => hS s
end GlobalTheory
