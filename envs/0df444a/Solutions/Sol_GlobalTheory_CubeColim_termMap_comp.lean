-- Prove2me | solution 1 for GlobalTheory.CubeColim.termMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:49.526435+00:00
-- url     : https://prove2.me/submissions/491926b2-a196-4ab9-960e-6528d0bcbd9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Filter
open GlobalTheory
open GlobalTheory.CubeColim
variable {ι : Type} [LinearOrder ι] [Fintype ι]
namespace GlobalTheory.CubeColim
theorem _root_.solution {X Y Z : Cube.{0} ι ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℕ)
    (x : Cube.Term X p) :
    Cube.termMap (f ≫ g) p x = Cube.termMap g p (Cube.termMap f p x) := rfl
end GlobalTheory.CubeColim
