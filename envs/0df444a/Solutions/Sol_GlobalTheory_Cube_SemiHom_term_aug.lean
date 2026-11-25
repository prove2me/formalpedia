-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.term_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:40:25.292307+00:00
-- url     : https://prove2.me/submissions/c6986855-7e25-4b53-a6e6-9c2b2859b8c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective

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
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
open GlobalTheory.Cube GlobalTheory.Cube.SemiHom
variable {f : R →+* S} {A A' : Cube.{v} ι R} {B B' : Cube.{v'} ι S} (ψ : Cube.SemiHom f A B)
omit [LinearOrder ι]
namespace GlobalTheory.Cube.SemiHom
theorem _root_.solution (a : A.obj ∅) : ψ.term 1 (Cube.aug A a) = Cube.aug B (ψ.app ∅ a) :=
  funext fun _ => ψ.app_res _ a
end GlobalTheory.Cube.SemiHom
