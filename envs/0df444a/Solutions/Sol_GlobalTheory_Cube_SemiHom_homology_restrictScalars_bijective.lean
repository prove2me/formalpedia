-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.homology_restrictScalars_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:40:20.809013+00:00
-- url     : https://prove2.me/submissions/bdfbd3d1-5e9a-4314-ae4d-3f10472ec737

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_bijective

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
namespace GlobalTheory.Cube.SemiHom
theorem _root_.solution (f : R →+* S) (B : Cube.{v} ι S) (p : ℕ) :
    Function.Bijective ((restrictScalars f B).homology p) :=
  homology_bijective _ (fun _ _ => Function.bijective_id) p
end GlobalTheory.Cube.SemiHom
