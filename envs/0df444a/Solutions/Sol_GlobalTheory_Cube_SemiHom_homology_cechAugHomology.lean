-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.homology_cechAugHomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:02:54.342168+00:00
-- url     : https://prove2.me/submissions/78d2d5c1-b023-4287-90da-7fbeff60e425

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Theorems.Thm_GlobalTheory_cechAugHomology_apply
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass

set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
open GlobalTheory.Cube GlobalTheory.Cube.SemiHom
variable {f : R →+* S} {A A' : Cube.{v} ι R} {B B' : Cube.{v'} ι S} (ψ : Cube.SemiHom f A B)
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B)
namespace GlobalTheory.Cube.SemiHom
namespace _root_.GlobalTheory.Cube.SemiHom
theorem _root_.solution (a : A.obj ∅) :
    ψ.homology 0 ((_root_.GlobalTheory.cechAugHomology A).hom a) =
      (_root_.GlobalTheory.cechAugHomology B).hom (ψ.app ∅ a) := by
  rw [_root_.GlobalTheory.cechAugHomology_apply, _root_.GlobalTheory.cechAugHomology_apply, _root_.GlobalTheory.Cube.SemiHom.homology_cechClass]
  congr 1
  apply Subtype.ext
  funext s
  rw [_root_.GlobalTheory.Cube.SemiHom.coe_cocycle, _root_.GlobalTheory.Cube.SemiHom.term_apply]
  unfold _root_.GlobalTheory.Cube.aug
  simp [_root_.GlobalTheory.Cube.SemiHom.app_res]
end _root_.GlobalTheory.Cube.SemiHom
end GlobalTheory.Cube.SemiHom
