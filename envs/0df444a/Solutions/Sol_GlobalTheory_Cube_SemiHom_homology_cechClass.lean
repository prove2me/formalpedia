-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.homology_cechClass
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:38.265853+00:00
-- url     : https://prove2.me/submissions/e3c0a5f9-030c-4f6f-aa70-cecb47f64db8

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
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B)
namespace GlobalTheory.Cube.SemiHom
namespace _root_.GlobalTheory.Cube.SemiHom
theorem _root_.solution (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1))) :
    ψ.homology p (_root_.GlobalTheory.cechClass A p x) =
      _root_.GlobalTheory.cechClass B p (ψ.cocycle (p + 1) x) := by
  have e : ((_root_.GlobalTheory.cechClass A p).quotKerEquivOfSurjective
      (_root_.GlobalTheory.cechClass_surjective A p)).symm (_root_.GlobalTheory.cechClass A p x) = Submodule.Quotient.mk x :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp only [_root_.GlobalTheory.Cube.SemiHom.homology, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e]
  rfl
end _root_.GlobalTheory.Cube.SemiHom
end GlobalTheory.Cube.SemiHom
