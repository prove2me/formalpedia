-- Prove2me | solution 1 for GlobalTheory.cechAugHomology_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:05.302982+00:00
-- url     : https://prove2.me/submissions/248b09d7-41c3-4b0b-929e-7c4d6b8592c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Theorems.Thm_GlobalTheory_cechAugHomology_comp


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
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (A : _root_.GlobalTheory.Cube.{v} ι R) (a : A.obj ∅) :
    (_root_.GlobalTheory.cechAugHomology A).hom a =
      _root_.GlobalTheory.cechClass A 0
        ⟨_root_.GlobalTheory.Cube.aug A a, _root_.GlobalTheory.Cube.d_aug A a⟩ := by
  rw [cechClass_zero_eq_iso_inv]
  have hinj : Function.Injective (_root_.GlobalTheory.cechHomologyZeroIso A).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  have h := congrArg (fun g => ModuleCat.Hom.hom g a)
    (_root_.GlobalTheory.cechAugHomology_comp A)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    Submodule.subtype_apply] at h
  apply Subtype.ext
  rw [h]
  simp
end _root_.GlobalTheory
end GlobalTheory
