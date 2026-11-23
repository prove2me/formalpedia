-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.homology_naturality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:10.045796+00:00
-- url     : https://prove2.me/submissions/74f8d9c8-eb01-4e2f-82bc-77df29433b09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Theorems.Thm_GlobalTheory_homologyMap_cechClass
import Theorems.Thm_GlobalTheory_Cube_termMap_mem_ker
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
theorem _root_.solution (ψ' : _root_.GlobalTheory.Cube.SemiHom f A' B') (α : A ⟶ A')
    (β : B ⟶ B')
    (h : ∀ s, s.Nonempty → ∀ x, ψ'.app s ((α.app s).hom x) =
      (β.app s).hom (ψ.app s x)) (p : ℕ)
    (x : (_root_.GlobalTheory.cechComplex A).homology p) :
    ψ'.homology p
        ((HomologicalComplex.homologyMap (_root_.GlobalTheory.cechComplexMap α) p).hom x) =
      (HomologicalComplex.homologyMap (_root_.GlobalTheory.cechComplexMap β) p).hom
        (ψ.homology p x) := by
  obtain ⟨x, rfl⟩ := _root_.GlobalTheory.cechClass_surjective A p x
  rw [_root_.GlobalTheory.homologyMap_cechClass α p x
      ⟨_root_.GlobalTheory.Cube.termMap α (p + 1) x.1, _root_.GlobalTheory.Cube.termMap_mem_ker α x.2⟩ rfl,
    _root_.GlobalTheory.Cube.SemiHom.homology_cechClass, _root_.GlobalTheory.Cube.SemiHom.homology_cechClass,
    _root_.GlobalTheory.homologyMap_cechClass β p _
      ⟨_root_.GlobalTheory.Cube.termMap β (p + 1) (ψ.cocycle (p + 1) x).1,
        _root_.GlobalTheory.Cube.termMap_mem_ker β (ψ.cocycle (p + 1) x).2⟩ rfl]
  congr 1
  apply Subtype.ext
  funext s
  simp only [_root_.GlobalTheory.Cube.SemiHom.coe_cocycle, _root_.GlobalTheory.Cube.SemiHom.term_apply, _root_.GlobalTheory.Cube.termMap_apply]
  exact h s.1 (Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos p)) (x.1 s)
end _root_.GlobalTheory.Cube.SemiHom
end GlobalTheory.Cube.SemiHom
