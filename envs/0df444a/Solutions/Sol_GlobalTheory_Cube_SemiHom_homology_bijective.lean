-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.homology_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:20:49.667616+00:00
-- url     : https://prove2.me/submissions/aaa074ca-2cb5-4ff4-a68c-93ef75aa5b02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Theorems.Thm_GlobalTheory_Cube_SemiHom_term_bijective
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
theorem _root_.solution
    (h : ∀ s : Finset ι, s.Nonempty → Function.Bijective (ψ.app s))
    (p : ℕ) : Function.Bijective (ψ.homology p) := by
  have hT := ψ.term_bijective h
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := _root_.GlobalTheory.cechClass_surjective A p z
    rw [_root_.GlobalTheory.Cube.SemiHom.homology_cechClass] at hz
    cases p with
    | zero =>
      rw [_root_.GlobalTheory.cechClass_zero_eq_zero_iff] at hz ⊢
      have hx := congrArg Subtype.val hz
      rw [_root_.GlobalTheory.Cube.SemiHom.coe_cocycle] at hx
      apply Subtype.ext
      apply (hT 0).1
      rw [hx]
      simp
    | succ p =>
      rw [_root_.GlobalTheory.cechClass_succ_eq_zero_iff] at hz ⊢
      obtain ⟨y, hy⟩ := hz
      obtain ⟨y', rfl⟩ := (hT p).2 y
      refine ⟨y', (hT (p + 1)).1 ?_⟩
      rw [_root_.GlobalTheory.Cube.SemiHom.term_d, hy, _root_.GlobalTheory.Cube.SemiHom.coe_cocycle]
  · intro z
    obtain ⟨y, rfl⟩ := _root_.GlobalTheory.cechClass_surjective B p z
    obtain ⟨x', hx'⟩ := (hT p).2 y.1
    have hker : x' ∈ LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1)) := by
      rw [LinearMap.mem_ker]
      apply (hT (p + 1)).1
      rw [_root_.GlobalTheory.Cube.SemiHom.term_d, hx', map_zero]
      exact LinearMap.mem_ker.1 y.2
    refine ⟨_root_.GlobalTheory.cechClass A p ⟨x', hker⟩, ?_⟩
    rw [_root_.GlobalTheory.Cube.SemiHom.homology_cechClass]
    congr 1
    exact Subtype.ext hx'
end _root_.GlobalTheory.Cube.SemiHom
end GlobalTheory.Cube.SemiHom
