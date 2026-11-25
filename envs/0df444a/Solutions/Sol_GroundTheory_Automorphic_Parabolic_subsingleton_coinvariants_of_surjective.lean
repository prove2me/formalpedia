-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.subsingleton_coinvariants_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:56:33.949812+00:00
-- url     : https://prove2.me/submissions/aaf04efd-3a86-4c81-b49b-1808609de250

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {H : Subgroup G}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Surjective f)
    (h : Subsingleton (Representation.Coinvariants (ρ.comp H.subtype))) :
    Subsingleton (Representation.Coinvariants (σ.comp H.subtype)) := by
  have hker : Representation.Coinvariants.ker (ρ.comp H.subtype) ≤
      (Representation.Coinvariants.ker (σ.comp H.subtype)).comap f.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, x⟩, rfl⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, SetLike.mem_coe,
      Submodule.mem_comap, map_sub, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Representation.IntertwiningMap.isIntertwining]
    exact Representation.Coinvariants.sub_mem_ker (ρ := σ.comp H.subtype) u (f x)
  have hzero : ∀ y : W, Representation.Coinvariants.mk (σ.comp H.subtype) y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact (Representation.Coinvariants.mk_eq_zero _).2 (hker
      ((Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)))
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  rw [hzero a, hzero b]
end GroundTheory.Automorphic.Parabolic
