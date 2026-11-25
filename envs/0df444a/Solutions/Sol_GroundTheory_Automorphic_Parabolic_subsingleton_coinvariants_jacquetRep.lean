-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.subsingleton_coinvariants_jacquetRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:17.661004+00:00
-- url     : https://prove2.me/submissions/474a0803-02f6-4c77-a619-b3093466d44c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_sqrtModular_leviIncl_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_inv_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {β γ : Fin n → ℕ}
    (hβγ : ∀ i j, β j < β i → γ j < γ i) (h : Subsingleton (JacquetModule F n γ π)) :
    Subsingleton (Representation.Coinvariants
      ((jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)) := by
  set q' := Representation.Coinvariants.mk
    ((jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)
  set qβ := Representation.Coinvariants.mk (π.comp (unipotentRadical F n β).subtype)
  have hβeq : ∀ i j, γ i = γ j → β i = β j := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hβγ j i hlt
      omega
    · have := hβγ i j hlt
      omega
  have hker : Representation.Coinvariants.ker (π.comp (unipotentRadical F n γ).subtype) ≤
      LinearMap.ker (q' ∘ₗ qβ) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, w⟩, rfl⟩
    obtain ⟨huP, hu1⟩ := mem_unipotentRadical.1 u.2
    have huβ : (u : GL (Fin n) F) ∈ blockUpper F n β := fun i j hij => huP (hβγ i j hij)
    set p : blockUpper F n β := ⟨u, huβ⟩
    set m := leviProj F n β p
    have hmN : ((m : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ := by
      refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
      · show ((m : levi F n β) : GL (Fin n) F) i j = 0
        rw [leviProj_apply]
        split_ifs
        · exact huP hij
        · rfl
      · rw [leviProj_apply, if_pos (hβeq i j hij)]
        exact hu1 i j hij
    have hn' := leviProj_inv_mul_mem p
    have hu : (u : GL (Fin n) F) = ((m : levi F n β) : GL (Fin n) F) *
        (((leviIncl m)⁻¹ * p : blockUpper F n β) : GL (Fin n) F) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      MonoidHom.coe_comp, Subgroup.coe_subtype, map_sub]
    rw [hu, map_mul, Module.End.mul_apply, mk_apply_levi, mk_apply_of_mem π _ hn',
      sqrtModular_leviIncl_of_mem m hmN, one_smul, sub_eq_zero]
    exact Representation.Coinvariants.mk_self_apply
      (ρ := (jacquetRep F n β π).comp (leviUnipotent F n β γ).subtype)
      ⟨m, Subgroup.mem_subgroupOf.2 hmN⟩ (qβ w)
  have hzero : ∀ x : V, q' (qβ x) = 0 := by
    intro x
    have hx : x ∈ Representation.Coinvariants.ker (π.comp (unipotentRadical F n γ).subtype) :=
      (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact hker hx
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  exact (hzero a).trans (hzero b).symm
end GroundTheory.Automorphic.Parabolic
