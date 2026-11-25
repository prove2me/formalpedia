-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_finset_span_jacquetRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:01:06.632172+00:00
-- url     : https://prove2.me/submissions/db48d15b-78b4-4a32-b039-4fc8760c6e6c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_hasBasis_nhds_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_inv_mul_mem
import Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_exists_blockUpper_mul_integralGL__7c8211cc1088


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsSmooth π) {v : V}
    (hv : Submodule.span ℂ (Set.range fun g : GL (Fin n) F => π g v) = ⊤) :
    ∃ S : Finset (JacquetModule F n β π),
      Submodule.span ℂ {x | ∃ m, ∃ s ∈ S, x = jacquetRep F n β π m s} = ⊤ := by
  classical
  obtain ⟨m₀, -, hm₀⟩ := (hasBasis_nhds_one F n).mem_iff.1 ((hπ v).mem_nhds (one_mem _))
  set K₀ := integralGL F n
  set Km := congruenceSubgroup F n m₀
  have hvK : v ∈ fixedVectors π Km := fun k hk => hm₀ hk
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ Km.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m₀).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ Km.subgroupOf K₀)
  let R : Finset (GL (Fin n) F) :=
    Finset.univ.image fun q : K₀ ⧸ Km.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, π k v = π r v := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq π hvK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ Km.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  set q := Representation.Coinvariants.mk (π.comp (unipotentRadical F n β).subtype)
  refine ⟨R.image fun r => q (π r v), ?_⟩
  set T := Submodule.span ℂ {x | ∃ m, ∃ s ∈ R.image fun r => q (π r v), x = jacquetRep F n β π m s}
  have hclaim : ∀ g : GL (Fin n) F, q (π g v) ∈ T := by
    intro g
    obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) g
    obtain ⟨r, hr, hrv⟩ := hR k hk
    set p' : blockUpper F n β := ⟨p, hp⟩
    set m := leviProj F n β p'
    have hn' := leviProj_inv_mul_mem p'
    have hpeq : p = ((m : levi F n β) : GL (Fin n) F) *
        (((leviIncl m)⁻¹ * p' : blockUpper F n β) : GL (Fin n) F) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]
    rw [map_mul, Module.End.mul_apply, hrv, hpeq, map_mul, Module.End.mul_apply, mk_apply_levi,
      mk_apply_of_mem π _ hn']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, q (π r v),
      Finset.mem_image_of_mem _ hr, rfl⟩)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  have hy : y ∈ Submodule.span ℂ (Set.range fun g : GL (Fin n) F => π g v) := by
    rw [hv]
    exact Submodule.mem_top
  have hmap : Submodule.map q (Submodule.span ℂ (Set.range fun g : GL (Fin n) F => π g v)) ≤ T := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact hclaim g
  exact hmap ⟨y, hy, rfl⟩
end GroundTheory.Automorphic.Parabolic
