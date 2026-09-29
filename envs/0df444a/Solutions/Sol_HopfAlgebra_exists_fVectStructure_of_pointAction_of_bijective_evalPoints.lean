-- Prove2me | solution 1 for HopfAlgebra.exists_fVectStructure_of_pointAction_of_bijective_evalPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/038c7da6-b838-56c8-90e1-5681bda67797

import Mathlib
import Definitions.Def_HopfAlgebra_FVectStructure
import Theorems.Thm_HopfAlgebra_exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range
import Theorems.Thm_AlgHom_eq_of_forall_comp_eq_of_injective_lift_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_fVectStructure_of_pointAction_of_bijective_evalPoints

set_option autoImplicit false

open scoped TensorProduct
universe u v

theorem solution
    (K : Type u) [Field K] [PerfectField K]
    (H : Type v) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    [Finite (WithConv (H →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (H →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (H →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : H →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] H →ₐ[AlgebraicClosure K]
          (WithConv (H →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (F : Type) [Field F] [Fintype F]
    (smulF : F → WithConv (H →ₐ[K] AlgebraicClosure K) → WithConv (H →ₐ[K] AlgebraicClosure K))
    (h_one : ∀ x, smulF 1 x = x)
    (h_mul : ∀ (a b : F) x, smulF (a * b) x = smulF a (smulF b x))
    (h_zero : ∀ x, smulF 0 x = 1)
    (h_add : ∀ (a b : F) x, smulF (a + b) x = smulF a x * smulF b x)
    (h_pt_one : ∀ a : F, smulF a 1 = 1)
    (h_pt_mul : ∀ (a : F) x y, smulF a (x * y) = smulF a x * smulF a y)
    (h_gal : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F)
        (x y : WithConv (H →ₐ[K] AlgebraicClosure K)),
        (∀ h : H, WithConv.ofConv y h = σ (WithConv.ofConv x h)) →
        ∀ h : H, WithConv.ofConv (smulF a y) h = σ (WithConv.ofConv (smulF a x) h)) :
    ∃ σF : HopfAlgebra.FVectStructure F K H,
      ∀ (a : F) (x : WithConv (H →ₐ[K] AlgebraicClosure K)),
        WithConv.toConv ((WithConv.ofConv x).comp (σF.act a : H →ₐ[K] H)) = smulF a x := by
  classical
  set L := AlgebraicClosure K with hL

  have hfix : ∀ x : L, (∀ σ ∈ (⊤ : Subgroup (L ≃ₐ[K] L)), σ x = x) → x ∈ Set.range (algebraMap K L) := by
    intro x hx
    have hmem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := fun σ => hx σ σ.2
    rw [← IntermediateField.fixingSubgroup_bot, InfiniteGalois.fixedField_fixingSubgroup] at hmem
    exact IntermediateField.mem_bot.mp hmem

  let φ : F → (WithConv (H →ₐ[K] L) →* WithConv (H →ₐ[K] L)) := fun a =>
    { toFun := smulF a, map_one' := h_pt_one a, map_mul' := h_pt_mul a }
  have hu : ∀ a : F, ∃ u : H →ₐc[K] H, ∀ ν : WithConv (H →ₐ[K] L),
      WithConv.toConv ((WithConv.ofConv ν).comp (u : H →ₐ[K] H)) = smulF a ν := fun a =>
    HopfAlgebra.exists_bialgHom_forall_comp_eq_of_equivariant_of_forall_fixed_mem_range ⊤ hfix hev (φ a)
      (fun σ _ ν ν' hνν' => h_gal σ a ν ν' hνν')
  choose u hu using hu

  have hdet : ∀ (v v' : H →ₐ[K] H),
      (∀ ν : WithConv (H →ₐ[K] L), (WithConv.ofConv ν).comp v = (WithConv.ofConv ν).comp v') → v = v' :=
    fun v v' h => AlgHom.eq_of_forall_comp_eq_of_injective_lift_pi
      (fun ν : WithConv (H →ₐ[K] L) => (WithConv.ofConv ν : H →ₐ[K] L)) hev.1 v v' h
  have hu' : ∀ (a : F) (ν : WithConv (H →ₐ[K] L)),
      (WithConv.ofConv ν).comp (u a : H →ₐ[K] H) = WithConv.ofConv (smulF a ν) := fun a ν =>
    congrArg WithConv.ofConv (hu a ν)
  refine ⟨{ act := u, act_one := ?_, act_mul := ?_, act_zero := ?_, act_add := ?_ }, hu⟩
  ·
    apply BialgHom.coe_algHom_injective
    apply hdet
    intro ν
    rw [hu', h_one]
    rfl
  ·
    intro a b
    apply BialgHom.coe_algHom_injective
    apply hdet
    intro ν
    rw [hu', mul_comm, h_mul]
    show _ = ((WithConv.ofConv ν).comp (u a : H →ₐ[K] H)).comp (u b : H →ₐ[K] H)
    rw [hu', hu']
  ·
    show WithConv.toConv (u 0 : H →ₐ[K] H) = 1
    rw [AlgHom.convOne_def]
    congr 1
    apply hdet
    intro ν
    rw [hu', h_zero]
    have h1 : (1 : WithConv (H →ₐ[K] L)) = WithConv.toConv ((Algebra.ofId K L).comp (Bialgebra.counitAlgHom K H)) :=
      AlgHom.convOne_def
    rw [h1, WithConv.ofConv_toConv, ← AlgHom.comp_assoc]
    congr 1
    apply AlgHom.ext
    intro x
    simp
  ·
    intro a b
    have key : (u (a + b) : H →ₐ[K] H)
        = WithConv.ofConv (WithConv.toConv (u a : H →ₐ[K] H) * WithConv.toConv (u b : H →ₐ[K] H)) := by
      apply hdet
      intro ν
      rw [hu', h_add, AlgHom.comp_convMul_distrib, WithConv.ofConv_toConv, WithConv.ofConv_toConv, hu, hu]
    rw [key, WithConv.toConv_ofConv]

end S_HopfAlgebra_exists_fVectStructure_of_pointAction_of_bijective_evalPoints
end P2MW
export P2MW.S_HopfAlgebra_exists_fVectStructure_of_pointAction_of_bijective_evalPoints (solution)
