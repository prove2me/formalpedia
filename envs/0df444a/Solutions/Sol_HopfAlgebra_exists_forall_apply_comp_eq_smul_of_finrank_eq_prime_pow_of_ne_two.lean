-- Prove2me | solution 1 for HopfAlgebra.exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/94273f94-0ef1-5094-bfb9-fb4926a88cb9

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

open scoped PadicInt

namespace E89KS

theorem e_one_eq_zero {P M : Type} [Monoid P] [AddCommGroup M] (e : P ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g) : e 1 = 0 := by
  have h := he 1 1
  rw [mul_one] at h
  have h2 : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

end E89KS

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {k : Type} [Field k] {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    [SMulCommClass (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) k M]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] (hrank : ∃ a : ℕ, Module.finrank ℤ_[p] H = p ^ a)
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H, g x = σ (f x)) → e g = σ • (e f)) :
    ∃ θ : k → (H →ₐc[ℤ_[p]] H),
      (∀ (a : k) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        e (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ (a : k) (g : H →ₐc[ℤ_[p]] H),
        (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          e (WithConv.toConv ((WithConv.ofConv f).comp (g : H →ₐ[ℤ_[p]] H))) = a • e f) → g = θ a) ∧
      (∀ a b : k, θ (a * b) = (θ a).comp (θ b)) ∧
      θ 1 = BialgHom.id ℤ_[p] H ∧
      (∀ a b : k, WithConv.toConv (θ (a + b) : H →ₐ[ℤ_[p]] H) =
        WithConv.toConv (θ a : H →ₐ[ℤ_[p]] H) * WithConv.toConv (θ b : H →ₐ[ℤ_[p]] H)) ∧
      WithConv.toConv (θ 0 : H →ₐ[ℤ_[p]] H) = 1 := by
  classical
  have key : ∀ a : k, ∃ g : H →ₐc[ℤ_[p]] H,
      (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        e (WithConv.toConv ((WithConv.ofConv f).comp (g : H →ₐ[ℤ_[p]] H))) = a • e f) ∧
      (∀ g' : H →ₐc[ℤ_[p]] H, (∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        e (WithConv.toConv ((WithConv.ofConv f).comp (g' : H →ₐ[ℤ_[p]] H))) = a • e f) → g' = g) := by
    intro a
    have hφ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M),
        DistribSMul.toAddMonoidHom M a (σ • m) = σ • DistribSMul.toAddMonoidHom M a m := by
      intro σ m
      simp only [DistribSMul.toAddMonoidHom_apply]
      exact (smul_comm σ a m).symm
    have h := HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
      p hp2 H hrank e he_add he_act H hrank e he_add he_act
      (DistribSMul.toAddMonoidHom M a) hφ
    simp only [DistribSMul.toAddMonoidHom_apply] at h
    exact h
  choose θ hθ hθu using key
  refine ⟨θ, hθ, fun a g hg => hθu a g hg, ?_, ?_, ?_, ?_⟩
  ·
    intro a b
    symm
    apply hθu
    intro f
    rw [BialgHom.comp_toAlgHom, ← AlgHom.comp_assoc]
    have h1 := hθ b (WithConv.toConv ((WithConv.ofConv f).comp (θ a : H →ₐ[ℤ_[p]] H)))
    rw [WithConv.ofConv_toConv] at h1
    rw [h1, hθ a, ← mul_smul, mul_comm b a]
  ·
    symm
    apply hθu
    intro f
    rw [BialgHom.id_toAlgHom, AlgHom.comp_id, WithConv.toConv_ofConv, one_smul]
  ·
    intro a b
    have hGab : (WithConv.toConv (θ a) * WithConv.toConv (θ b) : WithConv (H →ₐc[ℤ_[p]] H)).ofConv
        = θ (a + b) := by
      apply hθu
      intro f
      have hcoe : ((WithConv.toConv (θ a) * WithConv.toConv (θ b) :
            WithConv (H →ₐc[ℤ_[p]] H)).ofConv : H →ₐ[ℤ_[p]] H)
          = WithConv.ofConv (WithConv.toConv (θ a : H →ₐ[ℤ_[p]] H) *
              WithConv.toConv (θ b : H →ₐ[ℤ_[p]] H)) := by
        have := BialgHom.toAlgHom_convMul (WithConv.toConv (θ a)) (WithConv.toConv (θ b))
        rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv] at this
        rw [← this, WithConv.ofConv_toConv]
      rw [hcoe, AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv, he_add, hθ a, hθ b, add_smul]
    rw [← hGab]
    have := BialgHom.toAlgHom_convMul (WithConv.toConv (θ a)) (WithConv.toConv (θ b))
    rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv] at this
    exact this
  ·
    have h0 : (1 : WithConv (H →ₐc[ℤ_[p]] H)).ofConv = θ 0 := by
      apply hθu
      intro f
      have hc : (WithConv.ofConv f).comp ((1 : WithConv (H →ₐc[ℤ_[p]] H)).ofConv : H →ₐ[ℤ_[p]] H)
          = WithConv.ofConv (1 : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) := by
        apply AlgHom.ext
        intro x
        rw [AlgHom.comp_apply, AlgHom.convOne_apply, BialgHom.coe_toAlgHom, BialgHom.convOne_apply,
          AlgHom.commutes]
      rw [hc, WithConv.toConv_ofConv, E89KS.e_one_eq_zero e he_add, zero_smul]
    rw [← h0]
    exact BialgHom.toAlgHom_convOne

end S_HopfAlgebra_exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two
end P2MW
export P2MW.S_HopfAlgebra_exists_forall_apply_comp_eq_smul_of_finrank_eq_prime_pow_of_ne_two (solution)
