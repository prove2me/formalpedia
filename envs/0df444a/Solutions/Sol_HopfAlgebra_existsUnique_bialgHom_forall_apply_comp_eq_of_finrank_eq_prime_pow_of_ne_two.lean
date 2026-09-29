-- Prove2me | solution 1 for HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/612761f2-a0aa-585b-82f2-0c20e1867024

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_baseChange_eq_of_pow_eq_one
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped PadicInt TensorProduct

namespace E87RLB

variable (p : ℕ) [Fact p.Prime]

local notation "Qpb" => PadicAlgCl p

section pts
variable (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]

noncomputable def ptsK :
    ((ℚ_[p] ⊗[ℤ_[p]] H) →ₐ[ℚ_[p]] PadicAlgCl p) ≃ (H →ₐ[ℤ_[p]] PadicAlgCl p) :=
  { toFun := fun F => (F.restrictScalars ℤ_[p]).comp Algebra.TensorProduct.includeRight
    invFun := fun g => Algebra.TensorProduct.lift (Algebra.ofId ℚ_[p] (PadicAlgCl p)) g (fun _ _ => Commute.all _ _)
    left_inv := fun F => by
      apply Algebra.TensorProduct.ext'
      intro a h
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
        Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.ofId_apply]
      rw [show a ⊗ₜ[ℤ_[p]] h = (a ⊗ₜ 1) * (1 ⊗ₜ h) from by simp, map_mul]
      congr 1
      rw [show (a ⊗ₜ[ℤ_[p]] (1 : H)) = algebraMap ℚ_[p] _ a from by
        simp [Algebra.TensorProduct.algebraMap_apply], AlgHom.commutes]
    right_inv := fun g => by
      ext h
      simp }

theorem ptsK_apply (F : (ℚ_[p] ⊗[ℤ_[p]] H) →ₐ[ℚ_[p]] PadicAlgCl p) (h : H) :
    ptsK p H F h = F ((1 : ℚ_[p]) ⊗ₜ h) := rfl

noncomputable def reprK {h : H} {ι : Type*} (𝓡 : Coalgebra.Repr ℤ_[p] h ι) :
    Coalgebra.Repr ℚ_[p] ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] h) ι where
  index := 𝓡.index
  left i := (1 : ℚ_[p]) ⊗ₜ 𝓡.left i
  right i := (1 : ℚ_[p]) ⊗ₜ 𝓡.right i
  eq := by
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← 𝓡.eq, TensorProduct.tmul_sum, map_sum]
    simp

theorem ptsK_mul (F G : WithConv ((ℚ_[p] ⊗[ℤ_[p]] H) →ₐ[ℚ_[p]] PadicAlgCl p)) :
    ptsK p H (F * G).ofConv
      = (WithConv.toConv (ptsK p H F.ofConv) * WithConv.toConv (ptsK p H G.ofConv)).ofConv := by
  apply AlgHom.ext
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary ℤ_[p] h
  have hR : (WithConv.toConv (ptsK p H F.ofConv) * WithConv.toConv (ptsK p H G.ofConv)).ofConv h
      = ∑ i ∈ 𝓡.index, ptsK p H F.ofConv (𝓡.left i) * ptsK p H G.ofConv (𝓡.right i) := by
    have key := AlgHom.toLinearMap_convMul (WithConv.toConv (ptsK p H F.ofConv)) (WithConv.toConv (ptsK p H G.ofConv))
    have := congrArg (fun L => (WithConv.ofConv L) h) key
    simpa [Coalgebra.Repr.convMul_apply 𝓡] using this
  have hL : (F * G).ofConv ((1 : ℚ_[p]) ⊗ₜ h)
      = ∑ i ∈ 𝓡.index, F.ofConv ((1 : ℚ_[p]) ⊗ₜ 𝓡.left i) * G.ofConv ((1 : ℚ_[p]) ⊗ₜ 𝓡.right i) := by
    have key := AlgHom.toLinearMap_convMul F G
    have := congrArg (fun L => (WithConv.ofConv L) ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] h)) key
    simp [Coalgebra.Repr.convMul_apply (reprK p H 𝓡)] at this
    exact this
  rw [ptsK_apply, hL, hR]
  rfl

noncomputable def ptsKW : WithConv ((ℚ_[p] ⊗[ℤ_[p]] H) →ₐ[ℚ_[p]] PadicAlgCl p) ≃ WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) :=
  ⟨fun F => WithConv.toConv (ptsK p H F.ofConv), fun g => WithConv.toConv ((ptsK p H).symm g.ofConv),
    fun F => by simp, fun g => by simp⟩

end pts

section main
variable {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
  [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₁]
  [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₂]

noncomputable def eK (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] {M : Type}
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) :
    WithConv ((ℚ_[p] ⊗[ℤ_[p]] H) →ₐ[ℚ_[p]] PadicAlgCl p) ≃ M :=
  (ptsKW p H).trans e

theorem eK_apply (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] {M : Type}
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (F : WithConv ((ℚ_[p] ⊗[ℤ_[p]] H) →ₐ[ℚ_[p]] PadicAlgCl p)) :
    eK p H e F = e (WithConv.toConv (ptsK p H F.ofConv)) := rfl

theorem eK_add (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] {M : Type} [AddCommGroup M]
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (he : ∀ f g, e (f * g) = e f + e g)
    (F G : WithConv ((ℚ_[p] ⊗[ℤ_[p]] H) →ₐ[ℚ_[p]] PadicAlgCl p)) :
    eK p H e (F * G) = eK p H e F + eK p H e G := by
  rw [eK_apply, eK_apply, eK_apply, ← he, ptsK_mul]

theorem eK_act (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] {M : Type} [AddCommGroup M]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M]
    (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M)
    (he : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ x : H, g x = σ (f x)) → e g = σ • (e f))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (F G : WithConv ((ℚ_[p] ⊗[ℤ_[p]] H) →ₐ[ℚ_[p]] PadicAlgCl p))
    (hFG : ∀ x, G x = σ (F x)) : eK p H e G = σ • eK p H e F := by
  rw [eK_apply, eK_apply]
  apply he
  intro h
  exact hFG _

theorem ptsK_comp (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] (H₂ : Type) [CommRing H₂] [HopfAlgebra ℤ_[p] H₂]
    (g : H₂ →ₐ[ℤ_[p]] H₁) (ψ : (ℚ_[p] ⊗[ℤ_[p]] H₂) →ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] H₁))
    (hg : g.toLinearMap.baseChange ℚ_[p] = ψ.toLinearMap)
    (F : (ℚ_[p] ⊗[ℤ_[p]] H₁) →ₐ[ℚ_[p]] PadicAlgCl p) :
    ptsK p H₂ (F.comp ψ) = (ptsK p H₁ F).comp g := by
  apply AlgHom.ext
  intro h
  rw [ptsK_apply, AlgHom.comp_apply, AlgHom.comp_apply, ptsK_apply]
  congr 1
  have := congrArg (fun L => L ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] h)) hg
  simp only [LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply] at this
  exact this.symm

theorem main (hp2 : p ≠ 2)
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • (e₁ f))
    (H₂ : Type) [CommRing H₂] [HopfAlgebra ℤ_[p] H₂] [Module.Finite ℤ_[p] H₂] [Module.Free ℤ_[p] H₂]
    [Coalgebra.IsCocomm ℤ_[p] H₂] (hrank₂ : ∃ a : ℕ, Module.finrank ℤ_[p] H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • (e₂ f))
    (φ : M₁ →+ M₂)
    (hφ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₁), φ (σ • m) = σ • φ m) :
    ∃! g : H₂ →ₐc[ℤ_[p]] H₁,
      ∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[ℤ_[p]] H₁))) = φ (e₁ f) := by

  obtain ⟨ψ, hψ, hψu⟩ := HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero ℚ_[p] (PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] H₁) (eK p H₁ e₁) (eK_add p H₁ e₁ he₁_add) (eK_act p H₁ e₁ he₁_act)
    (ℚ_[p] ⊗[ℤ_[p]] H₂) (eK p H₂ e₂) (eK_add p H₂ e₂ he₂_add) (eK_act p H₂ e₂ he₂_act) φ hφ

  obtain ⟨a₁, ha₁⟩ := hrank₁
  obtain ⟨a₂, ha₂⟩ := hrank₂
  have hH₁ : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T] (f : WithConv (H₁ →ₐ[ℤ_[p]] T)), f ^ p ^ (a₁ + a₂) = 1 := by
    intro T _ _ f
    have h := HopfAlgebra.convPow_finrank_eq_one_of_isCocomm ℤ_[p] H₁ T f
    rw [ha₁] at h
    rw [pow_add, pow_mul, h, one_pow]
  have hH₂ : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T] (f : WithConv (H₂ →ₐ[ℤ_[p]] T)), f ^ p ^ (a₁ + a₂) = 1 := by
    intro T _ _ f
    have h := HopfAlgebra.convPow_finrank_eq_one_of_isCocomm ℤ_[p] H₂ T f
    rw [ha₂] at h
    rw [add_comm, pow_add, pow_mul, h, one_pow]

  obtain ⟨g, hg, hgu⟩ := HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one (R := ℤ_[p]) ℚ_[p] p hp2
    PadicInt.irreducible_p (H := H₂) (H' := H₁) (a₁ + a₂) hH₂ hH₁ ψ
  refine ⟨g, ?_, ?_⟩
  · intro f
    have key := hψ (WithConv.toConv ((ptsK p H₁).symm f.ofConv))
    rw [eK_apply, eK_apply] at key
    simp only [WithConv.ofConv_toConv, Equiv.apply_symm_apply] at key
    rw [ptsK_comp p H₁ H₂ (g : H₂ →ₐ[ℤ_[p]] H₁) (ψ : (ℚ_[p] ⊗[ℤ_[p]] H₂) →ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] H₁)) hg,
      Equiv.apply_symm_apply] at key
    simpa using key
  · intro g' hg'

    let ψ' : (ℚ_[p] ⊗[ℤ_[p]] H₂) →ₐc[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] H₁) :=
      Bialgebra.TensorProduct.map (BialgHom.id ℚ_[p] ℚ_[p]) g'
    have hbc : (g' : H₂ →ₐ[ℤ_[p]] H₁).toLinearMap.baseChange ℚ_[p]
        = (ψ' : (ℚ_[p] ⊗[ℤ_[p]] H₂) →ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] H₁)).toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro a h
      simp [ψ', LinearMap.baseChange_tmul, Bialgebra.TensorProduct.map_tmul]
    have hψ' : ∀ F : WithConv ((ℚ_[p] ⊗[ℤ_[p]] H₁) →ₐ[ℚ_[p]] PadicAlgCl p),
        eK p H₂ e₂ (WithConv.toConv ((WithConv.ofConv F).comp (ψ' : _ →ₐ[ℚ_[p]] _))) = φ (eK p H₁ e₁ F) := by
      intro F
      rw [eK_apply, eK_apply, WithConv.ofConv_toConv,
        ptsK_comp p H₁ H₂ (g' : H₂ →ₐ[ℤ_[p]] H₁) (ψ' : _ →ₐ[ℚ_[p]] _) hbc]
      have := hg' (WithConv.toConv (ptsK p H₁ F.ofConv))
      simpa using this
    have hψψ : ψ' = ψ := hψu ψ' hψ'
    apply hgu
    rw [hbc, hψψ]

end main

end E87RLB

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₁]
    [DistribMulAction (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra ℤ_[p] H₁] [Module.Finite ℤ_[p] H₁] [Module.Free ℤ_[p] H₁]
    [Coalgebra.IsCocomm ℤ_[p] H₁] (hrank₁ : ∃ a : ℕ, Module.finrank ℤ_[p] H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • (e₁ f))
    (H₂ : Type) [CommRing H₂] [HopfAlgebra ℤ_[p] H₂] [Module.Finite ℤ_[p] H₂] [Module.Free ℤ_[p] H₂]
    [Coalgebra.IsCocomm ℤ_[p] H₂] (hrank₂ : ∃ a : ℕ, Module.finrank ℤ_[p] H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
      (f g : WithConv (H₂ →ₐ[ℤ_[p]] PadicAlgCl p)), (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • (e₂ f))
    (φ : M₁ →+ M₂)
    (hφ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (m : M₁), φ (σ • m) = σ • φ m) :
    ∃! g : H₂ →ₐc[ℤ_[p]] H₁,
      ∀ f : WithConv (H₁ →ₐ[ℤ_[p]] PadicAlgCl p),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[ℤ_[p]] H₁))) = φ (e₁ f) :=
  E87RLB.main p hp2 H₁ hrank₁ e₁ he₁_add he₁_act H₂ hrank₂ e₂ he₂_add he₂_act φ hφ

end S_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two
end P2MW
export P2MW.S_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_ne_two (solution)
