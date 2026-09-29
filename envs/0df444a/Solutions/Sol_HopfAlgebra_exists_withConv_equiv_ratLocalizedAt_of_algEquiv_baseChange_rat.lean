-- Prove2me | solution 1 for HopfAlgebra.exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/aa633e24-a7ae-518c-bba3-9f88692076ec

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgHom_liftEquiv_symm_withConv_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat

set_option maxHeartbeats 8000000
open scoped NNReal TensorProduct
open TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ N)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    (ψ : (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H) ≃ₐ[ℚ] A)
    (hψcomul : ∀ x, Coalgebra.comul (R := ℚ) (ψ x) =
        (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := ℚ) x)) :
    ∃ e : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) ≃ N,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by
  classical
  let ι := AlgHom.liftEquiv (GaloisRep.ratLocalizedAt p) ℚ H (AlgebraicClosure ℚ)
  let ιW : WithConv (H →ₐ[(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) ≃
           WithConv (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H →ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⟨fun f => WithConv.toConv (ι f.ofConv), fun g => WithConv.toConv (ι.symm g.ofConv),
     fun f => by simp only [WithConv.ofConv_toConv, Equiv.symm_apply_apply, WithConv.toConv_ofConv],
     fun g => by simp only [WithConv.ofConv_toConv, Equiv.apply_symm_apply, WithConv.toConv_ofConv]⟩

  have hιWsymm_mul : ∀ F G, ιW.symm (F * G) = ιW.symm F * ιW.symm G :=
    fun F G => AlgHom.liftEquiv_symm_withConv_mul (GaloisRep.ratLocalizedAt p) ℚ H (AlgebraicClosure ℚ) F G
  have hιW_mul : ∀ f g, ιW (f * g) = ιW f * ιW g := fun f g => by
    have := hιWsymm_mul (ιW f) (ιW g)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
    exact ιW.symm.injective (by rw [Equiv.symm_apply_apply, this])

  let ψW : WithConv (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H →ₐ[ℚ] AlgebraicClosure ℚ) ≃
           WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⟨fun g => WithConv.toConv (g.ofConv.comp ψ.symm.toAlgHom),
     fun f => WithConv.toConv (f.ofConv.comp ψ.toAlgHom),
     fun g => by
       dsimp only
       rw [WithConv.ofConv_toConv, AlgHom.comp_assoc,
         show ψ.symm.toAlgHom.comp ψ.toAlgHom = AlgHom.id ℚ (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H) from
           AlgHom.ext fun x => ψ.symm_apply_apply x,
         AlgHom.comp_id, WithConv.toConv_ofConv],
     fun f => by
       dsimp only
       rw [WithConv.ofConv_toConv, AlgHom.comp_assoc,
         show ψ.toAlgHom.comp ψ.symm.toAlgHom = AlgHom.id ℚ A from
           AlgHom.ext fun a => ψ.apply_symm_apply a,
         AlgHom.comp_id, WithConv.toConv_ofConv]⟩

  have hψW_mul : ∀ f g, ψW (f * g) = ψW f * ψW g := by
    intro f g
    rw [show (ψW f * ψW g) = WithConv.toConv (ψW f * ψW g).ofConv from (WithConv.toConv_ofConv _).symm]
    congr 1
    ext a
    show LinearMap.mul' ℚ _ (TensorProduct.map f.ofConv.toLinearMap g.ofConv.toLinearMap
            (Coalgebra.comul (R := ℚ) (ψ.symm a)))
       = LinearMap.mul' ℚ _ (TensorProduct.map (f.ofConv.comp ψ.symm.toAlgHom).toLinearMap
            (g.ofConv.comp ψ.symm.toAlgHom).toLinearMap (Coalgebra.comul (R := ℚ) a))
    have key : Coalgebra.comul (R := ℚ) a
             = TensorProduct.map ψ.toLinearMap ψ.toLinearMap (Coalgebra.comul (R := ℚ) (ψ.symm a)) := by
      have := hψcomul (ψ.symm a); rwa [AlgEquiv.apply_symm_apply] at this
    rw [key]
    congr 1
    induction Coalgebra.comul (R := ℚ) (ψ.symm a) using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom, AlgEquiv.toLinearMap_apply,
        AlgEquiv.symm_apply_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨(ιW.trans ψW).trans eA, ?_, ?_⟩
  · intro f g
    simp only [Equiv.trans_apply, hιW_mul, hψW_mul]
    exact heA_add _ _
  ·
    intro σ f g hfg
    simp only [Equiv.trans_apply]
    apply heA_act σ
    intro a

    show (ι g.ofConv) (ψ.symm a) = σ ((ι f.ofConv) (ψ.symm a))

    have hext : ι g.ofConv = (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] _).toAlgHom.comp (ι f.ofConv) := by
      apply ι.symm.injective
      rw [Equiv.symm_apply_apply]
      ext h
      show g.ofConv h = (ι.symm ((σ : _).toAlgHom.comp (ι f.ofConv))) h
      rw [show ∀ (ψ : ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H →ₐ[ℚ] AlgebraicClosure ℚ) (h : H),
            (ι.symm ψ) h = ψ (1 ⊗ₜ[(GaloisRep.ratLocalizedAt p)] h) from fun _ _ => rfl]
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom]
      rw [show (ι f.ofConv) (1 ⊗ₜ[(GaloisRep.ratLocalizedAt p)] h) = f.ofConv h from by
        have : ι.symm (ι f.ofConv) h = f.ofConv h := by rw [Equiv.symm_apply_apply]
        rw [show ∀ (ψ : _) (h' : H), (ι.symm ψ) h' = ψ (1 ⊗ₜ[(GaloisRep.ratLocalizedAt p)] h') from fun _ _ => rfl] at this
        exact this]
      exact hfg h
    rw [hext]
    rfl

end S_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat
end P2MW
export P2MW.S_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat (solution)
