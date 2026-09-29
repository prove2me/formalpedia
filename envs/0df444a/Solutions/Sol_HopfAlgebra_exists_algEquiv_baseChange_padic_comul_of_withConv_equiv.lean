-- Prove2me | solution 1 for HopfAlgebra.exists_algEquiv_baseChange_padic_comul_of_withConv_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b8f6410b-1849-5bec-a8f3-0f4cd3c83941

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgHom_liftEquiv_symm_withConv_mul
import Theorems.Thm_HopfAlgebra_algebra_etale_of_module_finite_of_charZero
import Theorems.Thm_HopfAlgebra_exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_algEquiv_baseChange_padic_comul_of_withConv_equiv

set_option maxHeartbeats 8000000
open scoped TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (hAfin : Module.Finite ℚ A) (hAcocomm : Coalgebra.IsCocomm ℚ A)
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (hfin : Module.Finite ℤ_[p] Hp) (hflat : Module.Flat ℤ_[p] Hp)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] Hp)
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (eHp : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (heHp_add : ∀ f g, eHp (f * g) = eHp f + eHp g)
    (heHp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ x : Hp, g x = σ (f x)) → eHp g = σ • (eHp f))
    (eAp : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) ≃ M)
    (heAp_add : ∀ f g, eAp (f * g) = eAp f + eAp g)
    (heAp_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p])),
      (∀ a : A, g a = σ (f a)) → eAp g = σ • (eAp f)) :
    ∃ φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp),
      ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x) := by
  haveI := hAfin; haveI := hfin

  let ιH := AlgHom.liftEquiv ℤ_[p] ℚ_[p] Hp (AlgebraicClosure ℚ_[p])
  let ιHW : WithConv (ℚ_[p] ⊗[ℤ_[p]] Hp →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃
            WithConv (Hp →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
    ⟨fun g => WithConv.toConv (ιH.symm g.ofConv), fun f => WithConv.toConv (ιH f.ofConv),
     fun g => by simp only [WithConv.ofConv_toConv, Equiv.apply_symm_apply, WithConv.toConv_ofConv],
     fun f => by simp only [WithConv.ofConv_toConv, Equiv.symm_apply_apply, WithConv.toConv_ofConv]⟩
  have hιHW_mul : ∀ F G, ιHW (F * G) = ιHW F * ιHW G :=
    fun F G => AlgHom.liftEquiv_symm_withConv_mul ℤ_[p] ℚ_[p] Hp (AlgebraicClosure ℚ_[p]) F G
  let eH' := ιHW.trans eHp
  have heH'_add : ∀ f g, eH' (f * g) = eH' f + eH' g := fun f g => by
    simp only [eH', Equiv.trans_apply, hιHW_mul]; exact heHp_add _ _
  have heH'_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (ℚ_[p] ⊗[ℤ_[p]] Hp →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ b, g b = σ (f b)) → eH' g = σ • (eH' f) := fun σ f g hfg => by
    simp only [eH', Equiv.trans_apply]
    refine heHp_act σ _ _ fun h => ?_
    show (ιH.symm g.ofConv) h = σ ((ιH.symm f.ofConv) h)
    rw [show ∀ (ψ : ℚ_[p] ⊗[ℤ_[p]] Hp →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (h' : Hp),
          (ιH.symm ψ) h' = ψ (1 ⊗ₜ[ℤ_[p]] h') from fun _ _ => rfl,
        show ∀ (ψ : ℚ_[p] ⊗[ℤ_[p]] Hp →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (h' : Hp),
          (ιH.symm ψ) h' = ψ (1 ⊗ₜ[ℤ_[p]] h') from fun _ _ => rfl]
    exact hfg (1 ⊗ₜ[ℤ_[p]] h)

  let ιA := AlgHom.liftEquiv ℚ ℚ_[p] A (AlgebraicClosure ℚ_[p])
  let ιAW : WithConv (ℚ_[p] ⊗[ℚ] A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) ≃
            WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ_[p]) :=
    ⟨fun g => WithConv.toConv (ιA.symm g.ofConv), fun f => WithConv.toConv (ιA f.ofConv),
     fun g => by simp only [WithConv.ofConv_toConv, Equiv.apply_symm_apply, WithConv.toConv_ofConv],
     fun f => by simp only [WithConv.ofConv_toConv, Equiv.symm_apply_apply, WithConv.toConv_ofConv]⟩
  have hιAW_mul : ∀ F G, ιAW (F * G) = ιAW F * ιAW G :=
    fun F G => AlgHom.liftEquiv_symm_withConv_mul ℚ ℚ_[p] A (AlgebraicClosure ℚ_[p]) F G
  let eA' := ιAW.trans eAp
  have heA'_add : ∀ f g, eA' (f * g) = eA' f + eA' g := fun f g => by
    simp only [eA', Equiv.trans_apply, hιAW_mul]; exact heAp_add _ _
  have heA'_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (ℚ_[p] ⊗[ℚ] A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ b, g b = σ (f b)) → eA' g = σ • (eA' f) := fun σ f g hfg => by
    simp only [eA', Equiv.trans_apply]
    refine heAp_act σ _ _ fun a => ?_
    show (ιA.symm g.ofConv) a = σ ((ιA.symm f.ofConv) a)
    rw [show ∀ (ψ : ℚ_[p] ⊗[ℚ] A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (a' : A),
          (ιA.symm ψ) a' = ψ (1 ⊗ₜ[ℚ] a') from fun _ _ => rfl,
        show ∀ (ψ : ℚ_[p] ⊗[ℚ] A →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (a' : A),
          (ιA.symm ψ) a' = ψ (1 ⊗ₜ[ℚ] a') from fun _ _ => rfl]
    exact hfg (1 ⊗ₜ[ℚ] a)

  haveI : Algebra.Etale ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Hp) :=
    HopfAlgebra.algebra_etale_of_module_finite_of_charZero ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Hp)
  haveI : Algebra.Etale ℚ_[p] (ℚ_[p] ⊗[ℚ] A) :=
    HopfAlgebra.algebra_etale_of_module_finite_of_charZero ℚ_[p] (ℚ_[p] ⊗[ℚ] A)

  exact HopfAlgebra.exists_algEquiv_comul_of_etale_of_withConv_equiv_algClosure
    ℚ_[p] (AlgebraicClosure ℚ_[p]) (ℚ_[p] ⊗[ℤ_[p]] Hp) eH' heH'_add heH'_act
    (ℚ_[p] ⊗[ℚ] A) eA' heA'_add heA'_act

end S_HopfAlgebra_exists_algEquiv_baseChange_padic_comul_of_withConv_equiv
end P2MW
export P2MW.S_HopfAlgebra_exists_algEquiv_baseChange_padic_comul_of_withConv_equiv (solution)
