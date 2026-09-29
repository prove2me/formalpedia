-- Prove2me | solution 1 for HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6de8ff70-a231-50cf-9ef3-0dc103d79f9e

import Mathlib
import Theorems.Thm_BialgHom_exists_coe_eq_of_forall_withConv_comp
import Theorems.Thm_Algebra_Etale_existsUnique_algHom_forall_comp_eq_of_equivariant
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_Algebra_Etale_of_isReduced_of_perfectField
import Theorems.Thm_Algebra_Etale_algHom_ext_of_forall_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

set_option autoImplicit false

namespace E88GD

theorem etale_of_hopf (K : Type) [Field K] [CharZero K]
    (E : Type) [CommRing E] [HopfAlgebra K E] [Module.Finite K E] : Algebra.Etale K E := by
  haveI : IsReduced E := HopfAlgebra.isReduced_of_finiteType_of_charZero K E
  exact Algebra.Etale.of_isReduced_of_perfectField K E

theorem isGalois_algClosure (K : Type) [Field K] [CharZero K] (Kbar : Type) [Field Kbar] [Algebra K Kbar]
    [IsAlgClosure K Kbar] : IsGalois K Kbar := by
  haveI : Algebra.IsAlgebraic K Kbar := IsAlgClosure.isAlgebraic
  haveI : Normal K Kbar := IsAlgClosure.normal K Kbar
  haveI : Algebra.IsSeparable K Kbar := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact IsGalois.mk

theorem isAlgClosed_of_isAlgClosure (K : Type) [Field K] (Kbar : Type) [Field Kbar] [Algebra K Kbar]
    [IsAlgClosure K Kbar] : IsAlgClosed Kbar := IsAlgClosure.isAlgClosed K

theorem isAlgebraic_of_isAlgClosure (K : Type) [Field K] (Kbar : Type) [Field Kbar] [Algebra K Kbar]
    [IsAlgClosure K Kbar] : Algebra.IsAlgebraic K Kbar := IsAlgClosure.isAlgebraic

theorem sep (K : Type) [Field K] [CharZero K] (Kbar : Type) [Field Kbar] [Algebra K Kbar]
    [IsAlgClosure K Kbar] (E : Type) [CommRing E] [HopfAlgebra K E] [Module.Finite K E]
    (x : E) (hx : ∀ θ : E →ₐ[K] Kbar, θ x = 0) : x = 0 := by
  haveI : Algebra.Etale K E := etale_of_hopf K E
  haveI : IsAlgClosed Kbar := IsAlgClosure.isAlgClosed K

  have h : (Polynomial.aeval x : Polynomial K →ₐ[K] E) = Polynomial.aeval (0 : E) := by
    apply Algebra.Etale.algHom_ext_of_forall_comp_eq (Ω := Kbar)
    intro χ
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, hx χ, map_zero]
  have := congrArg (fun φ : Polynomial K →ₐ[K] E => φ Polynomial.X) h
  simpa using this

end E88GD

namespace E87GD

variable (K : Type) [Field K] [CharZero K] (Kbar : Type) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
  {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
  [DistribMulAction (Kbar ≃ₐ[K] Kbar) M₁] [DistribMulAction (Kbar ≃ₐ[K] Kbar) M₂]
  (E₁ : Type) [CommRing E₁] [HopfAlgebra K E₁] [Module.Finite K E₁]
  (e₁ : WithConv (E₁ →ₐ[K] Kbar) ≃ M₁)
  (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
  (he₁_act : ∀ (σ : Kbar ≃ₐ[K] Kbar) (f g : WithConv (E₁ →ₐ[K] Kbar)),
    (∀ x : E₁, g x = σ (f x)) → e₁ g = σ • (e₁ f))
  (E₂ : Type) [CommRing E₂] [HopfAlgebra K E₂] [Module.Finite K E₂]
  (e₂ : WithConv (E₂ →ₐ[K] Kbar) ≃ M₂)
  (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
  (he₂_act : ∀ (σ : Kbar ≃ₐ[K] Kbar) (f g : WithConv (E₂ →ₐ[K] Kbar)),
    (∀ x : E₂, g x = σ (f x)) → e₂ g = σ • (e₂ f))
  (φ : M₁ →+ M₂)
  (hφ : ∀ (σ : Kbar ≃ₐ[K] Kbar) (m : M₁), φ (σ • m) = σ • φ m)

noncomputable def Φ (f : E₁ →ₐ[K] Kbar) : E₂ →ₐ[K] Kbar := (e₂.symm (φ (e₁ (WithConv.toConv f)))).ofConv

theorem e₂_Φ (f : E₁ →ₐ[K] Kbar) : e₂ (WithConv.toConv (Φ K Kbar E₁ e₁ E₂ e₂ φ f)) = φ (e₁ (WithConv.toConv f)) := by
  simp [Φ]

include he₁_act he₂_act hφ in
theorem Φ_equivariant (σ : Kbar ≃ₐ[K] Kbar) (f : E₁ →ₐ[K] Kbar) :
    Φ K Kbar E₁ e₁ E₂ e₂ φ ((σ : Kbar →ₐ[K] Kbar).comp f) = (σ : Kbar →ₐ[K] Kbar).comp (Φ K Kbar E₁ e₁ E₂ e₂ φ f) := by
  have hinj : Function.Injective (fun g : E₂ →ₐ[K] Kbar => e₂ (WithConv.toConv g)) :=
    fun a b h => by simpa using congrArg WithConv.ofConv (e₂.injective h)
  apply hinj
  simp only
  rw [e₂_Φ, he₂_act σ (WithConv.toConv (Φ K Kbar E₁ e₁ E₂ e₂ φ f)) _ (fun x => rfl), e₂_Φ, ← hφ,
    he₁_act σ (WithConv.toConv f) _ (fun x => rfl)]

include he₁_add in
theorem e₁_one : e₁ 1 = 0 := by
  have := he₁_add 1 1
  rw [mul_one] at this
  exact left_eq_add.mp this

end E87GD

open E87GD in
theorem solution
    (K : Type) [Field K] [CharZero K] (Kbar : Type) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (Kbar ≃ₐ[K] Kbar) M₁] [DistribMulAction (Kbar ≃ₐ[K] Kbar) M₂]
    (E₁ : Type) [CommRing E₁] [HopfAlgebra K E₁] [Module.Finite K E₁]
    (e₁ : WithConv (E₁ →ₐ[K] Kbar) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : Kbar ≃ₐ[K] Kbar) (f g : WithConv (E₁ →ₐ[K] Kbar)),
      (∀ x : E₁, g x = σ (f x)) → e₁ g = σ • (e₁ f))
    (E₂ : Type) [CommRing E₂] [HopfAlgebra K E₂] [Module.Finite K E₂]
    (e₂ : WithConv (E₂ →ₐ[K] Kbar) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : Kbar ≃ₐ[K] Kbar) (f g : WithConv (E₂ →ₐ[K] Kbar)),
      (∀ x : E₂, g x = σ (f x)) → e₂ g = σ • (e₂ f))
    (φ : M₁ →+ M₂)
    (hφ : ∀ (σ : Kbar ≃ₐ[K] Kbar) (m : M₁), φ (σ • m) = σ • φ m) :
    ∃! ψ : E₂ →ₐc[K] E₁,
      ∀ f : WithConv (E₁ →ₐ[K] Kbar),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (ψ : E₂ →ₐ[K] E₁))) = φ (e₁ f) := by

  have hinj : ∀ a b : E₂ →ₐ[K] Kbar, e₂ (WithConv.toConv a) = e₂ (WithConv.toConv b) → a = b :=
    fun a b h => by simpa using congrArg WithConv.ofConv (e₂.injective h)

  haveI : Algebra.Etale K E₁ := E88GD.etale_of_hopf K E₁
  haveI : Algebra.Etale K E₂ := E88GD.etale_of_hopf K E₂
  haveI : IsGalois K Kbar := E88GD.isGalois_algClosure K Kbar
  haveI : IsAlgClosed Kbar := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Kbar := IsAlgClosure.isAlgebraic

  obtain ⟨ψ₀, hψ₀', -⟩ := Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant
    (K := K) (Ω := Kbar) (B := E₂) (C := E₁) (Φ K Kbar E₁ e₁ E₂ e₂ φ)
    (fun γ χ => by
      have := Φ_equivariant K Kbar E₁ e₁ he₁_act E₂ e₂ he₂_act φ hφ γ χ
      simpa [AlgEquiv.toAlgHom_eq_coe] using this)
  have hψ₀ : ∀ f : E₁ →ₐ[K] Kbar, Φ K Kbar E₁ e₁ E₂ e₂ φ f = f.comp ψ₀ := fun f => (hψ₀' f).symm

  have hsep : ∀ x : E₁ ⊗[K] E₁, (∀ θ : E₁ ⊗[K] E₁ →ₐ[K] Kbar, θ x = 0) → x = 0 :=
    fun x hx => E88GD.sep K Kbar (E₁ ⊗[K] E₁) x hx
  have hone : (1 : WithConv (E₁ →ₐ[K] Kbar)).ofConv.comp ψ₀ = (1 : WithConv (E₂ →ₐ[K] Kbar)).ofConv := by
    rw [← hψ₀]
    apply hinj
    rw [e₂_Φ]
    change φ (e₁ 1) = e₂ 1
    rw [e₁_one K Kbar E₁ e₁ he₁_add, map_zero, e₁_one K Kbar E₂ e₂ he₂_add]
  have hmul : ∀ χ χ' : WithConv (E₁ →ₐ[K] Kbar),
      (χ * χ').ofConv.comp ψ₀ = (WithConv.toConv (χ.ofConv.comp ψ₀) * WithConv.toConv (χ'.ofConv.comp ψ₀)).ofConv := by
    intro χ χ'
    rw [← hψ₀, ← hψ₀, ← hψ₀]
    apply hinj
    rw [e₂_Φ, WithConv.toConv_ofConv, he₂_add, e₂_Φ, e₂_Φ, WithConv.toConv_ofConv, he₁_add, map_add]
  obtain ⟨ψ, hψ⟩ := BialgHom.exists_coe_eq_of_forall_withConv_comp (R := K) (K := Kbar)
    (algebraMap K Kbar).injective ψ₀ hsep hone hmul
  refine ⟨ψ, ?_, ?_⟩
  · intro f
    rw [hψ, ← hψ₀, e₂_Φ, WithConv.toConv_ofConv]
  · intro ψ' hψ'
    apply BialgHom.coe_algHom_injective
    rw [hψ]
    apply AlgHom.ext
    intro y

    have key : ∀ θ : E₁ →ₐ[K] Kbar, θ ((ψ' : E₂ →ₐ[K] E₁) y) = θ (ψ₀ y) := by
      intro θ
      have h1 := hψ' (WithConv.toConv θ)
      rw [WithConv.ofConv_toConv, ← e₂_Φ K Kbar E₁ e₁ E₂ e₂ φ, hψ₀] at h1
      have h2 := hinj _ _ h1
      exact congrArg (fun (g : E₂ →ₐ[K] Kbar) => g y) h2
    have := E88GD.sep K Kbar E₁
      ((ψ' : E₂ →ₐ[K] E₁) y - ψ₀ y) (fun θ => by rw [map_sub, key θ, sub_self])
    exact sub_eq_zero.mp this

end S_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
end P2MW
export P2MW.S_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero (solution)
