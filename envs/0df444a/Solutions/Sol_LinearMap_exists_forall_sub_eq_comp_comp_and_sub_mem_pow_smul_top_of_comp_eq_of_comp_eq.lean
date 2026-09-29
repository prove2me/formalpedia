-- Prove2me | solution 1 for LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5cbc4462-5c6a-5ea3-b02f-0ce539a20720

import Mathlib
import Theorems.Thm_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq

set_option autoImplicit false

universe u v w

theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {GK : Type v} [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {GE : Type v} [AddCommGroup GE] [Module B GE] [Module.Finite B GE]
    {M : Type v} [AddCommGroup M] [Module B M]
    (ϑ : GK →ₗ[B] M) (θE : M →ₗ[B] GE) (hex : LinearMap.range ϑ = LinearMap.ker θE) (hθE : Function.Surjective θE)
    (F : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hF : ∀ k, I ^ (k + 1) • (⊤ : Submodule B (F k)) = ⊥)
    (lam : ∀ k, GK →ₗ[B] F k) (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k)
    (c : ℕ) (hlami : ∀ k, LinearMap.ker (lam (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule B GK))
    (E : ℕ → Type w) [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (ε : ∀ k, F k →ₗ[B] E k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (θ θ' : ∀ k, M →ₗ[B] F k)
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k) (hθ'c : ∀ k, φ k ∘ₗ θ' (k + 1) = θ' k)
    (hθϑ : ∀ k, θ k ∘ₗ ϑ = lam k) (hθ'ϑ : ∀ k, θ' k ∘ₗ ϑ = lam k)
    (hθε : ∀ k, ε k ∘ₗ θ k = ε k ∘ₗ θ' k) :
    ∃ g : ℕ → (GE →ₗ[B] GK),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (GE →ₗ[B] GK))) ∧
      (∀ k, θ' k - θ k = lam k ∘ₗ g k ∘ₗ θE) := by
  classical

  have hdϑ : ∀ k, (θ' k - θ k) ∘ₗ ϑ = 0 := fun k => by rw [LinearMap.sub_comp, hθ'ϑ, hθϑ, sub_self]
  have hdε : ∀ k, ε k ∘ₗ (θ' k - θ k) = 0 := fun k => by rw [LinearMap.comp_sub, hθε, sub_self]
  have hdc : ∀ k, φ k ∘ₗ (θ' (k + 1) - θ (k + 1)) = θ' k - θ k := fun k => by rw [LinearMap.comp_sub, hθ'c, hθc]

  have hkerle : ∀ k, LinearMap.ker θE ≤ LinearMap.ker (θ' k - θ k) := fun k => by
    rw [← hex, LinearMap.range_le_ker_iff]; exact hdϑ k
  let eE : (M ⧸ LinearMap.ker θE) ≃ₗ[B] GE := LinearMap.quotKerEquivOfSurjective θE hθE
  let dbar : ∀ k, GE →ₗ[B] F k := fun k => (LinearMap.ker θE).liftQ (θ' k - θ k) (hkerle k) ∘ₗ eE.symm.toLinearMap
  have hdbar_app : ∀ k x, dbar k (θE x) = (θ' k - θ k) x := by
    intro k x
    show (LinearMap.ker θE).liftQ (θ' k - θ k) (hkerle k) (eE.symm (θE x)) = (θ' k - θ k) x
    have : eE.symm (θE x) = Submodule.Quotient.mk x := by
      apply eE.injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [this]
    rfl
  have hdbar : ∀ k, dbar k ∘ₗ θE = θ' k - θ k := fun k => LinearMap.ext (hdbar_app k)
  have hdbarε : ∀ k y, dbar k y ∈ LinearMap.range (lam k) := by
    intro k y
    obtain ⟨x, rfl⟩ := hθE y
    rw [hlamr, LinearMap.mem_ker, hdbar_app, ← LinearMap.comp_apply, hdε]; rfl
  have hdbarc : ∀ k y, φ k (dbar (k + 1) y) = dbar k y := by
    intro k y
    obtain ⟨x, rfl⟩ := hθE y
    rw [hdbar_app, hdbar_app, ← LinearMap.comp_apply, hdc]

  have hJ : ∀ k, LinearMap.ker (lam (k + 1)) ≤ LinearMap.ker (lam k) := fun k x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hlamc k, LinearMap.comp_apply, hx, map_zero]
  have hIJ : ∀ k, I ^ (k + 1) • (⊤ : Submodule B GK) ≤ LinearMap.ker (lam k) := by
    intro k
    refine Submodule.smul_le.2 (fun r hr x _ => ?_)
    rw [LinearMap.mem_ker, map_smul]
    have : r • lam k x ∈ I ^ (k + 1) • (⊤ : Submodule B (F k)) := Submodule.smul_mem_smul hr Submodule.mem_top
    rwa [hF k, Submodule.mem_bot] at this
  let q : ∀ k, (GK ⧸ LinearMap.ker (lam k)) ≃ₗ[B] LinearMap.range (lam k) := fun k => LinearMap.quotKerEquivRange (lam k)
  let f : ∀ k, GE →ₗ[B] GK ⧸ LinearMap.ker (lam k) :=
    fun k => (q k).symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range (lam k)) (dbar k) (hdbarε k)

  have hqf : ∀ k y, ((q k) (f k y) : F k) = dbar k y := by
    intro k y
    show ((q k) ((q k).symm ⟨dbar k y, hdbarε k y⟩) : F k) = dbar k y
    rw [LinearEquiv.apply_symm_apply]
  have hq_mk : ∀ k (z : GK), ((q k) (Submodule.Quotient.mk z) : F k) = lam k z := fun k z =>
    LinearMap.quotKerEquivRange_apply_mk (lam k) z
  have hf : ∀ k, Submodule.factor (hJ k) ∘ₗ f (k + 1) = f k := by
    intro k
    apply LinearMap.ext; intro y
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective (LinearMap.ker (lam (k + 1))) (f (k + 1) y)
    apply (q k).injective
    apply Subtype.ext
    rw [LinearMap.comp_apply, ← hz]
    change ((q k) (Submodule.Quotient.mk z) : F k) = ((q k) (f k y) : F k)
    rw [hq_mk, hqf, ← hdbarc, ← hlamc k, LinearMap.comp_apply]
    congr 1
    have := hqf (k + 1) y
    rw [← hz] at this
    rw [← this]
    exact (hq_mk (k + 1) z).symm

  obtain ⟨g, hg1, hg2⟩ := LinearMap.exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible (B := B) I
    (fun k => LinearMap.ker (lam k)) hJ hIJ c hlami f hf
  refine ⟨g, hg1, fun k => ?_⟩
  rw [← hdbar k, ← LinearMap.comp_assoc]
  congr 1
  apply LinearMap.ext; intro y
  show dbar k y = lam k (g k y)
  rw [← hqf, ← hq_mk]
  congr 2
  exact (LinearMap.congr_fun (hg2 k) y).symm

end S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
end P2MW
export P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq (solution)
