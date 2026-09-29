-- Prove2me | solution 1 for LevelRaising.exists_ker_pair_castAddHom_comp_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/58c404f1-ab28-5fc8-945e-6b0cec0febf1

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LevelRaising_exists_ker_pair_castAddHom_comp_ne_zero

set_option Elab.async false
set_option autoImplicit false

open Polynomial

namespace LevelRaisingAux9

namespace KernelClassAux

section castAddHom

variable {A : Type*} [AddZeroClass A] {p : ℕ}

private theorem castAddHom_comp_eq_zero_iff (φ : A →+ ℤ) :
    (Int.castAddHom (ZMod p)).comp φ = 0 ↔ ∃ ψ : A →+ ℤ, φ = (p : ℤ) • ψ := by
  constructor
  · intro h
    have hdvd : ∀ m, (p : ℤ) ∣ φ m := fun m => by
      have := DFunLike.congr_fun h m
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
    refine ⟨⟨⟨fun m => φ m / (p : ℤ), ?_⟩, ?_⟩, ?_⟩
    · simp
    · intro a b
      show φ (a + b) / (p : ℤ) = φ a / (p : ℤ) + φ b / (p : ℤ)
      rw [φ.map_add, Int.add_ediv_of_dvd_left (hdvd a)]
    · ext m
      exact (Int.mul_ediv_cancel' (hdvd m)).symm
  · rintro ⟨ψ, rfl⟩
    ext m
    simp

end castAddHom

section module

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

private theorem exists_pow_apply_sub_pow_smul (T : V →ₗ[ℤ] V) (p c : ℤ) (g : V)
    (h : ∃ ψ : V, T g - c • g = p • ψ) (n : ℕ) :
    ∃ w : V, (T ^ n) g - c ^ n • g = p • w := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨ψ, hψ⟩ := h
    refine ⟨T w + c ^ n • ψ, ?_⟩
    have e1 : (T ^ (n + 1)) g = T ((T ^ n) g) := by
      rw [pow_succ', Module.End.mul_apply]
    have e2 : (T ^ n) g = c ^ n • g + p • w := by rw [← hw]; abel
    have e3 : T g = c • g + p • ψ := by rw [← hψ]; abel
    rw [e1, e2, map_add, map_smul, map_smul, e3, pow_succ, mul_smul, smul_add, smul_add,
      smul_comm (c ^ n) p ψ]
    abel

private theorem exists_aeval_sub_eval_smul (T : V →ₗ[ℤ] V) (p c : ℤ) (g : V)
    (h : ∃ ψ : V, T g - c • g = p • ψ) (s : ℤ[X]) :
    ∃ w : V, (aeval T s) g - (s.eval c) • g = p • w := by
  induction s using Polynomial.induction_on' with
  | add f f' hf hf' =>
    obtain ⟨w, hw⟩ := hf
    obtain ⟨w', hw'⟩ := hf'
    refine ⟨w + w', ?_⟩
    simp only [map_add, LinearMap.add_apply, eval_add, add_smul, smul_add]
    rw [← hw, ← hw']
    abel
  | monomial n d =>
    obtain ⟨w, hw⟩ := exists_pow_apply_sub_pow_smul T p c g h n
    refine ⟨d • w, ?_⟩
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, eval_monomial]
    rw [mul_comm d, mul_smul, smul_comm (c ^ n) d g, ← smul_sub, hw, smul_comm d p w]

private theorem apply_aeval_of_comm (U T : V →ₗ[ℤ] V) (hUT : ∀ v, U (T v) = T (U v)) (s : ℤ[X])
    (v : V) : U ((aeval T s) v) = (aeval T s) (U v) := by
  have hpow : ∀ (n : ℕ) (v : V), U ((T ^ n) v) = (T ^ n) (U v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih (T v), hUT]
  induction s using Polynomial.induction_on' generalizing v with
  | add f f' hf hf' => simp [hf, hf']
  | monomial n d =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [map_smul, hpow]

private theorem coe_aeval_restrict (f : V →ₗ[ℤ] V) {q : Submodule ℤ V} (hf : ∀ x ∈ q, f x ∈ q)
    (s : ℤ[X]) (v : q) : (((aeval (f.restrict hf) s) v : q) : V) = (aeval f s) (v : V) := by
  have hpow : ∀ (n : ℕ) (v : q), ((((f.restrict hf) ^ n) v : q) : V) = (f ^ n) (v : V) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  induction s using Polynomial.induction_on' generalizing v with
  | add g g' hg hg' => simp [hg, hg']
  | monomial n d =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow]

variable (τ₁ : V →ₗ[ℤ] V) (τ₀ : W →ₗ[ℤ] W) (β : V →ₗ[ℤ] W) (hβτ : β ∘ₗ τ₁ = τ₀ ∘ₗ β)

include hβτ in
private theorem map_pow_apply (n : ℕ) (v : V) : β ((τ₁ ^ n) v) = (τ₀ ^ n) (β v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih (τ₁ v)]
    exact congrArg (τ₀ ^ n) (LinearMap.congr_fun hβτ v)

include hβτ in
private theorem map_aeval_apply (s : ℤ[X]) (v : V) : β ((aeval τ₁ s) v) = (aeval τ₀ s) (β v) := by
  induction s using Polynomial.induction_on' generalizing v with
  | add f f' hf hf' => simp [hf, hf']
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [map_smul, map_pow_apply τ₁ τ₀ β hβτ]

include hβτ in

private theorem exists_kernel_rep {p : ℕ} (a : ℤ)
    (hsurj : ∀ h : W, ∃ s : ℤ[X], ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : V, (aeval τ₀ s) h = β x)
    (g : V) (hg : ∃ y : W, β g = (p : ℤ) • y) :
    ∃ (x : V) (s : ℤ[X]), β ((aeval τ₁ s) g - (p : ℤ) • x) = 0 ∧
      ((s.eval a : ℤ) : ZMod p) ≠ 0 := by
  obtain ⟨y, hy⟩ := hg
  obtain ⟨s, hs, x, hx⟩ := hsurj y
  refine ⟨x, s, ?_, hs⟩
  rw [map_sub, map_aeval_apply τ₁ τ₀ β hβτ, hy, map_smul, hx, map_smul, sub_self]

end module

end KernelClassAux

end LevelRaisingAux9

open LevelRaisingAux9.KernelClassAux in
theorem solution
    {A₁ A₀ : Type*} [AddZeroClass A₁] [AddZeroClass A₀]
    (par₁ : Submodule ℤ (A₁ →+ ℤ)) (par₀ : Submodule ℤ (A₀ →+ ℤ))
    {p : ℕ} [Fact p.Prime]
    (T₁ : (ℓ : ℕ) → [NeZero ℓ] → ((A₁ →+ ℤ) →+ (A₁ →+ ℤ)))
    (hT₁par : ∀ (ℓ : ℕ) [NeZero ℓ], ∀ x ∈ par₁, T₁ ℓ x ∈ par₁)
    (ℓ₀ : ℕ) [NeZero ℓ₀]
    (T₀ : (A₀ →+ ℤ) →+ (A₀ →+ ℤ)) (hT₀par : ∀ x ∈ par₀, T₀ x ∈ par₀)
    (β₀ β₁ : (A₁ →+ ℤ) →+ (A₀ →+ ℤ))
    (hβpar₀ : ∀ x ∈ par₁, β₀ x ∈ par₀) (hβpar₁ : ∀ x ∈ par₁, β₁ x ∈ par₀)
    (hβT : (LinearMap.prod (β₀.toIntLinearMap.restrict hβpar₀)
          (β₁.toIntLinearMap.restrict hβpar₁)) ∘ₗ
        ((T₁ ℓ₀).toIntLinearMap.restrict (hT₁par ℓ₀))
      = (LinearMap.prodMap (T₀.toIntLinearMap.restrict hT₀par)
          (T₀.toIntLinearMap.restrict hT₀par)) ∘ₗ
        (LinearMap.prod (β₀.toIntLinearMap.restrict hβpar₀)
          (β₁.toIntLinearMap.restrict hβpar₁)))
    (a : ℕ → ℤ) (S : ℕ → Prop)
    (hcomm : ∀ (ℓ : ℕ) [NeZero ℓ], S ℓ → ∀ x : A₁ →+ ℤ, T₁ ℓ (T₁ ℓ₀ x) = T₁ ℓ₀ (T₁ ℓ x))
    (hloc : ∀ h : ↥par₀ × ↥par₀, ∃ s : ℤ[X], ((s.eval (a ℓ₀) : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : ↥par₁,
        (aeval (LinearMap.prodMap (T₀.toIntLinearMap.restrict hT₀par)
          (T₀.toIntLinearMap.restrict hT₀par)) s) h
        = (LinearMap.prod (β₀.toIntLinearMap.restrict hβpar₀)
            (β₁.toIntLinearMap.restrict hβpar₁)) x)
    (hsat₀ : ∀ δ : A₀ →+ ℤ, (p : ℤ) • δ ∈ par₀ → δ ∈ par₀)
    (g : A₁ →+ ℤ) (hgpar : g ∈ par₁) (hgne : (Int.castAddHom (ZMod p)).comp g ≠ 0)
    (hgβ₀ : ∃ δ₀ : A₀ →+ ℤ, β₀ g = (p : ℤ) • δ₀)
    (hgβ₁ : ∃ δ₁ : A₀ →+ ℤ, β₁ g = (p : ℤ) • δ₁)
    (hg₀ : ∃ ψ : A₁ →+ ℤ, T₁ ℓ₀ g - a ℓ₀ • g = (p : ℤ) • ψ)
    (hgeig : ∀ (ℓ : ℕ) [NeZero ℓ], S ℓ → ∃ ψ : A₁ →+ ℤ, T₁ ℓ g - a ℓ • g = (p : ℤ) • ψ) :
    ∃ H : A₁ →+ ℤ, H ∈ par₁ ∧ β₀ H = 0 ∧ β₁ H = 0 ∧
      (Int.castAddHom (ZMod p)).comp H ≠ 0 ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], S ℓ →
        ∃ ψ : A₁ →+ ℤ, T₁ ℓ H - a ℓ • H = (p : ℤ) • ψ := by
  obtain ⟨δ₀, hδ₀⟩ := hgβ₀
  obtain ⟨δ₁, hδ₁⟩ := hgβ₁
  have hδ₀par : δ₀ ∈ par₀ := hsat₀ δ₀ (hδ₀ ▸ hβpar₀ g hgpar)
  have hδ₁par : δ₁ ∈ par₀ := hsat₀ δ₁ (hδ₁ ▸ hβpar₁ g hgpar)

  obtain ⟨x, s, hβH, hs⟩ := exists_kernel_rep
    ((T₁ ℓ₀).toIntLinearMap.restrict (hT₁par ℓ₀))
    (LinearMap.prodMap (T₀.toIntLinearMap.restrict hT₀par) (T₀.toIntLinearMap.restrict hT₀par))
    (LinearMap.prod (β₀.toIntLinearMap.restrict hβpar₀) (β₁.toIntLinearMap.restrict hβpar₁))
    hβT (a ℓ₀) hloc ⟨g, hgpar⟩
    ⟨(⟨δ₀, hδ₀par⟩, ⟨δ₁, hδ₁par⟩), Prod.ext (Subtype.ext hδ₀) (Subtype.ext hδ₁)⟩

  have hHval : (((aeval ((T₁ ℓ₀).toIntLinearMap.restrict (hT₁par ℓ₀)) s) ⟨g, hgpar⟩
        - (p : ℤ) • x : ↥par₁) : A₁ →+ ℤ)
      = (aeval (T₁ ℓ₀).toIntLinearMap s) g - (p : ℤ) • (x : A₁ →+ ℤ) := by
    rw [Submodule.coe_sub, Submodule.coe_smul, coe_aeval_restrict]
  refine ⟨(((aeval ((T₁ ℓ₀).toIntLinearMap.restrict (hT₁par ℓ₀)) s) ⟨g, hgpar⟩
      - (p : ℤ) • x : ↥par₁) : A₁ →+ ℤ), Submodule.coe_mem _, ?_, ?_, ?_, ?_⟩
  ·
    have h1 := congrArg (fun z : ↥par₀ × ↥par₀ => ((z.1 : ↥par₀) : A₀ →+ ℤ)) hβH
    simpa [LinearMap.prod_apply, Function.prod, LinearMap.coe_restrict_apply] using h1
  ·
    have h2 := congrArg (fun z : ↥par₀ × ↥par₀ => ((z.2 : ↥par₀) : A₀ →+ ℤ)) hβH
    simpa [LinearMap.prod_apply, Function.prod, LinearMap.coe_restrict_apply] using h2
  ·
    rw [hHval]
    intro hH
    obtain ⟨w, hw⟩ := exists_aeval_sub_eval_smul (T₁ ℓ₀).toIntLinearMap (p : ℤ) (a ℓ₀) g hg₀ s
    obtain ⟨H', hH'⟩ := (castAddHom_comp_eq_zero_iff _).mp hH

    have hsg : (s.eval (a ℓ₀)) • g = (p : ℤ) • (H' + (x : A₁ →+ ℤ) - w) := by
      have e : (aeval (T₁ ℓ₀).toIntLinearMap s) g
          = (p : ℤ) • H' + (p : ℤ) • (x : A₁ →+ ℤ) := by rw [← hH']; abel
      rw [smul_sub, smul_add, ← e, ← hw]
      abel

    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * s.eval (a ℓ₀) = 1 + (p : ℤ) * v := by
      have hval : (((((s.eval (a ℓ₀) : ℤ) : ZMod p)⁻¹).val : ℕ) : ZMod p)
          * ((s.eval (a ℓ₀) : ℤ) : ZMod p) = 1 := by
        rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ hs]
      refine ⟨((((s.eval (a ℓ₀) : ℤ) : ZMod p)⁻¹).val : ℤ), ?_⟩
      have hdvd : (p : ℤ) ∣ ((((s.eval (a ℓ₀) : ℤ) : ZMod p)⁻¹).val : ℤ) * s.eval (a ℓ₀) - 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hval, sub_self]
      obtain ⟨v, hv⟩ := hdvd
      exact ⟨v, by rw [← hv]; abel⟩
    apply hgne
    refine (castAddHom_comp_eq_zero_iff g).mpr ⟨u • (H' + (x : A₁ →+ ℤ) - w) - v • g, ?_⟩
    symm
    calc (p : ℤ) • (u • (H' + (x : A₁ →+ ℤ) - w) - v • g)
        = u • ((p : ℤ) • (H' + (x : A₁ →+ ℤ) - w)) - ((p : ℤ) * v) • g := by
          rw [smul_sub, smul_comm (p : ℤ) u, mul_smul]
      _ = u • ((s.eval (a ℓ₀)) • g) - ((p : ℤ) * v) • g := by rw [← hsg]
      _ = g := by rw [← mul_smul, huv, add_smul, one_smul, add_sub_cancel_right]
  ·
    intro ℓ _ hSℓ
    rw [hHval]
    obtain ⟨ψ, hψ⟩ := hgeig ℓ hSℓ
    refine ⟨(aeval (T₁ ℓ₀).toIntLinearMap s) ψ
      - (T₁ ℓ (x : A₁ →+ ℤ) - a ℓ • (x : A₁ →+ ℤ)), ?_⟩
    have hc : ∀ y : A₁ →+ ℤ, (T₁ ℓ).toIntLinearMap ((T₁ ℓ₀).toIntLinearMap y)
        = (T₁ ℓ₀).toIntLinearMap ((T₁ ℓ).toIntLinearMap y) := fun y => hcomm ℓ hSℓ y
    have e1 : T₁ ℓ ((aeval (T₁ ℓ₀).toIntLinearMap s) g)
        = (aeval (T₁ ℓ₀).toIntLinearMap s) (T₁ ℓ g) :=
      apply_aeval_of_comm (T₁ ℓ).toIntLinearMap (T₁ ℓ₀).toIntLinearMap hc s g
    have e2 : (aeval (T₁ ℓ₀).toIntLinearMap s) (T₁ ℓ g)
        = a ℓ • (aeval (T₁ ℓ₀).toIntLinearMap s) g
          + (p : ℤ) • (aeval (T₁ ℓ₀).toIntLinearMap s) ψ := by
      have : T₁ ℓ g = a ℓ • g + (p : ℤ) • ψ := by rw [← hψ]; abel
      rw [this, map_add, map_smul, map_smul]
    have e3 : T₁ ℓ ((aeval (T₁ ℓ₀).toIntLinearMap s) g - (p : ℤ) • (x : A₁ →+ ℤ))
        = (aeval (T₁ ℓ₀).toIntLinearMap s) (T₁ ℓ g) - (p : ℤ) • T₁ ℓ (x : A₁ →+ ℤ) := by
      rw [map_sub, map_zsmul, e1]
    rw [e3, e2]
    simp only [smul_sub]
    rw [smul_comm (a ℓ) (p : ℤ) (x : A₁ →+ ℤ)]
    abel

#print axioms solution

end S_LevelRaising_exists_ker_pair_castAddHom_comp_ne_zero
end P2MW
export P2MW.S_LevelRaising_exists_ker_pair_castAddHom_comp_ne_zero (solution)
