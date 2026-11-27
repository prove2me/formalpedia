-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:30.58784+00:00
-- url     : https://prove2.me/submissions/9690412c-2716-4444-84dd-70c16064e517

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isotropic_partner
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_extend_of_nondegenerate
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [FiniteDimensional E V] (h : HermitianForm F E V) (U : Submodule E V)
    (f : U →ₗ[E] V) (hf : Function.Injective f)
    (hfh : ∀ x y : U, h.toSesq (f x) (f y) = h.toSesq x y) :
    ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U, g x = f x := by
  suffices key : ∀ d : ℕ, ∀ (U : Submodule E V) (f : U →ₗ[E] V),
      finrank E V - finrank E U = d → Function.Injective f →
      (∀ x y : U, h.toSesq (f x) (f y) = h.toSesq x y) →
      ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U, g x = f x from
    key _ U f rfl hf hfh
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro U f hd hf hfh
  by_cases hU : ∀ u ∈ U, (∀ u' ∈ U, h.toSesq u u' = 0) → u = 0
  · obtain ⟨g, hg, hgf⟩ := h.exists_extend_of_nondegenerate hU (LinearEquiv.ofInjective f hf)
      (fun x y => by simp only [LinearEquiv.ofInjective_apply]; exact hfh x y)
    exact ⟨g, hg, fun x => by rw [hgf, LinearEquiv.ofInjective_apply]⟩
  push Not at hU
  obtain ⟨r, hrU, hr, hr0⟩ := hU

  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual E U, φ ⟨r, hrU⟩ ≠ 0 := by
    by_contra H
    push Not at H
    exact hr0 (congrArg Subtype.val ((Module.forall_dual_apply_eq_zero_iff E _).1 H))
  set μ : U →ₗ[E] E := (φ ⟨r, hrU⟩)⁻¹ • φ with hμ_def
  have hμ : μ ⟨r, hrU⟩ = 1 := by
    rw [hμ_def, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  obtain ⟨s, hs, hss⟩ := h.exists_isotropic_partner U hrU hr μ hμ

  set e := LinearEquiv.ofInjective f hf with he_def
  have he : ∀ x : U, ((e x : LinearMap.range f) : V) = f x := fun x =>
    LinearEquiv.ofInjective_apply _ _
  have hr₂ : ∀ u ∈ LinearMap.range f, h.toSesq (f ⟨r, hrU⟩) u = 0 := by
    rintro _ ⟨u, rfl⟩
    rw [hfh]
    exact hr u u.2
  have hrr : (⟨f ⟨r, hrU⟩, LinearMap.mem_range_self f _⟩ : LinearMap.range f) = e ⟨r, hrU⟩ :=
    Subtype.ext (he _).symm
  obtain ⟨s', hs', hss'⟩ := h.exists_isotropic_partner (LinearMap.range f)
    (LinearMap.mem_range_self f ⟨r, hrU⟩) hr₂ (μ ∘ₗ (e.symm : LinearMap.range f →ₗ[E] U))
    (by rw [LinearMap.comp_apply, hrr, LinearEquiv.coe_coe, e.symm_apply_apply, hμ])
  have hs'' : ∀ x : U, h.toSesq s' (f x) = μ x := by
    intro x
    have := hs' (e x)
    rwa [LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, he] at this

  have hsU : s ∉ U := by
    intro hsU
    have h1 := hr s hsU
    have h2 : h.toSesq s r = 1 := by rw [← hμ, ← hs]
    rw [← h.conj_toSesq, h2, map_one] at h1
    exact one_ne_zero h1

  set ψ : (U × E) →ₗ[E] V := U.subtype.coprod (LinearMap.toSpanSingleton E V s) with hψ_def
  have hψ : ∀ (u : U) (a : E), ψ (u, a) = u + a • s := fun u a => by
    simp [hψ_def]
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, a⟩ hp
    rw [hψ] at hp
    by_cases ha : a = 0
    · subst ha
      rw [zero_smul, add_zero] at hp
      rw [Submodule.coe_eq_zero.1 hp]
      rfl
    · exfalso
      apply hsU
      have h2 : a • s = -(u : V) := eq_neg_of_add_eq_zero_right hp
      have : s = a⁻¹ • -(u : V) := by rw [← h2, smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [this]
      exact U.smul_mem _ (U.neg_mem u.2)
  set f₀ : (U × E) →ₗ[E] V := f.coprod (LinearMap.toSpanSingleton E V s') with hf₀_def
  have hf₀ : ∀ (u : U) (a : E), f₀ (u, a) = f u + a • s' := fun u a => by
    simp [hf₀_def]
  have hL : ∀ (u v : U) (a b : E), h.toSesq (f u + a • s') (f v + b • s') =
      h.toSesq u v + b * conj F E (μ u) + conj F E a * μ v := by
    intro u v a b
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, hfh, hss']
    rw [← h.conj_toSesq s' (f u), hs'' u, hs'' v]
    ring
  have hR : ∀ (u v : U) (a b : E), h.toSesq ((u : V) + a • s) ((v : V) + b • s) =
      h.toSesq u v + b * conj F E (μ u) + conj F E a * μ v := by
    intro u v a b
    simp only [map_add, LinearMap.add_apply, h.toSesq_smul_left, h.toSesq_smul_right, hss]
    rw [← h.conj_toSesq s (u : V), hs u, hs v]
    ring
  have hf₀inj : Function.Injective f₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, a⟩ hp
    rw [hf₀] at hp
    have ha : a = 0 := by
      have h1 := congrArg (h.toSesq (f ⟨r, hrU⟩)) hp
      rw [map_add, h.toSesq_smul_right, hfh, hr u u.2, zero_add, map_zero,
        ← h.conj_toSesq s', hs'', hμ, map_one, mul_one] at h1
      exact h1
    subst ha
    rw [zero_smul, add_zero] at hp
    have hu : u = 0 := hf (by rw [hp, map_zero])
    rw [hu]
    rfl
  set e' := LinearEquiv.ofInjective ψ hψinj with he'_def
  have he' : ∀ p : U × E, ((e' p : LinearMap.range ψ) : V) = ψ p := fun p =>
    LinearEquiv.ofInjective_apply _ _
  set f' : LinearMap.range ψ →ₗ[E] V := f₀ ∘ₗ (e'.symm : LinearMap.range ψ →ₗ[E] U × E)
  have hf'inj : Function.Injective f' := hf₀inj.comp e'.symm.injective
  have hf'h : ∀ x y : LinearMap.range ψ, h.toSesq (f' x) (f' y) = h.toSesq x y := by
    intro x y
    obtain ⟨⟨u, a⟩, rfl⟩ := e'.surjective x
    obtain ⟨⟨v, b⟩, rfl⟩ := e'.surjective y
    simp only [f', LinearMap.comp_apply, LinearEquiv.coe_coe, e'.symm_apply_apply]
    rw [he', he', hf₀, hf₀, hψ, hψ, hL, hR]
  have hdim : finrank E (LinearMap.range ψ) = finrank E U + 1 := by
    rw [LinearMap.finrank_range_of_inj hψinj, Module.finrank_prod, Module.finrank_self]
  have hle : finrank E (LinearMap.range ψ) ≤ finrank E V := Submodule.finrank_le _
  obtain ⟨g, hg, hgf⟩ := ih (finrank E V - finrank E (LinearMap.range ψ)) (by omega)
    (LinearMap.range ψ) f' rfl hf'inj hf'h
  refine ⟨g, hg, fun u => ?_⟩
  have h1 := hgf (e' (u, 0))
  rw [he', hψ, zero_smul, add_zero] at h1
  rw [h1]
  simp only [f', LinearMap.comp_apply, LinearEquiv.coe_coe, e'.symm_apply_apply, hf₀, zero_smul,
    add_zero]
end GroundTheory.Automorphic.HermitianForm
