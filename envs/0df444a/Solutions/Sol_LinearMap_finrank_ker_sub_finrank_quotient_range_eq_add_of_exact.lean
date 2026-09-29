-- Prove2me | solution 1 for LinearMap.finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9163b4fd-e981-5fec-8fba-d07f7dfdeec7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact

set_option autoImplicit false

namespace C2EulerCharAux

open Function

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [DivisionRing k]
  {M : Type u₁} {N : Type u₂} {P : Type u₃}
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]

lemma finiteDimensional_of_exact {f : M →ₗ[k] N} {g : N →ₗ[k] P} (h : Exact f g)
    [FiniteDimensional k M] [FiniteDimensional k P] : FiniteDimensional k N :=
  Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict]; exact h.linearMap_ker_eq))
    g.surjective_rangeRestrict

lemma finrank_eq_of_exact {f : M →ₗ[k] N} {g : N →ₗ[k] P} (h : Exact f g)
    [FiniteDimensional k N] :
    Module.finrank k N
      = Module.finrank k (LinearMap.range f) + Module.finrank k (LinearMap.range g) := by
  rw [← g.finrank_range_add_finrank_ker, h.linearMap_ker_eq, add_comm]

end C2EulerCharAux

universe u v

open C2EulerCharAux in

theorem solution
    {k : Type u} [Field k]
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type v}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃)
    (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂)
    [FiniteDimensional k (LinearMap.ker d₁)] [FiniteDimensional k (B₁ ⧸ LinearMap.range d₁)]
    [FiniteDimensional k (LinearMap.ker d₃)] [FiniteDimensional k (B₃ ⧸ LinearMap.range d₃)] :
    FiniteDimensional k (LinearMap.ker d₂) ∧ FiniteDimensional k (B₂ ⧸ LinearMap.range d₂) ∧
    (Module.finrank k (LinearMap.ker d₂) : ℤ) - Module.finrank k (B₂ ⧸ LinearMap.range d₂)
      = ((Module.finrank k (LinearMap.ker d₁) : ℤ) - Module.finrank k (B₁ ⧸ LinearMap.range d₁))
        + ((Module.finrank k (LinearMap.ker d₃) : ℤ) - Module.finrank k (B₃ ⧸ LinearMap.range d₃)) := by

  have h₁' : ∀ x, g₁ (d₁ x) = d₂ (f₁ x) := fun x => LinearMap.congr_fun h₁ x
  have h₂' : ∀ x, g₂ (d₂ x) = d₃ (f₂ x) := fun x => LinearMap.congr_fun h₂ x

  have hF₁ : ∀ x ∈ LinearMap.ker d₁, f₁ x ∈ LinearMap.ker d₂ := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← h₁', hx, map_zero]
  have hF₂ : ∀ x ∈ LinearMap.ker d₂, f₂ x ∈ LinearMap.ker d₃ := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← h₂', hx, map_zero]
  let F₁ : LinearMap.ker d₁ →ₗ[k] LinearMap.ker d₂ := f₁.restrict hF₁
  let F₂ : LinearMap.ker d₂ →ₗ[k] LinearMap.ker d₃ := f₂.restrict hF₂

  have hG₁ : LinearMap.range d₁ ≤ (LinearMap.range d₂).comap g₁ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨f₁ a, (h₁' a).symm⟩
  have hG₂ : LinearMap.range d₂ ≤ (LinearMap.range d₃).comap g₂ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨f₂ a, (h₂' a).symm⟩
  let G₁ : (B₁ ⧸ LinearMap.range d₁) →ₗ[k] (B₂ ⧸ LinearMap.range d₂) :=
    (LinearMap.range d₁).mapQ (LinearMap.range d₂) g₁ hG₁
  let G₂ : (B₂ ⧸ LinearMap.range d₂) →ₗ[k] (B₃ ⧸ LinearMap.range d₃) :=
    (LinearMap.range d₂).mapQ (LinearMap.range d₃) g₂ hG₂

  let δ : LinearMap.ker d₃ →ₗ[k] (B₁ ⧸ LinearMap.range d₁) :=
    SnakeLemma.δ' d₁ d₂ d₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
      (LinearMap.ker d₃).subtype (LinearMap.exact_subtype_ker_map d₃)
      (LinearMap.range d₁).mkQ (LinearMap.exact_map_mkQ_range d₁) hf₂ hg₁

  have eF₁ : Function.Injective F₁ := fun x y hxy =>
    Subtype.ext (hf₁ (by simpa [F₁] using congrArg Subtype.val hxy))

  have eK₂ : Function.Exact F₁ F₂ := by
    intro x
    constructor
    · intro hx
      have hx' : f₂ (x : A₂) = 0 := by simpa [F₂] using congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (hf _).mp hx'
      have hy' : y ∈ LinearMap.ker d₁ := by
        rw [LinearMap.mem_ker]
        apply hg₁
        rw [h₁', hy, map_zero]
        exact x.2
      exact ⟨⟨y, hy'⟩, Subtype.ext (by simpa [F₁] using hy)⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simp [F₁, F₂, hf.apply_apply_eq_zero]

  have eK₃ : Function.Exact F₂ δ :=
    SnakeLemma.exact_δ'_right d₁ d₂ d₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
      (LinearMap.ker d₂).subtype (LinearMap.exact_subtype_ker_map d₂)
      (LinearMap.ker d₃).subtype (LinearMap.exact_subtype_ker_map d₃)
      (LinearMap.range d₁).mkQ (LinearMap.exact_map_mkQ_range d₁) hf₂ hg₁
      F₂ (by ext; rfl) (LinearMap.ker d₃).injective_subtype

  have eC₁ : Function.Exact δ G₁ :=
    SnakeLemma.exact_δ'_left d₁ d₂ d₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
      (LinearMap.ker d₃).subtype (LinearMap.exact_subtype_ker_map d₃)
      (LinearMap.range d₁).mkQ (LinearMap.exact_map_mkQ_range d₁)
      (LinearMap.range d₂).mkQ (LinearMap.exact_map_mkQ_range d₂) hf₂ hg₁
      G₁ (Submodule.mapQ_mkQ _ _ _) (Submodule.mkQ_surjective _)

  have eC₂ : Function.Exact G₁ G₂ := by
    intro c
    constructor
    · intro hy
      obtain ⟨y, rfl⟩ := (LinearMap.range d₂).mkQ_surjective c
      have hy' : g₂ y ∈ LinearMap.range d₃ := by
        simpa [G₂, Submodule.mapQ_apply] using hy
      obtain ⟨z, hz⟩ := hy'
      obtain ⟨w, rfl⟩ := hf₂ z
      have hv : y - d₂ w ∈ LinearMap.range g₁ := by
        rw [← hg.linearMap_ker_eq, LinearMap.mem_ker, map_sub, h₂', hz, sub_self]
      obtain ⟨v, hv⟩ := hv
      refine ⟨(LinearMap.range d₁).mkQ v, ?_⟩
      simp only [G₁, Submodule.mkQ_apply, Submodule.mapQ_apply, hv]
      rw [Submodule.Quotient.eq]
      exact ⟨-w, by simp⟩
    · rintro ⟨c', rfl⟩
      obtain ⟨v, rfl⟩ := (LinearMap.range d₁).mkQ_surjective c'
      simp [G₁, G₂, Submodule.mapQ_apply, hg.apply_apply_eq_zero]

  have eG₂ : Function.Surjective G₂ := by
    intro c
    obtain ⟨z, rfl⟩ := (LinearMap.range d₃).mkQ_surjective c
    obtain ⟨y, rfl⟩ := hg₂ z
    exact ⟨(LinearMap.range d₂).mkQ y, by simp [G₂, Submodule.mapQ_apply]⟩

  haveI iK₂ : FiniteDimensional k (LinearMap.ker d₂) := finiteDimensional_of_exact eK₂
  haveI iC₂ : FiniteDimensional k (B₂ ⧸ LinearMap.range d₂) := finiteDimensional_of_exact eC₂
  refine ⟨iK₂, iC₂, ?_⟩

  have n₁ : Module.finrank k (LinearMap.ker d₁) = Module.finrank k (LinearMap.range F₁) :=
    (LinearMap.finrank_range_of_inj eF₁).symm
  have n₂ := finrank_eq_of_exact eK₂
  have n₃ := finrank_eq_of_exact eK₃
  have n₄ := finrank_eq_of_exact eC₁
  have n₅ := finrank_eq_of_exact eC₂
  have n₆ : Module.finrank k (B₃ ⧸ LinearMap.range d₃) = Module.finrank k (LinearMap.range G₂) := by
    rw [LinearMap.range_eq_top.2 eG₂, finrank_top]
  omega

end S_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
end P2MW
export P2MW.S_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact (solution)
