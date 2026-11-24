-- Prove2me | solution 1 for GlobalTheory.eigenvector_mem_ker_of_ne_coord_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:03.794898+00:00
-- url     : https://prove2.me/submissions/d9505048-3a44-4fc0-9499-f90e531d5cce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionEigenvalueCompat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (Q : W →ₗ[ℂ] (Fin g → ℂ)), (∀ x, Q (P x) = x) →
    ∀ (O : Type) (T : O → Module.End ℂ W) (χ : O → Fin g → ℂ),
    (∀ a (x : Λ), (fun j ↦ χ a j * (x : Fin g → ℂ) j) ∈ Λ) →
    (∀ a (x y : Λ), (y : Fin g → ℂ) = (fun j ↦ χ a j * (x : Fin g → ℂ) j) → T a (P x) = P y) →
    ∀ ψ : O → ℂ, (∀ j, ∃ a, χ a j ≠ ψ a) →
    (⨅ a, Module.End.eigenspace (T a) (ψ a) : Submodule ℂ W) ≤ LinearMap.ker Q := by
  intro W _ _ g Λ P hspan Q hQ O T χ hΛ hT ψ hψ w hw

  let D : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a =>
    { toFun := fun v j => χ a j * v j
      map_add' := by intro u v; funext j; simp [mul_add]
      map_smul' := by intro c v; funext j; simp; ring }
  have hcomm : ∀ a, Q ∘ₗ T a = D a ∘ₗ Q := by
    intro a
    refine LinearMap.ext_on_range hspan ?_
    intro x
    have h1 : T a (P x) = P ⟨_, hΛ a x⟩ := hT a x ⟨_, hΛ a x⟩ rfl
    simp only [LinearMap.comp_apply, h1, hQ]
    rfl
  rw [LinearMap.mem_ker]
  have hw' : ∀ a, T a w = ψ a • w := by
    intro a
    have := (Submodule.mem_iInf _).1 hw a
    exact Module.End.mem_eigenspace_iff.1 this
  funext j
  obtain ⟨a, ha⟩ := hψ j
  have h2 := congrArg (fun f => f w) (hcomm a)
  simp only [LinearMap.comp_apply, hw', map_smul] at h2
  have h3 := congrFun h2 j
  change ψ a * Q w j = χ a j * Q w j at h3
  have h4 : (χ a j - ψ a) * Q w j = 0 := by rw [sub_mul, ← h3]; ring
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd (sub_eq_zero.1 h) ha
  · simpa using h
end GlobalTheory
