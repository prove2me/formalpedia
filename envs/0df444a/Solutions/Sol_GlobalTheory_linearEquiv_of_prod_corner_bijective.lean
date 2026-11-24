-- Prove2me | solution 1 for GlobalTheory.linearEquiv_of_prod_corner_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:18:04.90366+00:00
-- url     : https://prove2.me/submissions/4769470d-42b8-4f9c-b9bb-286d6a7a3fc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelProdSummandNilpotentOrBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R M M' P : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup P] [Module R P]
namespace GlobalTheory
theorem _root_.solution (e : (M × P) ≃ₗ[R] (M' × P))
    (hd : Function.Bijective ((LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P)) :
    Nonempty (M ≃ₗ[R] M') := by
  set d : P →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inr R M P with hd_def
  let dE : P ≃ₗ[R] P := LinearEquiv.ofBijective d hd
  let c : M →ₗ[R] P := (LinearMap.snd R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      LinearMap.inl R M P
  let φ : M →ₗ[R] M' := (LinearMap.fst R M' P) ∘ₗ (e : (M × P) →ₗ[R] (M' × P)) ∘ₗ
      (LinearMap.prod LinearMap.id (-((dE.symm : P →ₗ[R] P) ∘ₗ c)))
  let ψ : M' →ₗ[R] M := (LinearMap.fst R M P) ∘ₗ (e.symm : (M' × P) →ₗ[R] (M × P)) ∘ₗ
      LinearMap.inl R M' P
  have hsplit : ∀ x : M × P, (e x).2 = c x.1 + d x.2 := by
    intro x
    have hx : x = ((x.1, 0) : M × P) + (0, x.2) := by simp
    conv_lhs => rw [hx]
    rw [map_add]
    rfl
  have hdd : ∀ p : P, d (dE.symm p) = p := fun p => dE.apply_symm_apply p
  have key : ∀ m : M, e (m, -dE.symm (c m)) = (φ m, 0) := by
    intro m
    ext
    · rfl
    · rw [hsplit]
      simp only [map_neg, hdd]
      simp
  refine ⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩
  · apply LinearMap.ext
    intro m'
    set x := e.symm (m', 0) with hx
    have hex : e x = (m', 0) := by simp [hx]
    have hp : -dE.symm (c x.1) = x.2 := by
      have h0 := hsplit x
      rw [hex] at h0
      have h1 : d x.2 = -c x.1 := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h0.symm
      have h2 : dE.symm (d x.2) = x.2 := dE.symm_apply_apply x.2
      rw [h1, map_neg] at h2
      exact h2
    have hk := key x.1
    rw [hp] at hk
    have hψ : ψ m' = x.1 := rfl
    show φ (ψ m') = m'
    rw [hψ]
    have h3 : ((φ x.1, (0 : P)) : M' × P) = (m', 0) := by rw [← hk]; exact hex
    exact congrArg Prod.fst h3
  · apply LinearMap.ext
    intro m
    show ψ (φ m) = m
    have h : ψ (φ m) = (e.symm (φ m, 0)).1 := rfl
    rw [h, ← key m, LinearEquiv.symm_apply_apply]
end GlobalTheory
