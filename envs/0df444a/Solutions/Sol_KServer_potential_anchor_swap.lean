-- Prove2me | solution 1 for KServer.potential_anchor_swap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T22:02:17.627458+00:00
-- url     : https://prove2.me/submissions/ec21958e-9506-4da3-acbb-b46180938f71

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_perm

open KServer

variable {M : Type} [MetricSpace M]

private theorem perm3_eq (C₀ : Config 3 M) (σ : List M) (X Y : Config 3 M)
    (τ : Equiv.Perm (Fin 3)) (h : ∀ i, X i = Y (τ i)) :
    workFnU C₀ σ X = workFnU C₀ σ Y := by
  rw [show X = Y ∘ (τ : Equiv.Perm (Fin 3)) from funext h]
  exact workFnU_perm 3 M C₀ σ Y τ

private theorem swap01 (C₀ : Config 3 M) (σ : List M) (p q z : M) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![q, p, z] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 0 1) ?_
  intro i
  match i with
  | 0 => show p = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 0); rw [Equiv.swap_apply_left]; rfl
  | 1 => show q = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 1); rw [Equiv.swap_apply_right]; rfl
  | 2 => show z = ![q, p, z] ((Equiv.swap (0 : Fin 3) 1) 2)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl

/-- **Coester–Koutsoupias, the swap step of Lemma 25**: once the doubled antipode
resolves to the first anchor, the first two anchors of the potential may be
exchanged without increasing it. -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (bar : M → M) (hbar : ∀ p q : M, dist (bar p) q = dist p (bar q)) (x₁ x₂ x₃ : M)
    (hres : workFnU C₀ σ ![bar x₂, bar x₂, x₃]
      = workFnU C₀ σ ![bar x₂, x₁, x₃] + dist x₁ (bar x₂)) :
    workFnU C₀ σ ![x₂, x₁, x₃] + workFnU C₀ σ ![bar x₂, x₁, x₃]
        + workFnU C₀ σ ![bar x₁, bar x₁, x₃] + workFnU C₀ σ ![bar x₃, bar x₃, bar x₃]
      ≤ workFnU C₀ σ ![x₁, x₂, x₃] + workFnU C₀ σ ![bar x₁, x₂, x₃]
        + workFnU C₀ σ ![bar x₂, bar x₂, x₃] + workFnU C₀ σ ![bar x₃, bar x₃, bar x₃] := by
  have hlip := workFnU_lipschitz 3 (by norm_num) M C₀ σ
    (![bar x₁, bar x₁, x₃] : Config 3 M) (![bar x₁, x₂, x₃] : Config 3 M)
  have hmc : moveCost (![bar x₁, x₂, x₃] : Config 3 M) (![bar x₁, bar x₁, x₃] : Config 3 M)
      = dist x₂ (bar x₁) := by
    unfold moveCost
    rw [Fin.sum_univ_three]
    show dist (bar x₁) (bar x₁) + dist x₂ (bar x₁) + dist x₃ x₃ = dist x₂ (bar x₁)
    rw [dist_self, dist_self]
    ring
  have hsym : dist x₂ (bar x₁) = dist x₁ (bar x₂) := by
    rw [← hbar x₂ x₁, dist_comm (bar x₂) x₁]
  rw [hmc, hsym] at hlip
  have hfirst : workFnU C₀ σ ![x₂, x₁, x₃] = workFnU C₀ σ ![x₁, x₂, x₃] :=
    swap01 C₀ σ x₂ x₁ x₃
  rw [hfirst]
  linarith
