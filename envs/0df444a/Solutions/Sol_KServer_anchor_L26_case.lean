-- Prove2me | solution 1 for KServer.anchor_L26_case
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T07:20:09.369494+00:00
-- url     : https://prove2.me/submissions/ed1071be-07cc-42e2-82f6-063dcc60bbc9

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential
import Definitions.Def_KServer_tree_metric
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_tree_resolve_last_two

open KServer

variable {N : Type} [MetricSpace N]

private theorem perm3_eq (C₀ : Config 3 N) (σ : List N) (X Y : Config 3 N)
    (τ : Equiv.Perm (Fin 3)) (h : ∀ i, X i = Y (τ i)) :
    workFnU C₀ σ X = workFnU C₀ σ Y := by
  rw [show X = Y ∘ (τ : Equiv.Perm (Fin 3)) from funext h]
  exact workFnU_perm 3 N C₀ σ Y τ

private theorem swap12 (C₀ : Config 3 N) (σ : List N) (p q z : N) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![p, z, q] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 1 2) ?_
  intro i
  match i with
  | 0 => show p = ![p, z, q] ((Equiv.swap (1 : Fin 3) 2) 0)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl
  | 1 => show q = ![p, z, q] ((Equiv.swap (1 : Fin 3) 2) 1); rw [Equiv.swap_apply_left]; rfl
  | 2 => show z = ![p, z, q] ((Equiv.swap (1 : Fin 3) 2) 2); rw [Equiv.swap_apply_right]; rfl

private theorem rot3 (C₀ : Config 3 N) (σ : List N) (p q z : N) :
    workFnU C₀ σ ![p, q, z] = workFnU C₀ σ ![z, p, q] := by
  set c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  have c0 : c 0 = 1 := by rw [hc]; decide
  have c1 : c 1 = 2 := by rw [hc]; decide
  have c2 : c 2 = 0 := by rw [hc]; decide
  refine perm3_eq C₀ σ _ _ c ?_
  intro i
  match i with
  | 0 => show p = ![z, p, q] (c 0); rw [c0]; rfl
  | 1 => show q = ![z, p, q] (c 1); rw [c1]; rfl
  | 2 => show z = ![z, p, q] (c 2); rw [c2]; rfl

private theorem mc3 (A B : Config 3 N) :
    moveCost A B = dist (A 0) (B 0) + dist (A 1) (B 1) + dist (A 2) (B 2) := by
  unfold moveCost
  rw [Fin.sum_univ_three]

/-- **The Lemma-26 case of the anchoring theorem**: if the triple and its first-anchor
antipodal companion both resolve in the third slot, the last anchor may be replaced by
the request. -/
theorem solution (M : Type) [MetricSpace M] [Fintype M] (hM : IsTreeVertexSpace M)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ u v : M, dist u v ≤ Δ)
    (C₀ : Config 3 M) (σ : List M) (r a b c : M)
    (h0 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl a, Sum.inl b, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl a, Sum.inl b, Sum.inl r]
          + dist r c)
    (h1 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr a, Sum.inl b, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr a, Sum.inl b, Sum.inl r]
          + dist r c) :
    ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b c := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := (σ ++ [r]).map Sum.inl with hτ
  have hΦ : ∀ p q s : M, ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) p q s
      = workFnU E₀ τ ![Sum.inl p, Sum.inl q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr p, Sum.inl q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr q, Sum.inr q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr s, Sum.inr s, Sum.inr s] := fun p q s => rfl
  have hL26 := tree_resolve_last_two M hM Δ hΔ0 hΔ C₀ σ r b c
  rw [← hτ] at hL26
  rw [hΦ, hΦ]
  linarith
