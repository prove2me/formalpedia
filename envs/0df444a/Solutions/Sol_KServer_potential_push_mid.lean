-- Prove2me | solution 1 for KServer.potential_push_mid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T06:32:13.838992+00:00
-- url     : https://prove2.me/submissions/25ac973a-af45-4e68-9fc0-1247a63ca228

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_resolves

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

/-- **Pushing the request from the middle anchor slot to the last.** -/
theorem solution (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r z : M) :
    @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inl r]
      + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inr r]
    ≤ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inl z]
      + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inr z] := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := (σ ++ [r]).map Sum.inl with hτ
  have hτsplit : τ = σ.map Sum.inl ++ [Sum.inl r] := by rw [hτ]; simp
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have dLL : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inl b) = dist a b := fun _ _ => rfl
  have dRR : ∀ a b : M, dist (Sum.inr a : M ⊕ M) (Sum.inr b) = dist a b := fun _ _ => rfl
  have dLR : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inr b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  -- the all-antipodes configuration of z resolves, necessarily to (z̄, z̄, r)
  have hz3 : workFnU E₀ τ ![Sum.inr z, Sum.inr z, Sum.inr z]
      = workFnU E₀ τ ![Sum.inr z, Sum.inr z, Sum.inl r] + (2 * Δ - dist r z) := by
    obtain ⟨i, hi⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
      ![Sum.inr z, Sum.inr z, Sum.inr z]
    rw [← hτsplit] at hi
    have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr z, Sum.inr z, Sum.inr z] i)
        = 2 * Δ - dist r z := by
      match i with
      | 0 => exact dLR r z
      | 1 => exact dLR r z
      | 2 => exact dLR r z
    rw [hd] at hi
    match i, hi with
    | ⟨0, _⟩, hi =>
      have hupd : Function.update (![Sum.inr z, Sum.inr z, Sum.inr z] : Config 3 (M ⊕ M))
          ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inr z, Sum.inr z] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      rw [hi, ← rot3 E₀ τ (Sum.inr z) (Sum.inr z) (Sum.inl r)]
    | ⟨1, _⟩, hi =>
      have hupd : Function.update (![Sum.inr z, Sum.inr z, Sum.inr z] : Config 3 (M ⊕ M))
          ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inr z, Sum.inl r, Sum.inr z] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      rw [hi]
      exact congrArg (fun t => t + (2 * Δ - dist r z))
        (swap12 E₀ τ (Sum.inr z) (Sum.inl r) (Sum.inr z))
    | ⟨2, _⟩, hi =>
      have hupd : Function.update (![Sum.inr z, Sum.inr z, Sum.inr z] : Config 3 (M ⊕ M))
          ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inr z, Sum.inr z, Sum.inl r] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      exact hi
  -- resolve (r̄, r̄, z)
  obtain ⟨i, hi⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
    ![Sum.inr r, Sum.inr r, Sum.inl z]
  rw [← hτsplit] at hi
  have hrrz : (workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inl z]
        = workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inl r] + dist r z)
      ∨ (workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inl z]
        = workFnU E₀ τ ![Sum.inl r, Sum.inr r, Sum.inl z] + 2 * Δ) := by
    match i, hi with
    | ⟨0, _⟩, hi =>
      right
      have hupd : Function.update (![Sum.inr r, Sum.inr r, Sum.inl z] : Config 3 (M ⊕ M))
          ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inr r, Sum.inl z] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr r, Sum.inr r, Sum.inl z] ⟨0, by norm_num⟩)
          = 2 * Δ := by
        show dist (Sum.inl r : M ⊕ M) (Sum.inr r) = 2 * Δ
        rw [dLR, dist_self]
        ring
      rw [hd] at hi
      exact hi
    | ⟨1, _⟩, hi =>
      right
      have hupd : Function.update (![Sum.inr r, Sum.inr r, Sum.inl z] : Config 3 (M ⊕ M))
          ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inr r, Sum.inl r, Sum.inl z] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr r, Sum.inr r, Sum.inl z] ⟨1, by norm_num⟩)
          = 2 * Δ := by
        show dist (Sum.inl r : M ⊕ M) (Sum.inr r) = 2 * Δ
        rw [dLR, dist_self]
        ring
      rw [hd] at hi
      have hperm : workFnU E₀ τ ![Sum.inr r, Sum.inl r, Sum.inl z]
          = workFnU E₀ τ ![Sum.inl r, Sum.inr r, Sum.inl z] := by
        refine perm3_eq E₀ τ _ _ (Equiv.swap 0 1) ?_
        intro l
        match l with
        | 0 => show (Sum.inr r : M ⊕ M)
                 = ![Sum.inl r, Sum.inr r, Sum.inl z] ((Equiv.swap (0 : Fin 3) 1) 0)
               rw [Equiv.swap_apply_left]; rfl
        | 1 => show (Sum.inl r : M ⊕ M)
                 = ![Sum.inl r, Sum.inr r, Sum.inl z] ((Equiv.swap (0 : Fin 3) 1) 1)
               rw [Equiv.swap_apply_right]; rfl
        | 2 => show (Sum.inl z : M ⊕ M)
                 = ![Sum.inl r, Sum.inr r, Sum.inl z] ((Equiv.swap (0 : Fin 3) 1) 2)
               rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl
      rw [hperm] at hi
      exact hi
    | ⟨2, _⟩, hi =>
      left
      have hupd : Function.update (![Sum.inr r, Sum.inr r, Sum.inl z] : Config 3 (M ⊕ M))
          ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inr r, Sum.inr r, Sum.inl r] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr r, Sum.inr r, Sum.inl z] ⟨2, by norm_num⟩)
          = dist r z := dLL r z
      rw [hd] at hi
      exact hi
  rcases hrrz with hcase | hcase
  · -- (r̄, r̄, z) resolves from z
    have hlip : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
        ≤ workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inl r] + 2 * Δ := by
      have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inr r, Sum.inr r, Sum.inl r]
      have hmc : moveCost (![Sum.inr r, Sum.inr r, Sum.inl r] : Config 3 (M ⊕ M))
          ![Sum.inr r, Sum.inr r, Sum.inr r] = 2 * Δ := by
        rw [mc3]
        show dist (Sum.inr r : M ⊕ M) (Sum.inr r) + dist (Sum.inr r : M ⊕ M) (Sum.inr r)
            + dist (Sum.inl r : M ⊕ M) (Sum.inr r) = 2 * Δ
        rw [dRR, dLR, dist_self]
        ring
      rw [hmc] at h
      exact h
    have hzr : dist z r = dist r z := dist_comm z r
    rw [hz3]
    linarith
  · -- (r̄, r̄, z) resolves from a copy of r̄
    have hlip : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
        ≤ workFnU E₀ τ ![Sum.inl r, Sum.inr r, Sum.inl z] + (2 * Δ + (2 * Δ - dist z r)) := by
      have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inl r, Sum.inr r, Sum.inl z]
      have hmc : moveCost (![Sum.inl r, Sum.inr r, Sum.inl z] : Config 3 (M ⊕ M))
          ![Sum.inr r, Sum.inr r, Sum.inr r] = 2 * Δ + (2 * Δ - dist z r) := by
        rw [mc3]
        show dist (Sum.inl r : M ⊕ M) (Sum.inr r) + dist (Sum.inr r : M ⊕ M) (Sum.inr r)
            + dist (Sum.inl z : M ⊕ M) (Sum.inr r) = 2 * Δ + (2 * Δ - dist z r)
        rw [dLR, dRR, dLR, dist_self]
        ring
      rw [hmc] at h
      exact h
    have hzr : dist z r = dist r z := dist_comm z r
    rw [hz3]
    linarith
