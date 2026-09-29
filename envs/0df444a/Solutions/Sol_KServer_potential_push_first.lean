-- Prove2me | solution 1 for KServer.potential_push_first
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T06:46:18.983054+00:00
-- url     : https://prove2.me/submissions/9f3bd170-c7b4-49a8-8870-e9267994e7e2

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_resolves
import Theorems.Thm_KServer_workFnU_quasiconvex_three
import Theorems.Thm_KServer_potential_push_mid
import Theorems.Thm_KServer_antipode_config_resolves_original

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

private theorem swap01' {N : Type} [MetricSpace N] (C₀ : Config 3 N) (σ : List N)
    (p q c : N) : workFnU C₀ σ ![p, q, c] = workFnU C₀ σ ![q, p, c] := by
  refine perm3_eq C₀ σ _ _ (Equiv.swap 0 1) ?_
  intro i
  match i with
  | 0 => show p = ![q, p, c] ((Equiv.swap (0 : Fin 3) 1) 0); rw [Equiv.swap_apply_left]; rfl
  | 1 => show q = ![q, p, c] ((Equiv.swap (0 : Fin 3) 1) 1); rw [Equiv.swap_apply_right]; rfl
  | 2 => show c = ![q, p, c] ((Equiv.swap (0 : Fin 3) 1) 2)
         rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl

/-- **Pushing the request from the first anchor slot to the last.** -/
theorem solution (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r y z : M) :
    (@workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inl z, Sum.inl r]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inl r]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inr r]
      ≤ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl z]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inr y, Sum.inl z]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inr z])
    ∨ (@workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inl y, Sum.inl r]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inr y, Sum.inl r]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inr r]
      ≤ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl z]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inr y, Sum.inl z]
        + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr z, Sum.inr z, Sum.inr z]) := by
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
  have dRL : ∀ a b : M, dist (Sum.inr a : M ⊕ M) (Sum.inl b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  -- forced resolution of the all-antipodes configuration of z
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
  -- resolve (ȳ, ȳ, z)
  obtain ⟨i, hi⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
    ![Sum.inr y, Sum.inr y, Sum.inl z]
  rw [← hτsplit] at hi
  have hyyz : (workFnU E₀ τ ![Sum.inr y, Sum.inr y, Sum.inl z]
        = workFnU E₀ τ ![Sum.inr y, Sum.inl r, Sum.inl z] + (2 * Δ - dist r y))
      ∨ (workFnU E₀ τ ![Sum.inr y, Sum.inr y, Sum.inl z]
        = workFnU E₀ τ ![Sum.inr y, Sum.inr y, Sum.inl r] + dist r z) := by
    match i, hi with
    | ⟨0, _⟩, hi =>
      left
      have hupd : Function.update (![Sum.inr y, Sum.inr y, Sum.inl z] : Config 3 (M ⊕ M))
          ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inr y, Sum.inl z] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr y, Sum.inr y, Sum.inl z] ⟨0, by norm_num⟩)
          = 2 * Δ - dist r y := dLR r y
      rw [hd] at hi
      rw [hi]
      exact congrArg (fun t => t + (2 * Δ - dist r y))
        (swap01' E₀ τ (Sum.inl r) (Sum.inr y) (Sum.inl z))
    | ⟨1, _⟩, hi =>
      left
      have hupd : Function.update (![Sum.inr y, Sum.inr y, Sum.inl z] : Config 3 (M ⊕ M))
          ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inr y, Sum.inl r, Sum.inl z] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr y, Sum.inr y, Sum.inl z] ⟨1, by norm_num⟩)
          = 2 * Δ - dist r y := dLR r y
      rw [hd] at hi
      exact hi
    | ⟨2, _⟩, hi =>
      right
      have hupd : Function.update (![Sum.inr y, Sum.inr y, Sum.inl z] : Config 3 (M ⊕ M))
          ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inr y, Sum.inr y, Sum.inl r] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr y, Sum.inr y, Sum.inl z] ⟨2, by norm_num⟩)
          = dist r z := dLL r z
      rw [hd] at hi
      exact hi
  rcases hyyz with hres | hres
  · -- Case A: (ȳ,ȳ,z) resolves from a copy of ȳ
    left
    have h1 : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inl z]
        ≤ workFnU E₀ τ ![Sum.inr r, Sum.inl y, Sum.inl z] + (2 * Δ - dist y r) := by
      have h := lip ![Sum.inr r, Sum.inr r, Sum.inl z] ![Sum.inr r, Sum.inl y, Sum.inl z]
      have hmc : moveCost (![Sum.inr r, Sum.inl y, Sum.inl z] : Config 3 (M ⊕ M))
          ![Sum.inr r, Sum.inr r, Sum.inl z] = 2 * Δ - dist y r := by
        rw [mc3]
        show dist r r + dist (Sum.inl y : M ⊕ M) (Sum.inr r) + dist z z = 2 * Δ - dist y r
        rw [dist_self, dist_self, dLR]
        ring
      rw [hmc] at h
      exact h
    have hpm := potential_push_mid M Δ hΔ0 hΔ C₀ σ r z
    rw [← hτ] at hpm
    have hswap : workFnU E₀ τ ![Sum.inr y, Sum.inl z, Sum.inl r]
        = workFnU E₀ τ ![Sum.inr y, Sum.inl r, Sum.inl z] :=
      swap12 E₀ τ (Sum.inr y) (Sum.inl z) (Sum.inl r)
    have hc : dist r y = dist y r := dist_comm r y
    rw [hswap]
    linarith
  · -- Case B: (ȳ,ȳ,z) resolves from z
    rcases antipode_config_resolves_original M Δ hΔ0 hΔ C₀ σ r y z with hd | hd
    · -- B1: (r̄, y, z) resolves from y
      left
      rw [← hτ] at hd
      have qc := workFnU_quasiconvex_three (M ⊕ M) E₀ τ (Sum.inl r) (Sum.inr y) (Sum.inr y)
        (Sum.inr r) (Sum.inl z)
      have hmin : min (workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inr r]
            + workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inl z])
          (workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inl z]
            + workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inr r])
          = workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inr r]
            + workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inl z] := by
        rw [add_comm (workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inl z])
          (workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inr r])]
        exact min_self _
      rw [hmin] at qc
      have hlipr : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
          ≤ workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inr r] + (2 * Δ + dist y r) := by
        have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inl r, Sum.inr y, Sum.inr r]
        have hmc : moveCost (![Sum.inl r, Sum.inr y, Sum.inr r] : Config 3 (M ⊕ M))
            ![Sum.inr r, Sum.inr r, Sum.inr r] = 2 * Δ + dist y r := by
          rw [mc3]
          show dist (Sum.inl r : M ⊕ M) (Sum.inr r) + dist y r + dist r r = 2 * Δ + dist y r
          rw [dLR, dist_self]
          ring
        rw [hmc] at h
        exact h
      -- permutation normalisations
      have hp1 : workFnU E₀ τ ![Sum.inr y, Sum.inr y, Sum.inl r]
          = workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inr y] :=
        rot3 E₀ τ (Sum.inr y) (Sum.inr y) (Sum.inl r)
      have hp2 : workFnU E₀ τ ![Sum.inr r, Sum.inl r, Sum.inl z]
          = workFnU E₀ τ ![Sum.inl r, Sum.inr r, Sum.inl z] :=
        swap01' E₀ τ (Sum.inr r) (Sum.inl r) (Sum.inl z)
      have hp3 : workFnU E₀ τ ![Sum.inr y, Sum.inl z, Sum.inl r]
          = workFnU E₀ τ ![Sum.inl r, Sum.inr y, Sum.inl z] :=
        rot3 E₀ τ (Sum.inr y) (Sum.inl z) (Sum.inl r)
      have hc : dist r z = dist z r := dist_comm r z
      rw [hres, hz3, hd, hp3]
      rw [hp1] at hres ⊢
      rw [hp2] at hd ⊢
      linarith [qc, hlipr, hres, hd]
    · -- B2: (r̄, y, z) resolves from z
      right
      rw [← hτ] at hd
      have qc := workFnU_quasiconvex_three (M ⊕ M) E₀ τ (Sum.inl r) (Sum.inr z) (Sum.inr z)
        (Sum.inr r) (Sum.inl y)
      have hmin : min (workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inr r]
            + workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inl y])
          (workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inl y]
            + workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inr r])
          = workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inr r]
            + workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inl y] := by
        rw [add_comm (workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inl y])
          (workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inr r])]
        exact min_self _
      rw [hmin] at qc
      have hlipr : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
          ≤ workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inr r] + (2 * Δ + dist z r) := by
        have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inl r, Sum.inr z, Sum.inr r]
        have hmc : moveCost (![Sum.inl r, Sum.inr z, Sum.inr r] : Config 3 (M ⊕ M))
            ![Sum.inr r, Sum.inr r, Sum.inr r] = 2 * Δ + dist z r := by
          rw [mc3]
          show dist (Sum.inl r : M ⊕ M) (Sum.inr r) + dist z r + dist r r = 2 * Δ + dist z r
          rw [dLR, dist_self]
          ring
        rw [hmc] at h
        exact h
      have hp1 : workFnU E₀ τ ![Sum.inr z, Sum.inr z, Sum.inl r]
          = workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inr z] :=
        rot3 E₀ τ (Sum.inr z) (Sum.inr z) (Sum.inl r)
      have hp2 : workFnU E₀ τ ![Sum.inr r, Sum.inl y, Sum.inl r]
          = workFnU E₀ τ ![Sum.inl r, Sum.inr r, Sum.inl y] :=
        rot3 E₀ τ (Sum.inr r) (Sum.inl y) (Sum.inl r)
      have hp3 : workFnU E₀ τ ![Sum.inr z, Sum.inl y, Sum.inl r]
          = workFnU E₀ τ ![Sum.inl r, Sum.inr z, Sum.inl y] :=
        rot3 E₀ τ (Sum.inr z) (Sum.inl y) (Sum.inl r)
      have hc : dist r z = dist z r := dist_comm r z
      rw [hres, hz3, hd, hp3]
      rw [hp1] at hz3 ⊢
      rw [hp2] at hd ⊢
      linarith [qc, hlipr]
