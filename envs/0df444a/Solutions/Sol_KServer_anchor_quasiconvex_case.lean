-- Prove2me | solution 1 for KServer.anchor_quasiconvex_case
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T07:26:32.556003+00:00
-- url     : https://prove2.me/submissions/3dbdf139-bd8d-4f5b-876f-ad81bce2eff2

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_resolves
import Theorems.Thm_KServer_workFnU_quasiconvex_three

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

/-- **The quasiconvexity case of the anchoring theorem.** -/
theorem solution (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r x₁ x₂ x₃ : M)
    (h0 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl x₁, Sum.inl x₂, Sum.inl r]
          + dist r x₃)
    (h1 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x₁, Sum.inl r, Sum.inl x₃]
          + dist r x₂)
    (h2 : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x₂, Sum.inl r, Sum.inl x₃]
          + (2 * Δ - dist r x₂)) :
    ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₂ x₃ r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₁ x₂ x₃
    ∨ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₁ x₃ r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) x₁ x₂ x₃ := by
  classical
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  set E₀ : Config 3 (M ⊕ M) := fun i => Sum.inl (C₀ i) with hE₀
  set τ : List (M ⊕ M) := (σ ++ [r]).map Sum.inl with hτ
  have hτsplit : τ = σ.map Sum.inl ++ [Sum.inl r] := by rw [hτ]; simp
  have h3 : (1 : ℕ) ≤ 3 := by norm_num
  have dLR : ∀ a b : M, dist (Sum.inl a : M ⊕ M) (Sum.inr b) = 2 * Δ - dist a b :=
    fun _ _ => rfl
  have lip : ∀ X Y : Config 3 (M ⊕ M), workFnU E₀ τ X ≤ workFnU E₀ τ Y + moveCost Y X :=
    fun X Y => workFnU_lipschitz 3 h3 (M ⊕ M) E₀ τ X Y
  have hΦ : ∀ p q s : M, ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) p q s
      = workFnU E₀ τ ![Sum.inl p, Sum.inl q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr p, Sum.inl q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr q, Sum.inr q, Sum.inl s]
        + workFnU E₀ τ ![Sum.inr s, Sum.inr s, Sum.inr s] := fun p q s => rfl
  -- forced resolution of the all-antipodes configuration of x₃
  have h33 : workFnU E₀ τ ![Sum.inr x₃, Sum.inr x₃, Sum.inr x₃]
      = workFnU E₀ τ ![Sum.inr x₃, Sum.inr x₃, Sum.inl r] + (2 * Δ - dist r x₃) := by
    obtain ⟨i, hi⟩ := workFnU_resolves 3 h3 (M ⊕ M) E₀ (σ.map Sum.inl) (Sum.inl r)
      ![Sum.inr x₃, Sum.inr x₃, Sum.inr x₃]
    rw [← hτsplit] at hi
    have hd : dist (Sum.inl r : M ⊕ M) (![Sum.inr x₃, Sum.inr x₃, Sum.inr x₃] i)
        = 2 * Δ - dist r x₃ := by
      match i with
      | 0 => exact dLR r x₃
      | 1 => exact dLR r x₃
      | 2 => exact dLR r x₃
    rw [hd] at hi
    match i, hi with
    | ⟨0, _⟩, hi =>
      have hupd : Function.update (![Sum.inr x₃, Sum.inr x₃, Sum.inr x₃] : Config 3 (M ⊕ M))
          ⟨0, by norm_num⟩ (Sum.inl r) = ![Sum.inl r, Sum.inr x₃, Sum.inr x₃] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      rw [hi, ← rot3 E₀ τ (Sum.inr x₃) (Sum.inr x₃) (Sum.inl r)]
    | ⟨1, _⟩, hi =>
      have hupd : Function.update (![Sum.inr x₃, Sum.inr x₃, Sum.inr x₃] : Config 3 (M ⊕ M))
          ⟨1, by norm_num⟩ (Sum.inl r) = ![Sum.inr x₃, Sum.inl r, Sum.inr x₃] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      rw [hi]
      exact congrArg (fun t => t + (2 * Δ - dist r x₃))
        (swap12 E₀ τ (Sum.inr x₃) (Sum.inl r) (Sum.inr x₃))
    | ⟨2, _⟩, hi =>
      have hupd : Function.update (![Sum.inr x₃, Sum.inr x₃, Sum.inr x₃] : Config 3 (M ⊕ M))
          ⟨2, by norm_num⟩ (Sum.inl r) = ![Sum.inr x₃, Sum.inr x₃, Sum.inl r] := by
        funext l
        match l with
        | 0 => rfl
        | 1 => rfl
        | 2 => rfl
      rw [hupd] at hi
      exact hi
  -- quasiconvexity with the request as the common coordinate
  have qc := workFnU_quasiconvex_three (M ⊕ M) E₀ τ (Sum.inl r) (Sum.inl x₁) (Sum.inl x₂)
    (Sum.inr x₁) (Sum.inl x₃)
  -- permutation normalisations
  have p1 : workFnU E₀ τ ![Sum.inl x₁, Sum.inl x₂, Sum.inl r]
      = workFnU E₀ τ ![Sum.inl r, Sum.inl x₁, Sum.inl x₂] :=
    rot3 E₀ τ (Sum.inl x₁) (Sum.inl x₂) (Sum.inl r)
  have p2 : workFnU E₀ τ ![Sum.inr x₁, Sum.inl r, Sum.inl x₃]
      = workFnU E₀ τ ![Sum.inl r, Sum.inr x₁, Sum.inl x₃] :=
    swap01' E₀ τ (Sum.inr x₁) (Sum.inl r) (Sum.inl x₃)
  rcases min_cases (workFnU E₀ τ ![Sum.inl r, Sum.inl x₁, Sum.inr x₁]
      + workFnU E₀ τ ![Sum.inl r, Sum.inl x₂, Sum.inl x₃])
      (workFnU E₀ τ ![Sum.inl r, Sum.inl x₁, Sum.inl x₃]
      + workFnU E₀ τ ![Sum.inl r, Sum.inl x₂, Sum.inr x₁]) with ⟨he, -⟩ | ⟨he, -⟩ <;>
    rw [he] at qc
  · -- branch (a): pair (x₁, x̄₁) with (x₂, x₃)
    left
    have hb : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
        ≤ workFnU E₀ τ ![Sum.inl r, Sum.inl x₁, Sum.inr x₁] + 4 * Δ := by
      have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inl r, Sum.inl x₁, Sum.inr x₁]
      have hmc : moveCost (![Sum.inl r, Sum.inl x₁, Sum.inr x₁] : Config 3 (M ⊕ M))
          ![Sum.inr r, Sum.inr r, Sum.inr r] = 4 * Δ := by
        rw [mc3]
        show dist (Sum.inl r : M ⊕ M) (Sum.inr r) + dist (Sum.inl x₁ : M ⊕ M) (Sum.inr r)
            + dist x₁ r = 4 * Δ
        rw [dLR, dLR, dist_self]
        ring
      rw [hmc] at h
      exact h
    have pt0 : workFnU E₀ τ ![Sum.inl x₂, Sum.inl x₃, Sum.inl r]
        = workFnU E₀ τ ![Sum.inl r, Sum.inl x₂, Sum.inl x₃] :=
      rot3 E₀ τ (Sum.inl x₂) (Sum.inl x₃) (Sum.inl r)
    have pt1 : workFnU E₀ τ ![Sum.inr x₂, Sum.inl x₃, Sum.inl r]
        = workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₃] :=
      swap12 E₀ τ (Sum.inr x₂) (Sum.inl x₃) (Sum.inl r)
    rw [hΦ, hΦ, pt0, pt1]
    linarith [qc, hb, h0, h1, h2, h33, p1, p2]
  · -- branch (b): pair (x₁, x₃) with (x₂, x̄₁)
    right
    have hbA : workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
        ≤ workFnU E₀ τ ![Sum.inl r, Sum.inl x₂, Sum.inr x₁] + dist r x₃ := by
      have h := lip ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃] ![Sum.inr x₁, Sum.inl x₂, Sum.inl r]
      have hmc : moveCost (![Sum.inr x₁, Sum.inl x₂, Sum.inl r] : Config 3 (M ⊕ M))
          ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃] = dist r x₃ := by
        rw [mc3]
        show dist x₁ x₁ + dist x₂ x₂ + dist r x₃ = dist r x₃
        rw [dist_self, dist_self]
        ring
      rw [hmc] at h
      have hp : workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₂, Sum.inl r]
          = workFnU E₀ τ ![Sum.inl r, Sum.inl x₂, Sum.inr x₁] := by
        rw [rot3 E₀ τ (Sum.inr x₁) (Sum.inl x₂) (Sum.inl r)]
        exact swap12 E₀ τ (Sum.inl r) (Sum.inr x₁) (Sum.inl x₂)
      rw [hp] at h
      exact h
    have hbB : workFnU E₀ τ ![Sum.inr r, Sum.inr r, Sum.inr r]
        ≤ workFnU E₀ τ ![Sum.inr x₂, Sum.inl r, Sum.inl x₃]
          + (4 * Δ + dist x₂ r - dist x₃ r) := by
      have h := lip ![Sum.inr r, Sum.inr r, Sum.inr r] ![Sum.inr x₂, Sum.inl r, Sum.inl x₃]
      have hmc : moveCost (![Sum.inr x₂, Sum.inl r, Sum.inl x₃] : Config 3 (M ⊕ M))
          ![Sum.inr r, Sum.inr r, Sum.inr r] = 4 * Δ + dist x₂ r - dist x₃ r := by
        rw [mc3]
        show dist x₂ r + dist (Sum.inl r : M ⊕ M) (Sum.inr r)
            + dist (Sum.inl x₃ : M ⊕ M) (Sum.inr r) = 4 * Δ + dist x₂ r - dist x₃ r
        rw [dLR, dLR, dist_self]
        ring
      rw [hmc] at h
      exact h
    have pt0 : workFnU E₀ τ ![Sum.inl x₁, Sum.inl x₃, Sum.inl r]
        = workFnU E₀ τ ![Sum.inl r, Sum.inl x₁, Sum.inl x₃] :=
      rot3 E₀ τ (Sum.inl x₁) (Sum.inl x₃) (Sum.inl r)
    have pt1 : workFnU E₀ τ ![Sum.inr x₁, Sum.inl x₃, Sum.inl r]
        = workFnU E₀ τ ![Sum.inr x₁, Sum.inl r, Sum.inl x₃] :=
      swap12 E₀ τ (Sum.inr x₁) (Sum.inl x₃) (Sum.inl r)
    have hc1 : dist x₂ r = dist r x₂ := dist_comm x₂ r
    have hc2 : dist x₃ r = dist r x₃ := dist_comm x₃ r
    rw [hΦ, hΦ, pt0, pt1]
    linarith [qc, hbA, hbB, h0, h1, h2, h33, p1, p2, hc1, hc2]
