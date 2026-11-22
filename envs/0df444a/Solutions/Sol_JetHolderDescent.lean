-- Prove2me | solution 1 for JetHolderDescent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:10:17.005085+00:00
-- url     : https://prove2.me/submissions/1082a62d-b0fa-445f-bf88-c2495242a726

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_JetHolderDescent

set_option autoImplicit false

theorem _root_.solution (κ d : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ θ : ℝ, 1 ≤ θ ∧
      ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (U : Set Plane),
        IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
        ∀ (n : ℕ) (L : ℝ) (Φ : Plane → Z), 0 ≤ L → ContDiffOn ℝ (⊤ : ℕ∞) Φ U →
        (∀ i ≤ n + 1, ∀ x ∈ U, ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) →
        ((∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i Φ x‖ ≤ L * θ) ∧
          ∀ x ∈ U, ∀ y ∈ U,
            ‖iteratedFDeriv ℝ n Φ x - iteratedFDeriv ℝ n Φ y‖ ≤ L * θ * ‖x - y‖ ^ κ) := by
  -- `theta = max 1 (d ^ (1 - kappa))`, exactly as the .tex produces it.  It is kept opaque
  -- below: only `1 <= theta` and `d ^ (1 - kappa) <= theta` are ever used.
  obtain ⟨θ, hθdef⟩ : ∃ t : ℝ, t = max 1 (d ^ (1 - κ)) := ⟨_, rfl⟩
  have hθ1 : (1 : ℝ) ≤ θ := by rw [hθdef]; exact le_max_left _ _
  refine ⟨θ, hθ1, ?_⟩
  -- THE SCALAR CORE.  On `[0, d]`, `t` is dominated by `theta * t ^ kappa`.
  have hpow : ∀ t : ℝ, 0 ≤ t → t ≤ d → t ≤ θ * t ^ κ := by
    intro t ht htd
    rcases eq_or_lt_of_le ht with h0 | hpos
    · rw [← h0, Real.zero_rpow (ne_of_gt hκ0), mul_zero]
    · have hsplit : t ^ (1 - κ) * t ^ κ = t := by
        rw [← Real.rpow_add hpos, show (1 - κ) + κ = 1 by ring, Real.rpow_one]
      have h1 : t ^ (1 - κ) ≤ d ^ (1 - κ) := Real.rpow_le_rpow ht htd (by linarith)
      have h2 : d ^ (1 - κ) ≤ θ := by rw [hθdef]; exact le_max_right _ _
      calc t = t ^ (1 - κ) * t ^ κ := hsplit.symm
        _ ≤ θ * t ^ κ :=
            mul_le_mul_of_nonneg_right (le_trans h1 h2) (Real.rpow_nonneg ht κ)
  -- LIPSCHITZ TO HOLDER, on a set of diameter at most `d`.
  have hlipHol : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (U : Set Plane),
      (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) → ∀ (Ψ : Plane → Z) (L : ℝ), 0 ≤ L →
      (∀ x ∈ U, ∀ y ∈ U, ‖Ψ x - Ψ y‖ ≤ L * ‖x - y‖) →
      ∀ x ∈ U, ∀ y ∈ U, ‖Ψ x - Ψ y‖ ≤ L * θ * ‖x - y‖ ^ κ := by
    intro Z _ _ U hdiam Ψ L hL hlip x hx y hy
    calc ‖Ψ x - Ψ y‖ ≤ L * ‖x - y‖ := hlip x hx y hy
      _ ≤ L * (θ * ‖x - y‖ ^ κ) :=
          mul_le_mul_of_nonneg_left (hpow _ (norm_nonneg _) (hdiam x hx y hy)) hL
      _ = L * θ * ‖x - y‖ ^ κ := by ring
  -- Smoothness of an iterated derivative on an open set.
  have hiter : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (U : Set Plane),
      IsOpen U → ∀ (Φ : Plane → Z), ContDiffOn ℝ (⊤ : ℕ∞) Φ U →
      ∀ i : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ i Φ) U := by
    intro Z _ _ U hUo Φ hΦ i x hx
    exact ((hΦ.contDiffAt (hUo.mem_nhds hx)).iteratedFDeriv_right
      (by norm_cast)).contDiffWithinAt
  -- THE DESCENT:  goodness descends one order, at the cost of the factor `theta`.
  intro Z _ _ U hUo hUc hdiam n L Φ hL hΦ hsup
  refine ⟨fun i hi x hx => le_trans (hsup i (by omega) x hx) (by nlinarith), ?_⟩
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ n Φ) x := by
    intro x hx
    exact (((hiter Z U hUo Φ hΦ n).differentiableOn (by simp)) x hx).differentiableAt
      (hUo.mem_nhds hx)
  have hbd : ∀ x ∈ U, ‖fderiv ℝ (iteratedFDeriv ℝ n Φ) x‖ ≤ L := by
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    exact hsup (n + 1) le_rfl x hx
  exact hlipHol _ U hdiam (iteratedFDeriv ℝ n Φ) L hL
    (fun x hx y hy => hUc.norm_image_sub_le_of_norm_fderiv_le hdiff hbd hy hx)
