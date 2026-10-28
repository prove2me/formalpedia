-- Prove2me | solution 1 for MarketFreeze.Hetero.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:05:06.052065+00:00
-- url     : https://prove2.me/submissions/2eb59ea8-9f7a-4bdb-a737-337023c8a804

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

open MarketFreeze.Hetero in
theorem solution (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P)
    (hlam : 0 < P.lam) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 P.θbar)
    (n : ℝ) (hn : 0 ≤ n) :
    (∀ E : ℝ, E ∈ Set.Icc 0 P.I →
      (icRHS P θ E (P.I - E) ≤ icLHS P θ n E (P.I - E) ↔
        Ehet P θ n ≤ E)) ∧
    StrictAntiOn (fun m : ℝ => P.lam * (P.X - price P m) / (1 + m)) (Set.Ici 0) ∧
    (∀ lam' : ℝ, P.lam < lam' →
      P.lam * (P.X - price P n) / (1 + n) <
        lam' * (P.X - price P n) / (1 + n)) := by
  obtain ⟨hI, hδ0, hδ1, hθb0, hθbI, hc, hψ⟩ := h0
  obtain ⟨hA1a, hA1b⟩ := h1
  obtain ⟨_, _, _, _, hY0⟩ := h2
  have hXI : P.I < P.X := by nlinarith
  have hX : 0 < P.X := by linarith
  have hθ1 : θ < 1 := by
    have : P.I / P.X < 1 := by rw [div_lt_one hX]; exact hXI
    linarith [hθ.2]
  have hθ1' : 0 < 1 - θ := by linarith
  have hA : 0 < P.X - P.I := by linarith
  have hn1 : 0 < 1 + n := by linarith
  have hgap : ∀ m : ℝ, P.X - price P m = (P.X - P.I) / (1 + m) := by
    intro m; unfold price; ring
  refine ⟨?_, ?_, ?_⟩
  · intro E _
    have hB : 0 ≤ (1 / 2 : ℝ) * (1 - θ) * P.lam * (P.X - P.I) / (1 + n) ^ 2 := by positivity
    have hL1 : icLHS P θ n E (P.I - E) - (-P.ψ * E) =
        (P.X - P.I - P.c) + (1 / 2 : ℝ) * (1 - θ) * P.lam * (P.X - P.I) / (1 + n) ^ 2 := by
      unfold icLHS buyerMeet
      rw [hgap]
      field_simp
      ring
    have hL2 : icLHS P θ n E (P.I - E) -
        (-E - P.ψ * E + (θ + (1 / 2 : ℝ) * (1 - θ)) *
          (P.X - (P.I - E) + P.X - P.I) - (1 / 2 : ℝ) * (1 - θ) * P.Y θ) =
        (1 / 2 : ℝ) * (1 - θ) * (E - Ehet P θ n) := by
      unfold icLHS buyerMeet Ehet Ehom
      rw [hgap]
      field_simp
      ring
    have h3' : 0 < P.X - P.I - P.c - P.ψ * (2 * P.c - P.Y 0) := h3
    have hpos1 : 0 < P.X - P.I - P.c := by
      nlinarith [mul_pos hψ (by linarith : (0:ℝ) < 2 * P.c - P.Y 0)]
    unfold icRHS
    rw [max_le_iff]
    constructor
    · rintro ⟨_, h⟩
      have : 0 ≤ (1 / 2 : ℝ) * (1 - θ) * (E - Ehet P θ n) := by linarith
      have h' : 0 ≤ E - Ehet P θ n := by
        by_contra hc'
        push_neg at hc'
        have : (1 / 2 : ℝ) * (1 - θ) * (E - Ehet P θ n) < 0 :=
          mul_neg_of_pos_of_neg (by positivity) hc'
        linarith
      linarith
    · intro h
      constructor
      · linarith
      · have : 0 ≤ (1 / 2 : ℝ) * (1 - θ) * (E - Ehet P θ n) :=
          mul_nonneg (by positivity) (by linarith)
        linarith
  · intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    show P.lam * (P.X - price P b) / (1 + b) < P.lam * (P.X - price P a) / (1 + a)
    have key : ∀ m : ℝ, 0 ≤ m → P.lam * (P.X - price P m) / (1 + m) =
        P.lam * (P.X - P.I) / (1 + m) ^ 2 := by
      intro m hm
      rw [hgap]
      have : (1 + m) ≠ 0 := by linarith
      field_simp
    rw [key a ha, key b hb]
    apply div_lt_div_of_pos_left (by positivity) (by positivity)
    nlinarith
  · intro lam' hlt
    apply div_lt_div_of_pos_right _ hn1
    apply mul_lt_mul_of_pos_right hlt
    rw [hgap]
    positivity
