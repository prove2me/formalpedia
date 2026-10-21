-- Prove2me | solution 1 for LPCommunity.LPFail.xTilde_objective
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:40:43.547459+00:00
-- url     : https://prove2.me/submissions/1ca4ddf2-0cb1-4d96-b848-3d17621413e1

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_LPFail_XTilde

set_option autoImplicit false
open Finset
open scoped Classical ENNReal
open LPCommunity.LPFail

theorem lpf_card_pairs {n : ℕ} (G : SimpleGraph (Fin n)) :
    (univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2).card = G.edgeFinset.card := by
  apply Finset.card_bij (fun p _ => s(p.1, p.2))
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simpa using hp.2
  · intro p hp q hq h
    simp only [mem_filter, mem_univ, true_and] at hp hq
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have := hp.1; have := hq.1
      rw [h1] at *; rw [h2] at *
      omega
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he
      rcases lt_trichotomy a b with h | h | h
      · exact ⟨(a, b), by simp [h, hab], rfl⟩
      · exact absurd h hab.ne
      · exact ⟨(b, a), by simp [h, hab.symm], Sym2.eq_swap⟩

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hconn : G.Connected) (hn : 5 ≤ n) :
    LPCommunity.LPRecovery.lpObj G (xTilde G) =
      (1 + cG G) / ((rhoAvg G).toReal + cG G * (1 - 1 / (n : ℝ))) * (G.edgeFinset.card : ℝ) / 2 := by
  set K : ℝ := (1 + cG G) / (2 * (rhoAvg G).toReal + 2 * cG G * (1 - 1 / (n : ℝ))) with hK
  have h1 : LPCommunity.LPRecovery.lpObj G (xTilde G) =
      ∑ i, ∑ j, if i < j ∧ G.Adj i j then K else 0 := by
    unfold LPCommunity.LPRecovery.lpObj
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i < j ∧ G.Adj i j
    · simp only [h, and_self, if_true]
      have hne : i ≠ j := h.1.ne
      have : rho G i j = 1 := by
        unfold rho; exact SimpleGraph.edist_eq_one_iff_adj.mpr h.2
      simp only [xTilde, hne, if_false, this, hK]
      simp
    · simp [h]
  have h2 : (∑ i, ∑ j, if i < j ∧ G.Adj i j then K else 0) = K * (G.edgeFinset.card : ℝ) := by
    rw [← lpf_card_pairs G, ← Finset.sum_product' (f := fun i j => if i < j ∧ G.Adj i j then K else 0)]
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [h1, h2, hK]
  by_cases hD : (rhoAvg G).toReal + cG G * (1 - 1 / (n : ℝ)) = 0
  · have : 2 * (rhoAvg G).toReal + 2 * cG G * (1 - 1 / (n : ℝ)) = 0 := by linarith
    rw [hD, this]; simp
  · have : 2 * (rhoAvg G).toReal + 2 * cG G * (1 - 1 / (n : ℝ)) ≠ 0 := by
      intro h; apply hD; linarith
    field_simp
