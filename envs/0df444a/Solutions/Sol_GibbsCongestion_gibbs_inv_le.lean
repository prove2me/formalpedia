-- Prove2me | solution 1 for GibbsCongestion.gibbs_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:29:04.153476+00:00
-- url     : https://prove2.me/submissions/7ff5485e-d2b4-4a87-a480-998e93473bd9

import Mathlib
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_potentialMax
import Definitions.Def_GibbsCongestion_gibbs

open GibbsCongestion in
theorem solution {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) (T : ℝ) (hT : 0 ≤ T) (s : Fin n → P) :
    (gibbs P n c T s)⁻¹ ≤ (P.card : ℝ) ^ n * Real.exp (T * potentialMax P n c) := by
  have hΦ : ∀ t : Fin n → P, 0 ≤ potential c t := fun t =>
    Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun k _ => hc_nonneg e k))
  have hZ : ∑ t : Fin n → P, Real.exp (-T * potential c t) ≤ (P.card : ℝ) ^ n := by
    calc ∑ t : Fin n → P, Real.exp (-T * potential c t) ≤ ∑ _t : Fin n → P, (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ => by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by nlinarith [hΦ t]))
      _ = (P.card : ℝ) ^ n := by simp
  have hmax : potential c s ≤ potentialMax P n c :=
    le_ciSup (Set.finite_range _).bddAbove s
  unfold gibbs
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_mul, neg_neg]
  exact mul_le_mul hZ (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmax hT))
    (Real.exp_pos _).le (by positivity)
