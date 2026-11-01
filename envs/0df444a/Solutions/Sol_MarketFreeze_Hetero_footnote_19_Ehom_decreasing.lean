-- Prove2me | solution 1 for MarketFreeze.Hetero.footnote_19_Ehom_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:04:30.386194+00:00
-- url     : https://prove2.me/submissions/63828f4f-cac2-4e8c-860e-0d09eb8899e4

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero.FN19Aux

open MarketFreeze.Hetero Set

lemma hasDerivAt_Ehom (P : Params) (θ : ℝ) (hθ : θ < 1) (hY : DifferentiableAt ℝ P.Y θ) :
    HasDerivAt (Ehom P) (2 * (P.X - P.I + P.c) / (1 - θ) ^ 2 - deriv P.Y θ) θ := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x * (P.X - P.I) + 2 * P.c) (2 * (P.X - P.I)) θ := by
    have := ((hasDerivAt_id θ).const_mul 2).mul_const (P.X - P.I) |>.add_const (2 * P.c)
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) θ := by
    simpa using (hasDerivAt_id θ).const_sub 1
  have h3 := (h1.div h2 (by linarith)).sub hY.hasDerivAt
  have hne : (1 - θ) ≠ 0 := by linarith
  have e : (2 * (P.X - P.I) * (1 - θ) - (2 * θ * (P.X - P.I) + 2 * P.c) * -1) / (1 - θ) ^ 2
      - deriv P.Y θ = 2 * (P.X - P.I + P.c) / (1 - θ) ^ 2 - deriv P.Y θ := by
    congr 1; ring
  rw [← e]
  exact h3

end MarketFreeze.Hetero.FN19Aux

open MarketFreeze.Hetero MarketFreeze.Hetero.FN19Aux Set in
theorem solution (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P) :
    (∀ θ ∈ Set.Icc 0 P.θbar, deriv (Ehom P) θ < 0) ∧
    StrictAntiOn (Ehom P) (Set.Icc 0 P.θbar) := by
  obtain ⟨hI, hδ0, hδ1, hb0, hθb, hc, hψ⟩ := h0
  have hXI : P.I < P.X := by nlinarith [h1.1]
  have hX : 0 < P.X := hI.trans hXI
  have hb1 : P.θbar < 1 := hθb.trans (by rw [div_lt_one hX]; exact hXI)
  obtain ⟨-, hYc, hYd, hY2, -⟩ := h2
  have hanti := hYc.antitoneOn_deriv hYd
  have hneg : ∀ θ ∈ Set.Icc 0 P.θbar, deriv (Ehom P) θ < 0 := by
    intro θ hθ
    have h1θ : 0 < 1 - θ := by linarith [hθ.2]
    rw [(hasDerivAt_Ehom P θ (by linarith [hθ.2]) (hYd θ hθ)).deriv]
    have hle : deriv P.Y P.θbar ≤ deriv P.Y θ := hanti hθ ⟨hb0, le_refl _⟩ hθ.2
    have hK : 0 < P.X - P.I + P.c := by linarith
    have hsq : (1 - P.θbar) ^ 2 ≤ (1 - θ) ^ 2 := by
      have : 0 < 1 - P.θbar := by linarith
      nlinarith [hθ.2]
    have : 2 * (P.X - P.I + P.c) / (1 - θ) ^ 2 ≤ 2 * (P.X - P.I + P.c) / (1 - P.θbar) ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) (by nlinarith [hb1]) hsq
    linarith
  refine ⟨hneg, ?_⟩
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 P.θbar)
  · intro x hx
    exact (hasDerivAt_Ehom P x (by linarith [hx.2]) (hYd x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact hneg x (Ioo_subset_Icc_self hx)
