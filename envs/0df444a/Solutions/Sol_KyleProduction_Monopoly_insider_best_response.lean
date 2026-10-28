-- Prove2me | solution 1 for KyleProduction.Monopoly.insider_best_response
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:46:06.995354+00:00
-- url     : https://prove2.me/submissions/7516d42d-efb8-4d32-8128-cb8af7dd342e

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

open MeasureTheory ProbabilityTheory

namespace Aux_insider_br
open KyleProduction.Monopoly

theorem payoff_eq (P : Params) (e : LinStrat) (v d : ℝ) :
    insiderPayoff P e v d = (v - e.μ - e.lam * d) * d := by
  unfold insiderPayoff price lawU
  have hI : Integrable (fun u : ℝ => u) (gaussianReal 0 P.Su.toNNReal) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 (by simp))
  have e1 : (fun u : ℝ => (v - (e.μ + e.lam * (d + u))) * d) =
      fun u => (v - e.μ - e.lam * d) * d - (e.lam * d) * u := by
    funext u; ring
  rw [e1, integral_sub (integrable_const _) (hI.const_mul _), integral_const,
    integral_const_mul (e.lam * d) (fun u : ℝ => u), integral_id_gaussianReal]
  simp

end Aux_insider_br

open KyleProduction.Monopoly in
theorem solution (P : Params) (hS : P.Standing) (e : LinStrat) (v : ℝ) :
    (∀ d : ℝ, insiderPayoff P e v d = (v - e.μ - e.lam * d) * d) ∧
    (0 < e.lam → ∀ d : ℝ,
      ((∀ d' : ℝ, insiderPayoff P e v d' ≤ insiderPayoff P e v d) ↔
        d = -e.μ / (2 * e.lam) + v / (2 * e.lam))) := by
  refine ⟨Aux_insider_br.payoff_eq P e v, fun hl d => ?_⟩
  simp only [Aux_insider_br.payoff_eq]
  set ds := -e.μ / (2 * e.lam) + v / (2 * e.lam) with hds
  have key : ∀ x : ℝ, (v - e.μ - e.lam * x) * x =
      (v - e.μ - e.lam * ds) * ds - e.lam * (x - ds) ^ 2 := by
    intro x; rw [hds]; field_simp; ring
  constructor
  · intro h
    have h1 := h ds
    rw [key ds, key d] at h1
    have h2 : e.lam * (d - ds) ^ 2 ≤ 0 := by nlinarith
    have h3 : (d - ds) ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos hl hc
      linarith
    have : d - ds = 0 := by nlinarith [sq_nonneg (d - ds)]
    linarith
  · rintro rfl d'
    rw [key d', key ds]
    have : 0 ≤ e.lam * (d' - ds) ^ 2 := by positivity
    nlinarith
