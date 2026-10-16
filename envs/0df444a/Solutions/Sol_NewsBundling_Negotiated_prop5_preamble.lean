-- Prove2me | solution 1 for NewsBundling.Negotiated.prop5_preamble
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T05:44:30.39466+00:00
-- url     : https://prove2.me/submissions/8112f334-d2d0-4e17-9c9a-e7a01e5c5a6c

-- Formalization of de Cornière and Sarvary, TSE Working Paper 1152 (August
-- 2021), Appendix A, proof of Proposition 5, p. 33. Mathematical credit: authors.
-- Alexander Richard Towell (queelius) directed this contribution; OpenAI Codex
-- developed and checked the Lean proof against the platform definitions.
import Definitions.Def_NewsBundling_Negotiated_Setting

open NewsBundling.Negotiated

theorem solution (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    β < 1 → q2 β c Λ < β / c ∧ β / c < q1 β c := by
  rcases hN with ⟨⟨hβ, _hβ1⟩, hc, ⟨hΛ, hΛhalf⟩⟩
  intro hβ1
  have hc0 : 0 < c := by linarith
  have hΛ1 : 0 < 1 - Λ := by linarith
  have hden : 0 < 2 * (1 - Λ) * c := by positivity
  have htwo : 0 < 2 * c := by positivity
  have hgap : 0 < (1 - β) * c := mul_pos (sub_pos.mpr hβ1) hc0
  constructor
  · rw [q2, div_lt_div_iff₀ hden hc0]
    nlinarith [mul_pos hΛ hgap]
  · rw [q1, div_lt_div_iff₀ hc0 htwo]
    nlinarith
