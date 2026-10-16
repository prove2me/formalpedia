-- Prove2me | solution 1 for NewsBundling.Negotiated.q2_lt_q1_and_q1_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T05:41:57.421728+00:00
-- url     : https://prove2.me/submissions/36426cfe-050c-48d4-8262-56186ed9c038

-- Formalization of de Cornière and Sarvary, TSE Working Paper 1152 (August
-- 2021), Appendix A, proof of Lemma 5, pp. 32–33. The result is theirs.
-- Alexander Richard Towell (queelius) directed the contribution; OpenAI Codex
-- developed and checked this Lean proof against the platform definitions.
import Definitions.Def_NewsBundling_Negotiated_Setting

open NewsBundling.Negotiated

theorem solution (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    (β < 1 → q2 β c Λ < q1 β c) ∧ q1 β c < 1 := by
  rcases hN with ⟨⟨hβ, _hβ1⟩, hc, ⟨_hΛ, hΛhalf⟩⟩
  have hc0 : 0 < c := by linarith
  have hΛ1 : 0 < 1 - Λ := by linarith
  have hden : 0 < 2 * (1 - Λ) * c := by positivity
  have htwo : 0 < 2 * c := by positivity
  constructor
  · intro hβ1
    rw [q2, q1, div_lt_div_iff₀ hden htwo]
    nlinarith [mul_pos (sub_pos.mpr hβ1) hc0]
  · rw [q1, div_lt_one htwo]
    linarith
