-- Prove2me | solution 1 for MDPFinance.MeanVariance.mutual_fund_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T01:00:48.904237+00:00
-- url     : https://prove2.me/submissions/a8eba8ab-d092-4eb4-bf8a-24606c897fa5

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open MDPFinance.MeanVariance in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1)))
    (πstar : ℕ → ℝ → (Fin d → ℝ))
    (hπstar : ∀ n < M.N, ∀ x : ℝ, πstar n x =
      fun k => ((M.μ - dseq 0 * M.x0 * M.S0 M.N) / (1 - dseq 0) * (M.S0 n / M.S0 M.N) - x) *
        ((M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)) k)) :
    ∃ mutualFund : ℕ → (Fin d → ℝ), ∀ n < M.N, ∀ x : ℝ,
      ∃ s : ℝ, πstar n x = fun k => s * mutualFund n k := by
  refine ⟨fun n => (M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)), fun n hn x => ?_⟩
  exact ⟨_, hπstar n hn x⟩
