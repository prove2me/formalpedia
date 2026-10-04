-- Prove2me | solution 1 for MDPFinance.MeanVariance.mean_variance_solution
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:24:09.321859+00:00
-- url     : https://prove2.me/submissions/b697a5ea-793d-450a-bd5a-0ce530e9cf47

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary

open MeasureTheory ProbabilityTheory MDPFinance.MeanVariance

namespace MVCex

noncomputable def M0 : MVMarket Unit 1 where
  measIP := Measure.dirac ()
  isProb := inferInstance
  N := 0
  i := fun _ => 0
  hi_pos := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  R := fun _ _ _ => 0
  hR_meas := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  hR_indep := iIndepFun.of_subsingleton
  hR_L2 := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  hR_mean_ne := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  hCov_posdef := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  x0 := 1
  hx0 := one_pos
  μ := 2
  hμ := by norm_num

theorem meanXN_eq (π : ℕ → ℝ → (Fin 1 → ℝ)) : M0.meanXN π = 1 := by
  show ∫ ω, M0.terminalWealth π 0 0 1 ω ∂(Measure.dirac ()) = 1
  simp [MVMarket.terminalWealth]

end MVCex

open MVCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1))),
    ∃ πstar : ℕ → ℝ → (Fin d → ℝ), M.IsOptimalMV πstar ∧
      M.varXN πstar = (dseq 0 / (1 - dseq 0)) * (M.meanXN πstar - M.x0 * M.S0 M.N) ^ 2 ∧
      M.meanXN πstar = M.μ ∧
      (∀ n < M.N, ∀ x : ℝ, πstar n x =
        fun k => ((M.μ - dseq 0 * M.x0 * M.S0 M.N) / (1 - dseq 0) * (M.S0 n / M.S0 M.N) - x) *
          ((M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)) k))) := by
  intro h
  obtain ⟨π, ⟨_, hμ, _⟩, _⟩ := h M0 (fun _ => 1) rfl (fun n hn => absurd hn (Nat.not_lt_zero n))
  rw [meanXN_eq] at hμ
  have : M0.μ = 2 := rfl
  rw [this] at hμ
  norm_num at hμ

#print axioms solution
