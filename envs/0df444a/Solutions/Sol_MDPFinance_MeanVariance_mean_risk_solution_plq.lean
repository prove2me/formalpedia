-- Prove2me | solution 1 for MDPFinance.MeanVariance.mean_risk_solution_plq
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:25:30.281725+00:00
-- url     : https://prove2.me/submissions/9348b04c-c33e-4fea-8474-1e385527dce4

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket

open MeasureTheory ProbabilityTheory MDPFinance.MeanVariance

namespace MRPlqCex

noncomputable def M0 (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) : MeanRiskMarket Unit where
  measIP := Measure.dirac ()
  isProb := inferInstance
  N := 0
  u := 2
  d := 0
  hd_lt_one := by norm_num
  hone_lt_u := by norm_num
  p := p
  hp_mem := hp
  R := fun _ _ => 0
  hR_meas := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  hR_law := fun n h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  hR_indep := iIndepFun.of_subsingleton
  x0 := 1
  μ := 2
  hx0 := one_pos
  hx0μ := by norm_num
  γ := 1 / 2
  hγ := by norm_num

theorem q_eq (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) : (M0 p hp).q = 1 / 2 := by
  simp [MeanRiskMarket.q, M0]

theorem meanXN_eq (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (π : ℕ → ℝ → ℝ) :
    (M0 p hp).meanXN π = 1 := by
  show ∫ ω, (M0 p hp).terminalWealth π 0 0 1 ω ∂(Measure.dirac ()) = 1
  simp [MeanRiskMarket.terminalWealth]

theorem VMR_top (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) : (M0 p hp).VMR = ⊤ := by
  unfold MeanRiskMarket.VMR
  apply iInf₂_eq_top.mpr
  intro π hπ
  exfalso
  have h := hπ.2
  rw [meanXN_eq] at h
  have : (M0 p hp).μ = 2 := rfl
  rw [this] at h
  norm_num at h

end MRPlqCex

open MRPlqCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.p < M.q) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = (M.q ^ M.N - M.p ^ M.N) / M.q ^ M.N)
    (hγ2 : γ2 = (1 - M.p) ^ M.N * (M.q ^ M.N - M.p ^ M.N) /
      (((1 - M.p) * M.q) ^ M.N - ((1 - M.q) * M.p) ^ M.N))
    (hlamstar : lamstar = min ((1 - M.q) ^ M.N / ((1 - M.p) ^ M.N - (1 - M.q) ^ M.N))
      ((M.p ^ M.N * (1 - M.γ)⁻¹ - M.q ^ M.N) / (M.q ^ M.N - M.p ^ M.N))),
    (M.γ ≥ γ1 → M.VMR = (((M.μ - M.x0) * lamstar - M.x0 : ℝ) : EReal)) ∧
      (¬ M.γ ≥ γ1 → M.VMR = ⊥) ∧
      (γ1 ≤ M.γ → M.γ ≤ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.d)⁻¹ * ((M.μ - M.x0) * (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N)) - M.x0 + x))) ∧
      (M.γ ≥ γ2 → M.IsOptimalMR (fun _ x =>
        (1 - M.u)⁻¹ * ((M.x0 - M.μ) * ((1 - M.q) ^ M.N / ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) -
          M.x0 + x)))) := by
  intro h
  have hp : (1 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  have hpq : (M0 (1 / 4) hp).p < (M0 (1 / 4) hp).q := by
    rw [q_eq]; show (1 / 4 : ℝ) < 1 / 2; norm_num
  have H := (h (M0 (1 / 4) hp) hpq _ _ _ rfl rfl rfl).1
  have hγ : (M0 (1 / 4) hp).γ ≥ ((M0 (1 / 4) hp).q ^ (M0 (1 / 4) hp).N -
      (M0 (1 / 4) hp).p ^ (M0 (1 / 4) hp).N) / (M0 (1 / 4) hp).q ^ (M0 (1 / 4) hp).N := by
    show (1 / 2 : ℝ) ≥ ((M0 (1 / 4) hp).q ^ 0 - (M0 (1 / 4) hp).p ^ 0) / (M0 (1 / 4) hp).q ^ 0
    norm_num
  have := H hγ
  rw [VMR_top] at this
  exact EReal.coe_ne_top _ this.symm

#print axioms solution
