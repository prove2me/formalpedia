-- Prove2me | solution 1 for MDPFinance.MeanVariance.plambda_binomial_value
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:26:02.451898+00:00
-- url     : https://prove2.me/submissions/1bc7b2fd-0ac9-41d1-92db-356f47ae7f4c

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_MDPFinance_MeanVariance_MRcdSeq

open MeasureTheory ProbabilityTheory MDPFinance.MeanVariance

namespace PLamCex

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

end PLamCex

open PLamCex in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.q < M.p) (γ1 γ2 lamstar : ℝ)
    (hγ1 : γ1 = 1 - ((1 - M.p) / (1 - M.q)) ^ M.N)
    (hγ2 : γ2 = M.p ^ M.N * ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N) /
      ((M.p * (1 - M.q)) ^ M.N - (M.q * (1 - M.p)) ^ M.N))
    (hlamstar : lamstar = min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)))
    (lam : ℝ) (hlam : 0 ≤ lam),
    ((lam ∈ Set.Icc (0 : ℝ) lamstar ∧ M.γ ≥ γ1 →
        (⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) =
          (((M.μ - M.x0) * lam - M.x0 : ℝ) : EReal)) ∧
      (¬ (lam ∈ Set.Icc (0 : ℝ) lamstar ∧ M.γ ≥ γ1) →
        (⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π}, (M.Lagrangian π lam : EReal)) = ⊥)) ∧
      (M.γ ≥ γ1 →
        (lam < lamstar →
          M.IsOptimalPLambda lam (fun _ x => max ((x + -M.x0) / (1 - M.u)) ((x + -M.x0) / (1 - M.d)))) ∧
        (lam = lamstar → M.γ ≥ γ2 → ∀ b, -M.x0 ≤ b →
          M.IsOptimalPLambda lam (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d)))) ∧
        (lam = lamstar → γ1 ≤ M.γ → M.γ ≤ γ2 → ∀ b, b ≤ -M.x0 →
          M.IsOptimalPLambda lam (fun _ x => max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d)))))) := by
  intro h
  have hp : (3 / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  set M := M0 (3 / 4) hp with hM
  have hpq : M.q < M.p := by
    rw [hM, q_eq]; show (1 / 2 : ℝ) < 3 / 4; norm_num
  have H := (h M hpq _ _ _ rfl rfl rfl 1 zero_le_one).1.2
  have hls : min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N)) = 0 := by
    show min (M.q ^ 0 / (M.p ^ 0 - M.q ^ 0))
      (((1 - M.p) ^ 0 * (1 - M.γ)⁻¹ - (1 - M.q) ^ 0) / ((1 - M.q) ^ 0 - (1 - M.p) ^ 0)) = 0
    simp
  have hnot : ¬ ((1 : ℝ) ∈ Set.Icc (0 : ℝ) (min (M.q ^ M.N / (M.p ^ M.N - M.q ^ M.N))
      (((1 - M.p) ^ M.N * (1 - M.γ)⁻¹ - (1 - M.q) ^ M.N) /
        ((1 - M.q) ^ M.N - (1 - M.p) ^ M.N))) ∧
      M.γ ≥ 1 - ((1 - M.p) / (1 - M.q)) ^ M.N) := by
    rw [hls]
    rintro ⟨⟨_, h1⟩, _⟩
    norm_num at h1
  have H2 := H hnot
  have hc : ∀ π : ℕ → ℝ → ℝ, M.Lagrangian π 1 = M.Lagrangian (fun _ _ => 0) 1 := fun _ => rfl
  have hadm : M.IsAdmissible 0 (fun _ _ => 0) := fun k _ hk => absurd hk (Nat.not_lt_zero k)
  have hle : (⨅ π ∈ {π : ℕ → ℝ → ℝ | M.IsAdmissible 0 π}, (M.Lagrangian π 1 : EReal)) =
      (M.Lagrangian (fun _ _ => 0) 1 : EReal) := by
    apply le_antisymm
    · exact iInf₂_le (fun _ _ => 0) hadm
    · exact le_iInf₂ fun π _ => by rw [hc π]
  rw [hle] at H2
  exact EReal.coe_ne_bot _ H2

#print axioms solution
