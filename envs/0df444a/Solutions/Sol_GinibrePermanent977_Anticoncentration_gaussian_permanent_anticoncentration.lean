-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.gaussian_permanent_anticoncentration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:14:36.576711+00:00
-- url     : https://prove2.me/submissions/75221e4e-1fac-43c4-aeeb-5bc5199b849f

import Theorems.Thm_GinibrePermanent977_Anticoncentration_gaussian_permanent_exact_density
import Theorems.Thm_GinibrePermanent977_Anticoncentration_lemma_3_8_kappa_asymptotics

open MeasureTheory ProbabilityTheory Matrix Filter Asymptotics
open GinibrePermanent977.Anticoncentration
open scoped ENNReal Nat Topology BigOperators
set_option autoImplicit false

private lemma kappa_uniform_bound (F : Scalar) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      kappa F n ≤ D * (n : ℝ)^(((F.beta : ℝ)+2)/4) := by
  obtain ⟨d, hd, h⟩ := (lemma_3_8_kappa_asymptotics F).1.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp h.bound
  let M := ∑ i ∈ Finset.range N, ‖kappa F i‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨d+M+1, by positivity, fun n hn => ?_⟩
  have hg : 1 ≤ (n : ℝ)^(((F.beta : ℝ)+2)/4) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by positivity)
  by_cases hlarge : N ≤ n
  · have hu := hN n hlarge
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)^(((F.beta : ℝ)+2)/4))] at hu
    calc
      kappa F n ≤ ‖kappa F n‖ := le_abs_self _
      _ ≤ d * (n : ℝ)^(((F.beta : ℝ)+2)/4) := hu
      _ ≤ (d+M+1) * (n : ℝ)^(((F.beta : ℝ)+2)/4) := by gcongr; linarith
  · have hsmall : ‖kappa F n‖ ≤ M := by
      apply Finset.single_le_sum (fun i _ => norm_nonneg (kappa F i))
      exact Finset.mem_range.mpr (by omega)
    calc
      kappa F n ≤ ‖kappa F n‖ := le_abs_self _
      _ ≤ M := hsmall
      _ ≤ d+M+1 := by linarith
      _ ≤ (d+M+1) * (n : ℝ)^(((F.beta : ℝ)+2)/4) := by nlinarith

private lemma omega_pos (F : Scalar) : 0 < omegaBall F := by
  have hb := beta_pos F
  unfold omegaBall
  apply div_pos
  · positivity
  · apply Real.Gamma_pos_of_pos
    positivity

theorem solution (F : Scalar) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ p : F.K → ℝ≥0∞,
      Measurable p ∧
      (∀ s : Set F.K, MeasurableSet s →
        ginibre F n n (normPer ⁻¹' s) = ∫⁻ z in s, p z) ∧
      (∀ z w : F.K, ‖z‖ = ‖w‖ → p z = p w) ∧
      essSup p volume = p 0 ∧
      p 0 ≤ ENNReal.ofReal (C * (n : ℝ) ^ (((F.beta : ℝ) + 2) / 4)) ∧
      (∀ z : F.K, p z ≤ p 0) ∧
      p 0 ≤ ENNReal.ofReal (kappa F n) ∧
      ∀ ε : ℝ, 0 < ε → ∀ z : F.K,
        ginibre F n n {G | ‖normPer G - z‖ ≤ ε} ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (((F.beta : ℝ) + 2) / 4) * ε ^ F.beta) ∧
          ginibre F n n {G | ‖normPer G - z‖ ≤ ε} ≤
            ENNReal.ofReal (min 1 (omegaBall F * kappa F n * ε ^ F.beta)) := by
  obtain ⟨D, hD, hDb⟩ := kappa_uniform_bound F
  let C := D * max 1 (omegaBall F)
  have hmax : 0 < max 1 (omegaBall F) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hCD : D ≤ C := by dsimp [C]; nlinarith [le_max_left 1 (omegaBall F)]
  refine ⟨C, mul_pos hD hmax, fun n hn => ?_⟩
  obtain ⟨p, hpm, hplaw, hpr, hpe, hpb, hpk, hps⟩ := gaussian_permanent_exact_density F n hn
  have hnp : 0 ≤ (n : ℝ)^(((F.beta : ℝ)+2)/4) := by positivity
  have hku : kappa F n ≤ C * (n : ℝ)^(((F.beta : ℝ)+2)/4) :=
    (hDb n hn).trans (mul_le_mul_of_nonneg_right hCD hnp)
  refine ⟨p, hpm, hplaw, hpr, hpe, hpk.trans (ENNReal.ofReal_le_ofReal hku),
    hpb, hpk, fun ε hε z => ⟨?_, hps ε hε z⟩⟩
  apply (hps ε hε z).trans
  apply ENNReal.ofReal_le_ofReal
  apply (min_le_right 1 _).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hε.le _)
  calc
    omegaBall F * kappa F n ≤ omegaBall F * (D * (n : ℝ)^(((F.beta : ℝ)+2)/4)) :=
      mul_le_mul_of_nonneg_left (hDb n hn) (omega_pos F).le
    _ ≤ max 1 (omegaBall F) * (D * (n : ℝ)^(((F.beta : ℝ)+2)/4)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = C * (n : ℝ)^(((F.beta : ℝ)+2)/4) := by dsimp [C]; ring
