-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m15
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:16:23.493551+00:00
-- url     : https://prove2.me/submissions/6daa27ce-586f-4e91-b2c4-0b86d21db158

import Definitions.Def_NahmiasPerishable_Inventory_Stationary

open MeasureTheory Set Filter Topology
open scoped ENNReal
open NahmiasPerishable.Inventory

private noncomputable def mu15 : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ) + (1 / 2 : ℝ≥0∞) • Measure.dirac (2 : ℝ)

private instance : IsProbabilityMeasure mu15 := by
  constructor
  simp only [mu15, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
    smul_eq_mul, mul_one, one_div]
  exact ENNReal.inv_two_add_inv_two

private lemma mu15_apply_zero : mu15 ({0} : Set ℝ) = 2⁻¹ := by
  simp only [mu15, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)), smul_eq_mul]
  rw [Set.indicator_of_mem (Set.mem_singleton (0 : ℝ)),
    Set.indicator_of_notMem (by norm_num : (2 : ℝ) ∉ ({0} : Set ℝ))]
  norm_num

private lemma mu15_apply_pair : mu15 ({0, 2} : Set ℝ) = 1 := by
  have hmeas : MeasurableSet ({0, 2} : Set ℝ) :=
    (measurableSet_singleton 0).union (measurableSet_singleton 2)
  simp only [mu15, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hmeas,
    smul_eq_mul]
  rw [Set.indicator_of_mem (Set.mem_insert 0 {2}),
    Set.indicator_of_mem (Set.mem_insert_of_mem 0 (Set.mem_singleton 2))]
  simp only [Pi.one_apply, mul_one, one_div]
  exact ENNReal.inv_two_add_inv_two

private lemma mu15_discrete : DiscreteDemand mu15 := by
  refine ⟨inferInstance, ?_, ⟨({0, 2} : Set ℝ),
    ((Set.finite_singleton (2 : ℝ)).insert 0).countable, mu15_apply_pair⟩⟩
  rw [ae_iff]
  have hsub : {a : ℝ | ¬0 ≤ a} ⊆ ({0, 2} : Set ℝ)ᶜ := by
    intro x hx hxmem
    rcases hxmem with rfl | rfl <;> norm_num at hx
  refine measure_mono_null hsub ?_
  have hmeas : MeasurableSet ({0, 2} : Set ℝ) :=
    (measurableSet_singleton 0).union (measurableSet_singleton 2)
  rw [prob_compl_eq_zero_iff hmeas]
  exact mu15_apply_pair

private lemma lowerPrinted_mu15 : lowerPrinted mu15 (1 + 1) 2 = 1 / 2 := by
  unfold lowerPrinted mu15
  have hcast : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast]
  have hi0 : Integrable (fun d : ℝ => min d (2 / 2))
      ((1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have hi2 : Integrable (fun d : ℝ => min d (2 / 2))
      ((1 / 2 : ℝ≥0∞) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  rw [integral_add_measure hi0 hi2, integral_smul_measure, integral_smul_measure,
    integral_dirac _ 0, integral_dirac _ 2]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  norm_num

private lemma upperPrinted_mu15 : upperPrinted mu15 (1 + 1) 2 = 1 / 4 := by
  unfold upperPrinted
  have hcast : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast]
  let ν : Measure (Fin 2 → ℝ) := demandPaths mu15 2
  change 2 / 2 - ∫ d, min ((∑ i : Fin 2, d i) / 2) (2 / 2) ∂ν = 1 / 4
  have : IsProbabilityMeasure ν := by
    dsimp [ν, demandPaths]
    infer_instance
  let B : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ : Fin 2 => ({0, 2} : Set ℝ))
  let Z : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ : Fin 2 => ({0} : Set ℝ))
  have hBmeas : MeasurableSet B :=
    MeasurableSet.univ_pi (fun _ => (measurableSet_singleton 0).union (measurableSet_singleton 2))
  have hZmeas : MeasurableSet Z :=
    MeasurableSet.univ_pi (fun _ => measurableSet_singleton 0)
  have hνB : ν B = 1 := by
    dsimp [ν, demandPaths, B]
    rw [Measure.pi_pi, Fin.prod_univ_two, mu15_apply_pair, mul_one]
  have hνZ : ν Z = 2⁻¹ * 2⁻¹ := by
    dsimp [ν, demandPaths, Z]
    rw [Measure.pi_pi, Fin.prod_univ_two, mu15_apply_zero]
  have haeB : ∀ᵐ d ∂ν, d ∈ B := by
    rw [ae_iff]
    change ν Bᶜ = 0
    rw [prob_compl_eq_zero_iff hBmeas]
    exact hνB
  have hae_eq : (fun d : Fin 2 → ℝ => min ((∑ i : Fin 2, d i) / 2) (2 / 2)) =ᵐ[ν]
      Zᶜ.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [haeB] with d hd
    rw [Fin.sum_univ_two]
    have hd0 : d 0 = 0 ∨ d 0 = 2 := hd 0 (Set.mem_univ 0)
    have hd1 : d 1 = 0 ∨ d 1 = 2 := hd 1 (Set.mem_univ 1)
    by_cases hZ : d ∈ Z
    · have h0 : d 0 = 0 := hZ 0 (Set.mem_univ 0)
      have h1 : d 1 = 0 := hZ 1 (Set.mem_univ 1)
      rw [Set.indicator_of_notMem (not_not.mpr hZ), h0, h1]
      norm_num
    · rw [Set.indicator_of_mem hZ]
      rcases hd0 with h0 | h0 <;> rcases hd1 with h1 | h1
      · exfalso
        apply hZ
        intro i _
        fin_cases i
        · exact h0
        · exact h1
      · rw [h0, h1]; norm_num
      · rw [h0, h1]; norm_num
      · rw [h0, h1]; norm_num
  rw [integral_congr_ae hae_eq, integral_indicator_const 1 hZmeas.compl]
  unfold Measure.real
  rw [prob_compl_eq_one_sub hZmeas, hνZ]
  simp only [smul_eq_mul, mul_one]
  have hle : (2⁻¹ * 2⁻¹ : ℝ≥0∞) ≤ 1 := by
    calc (2⁻¹ * 2⁻¹ : ℝ≥0∞) ≤ 1 * 1 := mul_le_mul' (by norm_num) (by norm_num)
    _ = 1 := mul_one 1
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

set_option linter.unusedVariables false in
theorem solution : ¬ (∀ (μ : Measure ℝ) (hμ : DiscreteDemand μ) (k : ℕ),
    ∃ rate : ℝ → ℝ,
      (∀ S, 0 ≤ S → IsStationaryRate μ k S (rate S) ∧
        lowerPrinted μ (k+1) S ≤ rate S ∧ rate S ≤ upperPrinted μ (k+1) S) ∧
      Tendsto (fun S => rate S-lowerPrinted μ (k+1) S) atTop (𝓝 0) ∧
      Tendsto (fun S => upperPrinted μ (k+1) S-rate S) atTop (𝓝 0)) := by
  intro h
  rcases h mu15 mu15_discrete 1 with ⟨rate, hrate, _, _⟩
  have h2 := hrate 2 (by norm_num)
  have hlow := h2.2.1
  have hhigh := h2.2.2
  rw [lowerPrinted_mu15] at hlow
  rw [upperPrinted_mu15] at hhigh
  linarith
