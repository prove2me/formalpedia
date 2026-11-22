-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_levy_exponent_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:51:03.52306+00:00
-- url     : https://prove2.me/submissions/25f319bc-510a-4f17-b085-e0710cce569d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    {t : ℝ≥0} (ht : ¬ (∀ᵐ ω ∂P, A.X t ω ≤ 0)) (q : ℝ) :
    ∃ b : ℝ, 0 < b ∧ q < A.ψ b := by
  classical
  letI : IsProbabilityMeasure P := A.isProbability
  have htpos : 0 < t := by
    by_contra! hn
    have he : t = 0 := le_antisymm hn (zero_le : 0 ≤ t)
    exact ht (Eventually.of_forall fun ω => by simp only [he, A.X_zero, le_refl])
  have hnonzero : P {ω | 0 < A.X t ω} ≠ 0 := by
    exact fun h => ht ((ae_iff).2 (by simpa only [not_le] using h))
  let B (n : ℕ) := {ω | 1 / ((n : ℝ) + 1) ≤ A.X t ω}
  have hcover : {ω | 0 < A.X t ω} ⊆ ⋃ n : ℕ, B n := by
    intro ω hω
    have hx : 0 < A.X t ω := hω
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / A.X t ω)
    have hlt := hn.trans (lt_add_of_pos_right (n : ℝ) zero_lt_one)
    have hmul := (div_lt_iff₀ hx).mp hlt
    exact mem_iUnion.mpr ⟨n, (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
      (by simpa only [mul_comm] using hmul.le)⟩
  have hex : ∃ n, P (B n) ≠ 0 := by
    by_contra! h
    exact hnonzero (measure_mono_null hcover (measure_iUnion_null h))
  obtain ⟨n, hn⟩ := hex
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  let mass : ℝ := (P (B n)).toReal
  have hm : 0 < mass := ENNReal.toReal_pos hn (measure_ne_top P _)
  have hmeas : Measurable (A.X t) := A.adapted.measurable
  have hBn : MeasurableSet (B n) := hmeas measurableSet_Ici
  let b := (max 0 ((t : ℝ) * q - Real.log mass) + 1) / ε
  have hb : 0 < b := by dsimp [b]; positivity
  have hbε : b * ε = max 0 ((t : ℝ) * q - Real.log mass) + 1 :=
    div_mul_cancel₀ _ hε.ne'
  have hlin : (t : ℝ) * q < b * ε + Real.log mass := by
    linarith [le_max_right 0 ((t : ℝ) * q - Real.log mass)]
  have hlower := Real.exp_lt_exp.mpr hlin
  rw [Real.exp_add, Real.exp_log hm] at hlower
  obtain ⟨hi, hv⟩ := A.laplace t b hb.le
  have hI := integral_mono_ae
    ((integrable_const (Real.exp (b * ε))).indicator hBn) hi
    (Eventually.of_forall (Set.indicator_le'
      (fun ω hω => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hb.le))
      (fun ω hω => Real.exp_nonneg _)))
  rw [integral_indicator hBn, setIntegral_const, smul_eq_mul, hv] at hI
  have hbound : Real.exp (b * ε) * mass ≤ Real.exp ((t : ℝ) * A.ψ b) := by
    exact (mul_comm (Real.exp (b * ε)) mass).trans_le hI
  exact ⟨b, hb, lt_of_mul_lt_mul_left
    (Real.exp_lt_exp.mp (hlower.trans_le hbound)) t.2⟩
