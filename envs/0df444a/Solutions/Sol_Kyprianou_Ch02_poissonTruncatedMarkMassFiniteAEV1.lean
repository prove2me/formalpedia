-- Prove2me | solution 1 for Kyprianou.Ch02.poissonTruncatedMarkMassFiniteAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:03:15.973903+00:00
-- url     : https://prove2.me/submissions/da921796-353d-444c-a97c-e3bd1f2dc1af

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_poissonTruncatedMarkMassMeanV1
import Theorems.Thm_ProbabilityTheory_lintegral_poissonRandomMeasure
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Campbell finiteness on a common conull set. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∫⁻ p : ℝ × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|)
        else 0 ∂(poissonRandomMeasure K Z ω)) < ⊤ := by
  have hpos (x : ℝ) : 0 ≤ min (1 : ℝ) |x| :=
    le_min (by norm_num) (abs_nonneg x)
  have hm : (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) < ⊤ := by
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hpos _)] using
      hfin.lintegral_lt_top
  apply ae_all_iff.mpr
  intro n
  let w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (min (1 : ℝ) |x|)
  let g : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then w p.2 else 0
  have hw : Measurable w :=
    ENNReal.measurable_ofReal.comp (continuous_const.min continuous_abs).measurable
  have hg : Measurable g := Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const))
    (hw.comp measurable_snd) measurable_const
  have hmeas : Measurable (fun ω => ∫⁻ p, g p ∂poissonRandomMeasure K Z ω) := by
    have hs : ∀ s : SimpleFunc (ℝ × ℝ) ENNReal,
        Measurable (fun ω => s.lintegral (poissonRandomMeasure K Z ω)) := by
      intro s
      simp only [SimpleFunc.lintegral]
      exact Finset.measurable_sum _ fun x _ => measurable_const.mul
        (measurable_poissonRandomMeasure_apply hd.measurable_count
          hd.measurable_point (s.measurableSet_fiber x))
    simp_rw [lintegral_eq_iSup_eapprox_lintegral hg]
    exact Measurable.iSup fun n => hs (SimpleFunc.eapprox g n)
  apply ae_lt_top' hmeas.aemeasurable
  rw [show (∫⁻ ω, ∫⁻ p, g p ∂poissonRandomMeasure K Z ω ∂P) =
      (n : ℝ≥0∞) * (∫⁻ x, w x ∂ν) from
    Kyprianou.Ch02.poissonTruncatedMarkMassMeanV1 P ν K Z hd n]
  exact (ENNReal.mul_lt_top (by simp) hm).ne
