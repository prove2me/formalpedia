-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_avram_clock_pair_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:51:35.421802+00:00
-- url     : https://prove2.me/submissions/7e8d7c19-1368-448d-a307-c21bd7a7b2df

import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_true_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Source-faithful clock-law reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (F : Filtration ℝ≥0 mΩ)
      (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      ∀ q φ : ℝ, 0 < q → 0 < φ → X.ψ φ = q →
      let M := P.prod (expMeasure q)
      let I : Ω × ℝ → ℝ := fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}
      let J : Ω × ℝ → ℝ × ℝ :=
        fun z => (X.X z.2.toNNReal z.1 + I z, I z)
      Measurable J ∧ M.map J = (expMeasure φ).prod (M.map I) := by
  intro Ω mΩ P hP F X q φ hq hφ hroot
  dsimp only
  let M := P.prod (expMeasure q)
  let I : Ω × ℝ → ℝ := fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1}
  let T : Ω × ℝ → ℝ := fun z => X.X z.2.toNNReal z.1
  let S : Ω × ℝ → ℝ := fun z => AvramDividend.Classical.runningSup X z.2.toNNReal z.1
  let G : Ω × ℝ → ℝ := fun z => S z - T z
  let J : Ω × ℝ → ℝ × ℝ := fun z => (T z + I z, I z)
  change Measurable J ∧ M.map J = (expMeasure φ).prod (M.map I)
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  have ht := AvramDividend.Classical.levy_exponential_real_clock_extrema_drawdown_measurable X
  have hS : Measurable S := ht.fst.fst
  have hI : Measurable I := ht.fst.snd
  have hG : Measurable G := ht.snd
  have hT : Measurable T :=
    (AvramDividend.Classical.chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hJ : Measurable J := (hT.add hI).prodMk hI
  have hrev : M.map (fun z => (S z, G z)) = M.map J := by
    simpa only [M, S, G, T, J, I, X.X_zero, sub_zero, zero_add] using
      (AvramDividend.Classical.chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a X q hq)
  have hprod : M.map (fun z => (S z, G z)) = (M.map S).prod (M.map G) :=
    ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map hS.aemeasurable hG.aemeasurable
      (AvramDividend.Classical.avram_ws01e_bt_new_original_P_exp_clock_sup_drawdown_indepFun X q hq)
  have hsecond : M.map G = M.map I := by
    have hs := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.snd) hrev
    rw [Measure.map_map measurable_snd (hS.prodMk hG),
      Measure.map_map measurable_snd hJ] at hs
    exact hs
  have hsup : M.map S = expMeasure φ :=
    AvramDividend.Classical.levy_positive_root_true_exp_clock_supremum_full_law_ws01d X q hq φ hφ hroot
  exact ⟨hJ, hrev.symm.trans (hprod.trans (by rw [hsup, hsecond]))⟩
