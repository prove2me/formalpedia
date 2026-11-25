-- Prove2me | solution 1 for Kyprianou.Ch04.independentExpClockPathJointLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T07:46:59.407495+00:00
-- url     : https://prove2.me/submissions/2626706a-b432-4ce5-be64-ab2df361c90f

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem clockLaw {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ) (hq : 0 < q)
    (e : Ω → NNReal) (he : Measurable e)
    (hlaw : ∀ t : NNReal, (P {ω | t < e ω}).toReal =
      Real.exp (-q * (t : ℝ))) :
    P.map e = (expMeasure q).map Real.toNNReal := by
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  letI : IsProbabilityMeasure (P.map e) := Measure.isProbabilityMeasure_map he.aemeasurable
  letI : IsProbabilityMeasure ((expMeasure q).map Real.toNNReal) :=
    Measure.isProbabilityMeasure_map measurable_real_toNNReal.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  have hp : P.map e (Ioi t) = ENNReal.ofReal (Real.exp (-q * (t : ℝ))) := by
    rw [Measure.map_apply he measurableSet_Ioi]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    exact hlaw t
  have hpre : Real.toNNReal ⁻¹' Ioi t = Ioi (t : ℝ) := by
    ext y
    change t < y.toNNReal ↔ (t : ℝ) < y
    by_cases hy : 0 ≤ y
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hy]
    · rw [Real.toNNReal_of_nonpos (le_of_not_ge hy)]
      constructor
      · intro h
        exact False.elim (not_lt_of_ge (zero_le : 0 ≤ t) h)
      · intro h
        exact False.elim (hy (le_trans t.coe_nonneg h.le))
  have hqtail : (expMeasure q).map Real.toNNReal (Ioi t) =
      ENNReal.ofReal (Real.exp (-q * (t : ℝ))) := by
    rw [Measure.map_apply measurable_real_toNNReal measurableSet_Ioi, hpre]
    simpa [neg_mul] using
      avram_ws01e_b_expMeasure_strict_survival_real q (t : ℝ) hq t.coe_nonneg
  rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_compl measurableSet_Ioi (measure_ne_top _ _), hp, hqtail]
  simp

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q)
    (e : Ω → NNReal) (he : Measurable e)
    (hlaw : ∀ t : NNReal, (P {ω | t < e ω}).toReal =
      Real.exp (-q * (t : ℝ)))
    (hi : Indep (MeasurableSpace.comap e inferInstance)
      (MeasurableSpace.comap (fun ω : Ω => fun t : NNReal => L.X t ω)
        inferInstance) P) :
    P.map (fun ω => (e ω, fun t : NNReal => L.X t ω)) =
      (P.prod (expMeasure q)).map
        (fun z => (z.2.toNNReal, fun t : NNReal => L.X t z.1)) := by
  letI : IsProbabilityMeasure P := L.isProbability
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  let path : Ω → (NNReal → ℝ) := fun ω t => L.X t ω
  have hm : Measurable path := measurable_pi_lambda _ (fun t => L.adapted.measurable)
  have hind : IndepFun e path P := hi
  change P.map (fun ω => (e ω, path ω)) =
    (P.prod (expMeasure q)).map (fun z => (z.2.toNNReal, path z.1))
  rw [hind.map_prod_eq_prod_map_map he.aemeasurable hm.aemeasurable,
    clockLaw P q hq e he hlaw,
    Measure.map_prod_map _ _ measurable_real_toNNReal hm,
    ← Measure.prod_swap (μ := P) (ν := expMeasure q)]
  exact Measure.map_map (f := Prod.swap) (g := Prod.map Real.toNNReal path)
    (measurable_real_toNNReal.comp measurable_fst |>.prodMk (hm.comp measurable_snd))
    (measurable_snd.prodMk measurable_fst)
