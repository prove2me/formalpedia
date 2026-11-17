-- Prove2me | solution 1 for Kyprianou.Ch01.charFun_independentProductProcessSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:05:47.835808+00:00
-- url     : https://prove2.me/submissions/6f3cc0fd-ac89-499a-8485-b5dfa3f0d58f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem solution
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → ℝ) (Y : Λ → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (xi : ℝ) :
    charFun ((P.prod Q).map (fun p : Ω × Λ => X p.1 + Y p.2)) xi =
      charFun (P.map X) xi * charFun (Q.map Y) xi := by
  have hprod : Measurable (Prod.map X Y : Ω × Λ → ℝ × ℝ) :=
    (hX.comp measurable_fst).prodMk (hY.comp measurable_snd)
  have hsum :
      ((P.map X).prod (Q.map Y)).map
        (fun p : ℝ × ℝ => p.1 + p.2) =
      (P.prod Q).map (fun p : Ω × Λ => X p.1 + Y p.2) := by
    rw [Measure.map_prod_map P Q hX hY]
    have hadd : Measurable (fun p : ℝ × ℝ => p.1 + p.2) :=
      measurable_fst.add measurable_snd
    exact Measure.map_map hadd hprod
  letI : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure (Q.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  rw [← hsum, ProbabilityTheory.charFun_map_add_prod_eq_mul]
  simp only [Pi.mul_apply]
