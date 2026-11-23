-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPoissonCountCharacteristicV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:24:51.538554+00:00
-- url     : https://prove2.me/submissions/9d2fbcf6-f55c-4263-bcfb-c319c0a650e1

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonWindowCountLawV1
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) (t : ℝ≥0) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I *
      ((u * (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal : ℝ) : ℂ)) ∂P =
    Complex.exp ((LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal *
      (Complex.exp (Complex.I * (u : ℂ)) - 1))
 := by
  classical
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B
  have hR : MeasurableSet R := measurableSet_Ioc.prod hB
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν R).toNNReal with hrdef
  have hrR :
      ((r : ℝ) : ℂ) =
      ((LevyStochCalc.Poisson.referenceIntensity ν R).toReal : ℂ) := rfl
  set g : ℝ≥0∞ → ℂ := fun x =>
    Complex.exp (Complex.I * ((u * x.toReal : ℝ) : ℂ)) with hg
  have hgm : Measurable g := by
    rw [hg]
    fun_prop
  have hXm : Measurable fun ω => N.N ω R := N.measurable_eval hR
  have hstep1 :
      ∫ ω, g (N.N ω R) ∂P =
        ∫ x, g x ∂(P.map fun ω => N.N ω R) :=
    (integral_map hXm.aemeasurable hgm.aestronglyMeasurable).symm
  have hstep2 :
      ∫ x, g x ∂(P.map fun ω => N.N ω R) =
        ∫ n : ℕ, g ((n : ℝ≥0∞)) ∂(poissonMeasure r) := by
    rw [Kyprianou.Ch02.finiteRegionPoissonWindowCountLawV1
      P ν N B hB hfinite t, LevyStochCalc.Poisson.poissonMeasureENN, ← hrdef]
    exact integral_map (by fun_prop) hgm.aestronglyMeasurable
  have hstep3 :
      ∫ n : ℕ, g ((n : ℝ≥0∞)) ∂(poissonMeasure r) =
        charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) u := by
    rw [charFun_apply_real,
      integral_map (by fun_prop : AEMeasurable (Nat.cast : ℕ → ℝ) (poissonMeasure r))
        (by fun_prop : AEStronglyMeasurable
          (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)) _)]
    refine integral_congr_ae (Eventually.of_forall fun n => ?_)
    rw [hg]
    simp only [ENNReal.toReal_natCast]
    congr 1
    push_cast
    ring
  rw [hstep1, hstep2, hstep3, charFun_map_cast_poissonMeasure, hrR]
  congr 2
  rw [mul_comm]
