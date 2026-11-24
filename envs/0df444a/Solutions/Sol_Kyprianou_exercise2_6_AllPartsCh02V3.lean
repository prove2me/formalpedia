-- Prove2me | solution 1 for Kyprianou.exercise2_6_AllPartsCh02V3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:25:10.810828+00:00
-- url     : https://prove2.me/submissions/49941bd7-f904-4775-8ec8-4c3b1ca96c54
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Theorems.Thm_Kyprianou_Ch02_prmWindowNonnegativeMarkMomentFiniteIffV1
import Theorems.Thm_Kyprianou_Ch02_levyAbsPowIntegrableIffLargeV1
import Theorems.Thm_Kyprianou_Ch02_prmIntegrableMarkCompensatedMartingaleV1
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (n : ℕ) (hn : 2 ≤ n) :
    (∀ (t : ℝ≥0), 0 < t →
       ((∫⁻ ω, ∫⁻ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
            ENNReal.ofReal (|z.2| ^ n) ∂(N.N ω) ∂P) < ⊤ ↔
        Integrable (fun x : ℝ => |x| ^ n)
          (ν.restrict {x : ℝ | 1 ≤ |x|}))) ∧
    (Integrable (fun x : ℝ => |x| ^ n)
        (ν.restrict {x : ℝ | 1 ≤ |x|}) →
      ∃ ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
        Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
        MeasureTheory.Martingale
          (fun (t : ℝ≥0) ω =>
            (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
               z.2 ^ n ∂(N.N ω)) -
            (t : ℝ) * ∫ x, x ^ n ∂ν) ℱ P) := by
  have hp := Kyprianou.Ch02.levyAbsPowIntegrableIffLargeV1 ν hν n hn
  constructor
  · intro t ht
    exact (Kyprianou.Ch02.prmWindowNonnegativeMarkMomentFiniteIffV1 P ν N
      (fun x => |x| ^ n) (by fun_prop) (fun x => pow_nonneg (abs_nonneg x) n)
      t ht).trans hp.1
  · intro h
    exact Kyprianou.Ch02.prmIntegrableMarkCompensatedMartingaleV1 P ν N
      (fun x => x ^ n) (by fun_prop) (hp.2 h)
