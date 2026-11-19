-- Prove2me | solution 1 for Kyprianou.Ch03.exercise33StableFractionalMomentCriterion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:20:28.265982+00:00
-- url     : https://prove2.me/submissions/15a4c03d-8f8a-4661-9dc4-f6d97ba03c05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_stableFracMoment_forward
import Theorems.Thm_Kyprianou_Ch03_stableFracMoment_reverse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03


theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha cPlus cMinus eta : ℝ)
    (hAlpha : 0 < alpha ∧ alpha < 2)
    (hCPlus : 0 ≤ cPlus) (hCMinus : 0 ≤ cMinus)
    (hNonzero : 0 < cPlus + cMinus)
    (hMeasure : T.levyMeasure =
      (volume : Measure ℝ).withDensity
        (fun x : ℝ => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0)))
    (hEta : 0 < eta) :
    (∀ t : NNReal, 0 < t →
       Integrable (fun omega => |X t omega| ^ eta) P) ↔ eta < alpha := by
  exact Iff.intro (Kyprianou.Ch03.stableFracMoment_forward P X hX T hLK alpha cPlus cMinus eta hAlpha hCPlus hCMinus hNonzero hMeasure hEta) (Kyprianou.Ch03.stableFracMoment_reverse P X hX T hLK alpha cPlus cMinus eta hAlpha hCPlus hCMinus hNonzero hMeasure hEta)

