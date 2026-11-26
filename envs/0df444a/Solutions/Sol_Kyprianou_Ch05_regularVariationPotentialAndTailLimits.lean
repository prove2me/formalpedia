-- Prove2me | solution 1 for Kyprianou.Ch05.regularVariationPotentialAndTailLimits
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-26T03:15:07.52864+00:00
-- url     : https://prove2.me/submissions/9582f453-b89e-4647-bd1b-12d839d64cac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_regularVariationPotentialLimitAtZero
import Theorems.Thm_Kyprianou_Ch05_regularVariationTailLimitAtZero
import Theorems.Thm_Kyprianou_Ch05_regularVariationPotentialLimitAtInfinity
import Theorems.Thm_Kyprianou_Ch05_regularVariationTailLimitAtInfinity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

/-- Lemma 5.17 as a reduction: the two regimes and the two numbered
    conclusions are four independent limits. Each is a child lemma;
    the sketch is pure assembly (implication and conjunction
    introduction), so it is lossless: no hypothesis is dropped and no
    conclusion is weakened. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hRV : RegularlyVaryingAtZero Phi alpha ∨
            RegularlyVaryingAtInfinity Phi alpha) :
  ((RegularlyVaryingAtZero Phi alpha →
     ((∀ lambda : Real, 0 < lambda →
        Tendsto
          (fun x : Real =>
            ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
              Phi (1 / x))
          atTop
          (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) ∧
      (alpha < 1 →
        ∀ lambda : Real, 0 < lambda →
          Tendsto
            (fun x : Real =>
              (Pi (Set.Ioi (lambda*x))).toReal / Phi (1 / x))
            atTop
            (nhds (lambda ^ (-alpha) / Real.Gamma (1-alpha)))))) ∧
   (RegularlyVaryingAtInfinity Phi alpha →
     ((∀ lambda : Real, 0 < lambda →
        Tendsto
          (fun x : Real =>
            ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
              Phi (1 / x))
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) ∧
      (alpha < 1 →
        ∀ lambda : Real, 0 < lambda →
          Tendsto
            (fun x : Real =>
              (Pi (Set.Ioi (lambda*x))).toReal / Phi (1 / x))
            (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds (lambda ^ (-alpha) / Real.Gamma (1-alpha)))))))
 := by
  refine ⟨?_, ?_⟩
  · intro h0
    refine ⟨?_, ?_⟩
    · intro lambda hlam
      exact Kyprianou.Ch05.regularVariationPotentialLimitAtZero
        P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft
        U hPotential alpha hAlpha h0 lambda hlam
    · intro halt lambda hlam
      exact Kyprianou.Ch05.regularVariationTailLimitAtZero
        P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft
        U hPotential alpha hAlpha h0 halt lambda hlam
  · intro hinf
    refine ⟨?_, ?_⟩
    · intro lambda hlam
      exact Kyprianou.Ch05.regularVariationPotentialLimitAtInfinity
        P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft
        U hPotential alpha hAlpha hinf lambda hlam
    · intro halt lambda hlam
      exact Kyprianou.Ch05.regularVariationTailLimitAtInfinity
        P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft
        U hPotential alpha hAlpha hinf halt lambda hlam

