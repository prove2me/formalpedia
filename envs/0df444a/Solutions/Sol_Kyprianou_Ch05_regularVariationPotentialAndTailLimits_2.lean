-- Prove2me | solution 2 for Kyprianou.Ch05.regularVariationPotentialAndTailLimits
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T00:37:58.660613+00:00
-- url     : https://prove2.me/submissions/1335c25d-e180-44de-a6d9-640ce7cfefa3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Theorems.Thm_Kyprianou_Ch05_karamataTauberianInfinity
import Theorems.Thm_Kyprianou_Ch05_karamataTauberianZero
import Theorems.Thm_Kyprianou_Ch05_karamataMonotoneDensityInfinity
import Theorems.Thm_Kyprianou_Ch05_potentialLaplaceAsymptoticsV2
import Theorems.Thm_Kyprianou_Ch05_tailLaplaceAsymptotics
import Theorems.Thm_Kyprianou_Ch05_potentialSupportNonnegative
import Theorems.Thm_Kyprianou_Ch05_potentialScalingLimitsV2
import Theorems.Thm_Kyprianou_Ch05_tailScalingLimits
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

/-- Lemma 5.17, p.132: reduction to the Karamata Tauberian theorems (Route B-fixed: C1/C4 replaced by the corrected reciprocal-factor V2 versions, proved by WillR; the original C1 is inconsistent and C4 is false as published).
The Laplace transform of the potential measure is `1 / Phi`, and the
Laplace transform of the tail density is `(Phi - d * theta) / theta`;
regular variation of `Phi` transports to Karamata-ready Laplace
asymptotics (child lemmas `potentialLaplaceAsymptoticsV2` and
`tailLaplaceAsymptotics`), the Karamata theorems
(`karamataTauberianInfinity`, `karamataTauberianZero`,
`karamataMonotoneDensityInfinity`) convert those into cumulative /
density ratios tending to `1`, and the pure scaling lemmas
(`potentialScalingLimitsV2`, `tailScalingLimits`) convert the ratios
into the stated scaled limits, at both endpoints. -/
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
            (nhds (lambda ^ (-alpha) / Real.Gamma (1-alpha))))))) := by
  have hSup : (U 0) (Set.Iio (0 : Real)) = 0 :=
    potentialSupportNonnegative P Y death U hKilled hPotential
  have hLapPot :=
    potentialLaplaceAsymptoticsV2 P Y death d Pi Phi hKilled hTriplet hLaplaceLaw
      U hPotential alpha hAlpha
  constructor
  · intro h0
    obtain ⟨L, hLslow, hPhi, hLap⟩ := hLapPot.1 h0
    have hCum : Tendsto (fun x : Real => ((U 0) (Set.Icc (0 : Real) x)).toReal /
        (x ^ alpha * L x / Real.Gamma (1 + alpha))) atTop (nhds 1) :=
      (karamataTauberianInfinity (U 0) L alpha hLslow hAlpha.1 hSup).mp hLap
    have hPot := (potentialScalingLimitsV2 (U 0) Phi L alpha hAlpha.1 hPhi).1 hLslow hCum
    refine ⟨hPot, ?_⟩
    intro hlt
    obtain ⟨L₂, hL₂slow, hPhi₂, hMono, hMono₀, hSupV, hLapT⟩ :=
      (tailLaplaceAsymptotics P Y death d Pi Phi hKilled hTriplet hLaplaceLaw
        U hPotential alpha hAlpha hlt).1 h0
    have hDens : Tendsto (fun x : Real => (Pi (Set.Ioi x)).toReal /
        (x ^ ((1 - alpha) - 1) * L₂ x / Real.Gamma (1 - alpha))) atTop (nhds 1) :=
      (karamataMonotoneDensityInfinity
        (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
          (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)))
        (fun x : Real => (Pi (Set.Ioi x)).toReal) L₂ (1 - alpha) hL₂slow
        (by linarith : (0 : Real) < 1 - alpha)
        rfl
        (fun x _ => ENNReal.toReal_nonneg)
        hMono).mp hLapT
    exact (tailScalingLimits Pi Phi L₂ alpha hlt hPhi₂).1 hL₂slow hDens
  · intro hInf
    obtain ⟨L, hLslow, hPhi, hLap⟩ := hLapPot.2 hInf
    have hCum : Tendsto (fun x : Real => ((U 0) (Set.Icc (0 : Real) x)).toReal /
        (x ^ alpha * L x / Real.Gamma (1 + alpha)))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) :=
      (karamataTauberianZero (U 0) L alpha hLslow hAlpha.1 hSup).1.mp hLap
    have hPot := (potentialScalingLimitsV2 (U 0) Phi L alpha hAlpha.1 hPhi).2 hLslow hCum
    refine ⟨hPot, ?_⟩
    intro hlt
    obtain ⟨L₂, hL₂slow, hPhi₂, hMono, hMono₀, hSupV, hLapT⟩ :=
      (tailLaplaceAsymptotics P Y death d Pi Phi hKilled hTriplet hLaplaceLaw
        U hPotential alpha hAlpha hlt).2 hInf
    have hDens : Tendsto (fun x : Real => (Pi (Set.Ioi x)).toReal /
        (x ^ ((1 - alpha) - 1) * L₂ x / Real.Gamma (1 - alpha)))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) :=
      ((karamataTauberianZero
        (((volume : Measure Real).restrict (Set.Ici (0 : Real))).withDensity
          (fun x : Real => ENNReal.ofReal ((Pi (Set.Ioi x)).toReal)))
        L₂ (1 - alpha) hL₂slow (by linarith : (0 : Real) ≤ 1 - alpha) hSupV).2
        (by linarith : (0 : Real) < 1 - alpha)
        (fun x : Real => (Pi (Set.Ioi x)).toReal)
        rfl
        (fun x _ => ENNReal.toReal_nonneg)
        hMono₀).mp hLapT
    exact (tailScalingLimits Pi Phi L₂ alpha hlt hPhi₂).2 hL₂slow hDens
