-- Prove2me | solution 1 for Kyprianou.Ch05.potentialLaplaceAsymptoticsV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:39:43.789329+00:00
-- url     : https://prove2.me/submissions/934bc187-6d27-4aa4-ab5a-1f2686ef79a8

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Theorems.Thm_Kyprianou_Ch05_killedPotential_laplaceTransform
import Theorems.Thm_Kyprianou_Ch05_reciprocalRegularVariationFactor
import Theorems.Thm_Kyprianou_Ch05_potentialLaplaceNormalizedExact
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- Corrected reciprocal-factor proof. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1) :
  ((RegularlyVaryingAtZero Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtInfinity L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) / L x) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace (U 0) theta).toReal /
             (theta ^ (-alpha) * L (1 / theta)))
         (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1)) ∧
   (RegularlyVaryingAtInfinity Phi alpha →
     ∃ L : Real → Real, SlowlyVaryingAtZero L ∧
       (∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) / L x) ∧
       Tendsto
         (fun theta : Real =>
           (positiveLaplace (U 0) theta).toReal /
             (theta ^ (-alpha) * L (1 / theta)))
         atTop (nhds 1))) := by
  have hLap (t : Real) (ht : 0 < t) :
      positiveLaplace (U 0) t = (ENNReal.ofReal (Phi t))⁻¹ := by
    simpa [positiveLaplace] using
      killedPotential_laplaceTransform P Y death 0 d Pi Phi hKilled hTriplet
        (by simpa using hLaplaceLaw) U hPotential 0 le_rfl t ht.le
  constructor
  · intro hRV
    obtain ⟨L,hp,hL,hs⟩ := reciprocalRegularVariationFactor Phi alpha atTop
      (nhdsWithin (0 : Real) (Set.Ioi 0)) hRV.1 (eventually_gt_atTop 0)
      tendsto_inv_atTop_nhdsGT_zero hRV.2
    refine ⟨L,⟨hp,fun a ha => by simpa using hs a ha⟩,hL,?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin (a := (0 : Real)) (s := Set.Ioi 0)] with t ht
    exact (potentialLaplaceNormalizedExact (U 0) Phi L alpha hRV.1 hL hLap t ht).symm
  · intro hRV
    obtain ⟨L,hp,hL,hs⟩ := reciprocalRegularVariationFactor Phi alpha
      (nhdsWithin (0 : Real) (Set.Ioi 0)) atTop hRV.1 self_mem_nhdsWithin
      tendsto_inv_nhdsGT_zero hRV.2
    refine ⟨L,⟨hp,fun a ha => by simpa using hs a ha⟩,hL,?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with t ht
    exact (potentialLaplaceNormalizedExact (U 0) Phi L alpha hRV.1 hL hLap t ht).symm
