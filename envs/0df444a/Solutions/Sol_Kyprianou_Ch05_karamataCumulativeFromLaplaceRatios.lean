-- Prove2me | solution 1 for Kyprianou.Ch05.karamataCumulativeFromLaplaceRatios
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:43:54.548848+00:00
-- url     : https://prove2.me/submissions/2e52bd05-a2b0-49f4-9475-e12c0f0a54c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Theorems.Thm_Kyprianou_Ch05_karamataGammaReference
import Theorems.Thm_Kyprianou_Ch05_karamataScaledMeasureData
import Theorems.Thm_Kyprianou_Ch05_karamataLaplaceFamilyCumulative
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Karamata cumulative implication from normalised Laplace ratios at a general endpoint. -/
theorem solution
    (U : Measure Real) (c : Real → Real) (rho : Real)
    (l : Filter Real) (hrho : 0 ≤ rho)
    (hs : U (Iio 0) = 0)
    (hfin : ∀ t : Real, 0 < t → positiveLaplace U t ≠ ⊤)
    (he : ∀ᶠ x in l, 0 < x ∧ 0 ≤ c x)
    (hconv : ∀ t : Real, 0 < t → Tendsto
      (fun x => c x * (positiveLaplace U (t/x)).toReal) l
      (nhds (t^(-rho)))) :
    Tendsto (fun x => c x * (U (Icc 0 x)).toReal) l
      (nhds (1/Real.Gamma (1+rho))) := by
  obtain ⟨R,hsR,hAtom,hCum,hLap⟩ := karamataGammaReference rho hrho
  obtain ⟨M,hsM,hfinM,hLapM,hMass⟩ := karamataScaledMeasureData U c hs hfin
  have hfinR (t : Real) (ht : 0 < t) : positiveLaplace R t ≠ ⊤ := by
    rw [hLap t ht]
    exact ENNReal.ofReal_ne_top
  have hmom (n : Nat) : Tendsto
      (fun x => (positiveLaplace (M x) ((n : Real)+1)).toReal) l
      (nhds (positiveLaplace R ((n : Real)+1)).toReal) := by
    have ht : 0 < (n : Real)+1 := by positivity
    rw [hLap _ ht,ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _)]
    apply (hconv _ ht).congr'
    filter_upwards [he] with x hx
    exact (hLapM x _ hx.1 hx.2 ht).symm
  have h := karamataLaplaceFamilyCumulative l M R hsM hsR hfinM hfinR hmom hAtom
  rw [hCum] at h
  apply h.congr'
  filter_upwards [he] with x hx
  exact hMass x hx.1 hx.2
