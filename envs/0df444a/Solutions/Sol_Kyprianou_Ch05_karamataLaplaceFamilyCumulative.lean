-- Prove2me | solution 1 for Kyprianou.Ch05.karamataLaplaceFamilyCumulative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:50:59.363257+00:00
-- url     : https://prove2.me/submissions/100dccd7-11bc-447d-a6f8-f19105648b4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Theorems.Thm_Kyprianou_Ch05_karamataExpTiltData
import Theorems.Thm_Kyprianou_Ch05_karamataExpTiltRecoverMass
import Theorems.Thm_Kyprianou_Ch05_compactMomentWeightedUpperRay
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Convert Laplace convergence into compact moments and recover the cumulative mass. -/
theorem solution
    {I : Type} (l : Filter I) (M : I → Measure Real) (R : Measure Real)
    (hs : ∀ i, M i (Iio 0) = 0) (hsR : R (Iio 0) = 0)
    (hfin : ∀ i (t : Real), 0 < t → positiveLaplace (M i) t ≠ ⊤)
    (hfinR : ∀ t : Real, 0 < t → positiveLaplace R t ≠ ⊤)
    (hconv : ∀ n : Nat, Tendsto
      (fun i => (positiveLaplace (M i) ((n : Real)+1)).toReal) l
      (nhds (positiveLaplace R ((n : Real)+1)).toReal))
    (hAtom : R {1} = 0) :
    Tendsto (fun i => (M i (Icc 0 1)).toReal) l (nhds (R (Icc 0 1)).toReal) := by
  let T (m : Measure Real) := (m.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
    (fun z : Real => Real.exp (-z))
  have hD (i : I) := karamataExpTiltData (M i) (hs i) (hfin i)
  obtain ⟨hfR,hSR,hiR,hmR⟩ := karamataExpTiltData R hsR hfinR
  have hA := (karamataExpTiltRecoverMass R hsR).2 hAtom
  have h := compactMomentWeightedUpperRay l (fun i => T (M i)) (T R)
    (fun i => (hD i).1) hfR (fun i => (hD i).2.1) hSR
    (fun i => (hD i).2.2.1) hiR (by
      intro n
      simpa only [T,fun i => (hD i).2.2.2 n,hmR n] using hconv n)
    (Real.exp (-1)) (Real.exp_pos _) hA
  have hr := (karamataExpTiltRecoverMass R hsR).1
  rw [show ((T R).withDensity (fun z : Real => ENNReal.ofReal ((max z (Real.exp (-1)))⁻¹))) (Ici (Real.exp (-1))) = R (Icc 0 1) from hr] at h
  apply h.congr'
  filter_upwards [] with i
  exact congrArg ENNReal.toReal (karamataExpTiltRecoverMass (M i) (hs i)).1
