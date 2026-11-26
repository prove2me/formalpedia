-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_unweighted_quadratic_grid_ucp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:55:11.35438+00:00
-- url     : https://prove2.me/submissions/9ab4d22b-220e-4a5d-a130-33620c7c33ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_cosine_remainder_ucp
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_cosine_residual_small
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_approximation
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega)))
    :
    ∀ (T : NNReal) (epsilon : ℝ), 0 < epsilon →
      Tendsto (fun n : ℕ =>
        (P {omega : Omega | ∃ t : NNReal, t ≤ T ∧
          let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
          let v : ℕ → NNReal := fun k => min t (u k)
          epsilon ≤ |((triplet.gaussianVariance : ℝ) / 2) *
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), (1 : ℝ) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
      (X (v (k+1)) omega - X (v k) omega)^2 / 2)|}).toReal) atTop (nhds 0) := by
  intro T epsilon he
  let E : ℕ → NNReal → Omega → ℝ := fun n t omega =>
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    ((triplet.gaussianVariance : ℝ) / 2) *
    (∫ s in Set.Icc (0 : ℝ) (t : ℝ), (1 : ℝ) ∂volume) + (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
    z.2^2 / 2 ∂(pathJumpMeasure X Xleft omega)) - (∑ k ∈ Finset.range n,
    (X (v (k+1)) omega - X (v k) omega)^2 / 2)
  let A : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t omega =>
    let a : ℝ := (m:ℝ)+1
    let r : ℝ → ℝ := fun z => z^2/2-(1-Real.cos (a*z))/a^2
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
      r z.2 ∂(pathJumpMeasure X Xleft omega)) -
    (∑ k ∈ Finset.range n, r (X (v (k+1)) omega-X (v k) omega))
  let B : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w => E n t w-A m n t w
  have hA := Kyprianou.Ch04.ito43_qv_cosine_remainder_ucp
    P X hLevy triplet hTriplet Xleft hLeft T
  have hB := Kyprianou.Ch04.ito43_qv_cosine_residual_small
    P X hLevy triplet hTriplet Xleft hLeft T
  exact Kyprianou.Ch04.ito43_ucp_approximation P E A B T
    (fun m n t w => by dsimp [B]; ring) hA hB epsilon he
