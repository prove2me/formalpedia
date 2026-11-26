-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_cosine_remainder_ucp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:25:39.756353+00:00
-- url     : https://prove2.me/submissions/c2c031c2-60ee-4419-8f3b-c810f360ab5e

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_mark_subquadratic_ucp
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_remainder_scalar
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Omega : Type} [MeasurableSpace Omega]
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
    ∀ T : NNReal,
    let A : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t omega =>
      let a : ℝ := (m:ℝ)+1
      let r : ℝ → ℝ := fun z => z^2/2-(1-Real.cos (a*z))/a^2
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Set.prod (Set.Icc (0 : ℝ) (t : ℝ)) (Set.univ : Set ℝ),
        r z.2 ∂(pathJumpMeasure X Xleft omega)) -
      (∑ k ∈ Finset.range n, r (X (v (k+1)) omega-X (v k) omega))
    ∀ (m : ℕ) (e : ℝ), 0 < e →
      Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |A m n t w|}).toReal) atTop (nhds 0) := by
  intro T A m e he
  let a : ℝ := (m:ℝ)+1
  let r : ℝ → ℝ := fun z => z^2/2-(1-Real.cos (a*z))/a^2
  obtain ⟨hr,hb,hs⟩ := Kyprianou.Ch04.ito43_cosine_remainder_scalar a (by dsimp [a]; positivity)
  have hb' (z : ℝ) : |r z| ≤ (1/2:ℝ)*z^2 := by
    convert hb z using 1 <;> ring
  exact Kyprianou.Ch04.ito43_mark_subquadratic_ucp P X hLevy triplet hTriplet Xleft hLeft
    r hr (1/2) (by norm_num) hb' hs T e he
