-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_cosine_residual_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:42:19.023078+00:00
-- url     : https://prove2.me/submissions/014e3819-03e5-4d71-a429-6fb2764b0280

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_residual_exact
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_grid_high_frequency
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_jump_high_frequency
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
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, e ≤ |B m n t w|}).toReal ≤ η := by
  intro T E A B e he η hη
  let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
  let G : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w =>
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    ((triplet.gaussianVariance:ℝ)/2)*(t:ℝ) -
      ∑ k ∈ Finset.range n, q m (X (v (k+1)) w-X (v k) w)
  let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
    ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
      q m z.2 ∂(pathJumpMeasure X Xleft w)
  have hg := Kyprianou.Ch04.ito43_cosine_grid_high_frequency P X hLevy triplet hTriplet
    Xleft hLeft T (e/2) (by positivity) (η/2) (by positivity)
  have hj := Kyprianou.Ch04.ito43_cosine_jump_high_frequency P X hLevy triplet hTriplet
    Xleft hLeft T (e/2) (by positivity) (η/2) (by positivity)
  obtain ⟨m,hm⟩ := (hg.and hj).exists
  refine ⟨m,?_⟩
  have heq := Kyprianou.Ch04.ito43_cosine_residual_exact P X hLevy triplet hTriplet
    Xleft hLeft T
  filter_upwards [hm.1] with n hn
  let U : Set Omega := {w | ∃ t ≤ T, e/2 ≤ |G m n t w|}
  let V : Set Omega := {w | ∃ t ≤ T, e/2 ≤ |J m t w|}
  let W : Set Omega := {w | ∃ t ≤ T, e ≤ |B m n t w|}
  have hsub : ∀ᵐ w ∂P, w ∈ W → w ∈ U ∪ V := by
    filter_upwards [heq] with w hw
    rintro ⟨t,ht,hb⟩
    by_contra h
    have h1 : |G m n t w| < e/2 := lt_of_not_ge (fun h' => h (Or.inl ⟨t,ht,h'⟩))
    have h2 : |J m t w| < e/2 := lt_of_not_ge (fun h' => h (Or.inr ⟨t,ht,h'⟩))
    have hw' : B m n t w = G m n t w+J m t w := hw m n t ht
    rw [hw'] at hb
    linarith [abs_add_le (G m n t w) (J m t w)]
  have hU : P.real U ≤ η/2 := hn
  have hV : P.real V ≤ η/2 := hm.2
  exact (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans
    ((measureReal_union_le U V).trans (by linarith only [hU,hV]))
