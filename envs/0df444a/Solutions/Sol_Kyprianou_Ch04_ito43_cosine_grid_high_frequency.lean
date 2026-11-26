-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_grid_high_frequency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:49:24.418034+00:00
-- url     : https://prove2.me/submissions/d848e3e9-d400-42cf-9063-cd6bc967ee9c

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_grid_mean_rate
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_prefix_centered_tail
import Theorems.Thm_Kyprianou_Ch04_ito43_bounded_mark_grid_event_inclusion
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_deficit_square_bound
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
          (nhds (Xleft t omega))) :
    ∀ T : NNReal,
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let G : ℕ → ℕ → NNReal → Omega → ℝ := fun m n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ((triplet.gaussianVariance:ℝ)/2)*(t:ℝ) -
        ∑ k ∈ Finset.range n, q m (X (v (k+1)) w-X (v k) w)
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      ∀ᶠ n : ℕ in atTop, (P {w | ∃ t ≤ T, e ≤ |G m n t w|}).toReal ≤ η := by
  intro T q G e he η hη
  let μ : ℕ → ℕ → ℝ := fun m n =>
    ∫ w, q m (X (T/(n:NNReal)) w) ∂P
  let D : ℕ → ℕ → ℕ → Omega → ℝ := fun m n k w =>
    q m (X (T*((k+1:ℕ):NNReal)/(n:NNReal)) w -
      X (T*(k:NNReal)/(n:NNReal)) w) - μ m n
  let c : ℝ := (triplet.gaussianVariance:ℝ)/2
  have hm := ito43_cosine_grid_mean_rate P X hLevy triplet hTriplet Xleft hLeft T (e/4) (by positivity)
  have hp := ito43_cosine_prefix_centered_tail P X hLevy triplet hTriplet Xleft hLeft T (e/4) (by positivity) η hη
  have hfreq : Tendsto (fun m : ℕ => (2:ℝ)/((m:ℝ)+1)^2) atTop (nhds 0) := by
    have h : Tendsto (fun m : ℕ => (1:ℝ)/((m:ℝ)+1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    convert (h.mul h).const_mul (2:ℝ) using 1
    · funext m
      have hn : (m:ℝ)+1 ≠ 0 := by positivity
      field_simp
      <;> ring
    · norm_num
  filter_upwards [hm,hp,hfreq.eventually (gt_mem_nhds (show 0 < e/4 by positivity))]
    with m hmean hprob hcut
  have hmesh : Tendsto (fun n : ℕ => |c| * ((T:ℝ)/(n:ℝ))) atTop (nhds 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (T:ℝ)).const_mul |c|
  filter_upwards [hmean,hprob,hmesh.eventually (gt_mem_nhds (show 0 < e/4 by positivity)),
    eventually_gt_atTop (0:ℕ)] with n hmean' hprob' hmesh' hn
  apply le_trans (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono ?_)) hprob'
  rintro w ⟨t,ht,herr⟩
  let a : ℝ := (m:ℝ)+1
  have ha : 0 < a := by dsimp [a]; positivity
  have hq (z : ℝ) : 0 ≤ q m z ∧ q m z ≤ 2/a^2 := by
    have h := ito43_cosine_deficit_square_bound a z ha
    exact ⟨h.1,h.2.2⟩
  exact ito43_bounded_mark_grid_event_inclusion (fun t => X t w) (q m)
    (by simp [q]) T c (μ m n) (2/a^2) e he (by positivity) hq n hn
    hmean' hmesh' hcut t ht herr
