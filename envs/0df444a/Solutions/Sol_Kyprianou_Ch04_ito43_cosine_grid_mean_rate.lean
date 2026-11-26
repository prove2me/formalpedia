-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_grid_mean_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:52:30.190373+00:00
-- url     : https://prove2.me/submissions/9a26f28b-1260-46e7-85dc-b103017db6ca

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_normalised_exponent_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_exponential_cosine_mesh_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_mean_exact
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution  {Omega : Type} [MeasurableSpace Omega]
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
    let μ : ℕ → ℕ → ℝ := fun m n =>
      ∫ w, q m (X (T/(n:NNReal)) w) ∂P
    ∀ e : ℝ, 0 < e → ∀ᶠ m : ℕ in atTop, ∀ᶠ n : ℕ in atTop,
      |(n:ℝ)*μ m n-((triplet.gaussianVariance:ℝ)/2)*(T:ℝ)| < e := by
  intro T q μ e he
  let c : ℝ := (triplet.gaussianVariance:ℝ)/2
  let a : ℕ → ℝ := fun m => (m:ℝ)+1
  let Z : ℕ → ℂ := fun m => Kyprianou.Ch01.levyTripleExponent triplet (a m)
  have hfreq : Tendsto (fun m => (-(Z m).re/(a m)^2)*(T:ℝ)) atTop (nhds (c*(T:ℝ))) :=
    (ito43_cosine_normalised_exponent_limit triplet).mul_const (T:ℝ)
  have hfreq' := (Metric.tendsto_atTop.mp hfreq) (e/2) (by positivity)
  obtain ⟨M,hM⟩ := hfreq'
  filter_upwards [eventually_ge_atTop M] with m hm
  have hmesh := (ito43_exponential_cosine_mesh_limit T (Z m)).div_const ((a m)^2)
  have hmean : Tendsto (fun n : ℕ => (n:ℝ)*μ m n) atTop
      (nhds ((-(Z m).re/(a m)^2)*(T:ℝ))) := by
    convert hmesh using 1
    · funext n
      rw [show μ m n = (1-(Complex.exp (((((T/(n:NNReal)):NNReal):ℝ):ℂ)*(Z m))).re)/(a m)^2 from
        ito43_cosine_mean_exact P X hLevy triplet hTriplet Xleft hLeft T m n]
      ring
    · ring
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.mp hmean) (e/2) (by positivity)
  filter_upwards [eventually_ge_atTop (N:ℕ)] with n hn
  have h1 := hN n hn
  have h2 := hM m hm
  rw [Real.dist_eq] at h1 h2
  have h3 := abs_sub_le ((n:ℝ)*μ m n) ((-(Z m).re/(a m)^2)*(T:ℝ)) (c*(T:ℝ))
  change |(n:ℝ)*μ m n-c*(T:ℝ)| < e
  linarith
