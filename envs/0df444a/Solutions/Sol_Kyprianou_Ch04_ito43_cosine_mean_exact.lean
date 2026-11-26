-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_mean_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:52:26.383378+00:00
-- url     : https://prove2.me/submissions/11f4f0e1-424a-4c43-8ede-d197e5a430ba

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_ProbabilityTheory_leanlevy_chat24_re_one_sub_charFun_eq_integral
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution   {Omega : Type} [MeasurableSpace Omega]
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
    ∀ m n : ℕ, μ m n =
      (1-(Complex.exp (((((T/(n:NNReal)):NNReal):ℝ):ℂ) *
        Kyprianou.Ch01.levyTripleExponent triplet ((m:ℝ)+1))).re)/((m:ℝ)+1)^2 := by
  intro T q μ m n
  let h : NNReal := T/(n:NNReal)
  let a : ℝ := (m:ℝ)+1
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hLevy h
  haveI : IsProbabilityMeasure (P.map (X h)) := Measure.isProbabilityMeasure_map hm
  have hg : Continuous (fun x : ℝ => 1-Real.cos (a*x)) := by fun_prop
  change (∫ w, (1-Real.cos (a*X h w))/a^2 ∂P) = _
  rw [integral_div]
  have hi : (∫ w, 1-Real.cos (a*X h w) ∂P) =
      (1-charFun (P.map (X h)) a).re := by
    rw [ProbabilityTheory.leanlevy_chat24_re_one_sub_charFun_eq_integral]
    exact (integral_map hm hg.measurable.aestronglyMeasurable).symm
  rw [hi,hTriplet]
  simp only [Complex.sub_re,Complex.one_re]
  rfl
