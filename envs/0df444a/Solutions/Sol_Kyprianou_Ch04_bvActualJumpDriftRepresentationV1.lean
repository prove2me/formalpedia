-- Prove2me | solution 1 for Kyprianou.Ch04.bvActualJumpDriftRepresentationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:41:33.600134+00:00
-- url     : https://prove2.me/submissions/5276a983-83fc-4cf8-9b65-11fc23a4a2e9

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch02_levyActualCompactJumpAbsoluteSummabilityV1
import Theorems.Thm_Kyprianou_Ch02_levySignedResidualAtTimeTransferV1
import Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfCharFunV1
import Theorems.Thm_Kyprianou_Ch02_cadlagLinearResidualFromDenseGridV1
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_lintegral_min_one_sq_lt_top
import Theorems.Thm_Kyprianou_Ch04_bvCanonicalPoissonExactDriftV1
open MeasureTheory ProbabilityTheory Filter Function
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (Xleft : NNReal → Omega → Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      0 < t →
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega))) :
    ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + (triplet.drift - ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure) * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega) := by
  rcases triplet with ⟨b, σ, ν, hν⟩
  rcases hBV with ⟨hσ, hsmall⟩
  change σ = 0 at hσ
  subst σ
  have hs : Integrable (fun x : ℝ => |x|) (ν.restrict (Set.Ioo (-1 : ℝ) 1)) := by
    refine ⟨by fun_prop, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => abs_nonneg x)).2 hsmall
  have hi : Integrable (Set.indicator (Set.Ioo (-1 : ℝ) 1) fun x => |x|) ν := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact hs
  have hl : Integrable (fun x : ℝ => min 1 (x ^ 2)) ν := by
    refine ⟨by fun_prop, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun x => le_min zero_le_one (sq_nonneg x))).2
        (ProbabilityTheory.IsLevyMeasure.lintegral_min_one_sq_lt_top hν)
  have hf : Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν := by
    apply (hi.add hl).mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (abs_nonneg x))]
    change min 1 |x| ≤ (Set.Ioo (-1 : ℝ) 1).indicator (fun x => |x|) x + min 1 (x ^ 2)
    by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hx]
      have hn : 0 ≤ min (1 : ℝ) (x ^ 2) := le_min zero_le_one (sq_nonneg x)
      exact (min_le_right 1 |x|).trans (le_add_of_nonneg_right hn)
    · rw [Set.indicator_of_notMem hx, zero_add]
      have hx' : 1 ≤ |x| := by
        by_contra hn
        exact hx (abs_lt.mp (lt_of_not_ge hn))
      have hsq : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      rw [min_eq_left hx', min_eq_left hsq]
  have hchar : ∀ (t : NNReal) (ξ : ℝ),
      charFun (P.map (X t)) ξ = Complex.exp (((t : ℝ) : ℂ) *
        Kyprianou.Ch01.levyTripleExponent ⟨-(-b), (0 : NNReal)^2, ν, hν⟩ ξ) := by
    intro t ξ
    simpa using hTriplet t ξ
  have hsum := Kyprianou.Ch02.levyActualCompactJumpAbsoluteSummabilityV1
    (-b) 0 ν hν P X hLevy hchar hf
  obtain ⟨A, mA, Q, Y, hprob, hY, hcharY, hres⟩ :=
    Kyprianou.Ch04.bvCanonicalPoissonExactDriftV1 (-b) ν hν hf
  letI : MeasurableSpace A := mA
  letI : IsProbabilityMeasure Q := hprob
  let c := b - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂ν
  have hpath := Kyprianou.Ch02.levyWholePathLawEqOfCharFunV1 P Q X Y hLevy hY
    (fun t ξ => by
      rw [hTriplet t ξ, hcharY t ξ]
      simp [Kyprianou.Ch01.levyTripleExponent])
  obtain ⟨grid, hdense⟩ := TopologicalSpace.exists_dense_seq NNReal
  have hgrid (k : ℕ) := Kyprianou.Ch02.levySignedResidualAtTimeTransferV1
    P Q X Y hLevy hY hpath (grid k) c (hsum.mono fun ω h => h (grid k))
    (hres.mono fun ω h => (h (grid k)).1)
    (hres.mono fun ω h => by simpa [c] using (h (grid k)).2)
  filter_upwards [hLevy.cadlag_ae, hsum, ae_all_iff.mpr hgrid, hLeft] with ω hc hs he hl
  have hall := Kyprianou.Ch02.cadlagLinearResidualFromDenseGridV1
    (fun t => X t ω) c grid hdense (fun t => (hc t).1) hs he
  intro t
  have hEq (s : Set.Ioc (0 : NNReal) t) :
      Function.leftLim (fun u => X u ω) s = Xleft s ω := by
    haveI : (nhdsWithin (s : NNReal) (Set.Iio (s : NNReal))).NeBot :=
      nhdsWithin_Iio_neBot' ⟨0, s.property.1⟩ le_rfl
    exact leftLim_eq_of_tendsto (hl s s.property.1)
  have hzero : X 0 ω = 0 := congrFun hLevy.start_zero ω
  constructor
  · simpa only [hEq] using hs t
  · simpa only [hEq, hzero, zero_add] using hall t
