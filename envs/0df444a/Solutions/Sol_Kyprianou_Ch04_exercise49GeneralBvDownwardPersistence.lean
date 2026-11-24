-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49GeneralBvDownwardPersistence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:42:59.959682+00:00
-- url     : https://prove2.me/submissions/eb412f23-dfdf-4401-8271-b0e410b7dd2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_exercise49GeneralBvSmallTimeDrift
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

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
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (drift : Real)
    (hDrift : drift =
       triplet.drift -
         ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure)
    (hd : 0 < drift)
    (hNotSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Monotone (fun t : NNReal => X t omega))) :
    let tau : Omega -> WithTop NNReal := fun omega =>
      sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t omega < 0};
    0 < P {omega : Omega | 0 < tau omega} := by
  dsimp only
  have hae : ∀ᵐ w ∂P, 0 < sInf {u : WithTop NNReal |
      ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t w < 0} := by
    filter_upwards [Kyprianou.Ch04.exercise49GeneralBvSmallTimeDrift
      P X hLevy triplet hTriplet hBV drift hDrift hd hNotSubordinator] with w hw
    have hpos : {t : NNReal | 0 < X t w / (t : Real)} ∈
        nhdsWithin (0 : NNReal) (Ioi 0) :=
      hw.eventually (eventually_gt_nhds hd)
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hpos
    let a : NNReal := ⟨ε, hε.le⟩
    have ha : 0 < a := hε
    refine lt_of_lt_of_le (show (0 : WithTop NNReal) < (a : WithTop NNReal) by
      exact_mod_cast ha) (le_sInf ?_)
    rintro u ⟨t, rfl, ht, hneg⟩
    apply WithTop.coe_le_coe.mpr
    by_contra! hlt
    have hball : t ∈ Metric.ball (0 : NNReal) ε := by
      rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
        abs_of_nonneg (NNReal.coe_nonneg t)]
      exact_mod_cast hlt
    have hp := hsub ⟨hball, ht⟩
    exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg hneg.le
      (NNReal.coe_nonneg t))) hp
  have heq : P {w : Omega | 0 < sInf {u : WithTop NNReal |
      ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t w < 0}} = P univ :=
    measure_congr (hae.mono fun w hw => by
      change (0 < sInf {u : WithTop NNReal |
        ∃ t : NNReal, u = ↑t ∧ 0 < t ∧ X t w < 0}) = True
      exact propext (iff_true_intro hw))
  rw [heq, measure_univ]
  exact zero_lt_one
