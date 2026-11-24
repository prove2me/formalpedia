-- Prove2me | solution 1 for Kyprianou.Ch03.submulMoment_reverse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:32:11.787067+00:00
-- url     : https://prove2.me/submissions/7dcc490c-3f51-459e-b3e4-2daa8ffad326
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_momentMarginalLargeSmallFactorizationV1
import Theorems.Thm_Kyprianou_Ch03_momentLargeJumpLawCriterionV1
import Theorems.Thm_Kyprianou_Ch03_momentLightMarginalExpAbsV1
import Theorems.Thm_Kyprianou_Ch03_momentSubmulProductSumIffV1
import Theorems.Thm_Kyprianou_Ch03_momentSubmulLightLawIntegrableV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (g : Real -> Real)
    (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hg_bounded : forall R : Real, 0 <= R ->
      exists M : Real, forall x : Real, abs x <= R -> g x <= M) :
    ((forall (t : NNReal), 0 < t ->
      Integrable (fun omega => g (X t omega)) P)) -> ((IntegrableOn g {x : Real | 1 <= abs x} T.levyMeasure)) := by
  intro hmoment
  let t : NNReal := 1
  have ht : 0 < t := by norm_num [t]
  obtain ⟨mu, nu, hmu, hnu, heq, hm, hn⟩ :=
    Kyprianou.Ch03.momentMarginalLargeSmallFactorizationV1 P X hX T hLK t ht
  letI : IsProbabilityMeasure mu := hmu
  letI : IsProbabilityMeasure nu := hnu
  have hlight : Integrable g nu :=
    Kyprianou.Ch03.momentSubmulLightLawIntegrableV1 nu g hg hg_meas hg_bounded
      (fun b hb => Kyprianou.Ch03.momentLightMarginalExpAbsV1 T t ht nu hn b hb)
  have hlarge := Kyprianou.Ch03.momentLargeJumpLawCriterionV1 T t ht mu hm g hg hg_meas
  have hsum := Kyprianou.Ch03.momentSubmulProductSumIffV1 mu nu g hg hg_meas hlight
  have hcoord := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
  have h : Integrable g (P.map (X t)) :=
    (integrable_map_measure hg_meas.aestronglyMeasurable hcoord).mpr (hmoment t ht)
  rw [heq] at h
  exact hlarge.mp (hsum.mp h)
