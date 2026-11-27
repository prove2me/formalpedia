-- Prove2me | solution 1 for Kyprianou.Ch05.creepingLowerRelativeBound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:27:44.82473+00:00
-- url     : https://prove2.me/submissions/9e254b5d-c871-4a22-8bc0-4bbcbea179ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_creepingLowerBackwardWindowBound
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (hNonLattice : NonLatticeMeasure (U 0))
    (hPotLim : ∀ y : Real, 0 < y →
      Tendsto (fun x : Real => ((U 0) (Set.Ioc x (x + y))).toReal)
        atTop (nhds (y / (∫ omega, Y 1 omega ∂P))))
    (hd : 0 < d) :
  ∀ δ : Real, 0 < δ → ∀ᶠ x : Real in atTop,
    (d - δ) * ((U 0) (Set.Ioc x (x + 1))).toReal ≤ creepingProbability P Y death x := by
  intro δ hδ
  have hμ : 0 < (∫ omega, Y 1 omega ∂P) := hPositiveMean
  by_cases hcase : δ < d
  · have h1μ : (1 : Real) / (∫ omega, Y 1 omega ∂P) ≠ 0 := ne_of_gt (one_div_pos.mpr hμ)
    have hUb : Tendsto (fun x : Real => ((U 0) (Set.Ioc (x - 1) x)).toReal) atTop (nhds (1 / (∫ omega, Y 1 omega ∂P))) := by
      have hcomp := (hPotLim 1 one_pos).comp (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
      refine hcomp.congr fun x => ?_
      simp only [Function.comp_apply, sub_eq_add_neg, id_eq]
      rw [show x + -1 + 1 = x by ring]
    have hUf := hPotLim 1 one_pos
    have hratio : Tendsto (fun x : Real => ((U 0) (Set.Ioc (x - 1) x)).toReal / ((U 0) (Set.Ioc x (x + 1))).toReal) atTop (nhds 1) := by
      have h := hUb.div hUf h1μ
      rwa [div_self h1μ] at h
    have hpos : ∀ᶠ x : Real in atTop, (0 : Real) < ((U 0) (Set.Ioc x (x + 1))).toReal :=
      hUf.eventually (eventually_gt_nhds (one_div_pos.mpr hμ))
    have hd2 : 0 < d - δ / 2 := by linarith
    have hη : 0 < (δ / 2) / (d - δ / 2) := div_pos (half_pos hδ) hd2
    have h2 := Metric.tendsto_nhds.mp hratio ((δ / 2) / (d - δ / 2)) hη
    have h3 := Kyprianou.Ch05.creepingLowerBackwardWindowBound P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential hFiniteMean hPositiveMean hNonLattice hPotLim hd (δ / 2) (half_pos hδ)
    filter_upwards [h2, hpos, h3] with x hx2 hxp hx3
    rw [Real.dist_eq] at hx2
    have hgt : 1 - (δ / 2) / (d - δ / 2) < ((U 0) (Set.Ioc (x - 1) x)).toReal / ((U 0) (Set.Ioc x (x + 1))).toReal := by
      have h := (abs_lt.mp hx2).1
      linarith
    rw [lt_div_iff₀ hxp] at hgt
    have hd2ne : d - δ / 2 ≠ 0 := ne_of_gt hd2
    have hfactor : (d - δ / 2) * (1 - (δ / 2) / (d - δ / 2)) = d - δ := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hd2ne]
      ring
    calc (d - δ) * ((U 0) (Set.Ioc x (x + 1))).toReal = (d - δ / 2) * ((1 - (δ / 2) / (d - δ / 2)) * ((U 0) (Set.Ioc x (x + 1))).toReal) := by
          rw [← mul_assoc, hfactor]
      _ ≤ (d - δ / 2) * ((U 0) (Set.Ioc (x - 1) x)).toReal := mul_le_mul_of_nonneg_left (le_of_lt hgt) (le_of_lt hd2)
      _ ≤ creepingProbability P Y death x := hx3
  · filter_upwards with x
    have hU : 0 ≤ ((U 0) (Set.Ioc x (x + 1))).toReal := ENNReal.toReal_nonneg
    have hnn : 0 ≤ creepingProbability P Y death x := ENNReal.toReal_nonneg
    have hle : (d - δ) * ((U 0) (Set.Ioc x (x + 1))).toReal ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hU
    linarith
