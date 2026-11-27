-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPotentialUnitSupportV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:39:52.49636+00:00
-- url     : https://prove2.me/submissions/056b44f1-ada4-4ed7-9fdd-bb5ec27e179f

import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialMapV1
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Nonnegative paths and strictly positive exponential weights transfer support and nonlattice properties. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    (U 1) (Set.Iio (0 : Real)) = 0 ∧
      (NonLatticeMeasure (U 0) → NonLatticeMeasure (U 1)) := by
  obtain ⟨Z, hZ, he, hm⟩ := unkilledPotentialMapV1 P Y death hKilled U hPotential
  have hocc (q : Real) (hq : 0 ≤ q) (B : Set Real) (hB : MeasurableSet B) :
      U q B = ∫⁻ t in Set.Ici (0 : Real),
        ENNReal.ofReal (Real.exp (-q*t)) * P (Z (Real.toNNReal t) ⁻¹' B) ∂volume := by
    rw [hm q hq, Measure.map_apply hZ hB, Measure.prod_apply (hZ hB),
      lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
        (measurable_measure_prodMk_left (hZ hB))]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hocc 1 (by norm_num) _ measurableSet_Iio]
    have hz (t : Real) : P (Z (Real.toNNReal t) ⁻¹' Set.Iio 0) = 0 := by
      have hs : Z (Real.toNNReal t) ⁻¹' Set.Iio 0 = {w | ¬ 0 ≤ Z (Real.toNNReal t) w} := by
        ext w; simp [not_le]
      rw [hs, ← ae_iff]
      filter_upwards [he, hKilled.1.2] with w hw hp
      simpa [hw (Real.toNNReal t), hKilled.1.1.start_zero] using hp (bot_le : 0 ≤ Real.toNNReal t)
    simp [hz]
  intro hnl h hh hz
  let B : Set Real := {x | ∀ n : Int, x ≠ (n : Real)*h}
  have hB : MeasurableSet B := by
    have hBe : B = ⋂ n : Int, ({(n : Real)*h} : Set Real)ᶜ := by ext x; simp [B]
    rw [hBe]
    exact MeasurableSet.iInter fun n => (measurableSet_singleton _).compl
  have hg : Measurable (fun t : Real => P (Z (Real.toNNReal t) ⁻¹' B)) :=
    measurable_measure_prodMk_left (hZ hB)
  change U 1 B = 0 at hz
  rw [hocc 1 (by norm_num) B hB] at hz
  have hzAE := (lintegral_eq_zero_iff ((by fun_prop : Measurable
    (fun t : Real => ENNReal.ofReal (Real.exp (-(1 : Real)*t)))).mul hg)).mp hz
  apply hnl h hh
  change U 0 B = 0
  rw [hocc 0 le_rfl B hB]
  simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hzAE] with t ht
  exact (mul_eq_zero.mp ht).resolve_left (by positivity)
