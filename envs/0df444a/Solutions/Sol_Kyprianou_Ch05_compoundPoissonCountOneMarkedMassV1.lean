-- Prove2me | solution 1 for Kyprianou.Ch05.compoundPoissonCountOneMarkedMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:02:12.244044+00:00
-- url     : https://prove2.me/submissions/f862fd5d-cd36-40bc-acc6-3c31487b84c7

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_compoundPoissonCountOneEventV1
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_jumpCount
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05 Set Complex
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (r : NNReal) (hr : 0 < r) (F : Measure ℝ) [IsProbabilityMeasure F]
    (tau M : ℕ → Omega → ℝ)
    (hDriver : LevyFoundations.IsCompoundPoissonDriver tau M r F P)
    (hCount : ∀ t : NNReal,
      P.map (fun w => LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival tau n w) (t : ℝ)) = poissonMeasure (r*t))    (t : ℝ) (ht : 0 ≤ t) (B : Set ℝ) (hB : MeasurableSet B) :
    P {w | LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival tau n w) t = 1 ∧ M 0 w ∈ B} =
      ENNReal.ofReal (Real.exp (-(r:ℝ)*t) * ((r:ℝ)*t)) * F B := by
  classical
  let N : Omega → ℕ := fun w => LevyFoundations.jumpCount
    (fun n => LevyFoundations.arrival tau n w) t
  let A : Set (ℝ × ℝ) := {p | p.1 ≤ t ∧ t < p.1 + p.2}
  let E : Set Omega := (fun w => (tau 0 w,tau 1 w)) ⁻¹' A
  have hE : E = N ⁻¹' {1} := by
    ext w
    change (tau 0 w ≤ t ∧ t < tau 0 w+tau 1 w) ↔ N w = 1
    symm
    simpa [N,LevyFoundations.arrival,Finset.sum_range_succ] using
      Kyprianou.Ch05.compoundPoissonCountOneEventV1
        (fun n => LevyFoundations.arrival tau n w) t
  have hNlaw : P.map N = poissonMeasure (r * Real.toNNReal t) := by
    simpa only [N,Real.coe_toNNReal t ht] using hCount (Real.toNNReal t)
  have hNm : AEMeasurable N P := by
    apply AEMeasurable.of_map_ne_zero
    rw [hNlaw]
    intro hz
    have hu := congrArg (fun mu : Measure ℕ => mu univ) hz
    simp at hu
  have hEP : P E = ENNReal.ofReal (Real.exp (-(r:ℝ)*t) * ((r:ℝ)*t)) := by
    rw [hE,← Measure.map_apply_of_aemeasurable hNm (measurableSet_singleton 1),hNlaw,
      poissonMeasure_singleton]
    simp [NNReal.coe_mul,Real.coe_toNNReal t ht,neg_mul]
  have hAll (i : ℕ ⊕ ℕ) : Measurable (Sum.elim tau M i) := by
    cases i with
    | inl i => exact hDriver.measurable_interarrival i
    | inr i => exact hDriver.measurable_mark i
  have hInd : IndepFun (fun w => (tau 0 w,tau 1 w)) (M 0) P :=
    hDriver.indep.indepFun_prodMk hAll (Sum.inl 0) (Sum.inl 1) (Sum.inr 0)
      (by simp) (by simp)
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
  have hprod := hInd.measure_inter_preimage_eq_mul A B hA hB
  have hMark : P (M 0 ⁻¹' B) = F B := by
    rw [← Measure.map_apply (hDriver.measurable_mark 0) hB,
      (hDriver.law_mark 0).map_eq]
  have he : {w | N w = 1 ∧ M 0 w ∈ B} = E ∩ (M 0 ⁻¹' B) := by
    rw [hE]
    rfl
  change P {w | N w = 1 ∧ M 0 w ∈ B} = _
  rw [he]
  change P (E ∩ (M 0 ⁻¹' B)) = _ at hprod ⊢
  rw [hprod,hEP,hMark]
