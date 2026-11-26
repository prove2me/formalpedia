-- Prove2me | solution 1 for Kyprianou.Ch05.potentialRenewalOfZeroMarginals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:24:49.296118+00:00
-- url     : https://prove2.me/submissions/bec7552b-ab55-4970-818c-5b35648837e4

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_expNeg_setLintegral
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The zero subordinator has unit-discount potential equal to the Dirac measure at zero and infinite undiscounted occupation there, giving the renewal identity without finite-transform assumptions. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hzero : ∀ t : NNReal, ∀ᵐ w ∂P, Y t w = 0) :
    renewalMeasure (U 1) = Measure.dirac (0 : Real) + U 0 := by
  classical
  have hd := hKilled.2.2.2.1 rfl
  have hmass (t : Real) (B : Set Real) :
      P {w : Omega | (Real.toNNReal t : WithTop NNReal) < death w ∧
        Y (Real.toNNReal t) w ∈ B} = if (0 : Real) ∈ B then 1 else 0 := by
    have he : {w : Omega | (Real.toNNReal t : WithTop NNReal) < death w ∧
        Y (Real.toNNReal t) w ∈ B} =ᵐ[P] {w : Omega | (0 : Real) ∈ B} := by
      filter_upwards [hzero (Real.toNNReal t)] with w hw
      apply propext
      change ((Real.toNNReal t : WithTop NNReal) < death w ∧ Y (Real.toNNReal t) w ∈ B) ↔ (0 : Real) ∈ B
      have htop : (Real.toNNReal t : WithTop NNReal) < ⊤ := by
        first | exact WithTop.coe_lt_top _ | exact WithTop.coe_lt_top
      rw [hd w, hw]
      exact ⟨fun h => h.2, fun h => ⟨htop, h⟩⟩
    rw [measure_congr he]
    split_ifs with h
    · simp [h]
    · simp [h]
  have hU (q : Real) (hq : 0 ≤ q) (B : Set Real) (hB : MeasurableSet B) :
      U q B = if (0 : Real) ∈ B then (ENNReal.ofReal q)⁻¹ else 0 := by
    rw [(hPotential q hq).2 B hB]
    simp_rw [hmass]
    split_ifs with h
    · simp only [mul_one]
      exact killedPotential_expNeg_setLintegral q hq
    · simp
  have h1 : U 1 = Measure.dirac (0 : Real) := by
    ext B hB
    rw [hU 1 (by norm_num) B hB, Measure.dirac_apply' _ hB]
    simp [Set.indicator]
  have hp (n : Nat) : renewalConvolutionPower (U 1) n = Measure.dirac (0 : Real) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (renewalConvolutionPower (U 1) n).conv (U 1) = _
      rw [ih, h1, Measure.dirac_conv_dirac]
      simp
  ext B hB
  rw [renewalMeasure, Measure.sum_apply _ hB, Measure.add_apply,
    hU 0 le_rfl B hB]
  simp_rw [hp, Measure.dirac_apply' _ hB]
  by_cases h : (0 : Real) ∈ B
  · simp [h, ENNReal.tsum_const_eq_top_of_ne_zero]
  · simp [h]
