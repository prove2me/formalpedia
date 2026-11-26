-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_oneJump_shiftedChunk_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:18:06.664703+00:00
-- url     : https://prove2.me/submissions/0f747722-98eb-4c14-a62c-bb168b51ff51

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_oneJump_unkilled_lower
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
    ∀ h : Real, 0 < h → ∀ a b : Real, 0 < a → a ≤ b →
      (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) →
      ∃ δ : Real, 0 < δ ∧ ∀ t ∈ Set.Ioc (0 : Real) δ,
        ENNReal.ofReal (2 * t / 3) * Pi (Set.Icc a b) ≤
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}}) := by
  intro hPi _h _hh a b ha hab _hoff
  have heta : 0 ≤ eta := hKilled.2.1
  have hsurv := hKilled.2.2.2.2.1
  have hindep := hKilled.2.2.2.2.2
  obtain ⟨δc, hδc, hcore⟩ :=
    Kyprianou.Ch05.killedPotential_oneJump_unkilled_lower P Y death eta d Pi Phi
      hKilled hTriplet hLaplaceLaw hPi a b ha hab
  have heta1 : (0 : Real) < eta + 1 := by linarith
  refine ⟨min δc (1 / (9 * (eta + 1))), lt_min hδc (one_div_pos.mpr (mul_pos (by norm_num) heta1)), ?_⟩
  intro t ht
  rw [Set.mem_Ioc] at ht
  obtain ⟨ht0, htδ⟩ := ht
  have htδc : t ≤ δc := le_trans htδ (min_le_left _ _)
  have ht9' : t ≤ 1 / (9 * (eta + 1)) := le_trans htδ (min_le_right _ _)
  -- eta * t ≤ 1 / 9
  have h9 : eta * t ≤ 1 / 9 := by
    have step1 : eta * (1 / (9 * (eta + 1))) ≤ 1 / 9 := by
      rw [mul_one_div, div_le_iff₀ (mul_pos (by norm_num) heta1)]
      have e : (1 : Real) / 9 * (9 * (eta + 1)) = eta + 1 := by ring
      rw [e]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left ht9' heta) step1
  -- exp (-eta * t) ≥ 8 / 9
  have hexp : (8 : Real) / 9 ≤ Real.exp (-eta * t) := by
    have h1 : -(eta * t) + 1 ≤ Real.exp (-(eta * t)) := Real.add_one_le_exp _
    rw [← neg_mul] at h1
    linarith
  -- the shifted chunk is a closed interval, hence measurable
  set S : Set Real := {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} with hSdef
  have hSeq : S = Set.Icc (d * t + a) (d * t + b) := by
    ext z
    simp only [hSdef, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      constructor <;> linarith
    · rintro ⟨hz1, hz2⟩
      exact ⟨z - d * t, ⟨by linarith, by linarith⟩, by ring⟩
  have hS : MeasurableSet S := by
    rw [hSeq]
    exact measurableSet_Icc
  -- the two events, in the two independent σ-algebras
  set A : Set Omega := {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega} with hAdef
  set B : Set Omega := {omega : Omega | Y (Real.toNNReal t) omega ∈ S} with hBdef
  have hA : MeasurableSet[MeasurableSpace.comap death inferInstance] A :=
    ⟨Set.Ioi (Real.toNNReal t : WithTop NNReal), measurableSet_Ioi, rfl⟩
  have hB : MeasurableSet[MeasurableSpace.comap (fun omega : Omega => fun t : NNReal => Y t omega)
      inferInstance] B :=
    ⟨{f : NNReal → Real | f (Real.toNNReal t) ∈ S}, measurable_pi_apply _ hS, rfl⟩
  have hfact : P (A ∩ B) = P A * P B :=
    (hindep.indepSet_of_measurableSet hA hB).measure_inter_eq_mul
  have hsurv_t : P A = ENNReal.ofReal (Real.exp (-eta * t)) := by
    have h := hsurv (Real.toNNReal t)
    rw [Real.coe_toNNReal t ht0.le] at h
    exact h
  have hcore_t : ENNReal.ofReal (3 * t / 4) * Pi (Set.Icc a b) ≤ P B :=
    hcore t ⟨ht0, htδc⟩
  have hset : {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
      Y (Real.toNNReal t) omega ∈ S} = A ∩ B := Set.setOf_and
  rw [hset, hfact, hsurv_t]
  calc ENNReal.ofReal (Real.exp (-eta * t)) * P B
      ≥ ENNReal.ofReal (8 / 9) * (ENNReal.ofReal (3 * t / 4) * Pi (Set.Icc a b)) :=
        mul_le_mul (ENNReal.ofReal_le_ofReal hexp) hcore_t zero_le zero_le
    _ = (ENNReal.ofReal (8 / 9) * ENNReal.ofReal (3 * t / 4)) * Pi (Set.Icc a b) :=
        (mul_assoc _ _ _).symm
    _ = ENNReal.ofReal (2 * t / 3) * Pi (Set.Icc a b) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 8 / 9)]
        congr 1
        ring
