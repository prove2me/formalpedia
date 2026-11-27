-- Prove2me | solution 1 for Kyprianou.Ch05.subordinatorMeanLinearV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:24:09.665682+00:00
-- url     : https://prove2.me/submissions/5a99d794-7682-4c5d-8fac-2912beb4fbdd

import Theorems.Thm_Kyprianou_Ch05_monotoneAdditiveNNRealLinear
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_identDistrib_increment
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Stationary increments and monotone paths give integrability at all times and a monotone additive mean. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P) :
    ∀ t : NNReal, Integrable (Y t) P ∧
      (∫ w, Y t w ∂P) = (t : Real) * (∫ w, Y 1 w ∂P) := by
  have hm (t : NNReal) := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hY.1 t
  have hnonneg (t : NNReal) : 0 ≤ᵐ[P] Y t := by
    filter_upwards [hY.2] with w hw
    have h := hw (show (0 : NNReal) ≤ t from bot_le)
    simpa [hY.1.start_zero] using h
  have hinc (s t : NNReal) : IdentDistrib (fun w => Y (s+t) w - Y s w) (Y t) P P := by
    have h := hY.1.identDistrib_increment s t
    have he : ProbabilityTheory.increment Y 0 t = Y t := by
      funext w
      simp [ProbabilityTheory.increment, hY.1.start_zero]
    rw [he] at h
    exact h
  have hsum (s t : NNReal) (hs : Integrable (Y s) P)
      (ht : Integrable (Y t) P) : Integrable (Y (s+t)) P := by
    have hj := (hinc s t).integrable_iff.mpr ht
    have he : (fun w => Y s w + (Y (s+t) w - Y s w)) = Y (s+t) := by
      funext w
      ring
    simpa only [Pi.add_def, he] using hs.add hj
  have hn (n : Nat) : Integrable (Y (n : NNReal)) P := by
    induction n with
    | zero => simp [hY.1.start_zero]
    | succ n ih =>
      simpa [Nat.cast_succ] using hsum (n : NNReal) 1 ih hFiniteMean
  have hi (t : NNReal) : Integrable (Y t) P := by
    obtain ⟨n, hnge⟩ := exists_nat_ge t
    refine (hn n).mono (hm t).aestronglyMeasurable ?_
    filter_upwards [hY.2, hnonneg t, hnonneg (n : NNReal)] with w hw h0 h1
    simpa [Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg h1] using hw hnge
  have hadd (s t : NNReal) :
      (∫ w, Y (s+t) w ∂P) = (∫ w, Y s w ∂P) + ∫ w, Y t w ∂P := by
    have hj := (hinc s t).integrable_iff.mpr (hi t)
    rw [← (hinc s t).integral_eq, ← integral_add (hi s) hj]
    congr 1
    funext w
    simp
  have hmono : Monotone (fun t : NNReal => ∫ w, Y t w ∂P) := by
    intro s t hst
    apply integral_mono_ae (hi s) (hi t)
    filter_upwards [hY.2] with w hw using hw hst
  exact fun t => ⟨hi t, monotoneAdditiveNNRealLinear _ hadd hmono t⟩
