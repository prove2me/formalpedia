-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_independent_centered_prefix_maximal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:11:11.733656+00:00
-- url     : https://prove2.me/submissions/bb6b7808-eae3-4b2b-b801-fbf1869c0775

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_bounded_nonnegative_variance
import Theorems.Thm_Kyprianou_Ch04_ito43_measurable_centered_prefix_maximal
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (C μ : ℝ) (hC : 0 ≤ C)
    (hm : ∀ k, AEMeasurable (F k) P) (hi : iIndepFun F P)
    (hb : ∀ k, ∀ᵐ w ∂P, 0 ≤ F k w ∧ F k w ≤ C)
    (hmean : ∀ k, (∫ w, F k w ∂P) = μ)
    (n : ℕ) (e : ℝ) (he : 0 < e) :
    (P {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, (F k w-μ)|}).toReal
      ≤ (n:ℝ)*C*μ/e^2 := by
  let G : ℕ → Ω → ℝ := fun k => (hm k).mk (F k)
  let Y : ℕ → Ω → ℝ := fun k w => G k w-μ
  have hG (k : ℕ) : Measurable (G k) := (hm k).measurable_mk
  have hFG (k : ℕ) : F k =ᵐ[P] G k := (hm k).ae_eq_mk
  have hGi : iIndepFun G P := iIndepFun.congr hFG hi
  have hYi : iIndepFun Y P := hGi.comp (fun _ x => x-μ)
    (fun _ => measurable_id.sub measurable_const)
  have hY (k : ℕ) : Measurable (Y k) := (hG k).sub_const μ
  have hbG (k : ℕ) : ∀ᵐ w ∂P, 0 ≤ G k w ∧ G k w ≤ C := by
    filter_upwards [hb k,hFG k] with w hw h
    simpa only [← h] using hw
  have hmg (k : ℕ) : (∫ w,G k w ∂P) = μ :=
    (integral_congr_ae (hFG k).symm).trans (hmean k)
  have hbound (k : ℕ) := Kyprianou.Ch04.ito43_bounded_nonnegative_variance P (G k) C hC
    (hG k).aemeasurable (hbG k)
  have hL (k : ℕ) : MemLp (Y k) 2 P := (hbound k).1.sub (memLp_const μ)
  have hzero (k : ℕ) : (∫ w,Y k w ∂P) = 0 := by
    change (∫ w,G k w-μ ∂P) = 0
    rw [integral_sub ((hbound k).1.integrable one_le_two) (integrable_const μ),hmg]
    simp
  have hv (k : ℕ) : variance (Y k) P ≤ C*μ := by
    rw [show variance (Y k) P = variance (G k) P from variance_sub_const (hG k).aestronglyMeasurable μ]
    simpa only [hmg] using (hbound k).2
  have hEq : (∀ᵐ w ∂P, ∀ k, F k w = G k w) := ae_all_iff.mpr hFG
  have hEvent : {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, (F k w-μ)|} =ᵐ[P]
      {w | ∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, Y k w|} := by
    filter_upwards [hEq] with w hw
    change (∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, (F k w-μ)|) =
      (∃ j ≤ n, e ≤ |∑ k ∈ Finset.range j, (G k w-μ)|)
    simp_rw [hw]
  rw [measure_congr hEvent]
  simpa only [mul_assoc] using Kyprianou.Ch04.ito43_measurable_centered_prefix_maximal P Y
    hY hYi hL hzero (C*μ) hv n e he
