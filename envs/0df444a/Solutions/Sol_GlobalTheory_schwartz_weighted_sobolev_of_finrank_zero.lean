-- Prove2me | solution 1 for GlobalTheory.schwartz_weighted_sobolev_of_finrank_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:46.219659+00:00
-- url     : https://prove2.me/submissions/5f0d1401-9dbd-4a19-b6cc-0e68d7f71cf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzWeightedSobolevOfFinrankZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure], finrank ℝ E = 0 → ∀ (k n : ℕ), ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap E ℂ) (x : E), ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C * Real.sqrt (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ) := by
  intro E _ _ _ _ _ μ _ hE k n
  haveI : Subsingleton E := Module.finrank_zero_iff.mp hE
  have hcpt : IsCompact (univ : Set E) := (Set.subsingleton_univ).isCompact
  have hfin : μ univ ≠ ∞ := hcpt.measure_lt_top.ne
  have hne : μ univ ≠ 0 := isOpen_univ.measure_ne_zero μ univ_nonempty
  set m : ℝ := μ.real univ with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hne hfin
  refine ⟨n, Real.sqrt m⁻¹, Real.sqrt_nonneg _, fun f x => ?_⟩
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  set a : ℝ := ‖iteratedFDeriv ℝ n f (0 : E)‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have h1 : ‖(0 : E)‖ ^ k * a ≤ a := by
    apply mul_le_of_le_one_left ha0
    rw [norm_zero]
    exact pow_le_one₀ le_rfl zero_le_one
  refine h1.trans ?_
  have hterm : ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2 ∂μ = m * a ^ 2 := by
    have : (fun z : E => (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n f z‖) ^ 2) = fun _ => a ^ 2 := by
      funext z
      rw [Subsingleton.elim z 0, pow_zero, one_mul]
    rw [this, integral_const, smul_eq_mul]
  have hnn : ∀ i j : ℕ, 0 ≤ ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ :=
    fun i j => integral_nonneg fun z => sq_nonneg _
  have hle : m * a ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ := by
    rw [← hterm]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i => ∑ j ∈ Finset.range (n + 1),
        ∫ z, (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun i _ => Finset.sum_nonneg fun j _ => hnn i j)
      (Finset.mem_range.mpr (Nat.succ_pos n)))
    exact Finset.single_le_sum
      (f := fun j => ∫ z, (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ j f z‖) ^ 2 ∂μ)
      (fun j _ => hnn 0 j) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  rw [← Real.sqrt_mul (inv_nonneg.mpr hmpos.le)]
  apply Real.le_sqrt_of_sq_le
  calc a ^ 2 = m⁻¹ * (m * a ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hmpos.le)
end GlobalTheory
