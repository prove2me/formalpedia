-- Prove2me | solution 1 for GlobalTheory.PrimeMeanValue.prime_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:35:10.803403+00:00
-- url     : https://prove2.me/submissions/033334b6-6b39-43d7-8c9f-cebeb2006e32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe
import Theorems.Thm_GlobalTheory_PrimeMeanValue_sum_integral_le
import Theorems.Thm_GlobalTheory_PrimeMeanValue_kernel_integral
import Theorems.Thm_GlobalTheory_PrimeMeanValue_mem_primesIoc
import Theorems.Thm_GlobalTheory_PrimeMeanValue_window
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_GlobalTheory_GallagherLemma_gallagher
import Theorems.Thm_GlobalTheory_T_brunTitchmarsh_exists_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.PrimeMeanValue
namespace GlobalTheory.PrimeMeanValue
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T N y : ℝ) (a : ℕ → ℂ), 1 ≤ T →
    (2 * q * T) ^ 2 ≤ N → ∑ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T,
      ‖∑ p ∈ primesIoc N y, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * ∑ p ∈ primesIoc N y, (p : ℝ) * ‖a p‖ ^ 2 / Real.log p := by
  obtain ⟨C, hC, hG⟩ := GlobalTheory.GallagherLemma.gallagher
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.brunTitchmarsh_exists_const
  refine ⟨C * (4 * B), by positivity, fun q _ T N y a hT hN => ?_⟩
  have hT0 : 0 < T := by linarith
  have hδ : 0 ≤ 1 / T := by positivity
  have hN0 : 0 ≤ N := (sq_nonneg _).trans hN
  set P := primesIoc N y with hP
  have hmem : ∀ p ∈ P, N < p ∧ (p : ℝ) ≤ y ∧ p.Prime := fun p hp => (mem_primesIoc hN0).1 hp
  have hsub : P ⊆ Finset.Icc 1 ⌊y⌋₊ := fun p hp =>
    Finset.mem_Icc.2 ⟨(hmem p hp).2.2.one_le, Nat.le_floor (hmem p hp).2.1⟩
  have hgal : ∀ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T,
      ‖∑ p ∈ P, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)‖ ^ 2 / x := by
    intro χ
    have h := hG ⌊y⌋₊ (fun n => if n ∈ P then a n * χ (n : ZMod q) else 0) T hT
    have r1 : ∀ t : ℝ, ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n ∈ P then a n * χ (n : ZMod q) else 0) *
        (n : ℂ) ^ (-(t * I)) = ∑ p ∈ P, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I)) := by
      intro t
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    have r2 : ∀ x : ℝ, ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
        (if n ∈ P then a n * χ (n : ZMod q) else 0) = ∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q) := by
      intro x
      rw [Finset.sum_ite_mem, Finset.filter_inter, Finset.inter_eq_right.2 hsub]
    simp_rw [r1, r2] at h
    exact h
  refine (Finset.sum_le_sum fun χ _ => hgal χ).trans ?_
  rw [← Finset.mul_sum]
  set w : ℕ → ℝ := fun n => 4 * B * n / (T * Real.log n) * ‖a n‖ ^ 2 with hw
  have hk : ∀ n ∈ P, (0 : ℝ) < n := fun n hn => by exact_mod_cast (hmem n hn).2.2.pos
  have hint : ∀ n ∈ P, Integrable (fun x : ℝ => w n *
      (if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0))
      (volume.restrict (Set.Ioi 0)) := fun n hn =>
    (kernel_integral n (1 / T) (hk n hn) hδ).1.const_mul _
  have key := sum_integral_le (Finset.univ : Finset (DirichletCharacter ℂ q))
    (volume.restrict (Set.Ioi 0))
    (fun χ x => ‖∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)‖ ^ 2 / x)
    (fun x => ∑ n ∈ P, w n *
      (if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0))
    (fun p => by
      refine Measurable.aestronglyMeasurable ?_
      simp_rw [Finset.sum_filter]
      refine Measurable.div (Measurable.pow_const (Measurable.norm ?_) 2) measurable_id
      refine Finset.measurable_sum _ fun n _ => Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_lt measurable_id measurable_const).inter
        (measurableSet_le measurable_const (measurable_id.mul_const _)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx p
      have hx' : 0 < x := hx
      positivity)
    (integrable_finsetSum _ hint)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : 0 < x := hx
      have hwin := window B hB0 hB q T N x a (P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T))) hT hN hx' (fun n hn => by
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hn
          exact ⟨(hmem n h1).2.2, (hmem n h1).1, h2.1, h2.2⟩)
      rw [← Finset.sum_div]
      refine (div_le_div_of_nonneg_right hwin hx'.le).trans (le_of_eq ?_)
      rw [Finset.sum_filter, Finset.sum_div]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs
      · rw [mul_one_div]
      · simp)
  refine (mul_le_mul_of_nonneg_left key (by positivity)).trans ?_
  rw [integral_finsetSum _ hint, mul_assoc, mul_assoc, Finset.mul_sum, Finset.mul_sum _ _ (4 * B)]
  refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl fun n hn => ?_)) hC.le
  rw [integral_const_mul, (kernel_integral n (1 / T) (hk n hn) hδ).2]
  simp only [hw]
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (hmem n hn).2.2.one_lt)
  field_simp
end GlobalTheory.PrimeMeanValue
