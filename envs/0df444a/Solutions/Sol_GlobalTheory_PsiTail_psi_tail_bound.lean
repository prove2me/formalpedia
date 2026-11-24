-- Prove2me | solution 1 for GlobalTheory.PsiTail.psi_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:20.261809+00:00
-- url     : https://prove2.me/submissions/fa681e0e-b400-4479-b907-6d03210a5b54

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2Integrality
import Theorems.Thm_GlobalTheory_PsiTail_one_le_log
import Theorems.Thm_GlobalTheory_PsiTail_error_terms
import Theorems.Thm_GlobalTheory_PsiTail_hasDerivAt_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.PsiTail
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory.PsiTail
theorem _root_.solution : PartialSumIntegralBound := by
  intro C₁ c₁ hC₁ hc₁
  obtain ⟨K, c, hK, hc, herr⟩ := error_terms c₁ hc₁
  refine ⟨C₁ * (128320401 + 5 * K), c, by positivity, hc, ?_⟩
  intro Q a hQ h1 h2 Z U hZ hZU
  have hQ0 : 0 < Q := by linarith
  have hL := one_le_log hQ
  set E := K * Q ^ (-c) with hE
  have hE0 : 0 < E := by rw [hE]; positivity
  have hpt : ∀ u : ℝ, 2 ≤ u →
      ‖psum a u‖ / u ≤ C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    rw [div_le_iff₀ hu0]
    rcases le_total u (Real.exp (Real.log Q ^ 2)) with h | h
    · have e := (herr Q u hQ hu).1 h
      have e1 : u ^ (1 - (1 : ℝ) / 400) = u ^ (-(1 : ℝ) / 400) * u := by
        rw [← Real.rpow_add_one hu0.ne']; congr 1; ring
      calc ‖psum a u‖ ≤ _ := h1 u hu
        _ = C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + Real.log (u * Q) ^ 2 / Q) * u := by
          rw [e1]; ring
        _ ≤ _ := by gcongr
    · have e := (herr Q u hQ hu).2 h
      have e1 : 0 ≤ u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 := by positivity
      calc ‖psum a u‖ ≤ _ := h2 u h
        _ = C₁ * Real.exp (-c₁ * Real.sqrt (Real.log u)) * u := by ring
        _ ≤ _ := by gcongr; linarith
  set g : ℝ → ℝ := fun u =>
    C₁ * ((u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u) with hg
  have hpt2 : ∀ u ∈ Set.Icc Z U, ‖psum a u‖ / u ^ 2 ≤ g u := by
    intro u hu
    have hu2 : 2 ≤ u := hZ.trans hu.1
    have hu0 : 0 < u := by linarith
    calc ‖psum a u‖ / u ^ 2 = ‖psum a u‖ / u / u := by field_simp
      _ ≤ C₁ * (u ^ (-(1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + E / Real.log u ^ 2) / u := by
        gcongr; exact hpt u hu2
      _ = g u := by rw [hg]; ring
  have hgc : ContinuousOn g (Set.Icc Z U) := by
    intro u hu
    have hu2 : 2 ≤ u := hZ.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlu : Real.log u ^ 2 ≠ 0 := (pow_pos (Real.log_pos (by linarith)) 2).ne'
    have huQ : u * Q ≠ 0 := mul_ne_zero hu0 hQ0.ne'
    apply ContinuousAt.continuousWithinAt
    rw [hg]
    fun_prop (disch := first | assumption | exact Or.inl hu0)
  have hgi : IntervalIntegrable g volume Z U := hgc.intervalIntegrable_of_Icc hZU
  have hmeas : Measurable (fun u : ℝ => ‖psum a u‖ / u ^ 2) := by
    have : Measurable (fun u : ℝ => ‖psum a u‖) :=
      (measurable_from_top (f := fun N : ℕ => ‖∑ n ∈ Icc 1 N, a n‖)).comp Nat.measurable_floor
    exact this.div (measurable_id.pow_const 2)
  have hfi : IntervalIntegrable (fun u : ℝ => ‖psum a u‖ / u ^ 2) volume Z U := by
    refine hgi.mono_fun' hmeas.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hZU]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt2 u (Set.Ioc_subset_Icc_self hu)
  have hint := intervalIntegral.integral_mono_on hZU hfi hgi hpt2
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt (f' := g)
    (f := fun t : ℝ => C₁ * -(t ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (t * Q) ^ 2 + 320000 * Real.log (t * Q) + 128000000) + E / Real.log t))
    (a := Z) (b := U) (fun u hu => by
      rw [Set.uIcc_of_le hZU] at hu
      exact (hasDerivAt_prim Q E u hQ0 (by linarith [hu.1])).const_mul C₁) hgi
  have hZ0 : 0 < Z := by linarith
  have hU0 : 0 < U := by linarith
  have hlU : 0 < Real.log U := Real.log_pos (by linarith)
  have hlUQ : 0 < Real.log (U * Q) := Real.log_pos (by nlinarith)
  have hlZ : 2 / 3 ≤ Real.log Z := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hZ
    linarith
  have hlZQ : 1 ≤ Real.log (Z * Q) := by rw [Real.log_mul hZ0.ne' hQ0.ne']; linarith
  have hUnn : 0 ≤ C₁ * (U ^ (-(1 : ℝ) / 400) *
        (400 * Real.log (U * Q) ^ 2 + 320000 * Real.log (U * Q) + 128000000) + E / Real.log U) := by
    positivity
  have hZpt := hpt Z hZ
  set w := Z ^ (-(1 : ℝ) / 400) with hw
  have hw0 : 0 < w := by rw [hw]; positivity
  set l := Real.log (Z * Q) with hl
  have b1 : 400 * l ^ 2 + 320000 * l + 128000000 ≤ 128320400 * l ^ 2 := by nlinarith
  have b2 : E / Real.log Z ≤ 2 * E := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have b3 : E / Real.log Z ^ 2 ≤ 3 * E := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ 3 * Real.log Z ^ 2 := by nlinarith
    nlinarith
  have hq : 0 < Q ^ (-c) := by positivity
  have hwl : 0 < w * l ^ 2 := by positivity
  calc ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2)
      ≤ C₁ * (w * l ^ 2 + E / Real.log Z ^ 2) +
        C₁ * (w * (400 * l ^ 2 + 320000 * l + 128000000) + E / Real.log Z) := by
        refine add_le_add hZpt (hint.trans ?_)
        rw [hval]
        linarith
    _ ≤ C₁ * (w * l ^ 2 + 3 * E) + C₁ * (w * (128320400 * l ^ 2) + 2 * E) := by gcongr
    _ = C₁ * (128320401 * (w * l ^ 2) + 5 * K * Q ^ (-c)) := by rw [hE]; ring
    _ ≤ C₁ * ((128320401 + 5 * K) * (w * l ^ 2 + Q ^ (-c))) := by
        gcongr
        nlinarith [mul_pos hK hwl]
    _ = _ := by ring
end GlobalTheory.PsiTail
