-- Prove2me | solution 1 for NoisyPrototyping.ReservationPolicy.footnote_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:19:38.773841+00:00
-- url     : https://prove2.me/submissions/c6fc8ec8-821c-4d41-883a-8752f61fc296

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model

open MeasureTheory Filter Topology

open NoisyPrototyping.ReservationPolicy in
theorem solution (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : Integrable (fun x : ℝ => x) G) (w : ℝ) (hw : 0 < w) :
    (∀ r : ℝ, (∫ x, max r x ∂G) - r = ∫ x, max (x - r) 0 ∂G) ∧
    Antitone (fun r : ℝ => ∫ x, max (x - r) 0 ∂G) ∧
    Set.Ioi (0 : ℝ) ⊆ Set.range (fun r : ℝ => ∫ x, max (x - r) 0 ∂G) ∧
    ∃ R : ℝ, IsLeast {r : ℝ | ∫ x, max (x - r) 0 ∂G = w} R := by
  set φ : ℝ → ℝ := fun r => ∫ x, max (x - r) 0 ∂G with hφ
  have hint : ∀ r : ℝ, Integrable (fun x : ℝ => max (x - r) 0) G := by
    intro r
    refine Integrable.mono' (hG.abs.add (integrable_const |r|)) ?_ ?_
    · exact ((measurable_id.sub_const r).max measurable_const).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have h1 := abs_sub x r
      have h2 : max (x - r) 0 ≤ |x - r| := max_le (le_abs_self _) (abs_nonneg _)
      simp only [Pi.add_apply]
      linarith
  have hconst : ∀ c : ℝ, ∫ _x, c ∂G = c := by
    intro c
    simp
  have hlow : ∀ r, (∫ x, x ∂G) - r ≤ φ r := by
    intro r
    have hsub : Integrable (fun x : ℝ => x - r) G := hG.sub (integrable_const r)
    have h := integral_mono hsub (hint r) (fun x => le_max_left (x - r) 0)
    rw [integral_sub hG (integrable_const r), hconst] at h
    exact h
  have hlip : ∀ r s, φ r ≤ φ s + |r - s| := by
    intro r s
    have hadd : Integrable (fun x : ℝ => max (x - s) 0 + |r - s|) G :=
      (hint s).add (integrable_const |r - s|)
    have h := integral_mono (hint r) hadd (fun x => by
      show max (x - r) 0 ≤ max (x - s) 0 + |r - s|
      have := abs_max_sub_max_le_max (x - r) 0 (x - s) 0
      rw [show x - r - (x - s) = s - r by ring, sub_self, abs_zero, abs_sub_comm s r] at this
      have h3 := le_abs_self (max (x - r) 0 - max (x - s) 0)
      have h4 : max |r - s| 0 = |r - s| := max_eq_left (abs_nonneg _)
      linarith)
    rw [integral_add (hint s) (integrable_const _), hconst] at h
    exact h
  have hcont : Continuous φ := by
    apply LipschitzWith.continuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro r s
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
    constructor
    · have := hlip s r; rw [abs_sub_comm] at this; linarith
    · have := hlip r s; linarith
  have hanti : Antitone φ := by
    intro r s hrs
    apply integral_mono (hint s) (hint r)
    intro x
    exact max_le_max (by linarith) le_rfl
  have hlim : Tendsto φ atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := G) (l := atTop)
      (F := fun r x => max (x - r) 0) (f := fun _ => (0 : ℝ)) (fun x => max (x - 0) 0)
      (Eventually.of_forall (fun r => (hint r).aestronglyMeasurable))
      (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le_max (by linarith) le_rfl)
      (hint 0)
      (by
        filter_upwards with x
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop x] with r hr
        rw [max_eq_right (by linarith)])
    simpa using this
  have hrange : Set.Ioi (0 : ℝ) ⊆ Set.range φ := by
    intro y hy
    obtain ⟨r2, hr2⟩ := ((tendsto_order.1 hlim).2 y hy).exists
    set r1 := (∫ x, x ∂G) - y with hr1
    have h1 : y ≤ φ r1 := by have := hlow r1; rw [hr1] at this; linarith
    have hle : r1 ≤ r2 := by
      by_contra hc
      push_neg at hc
      have := hanti hc.le
      linarith
    have := intermediate_value_Icc' hle hcont.continuousOn ⟨hr2.le, h1⟩
    obtain ⟨r, _, hr⟩ := this
    exact ⟨r, hr⟩
  refine ⟨?_, hanti, hrange, ?_⟩
  · intro r
    have e : (fun x : ℝ => max r x) = fun x => max (x - r) 0 + r := by
      funext x
      rcases le_total r x with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    rw [e, integral_add (hint r) (integrable_const r), hconst]
    ring
  · obtain ⟨r0, hr0⟩ := hrange (Set.mem_Ioi.mpr hw)
    set A := {r : ℝ | ∫ x, max (x - r) 0 ∂G = w} with hA
    have hAeq : A = φ ⁻¹' {w} := rfl
    have hclosed : IsClosed A := by rw [hAeq]; exact isClosed_singleton.preimage hcont
    have hne : A.Nonempty := ⟨r0, hr0⟩
    have hbdd : BddBelow A := by
      refine ⟨(∫ x, x ∂G) - w, fun r hr => ?_⟩
      have := hlow r
      have hr' : φ r = w := hr
      linarith
    exact ⟨sInf A, hclosed.csInf_mem hne hbdd, fun r hr => csInf_le hbdd hr⟩
