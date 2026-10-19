-- Prove2me | solution 1 for ModernOnlineLearning.OGD.theorem_2_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:03:00.897975+00:00
-- url     : https://prove2.me/submissions/4a15f88d-10b6-4a5c-a90e-796c051c1181

import Mathlib

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hconv : Convex ℝ V)
    (f : E → ℝ) (xstar : E) (hx : xstar ∈ V)
    (hopen : ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ ConvexOn ℝ U f ∧ DifferentiableOn ℝ f U) :
    (∀ y ∈ V, f xstar ≤ f y) ↔
      ∀ y ∈ V, 0 ≤ inner ℝ (gradient f xstar) (y - xstar) := by
  obtain ⟨U, hU, hVU, hfc, hfd⟩ := hopen
  have hdiff : DifferentiableAt ℝ f xstar := hfd.differentiableAt (hU.mem_nhds (hVU hx))
  have hinner : ∀ v, inner ℝ (gradient f xstar) v = fderiv ℝ f xstar v := by
    intro v
    unfold gradient
    exact InnerProductSpace.toDual_symm_apply
  constructor
  · intro h y hy
    rw [hinner]
    have hmin : IsLocalMinOn f V xstar :=
      Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => h z hz)
    have hseg : segment ℝ xstar (xstar + (y - xstar)) ⊆ V := by
      have : xstar + (y - xstar) = y := by abel
      rw [this]
      exact hconv.segment_subset hx hy
    exact hmin.hasFDerivWithinAt_nonneg hdiff.hasFDerivAt.hasFDerivWithinAt
      (mem_posTangentConeAt_of_segment_subset hseg)
  · intro h y hy
    have h0 := h y hy
    rw [hinner] at h0
    set v := y - xstar with hv
    have hd : HasDerivAt (fun t : ℝ => f (xstar + t • v)) (fderiv ℝ f xstar v) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => xstar + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add xstar
      have h2 : HasFDerivAt f (fderiv ℝ f xstar) (xstar + (0:ℝ) • v) := by
        simpa using hdiff.hasFDerivAt
      exact h2.comp_hasDerivAt (0:ℝ) h1
    have ht := hd.tendsto_slope_zero_right
    have hle : fderiv ℝ f xstar v ≤ f y - f xstar := by
      refine le_of_tendsto ht ?_
      have : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT one_pos
      filter_upwards [this] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      have hc := hfc.2 (hVU hx) (hVU hy) (sub_nonneg.2 ht1.le) ht0.le (by ring)
      have he : (1 - t) • xstar + t • y = xstar + t • v := by
        rw [hv, smul_sub, sub_smul, one_smul]; abel
      rw [he] at hc
      simp only [smul_eq_mul] at hc
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
      rw [inv_mul_le_iff₀ ht0]
      nlinarith [hc]
    linarith
