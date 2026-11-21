-- Prove2me | solution 2 for MasulloGRH.nuclear_bounded_precompact
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:03:28.045881+00:00
-- url     : https://prove2.me/submissions/8ceca30e-547a-43a5-a26e-a0b1262dec88

import Theorems.Thm_MasulloGRH_nuclear_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH Filter Set Topology Metric
open scoped Pointwise

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsNuclear E) (B : Set E) (hB : Bornology.IsVonNBounded ℂ B) :
    ∀ V ∈ 𝓝 (0 : E), ∃ t : Finset E, B ⊆ ⋃ x ∈ t, {y : E | y - x ∈ V} := by
  classical
  obtain ⟨ι, _, P, hP⟩ := hE.1.1
  let : IsTopologicalAddGroup E := hP.topologicalAddGroup
  let : ContinuousSMul ℂ E := hP.continuousSMul
  let : PolynormableSpace ℂ E := hP.toPolynormableSpace
  intro V hV
  obtain ⟨⟨J, r⟩, hr, hball⟩ := hP.hasBasis_zero_ball.mem_iff.mp hV
  let p := J.sup P
  have hp : Continuous p := Seminorm.continuous
    (hP.hasBasis_zero_ball.mem_of_mem (i := (J, r)) hr)
  obtain ⟨q, f, c, hq, hc_nonneg, hc, hf, hdom⟩ :=
    nuclear_quasinuclear_domination E hE p hp
  obtain ⟨M, hM, hMq⟩ :=
    ((PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bounded.mp hB) ⟨q, hq⟩
  let term (n : ℕ) (z : E) := c n * ‖f n z‖
  -- The seminorm bound gives uniform convergence on all differences of points of B.
  have huniform : TendstoUniformlyOn (fun I : Finset ℕ => fun z => ∑ n ∈ I, term n z)
      (fun z => ∑' n, term n z) atTop (B - B) := by
    apply tendstoUniformlyOn_tsum (hc.mul_right (2 * M))
    intro n z hz
    obtain ⟨y, hy, x, hx, rfl⟩ := mem_sub.mp hz
    have hqx : q (y - x) ≤ 2 * M := calc
      q (y - x) ≤ q y + q x := map_sub_le_add q y x
      _ ≤ 2 * M := by linarith only [hMq y hy, hMq x hx]
    rw [Real.norm_of_nonneg (mul_nonneg (hc_nonneg n) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left ((hf _ _).trans hqx) (hc_nonneg n)
  obtain ⟨I, hI⟩ := ((Metric.tendstoUniformlyOn_iff.mp huniform) (r / 2) (half_pos hr)).exists
  let C := ∑' n, c n
  have hC : 0 ≤ C := tsum_nonneg hc_nonneg
  let η := (r / 2) / (C + 1)
  have hCpos : 0 < C + 1 := by linarith
  have hη : 0 < η := div_pos (half_pos hr) hCpos
  have hhead : C * η < r / 2 := by
    have heq : η * (C + 1) = r / 2 := div_mul_cancel₀ _ hCpos.ne'
    nlinarith only [heq, hη]
  -- The retained coordinates form a bounded set in a finite product of copies of ℂ.
  let evaluate (z : E) : I → ℂ := fun n => f n.val z
  have hbounded : evaluate '' B ⊆ closedBall 0 M := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hM.le).mpr fun n => (hf _ _).trans (hMq x hx).le
  have htotal : TotallyBounded (evaluate '' B) := (isCompact_closedBall _ _).totallyBounded.subset hbounded
  obtain ⟨S, hS, hfinite, hcover⟩ := finite_approx_of_totallyBounded htotal η hη
  have hreps (s : S) : ∃ x ∈ B, evaluate x = s.val := hS s.property
  choose rep hrepB hrep using hreps
  let : Finite S := hfinite.to_subtype
  refine ⟨(finite_range rep).toFinset, fun y hy => ?_⟩
  obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem evaluate hy))
  let x := rep ⟨s, hs⟩
  have hx : x ∈ B := hrepB ⟨s, hs⟩
  have heval : ‖evaluate y - evaluate x‖ < η := by
    rw [← dist_eq_norm, hrep ⟨s, hs⟩]
    exact hys
  have hcoords (n : ℕ) (hn : n ∈ I) : ‖f n (y - x)‖ ≤ η := by
    have h := (norm_le_pi_norm (evaluate y - evaluate x) ⟨n, hn⟩).trans heval.le
    simpa only [evaluate, Pi.sub_apply, map_sub] using h
  have hsum : (∑ n ∈ I, term n (y - x)) ≤ C * η := calc
    (∑ n ∈ I, term n (y - x)) ≤ (∑ n ∈ I, c n) * η := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hcoords n hn) (hc_nonneg n)
    _ ≤ C * η := mul_le_mul_of_nonneg_right (hc.sum_le_tsum I (fun n _ => hc_nonneg n)) hη.le
  have htail := hI (y - x) (mem_sub.mpr ⟨y, hy, x, hx, rfl⟩)
  rw [Real.dist_eq] at htail
  have hbound : p (y - x) ≤ ∑' n, term n (y - x) := hdom (y - x)
  have hsmall : p (y - x) < r := by
    linarith only [hbound, hsum, hhead, (abs_lt.mp htail).2]
  exact mem_iUnion₂.mpr ⟨x, (finite_range rep).mem_toFinset.mpr ⟨⟨s, hs⟩, rfl⟩,
    hball ((Seminorm.ball_zero_eq p).symm ▸ hsmall)⟩
