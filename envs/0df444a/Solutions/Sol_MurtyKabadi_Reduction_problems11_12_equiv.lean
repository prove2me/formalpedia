-- Prove2me | solution 1 for MurtyKabadi.Reduction.problems11_12_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:28:06.054759+00:00
-- url     : https://prove2.me/submissions/46d07099-bdee-4158-994a-e2ab70b127ef

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

open MurtyKabadi.Reduction

/-- The range of `h` is exactly the image of `Q` over the nonnegative orthant, since
`x ≥ 0` iff `x = (u₁², …, u_n²)` for some `u`. -/
private theorem range_h {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) :
    Set.range (h D) = Q D '' {x : ι → ℝ | 0 ≤ x} := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨fun i => u i ^ 2, fun i => sq_nonneg (u i), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun i => Real.sqrt (x i), ?_⟩
    simp only [h]
    congr 1
    funext i
    exact Real.sq_sqrt (hx i)

private theorem norm_sq_le {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    ‖fun i => u i ^ 2‖ ≤ ‖u‖ ^ 2 := by
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.mpr ?_
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : |u i| ≤ ‖u‖ := by
    have := norm_le_pi_norm u i
    rwa [Real.norm_eq_abs] at this
  nlinarith [abs_nonneg (u i), sq_abs (u i)]

private theorem norm_sqrt_le {ι : Type*} [Fintype ι] {x : ι → ℝ} (hx : 0 ≤ x) :
    ‖fun i => Real.sqrt (x i)‖ ≤ Real.sqrt ‖x‖ := by
  refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr ?_
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have := norm_le_pi_norm x i
  rw [Real.norm_eq_abs, abs_of_nonneg (hx i)] at this
  exact this

theorem solution {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) :
    (Problem11 D ↔ Problem1 D) ∧ (Problem12 D ↔ Problem2 D) := by
  have hzero : h D 0 = Q D 0 := by
    simp only [h]
    congr 1
    funext i
    simp
  constructor
  · -- `0` is a local minimum of `h` iff it is a local minimum of `Q` on the orthant
    have hiff : IsLocalMin (h D) 0 ↔ IsLocalMinOn (Q D) {x : ι → ℝ | 0 ≤ x} 0 := by
      constructor
      · intro hmin
        obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hmin
        have hδ2 : 0 < δ ^ 2 := by positivity
        have hmem : {z : ι → ℝ | Q D 0 ≤ Q D z} ∈
            nhdsWithin (0 : ι → ℝ) {x : ι → ℝ | 0 ≤ x} := by
          refine Metric.mem_nhdsWithin_iff.mpr ⟨δ ^ 2, hδ2, ?_⟩
          rintro z ⟨hzball, hznn⟩
          simp only [Metric.mem_ball, dist_zero_right] at hzball
          have hu : (fun i => Real.sqrt (z i)) ∈ Metric.ball (0 : ι → ℝ) δ := by
            simp only [Metric.mem_ball, dist_zero_right]
            refine lt_of_le_of_lt (norm_sqrt_le hznn) ?_
            have : Real.sqrt ‖z‖ < Real.sqrt (δ ^ 2) := by
              refine Real.sqrt_lt_sqrt (norm_nonneg z) hzball
            rwa [Real.sqrt_sq hδ.le] at this
          have hval := hsub hu
          simp only [Set.mem_setOf_eq] at hval ⊢
          have hz : (fun i => Real.sqrt (z i) ^ 2) = z := by
            funext i
            exact Real.sq_sqrt (hznn i)
          rw [hzero] at hval
          simp only [h, hz] at hval
          exact hval
        exact hmem
      · intro hmin
        obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hmin
        refine Metric.mem_nhds_iff.mpr ⟨Real.sqrt ε, Real.sqrt_pos.mpr hε, ?_⟩
        intro u hu
        simp only [Metric.mem_ball, dist_zero_right] at hu
        have hmemb : (fun i => u i ^ 2) ∈
            Metric.ball (0 : ι → ℝ) ε ∩ {x : ι → ℝ | 0 ≤ x} := by
          refine ⟨?_, fun i => sq_nonneg (u i)⟩
          simp only [Metric.mem_ball, dist_zero_right]
          refine lt_of_le_of_lt (norm_sq_le u) ?_
          have h1 : ‖u‖ ^ 2 < Real.sqrt ε ^ 2 := by
            have := norm_nonneg u
            nlinarith [Real.sqrt_nonneg ε]
          rwa [Real.sq_sqrt hε.le] at h1
        have hval := hsub hmemb
        simp only [Set.mem_setOf_eq] at hval ⊢
        rw [hzero]
        exact hval
    exact not_congr hiff
  · rw [Problem12, Problem2, range_h]
