-- Prove2me | solution 1 for ManyServerQED.Scheduling.filtered_brownian_coordinate_finite_sample_maximal_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:15.626393+00:00
-- url     : https://prove2.me/submissions/6427e152-f693-44a6-9c23-15d92c48ed47

import Theorems.Thm_AvramDividend_Classical_finiteTimeSet_monotoneZeroBasedGrid
import Theorems.Thm_AvramDividend_Classical_avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
import Theorems.Thm_ManyServerQED_Scheduling_adapted_brownian_coordinate_at_monotone_times_is_martingale

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

set_option maxHeartbeats 1300000 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → Fin k → ℝ)
    (hW : IsStdFBrownian P F W) (i : Fin k)
    (T : ℝ≥0) (J : Finset ℝ≥0) (hJ : J.Nonempty) (hJT : ∀ t ∈ J, t ≤ T)
    (p : ℝ) (hp : 1 < p) :
    eLpNorm (fun ω => J.sup' hJ (fun t => ‖W t ω i‖)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (p/(p-1))*eLpNorm (fun ω => W T ω i) (ENNReal.ofReal p) P := by
  obtain ⟨n,a,e,ha,ha0,hE⟩ := AvramDividend.Classical.finiteTimeSet_monotoneZeroBasedGrid J
  let u (j : ℕ) := if j ≤ n then min (a j) T else T
  have hu : Monotone u := by
    intro j l hjl
    by_cases hl : l ≤ n
    · simp only [u,if_pos (hjl.trans hl),if_pos hl]
      exact min_le_min_right T (ha hjl)
    · simp only [u,if_neg hl]
      split
      · exact min_le_right _ _
      · exact le_rfl
  have huT : u (n+1) = T := by simp [u]
  let F' : Filtration ℕ mΩ :=
    ⟨fun j => F (u j),fun _ _ h => F.mono (hu h),fun j => F.le (u j)⟩
  let f (j : ℕ) (ω : Ω) := W (u j) ω i
  have hf : Martingale f F' P :=
    adapted_brownian_coordinate_at_monotone_times_is_martingale F W hW hu i
  have hDoob := AvramDividend.Classical.avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
    hf hp (n+1)
  let L (ω : Ω) := J.sup' hJ (fun t => ‖W t ω i‖)
  let H (ω : Ω) := (Finset.range (n+1+1)).sup' Finset.nonempty_range_add_one (fun j => ‖f j ω‖)
  have hNorm (ω : Ω) : ‖L ω‖ ≤ H ω := by
    have hPos : 0 ≤ L ω := by
      obtain ⟨t,ht⟩ := hJ
      exact (norm_nonneg (W t ω i)).trans (Finset.le_sup' (fun t => ‖W t ω i‖) ht)
    rw [Real.norm_of_nonneg hPos]
    apply Finset.sup'_le
    intro t ht
    let j := (e ⟨t,ht⟩).val+1
    have hj : j ≤ n := Nat.succ_le_of_lt (e ⟨t,ht⟩).2
    have hm : u j = t := by
      simp only [u,if_pos hj,j,hE ⟨t,ht⟩,min_eq_left (hJT t ht)]
    have hjR : j ∈ Finset.range (n+1+1) := Finset.mem_range.2 (by omega)
    have h := Finset.le_sup' (fun j => ‖f j ω‖) hjR
    simpa only [f,hm] using h
  refine (eLpNorm_mono_real hNorm).trans ?_
  simpa only [H,f,huT] using hDoob
