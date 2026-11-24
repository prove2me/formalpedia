-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagSmallJumpMassLeTimeMeasureV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:16:39.902894+00:00
-- url     : https://prove2.me/submissions/5d150830-2971-4e25-8e80-f8c003014090
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_cadlagTruncatedJumpLeTimeAtomV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (hf : IsCadlag f) (m : Measure ℝ≥0)
    (T : ℝ≥0) (C : ℝ) (hm : m (Set.Ioc 0 T) < ⊤)
    (hinc : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ENNReal.ofReal (min (1 : ℝ) |f t - f s|) ≤
        m (Set.Ioc s t) + ENNReal.ofReal (C * ((t : ℝ) - (s : ℝ)))) :
    (∑' u : Set.Ioc (0 : ℝ≥0) T,
      ENNReal.ofReal (if |f u - Function.leftLim f u| ≤ (1 : ℝ)
        then |f u - Function.leftLim f u| else 0)) ≤ m (Set.Ioc 0 T) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  calc
    _ ≤ ∑ u ∈ S, m {u.val} := by
      apply Finset.sum_le_sum
      intro u _
      apply le_trans _ (Kyprianou.Ch02.cadlagTruncatedJumpLeTimeAtomV1
        f hf m T C hm hinc u)
      apply ENNReal.ofReal_le_ofReal
      split_ifs with h
      · simp [min_eq_right h]
      · exact le_min (by norm_num) (abs_nonneg _)
    _ = m (⋃ u ∈ S, {u.val}) := by
      symm
      apply measure_biUnion_finset
      · intro i _ j _ hij
        exact Set.disjoint_singleton.mpr (fun h => hij (Subtype.ext h))
      · intro u _
        exact measurableSet_singleton _
    _ ≤ m (Ioc 0 T) := by
      apply measure_mono
      intro x hx
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
      obtain ⟨u, _, rfl⟩ := hx
      exact u.property
