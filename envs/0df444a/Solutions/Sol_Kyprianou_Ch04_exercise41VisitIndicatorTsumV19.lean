-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41VisitIndicatorTsumV19
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:20:52.341407+00:00
-- url     : https://prove2.me/submissions/55f1d8c9-9086-4b4a-b12d-6a34e43b2fae

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (t : NNReal)
    (hv : Set.Finite {s : NNReal | 0 < s ∧ s ≤ t ∧ x s = 0})
    (p : NNReal → Prop) [DecidablePred p]
    (hp : ∀ s, 0 < s → p s → x s = 0) :
    Set.Finite (Function.support (fun s : Ioc (0 : NNReal) t => if p s then (1 : ℝ) else 0)) ∧
    (∑' s : Ioc (0 : NNReal) t, (if p s then (1 : ℝ) else 0)) =
      ∑ s ∈ hv.toFinset, (if p s then (1 : ℝ) else 0) := by
  classical
  refine ⟨?_,?_⟩
  · apply (Set.Finite.preimage Subtype.val_injective.injOn hv).subset
    intro s hs
    have hps : p s := by simpa [Function.mem_support] using hs
    exact ⟨s.2.1,s.2.2,hp s s.2.1 hps⟩
  · rw [tsum_subtype (Ioc (0 : NNReal) t) (fun s => if p s then (1 : ℝ) else 0)]
    rw [tsum_eq_sum (s := hv.toFinset)]
    · apply Finset.sum_congr rfl
      intro s hs
      have h := hv.mem_toFinset.mp hs
      rw [Set.indicator_of_mem (show s ∈ Ioc (0 : NNReal) t from ⟨h.1,h.2.1⟩)]
    · intro s hs
      by_cases hst : s ∈ Ioc (0 : NNReal) t
      · rw [Set.indicator_of_mem hst]
        by_cases hps : p s
        · exact False.elim (hs (hv.mem_toFinset.mpr ⟨hst.1,hst.2,hp s hst.1 hps⟩))
        · simp [hps]
      · exact Set.indicator_of_notMem hst _
