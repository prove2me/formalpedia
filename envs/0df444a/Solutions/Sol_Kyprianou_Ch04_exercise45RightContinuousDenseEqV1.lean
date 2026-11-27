-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45RightContinuousDenseEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:33:49.763125+00:00
-- url     : https://prove2.me/submissions/3b264867-506e-4ba7-a367-f238f451fd9a

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal
set_option autoImplicit false

/-- Two right-continuous functions agreeing on a dense grid agree everywhere. -/
theorem solution (f g : NNReal → ℝ) (grid : ℕ → NNReal) (hd : DenseRange grid)
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hg : ∀ t, ContinuousWithinAt g (Ici t) t)
    (he : ∀ k, f (grid k) = g (grid k)) : ∀ t, f t = g t := by
  intro t
  have hs : Ioi t ⊆ closure (Ioi t ∩ range grid) :=
    hd.open_subset_closure_inter isOpen_Ioi
  have ht : t ∈ closure (Ioi t ∩ range grid) := by
    apply closure_minimal hs isClosed_closure
    rw [closure_Ioi]
    exact mem_Ici.mpr le_rfl
  obtain ⟨q,hq,hl⟩ := mem_closure_iff_seq_limit.mp ht
  have hw : Tendsto q atTop (nhdsWithin t (Ici t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl,Eventually.of_forall fun n => mem_Ici.mpr (le_of_lt (mem_Ioi.mp (hq n).1))⟩
  have heq (n : ℕ) : f (q n) = g (q n) := by
    obtain ⟨k,hk⟩ := (hq n).2
    rw [← hk]
    exact he k
  exact tendsto_nhds_unique ((show Tendsto f (nhdsWithin t (Ici t)) (nhds (f t)) from hf t).comp hw)
    (((show Tendsto g (nhdsWithin t (Ici t)) (nhds (g t)) from hg t).comp hw).congr fun n => (heq n).symm)
