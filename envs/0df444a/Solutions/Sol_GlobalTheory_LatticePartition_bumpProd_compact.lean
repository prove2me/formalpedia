-- Prove2me | solution 1 for GlobalTheory.LatticePartition.bumpProd_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:49.826567+00:00
-- url     : https://prove2.me/submissions/9e8489db-25e1-474d-bdc3-71d282284dbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity
import Theorems.Thm_GlobalTheory_LatticePartition_bump_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
noncomputable section
open GlobalTheory GlobalTheory.LatticePartition
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
namespace GlobalTheory.LatticePartition
theorem _root_.solution (e : V ≃L[ℝ] (Fin n → ℝ)) : HasCompactSupport (bumpProd e) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine HasCompactSupport.intro (hK.image e.symm.continuous) ?_
  intro x hx
  have : ∃ i, 1 ≤ |e x i| := by
    by_contra h
    simp only [not_exists, not_le] at h
    exact hx ⟨e x, Set.mem_univ_pi.2 fun i => ⟨(abs_lt.1 (h i)).1.le, (abs_lt.1 (h i)).2.le⟩,
      e.symm_apply_apply x⟩
  obtain ⟨i, hi⟩ := this
  exact Finset.prod_eq_zero (Finset.mem_univ i) (bump_eq_zero hi)
end GlobalTheory.LatticePartition
