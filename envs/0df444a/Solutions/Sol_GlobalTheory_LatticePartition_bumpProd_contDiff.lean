-- Prove2me | solution 1 for GlobalTheory.LatticePartition.bumpProd_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:25.993189+00:00
-- url     : https://prove2.me/submissions/41b7cb83-2b22-4085-ada1-ef30e6f18581

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity
import Theorems.Thm_GlobalTheory_LatticePartition_bump_contDiff

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
theorem _root_.solution (e : V ≃L[ℝ] (Fin n → ℝ)) : ContDiff ℝ ∞ (bumpProd e) := by
  unfold bumpProd
  refine contDiff_prod fun i _ => bump_contDiff.comp ?_
  exact (contDiff_apply ℝ ℝ i).comp e.contDiff
end GlobalTheory.LatticePartition
