-- Prove2me | solution 1 for GlobalTheory.LatticePartition.bumpProd_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:50.632428+00:00
-- url     : https://prove2.me/submissions/2be31f1b-7a36-42af-83b6-97ae724d31e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity

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
theorem _root_.solution (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) (j : Fin n → ℤ) :
    bumpProd e (x - latPt e j) = ∏ i, bump (e x i - j i) := by
  simp [bumpProd, latPt, map_sub]
end GlobalTheory.LatticePartition
