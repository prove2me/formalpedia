-- Prove2me | solution 1 for GlobalTheory.JR.DeltaLift.dot_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:17.211827+00:00
-- url     : https://prove2.me/submissions/719ab500-8d83-4c4a-9604-7526cdfcd76f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DeltaLift
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.DeltaLift
theorem _root_.solution (W V : Fin (r + 1) → k) :
    W ⬝ᵥ V = (fun i => W (Fin.castSucc i)) ⬝ᵥ (fun i => V (Fin.castSucc i)) + W (Fin.last r) * V (Fin.last r) := by
  simp only [dotProduct, Fin.sum_univ_castSucc]
end GlobalTheory.JR.DeltaLift
