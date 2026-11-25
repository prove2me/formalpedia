-- Prove2me | solution 1 for GlobalTheory.abs_log_norm_le_logWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:54.205017+00:00
-- url     : https://prove2.me/submissions/e7293d38-44ee-487d-b1ee-eb2a15cf8c23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ X : Type*}
namespace GlobalTheory
theorem _root_.solution {S : Finset κ} (z : κ → ℂ) {j : κ} (hj : j ∈ S) :
    |Real.log ‖z j‖| ≤ lwP₂ S z :=
  (Finset.single_le_sum (f := fun j => |Real.log ‖z j‖|) (fun _ _ => abs_nonneg _) hj).trans
    (le_add_of_nonneg_left zero_le_one)
end GlobalTheory
