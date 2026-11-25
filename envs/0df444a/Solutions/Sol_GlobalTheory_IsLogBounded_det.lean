-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:54.902539+00:00
-- url     : https://prove2.me/submissions/caaf60b3-12bc-40ba-8c28-8906d6c40067

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_IsLogBounded_det_zpow

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
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]
open GlobalTheory.IsLogBounded
namespace GlobalTheory.IsLogBounded
theorem _root_.solution (hG : IsLogBounded S w U G) (p : Type*) [Unique p] [DecidableEq p] :
    IsLogBounded S w U fun x => Matrix.of fun _ _ : p => (G x).det := by
  simpa using hG.det_zpow 1 p
end GlobalTheory.IsLogBounded
