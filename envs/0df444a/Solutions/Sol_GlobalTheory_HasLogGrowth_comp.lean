-- Prove2me | solution 1 for GlobalTheory.HasLogGrowth.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:06:36.598814+00:00
-- url     : https://prove2.me/submissions/80a79367-8a57-4904-8297-d442a8a8aefa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_HasLogGrowth_comp_of_logWeight
import Theorems.Thm_GlobalTheory_IsUnitMulMonomialOn_notMem
import Theorems.Thm_GlobalTheory_IsUnitMulMonomialOn_hasLogGrowth_logWeight

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
variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
namespace GlobalTheory
namespace HasLogGrowth
theorem _root_.solution {f : X → E} (hf : HasLogGrowth S w U f) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hw : IsUnitMulMonomialOn S (fun x => w (π x)) S' w' U') :
    HasLogGrowth S' w' U' fun x => f (π x) :=
  hf.comp_of_logWeight hπ hU (fun _ hx hB => hw.notMem hx hB) hw.hasLogGrowth_logWeight
end HasLogGrowth
end GlobalTheory
