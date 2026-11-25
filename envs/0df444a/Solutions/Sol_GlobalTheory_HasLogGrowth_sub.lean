-- Prove2me | solution 1 for GlobalTheory.HasLogGrowth.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:49.384616+00:00
-- url     : https://prove2.me/submissions/eb8995d3-758e-4638-9526-0cefccd65a4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_HasLogGrowth_neg

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
open GlobalTheory.HasLogGrowth
namespace GlobalTheory.HasLogGrowth
theorem _root_.solution {f g : X → E} (hf : HasLogGrowth S w U f) (hg : HasLogGrowth S w U g) :
    HasLogGrowth S w U fun x => f x - g x :=
  (hf.add hg.neg).congr fun _ _ _ => sub_eq_add_neg _ _
end GlobalTheory.HasLogGrowth
