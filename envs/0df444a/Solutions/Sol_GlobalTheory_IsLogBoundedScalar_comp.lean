-- Prove2me | solution 1 for GlobalTheory.IsLogBoundedScalar.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:20:40.175287+00:00
-- url     : https://prove2.me/submissions/f45dab4a-577d-4e67-adce-ef3a3585e29b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_IsUnitMulMonomialOn_notMem
import Theorems.Thm_GlobalTheory_HasLogGrowth_comp

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
variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}
open GlobalTheory.IsLogBoundedScalar
namespace GlobalTheory.IsLogBoundedScalar
theorem _root_.solution (hg : IsLogBoundedScalar S w U g) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hw : IsUnitMulMonomialOn S (fun x => w (π x)) S' w' U') :
    IsLogBoundedScalar S' w' U' fun x => g (π x) :=
  isLogBoundedScalar_iff.2 ⟨fun _ hx hB => hg.pos (hU hx) (hw.notMem hx hB),
    hg.hasLogGrowth.comp hπ hU hw, hg.hasLogGrowth_inv.comp hπ hU hw⟩
end GlobalTheory.IsLogBoundedScalar
