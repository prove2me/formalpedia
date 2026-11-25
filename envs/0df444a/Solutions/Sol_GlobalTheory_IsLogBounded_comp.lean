-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:01:27.943642+00:00
-- url     : https://prove2.me/submissions/f8c40440-c30c-4e21-a19a-17bd4105c780

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_IsUnitMulMonomialOn_notMem
import Theorems.Thm_GlobalTheory_HasLogGrowth_comp
import Theorems.Thm_GlobalTheory_IsLogBoundedScalar_comp

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
theorem _root_.solution (hG : IsLogBounded S w U G) {S' : Finset κ'}
    {w' : X' → κ' → ℂ} {U' : Set X'} {π : X' → X} (hπ : ContinuousOn π U') (hU : MapsTo π U' U)
    (hw : IsUnitMulMonomialOn S (fun x => w (π x)) S' w' U') :
    IsLogBounded S' w' U' fun x => G (π x) :=
  isLogBounded_iff_entries.2 ⟨fun _ hx hB => hG.posDef (hU hx) (hw.notMem hx hB),
    fun i j => (hG.hasLogGrowthEntries i j).comp hπ hU hw,
    fun i j => (hG.hasLogGrowthEntries_inv i j).comp hπ hU hw⟩
end GlobalTheory.IsLogBounded
