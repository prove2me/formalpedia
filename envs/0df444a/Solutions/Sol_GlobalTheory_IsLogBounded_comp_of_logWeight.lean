-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.comp_of_logWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:05.065133+00:00
-- url     : https://prove2.me/submissions/a01d4a27-e86c-4d1d-8e08-e4f0872f087a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_HasLogGrowth_comp_of_logWeight

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
    (hB : ∀ x ∈ U', x ∉ coordDivisor S' w' → π x ∉ coordDivisor S w)
    (hw : HasLogGrowth S' w' U' fun x => lwP₂ S (w (π x))) :
    IsLogBounded S' w' U' fun x => G (π x) :=
  isLogBounded_iff_entries.2 ⟨fun x hx hx' => hG.posDef (hU hx) (hB x hx hx'),
    fun i j => (hG.hasLogGrowthEntries i j).comp_of_logWeight hπ hU hB hw,
    fun i j => (hG.hasLogGrowthEntries_inv i j).comp_of_logWeight hπ hU hB hw⟩
end GlobalTheory.IsLogBounded
