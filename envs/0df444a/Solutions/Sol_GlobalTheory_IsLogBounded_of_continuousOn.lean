-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:27.947738+00:00
-- url     : https://prove2.me/submissions/4d82255a-c8fe-405e-bf97-757aaa8138e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_HasLogGrowthEntries_of_continuousOn
import Theorems.Thm_GlobalTheory_continuousOn_matrix_inv

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
theorem _root_.solution (hG : ContinuousOn G U) (h0 : ∀ x ∈ U, (G x).PosDef) :
    IsLogBounded S w U G :=
  isLogBounded_iff_entries.2 ⟨fun x hx _ => h0 x hx, .of_continuousOn hG,
    .of_continuousOn (continuousOn_matrix_inv hG fun x hx => (h0 x hx).isUnit)⟩
end GlobalTheory.IsLogBounded
