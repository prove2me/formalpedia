-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:10.032122+00:00
-- url     : https://prove2.me/submissions/de278042-49c5-4b4d-aaa9-b27dac2c61bc

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
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
open GlobalTheory.IsLogBounded
namespace GlobalTheory.IsLogBounded
theorem _root_.solution (hG : IsLogBounded S w U G) {V : Set X} (hV : V ⊆ U) : IsLogBounded S w V G :=
  fun K hK => hG K (hK.trans hV)
end GlobalTheory.IsLogBounded
