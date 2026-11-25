-- Prove2me | solution 1 for GlobalTheory.HasLogGrowth.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:44.776859+00:00
-- url     : https://prove2.me/submissions/a6495dad-2f6b-4add-a9e4-c58a2550a956

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
variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
open GlobalTheory.HasLogGrowth
namespace GlobalTheory.HasLogGrowth
theorem _root_.solution {R : Type*} [SeminormedRing R] {f : X → R} (hf : HasLogGrowth S w U f) (k : ℕ) :
    HasLogGrowth S w U fun x => f x ^ k := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf
end GlobalTheory.HasLogGrowth
