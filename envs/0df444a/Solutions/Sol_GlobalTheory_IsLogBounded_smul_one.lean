-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:11:20.66886+00:00
-- url     : https://prove2.me/submissions/50b2d463-88f8-4811-9b84-e7270766f154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_HasLogGrowthEntries_of_continuousOn
import Theorems.Thm_GlobalTheory_IsLogBounded_of_continuousOn
import Theorems.Thm_GlobalTheory_IsLogBounded_smul

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
theorem _root_.solution {g : X → ℝ} (hg : IsLogBoundedScalar S w U g) :
    IsLogBounded S w U fun x => g x • (1 : Matrix n n ℂ) :=
  smul hg (of_continuousOn continuousOn_const fun _ _ => PosDef.one)
end GlobalTheory.IsLogBounded
