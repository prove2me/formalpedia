-- Prove2me | solution 1 for GlobalTheory.FockDetDer.trace_fromBlocks_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:27:13.715362+00:00
-- url     : https://prove2.me/submissions/6d6aceb3-6fd6-468a-9a19-00f34f79a1e9

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SymmetricBlockTraceInverseEqTwoMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.FockDetDer
namespace GlobalTheory.FockDetDer
theorem _root_.solution {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    (fromBlocks X 0 0 Y).trace = X.trace + Y.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]
end GlobalTheory.FockDetDer
