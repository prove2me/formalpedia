-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:59:02.560625+00:00
-- url     : https://prove2.me/submissions/89806f1e-8c27-4a52-b3e1-d6631ef2e96f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_transpose_le_transpose_of_le


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
theorem _root_.solution (hG : IsLogBounded S w U G) : IsLogBounded S w U fun x => (G x)ᵀ := by
  intro K hKU hK
  obtain ⟨C, N, hC, h⟩ := hG K hKU hK
  refine ⟨C, N, hC, fun x hx hB => ⟨?_, ?_⟩⟩
  · simpa using transpose_le_transpose_of_le (h x hx hB).1
  · simpa using transpose_le_transpose_of_le (h x hx hB).2
end GlobalTheory.IsLogBounded
