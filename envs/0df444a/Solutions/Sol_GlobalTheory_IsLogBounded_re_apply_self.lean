-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.re_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:50.031212+00:00
-- url     : https://prove2.me/submissions/c504f3cb-c486-4064-9783-db83723e73b3

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
variable [Fintype n]
open GlobalTheory.IsLogBounded
omit [Fintype n]
namespace GlobalTheory.IsLogBounded
theorem _root_.solution (hG : IsLogBounded S w U G) (i : n) :
    IsLogBoundedScalar S w U fun x => (G x i i).re := by
  intro K hKU hK
  obtain ⟨C, N, hC, h⟩ := hG K hKU hK
  refine ⟨C, N, hC, fun x hx hB => ?_⟩
  have h' := h x hx hB
  generalize C * lwP₂ S (w x) ^ N = a at h' ⊢
  constructor
  · simpa using (Complex.nonneg_iff.1 ((Matrix.le_iff.1 h'.1).diag_nonneg (i := i))).1
  · simpa using (Complex.nonneg_iff.1 ((Matrix.le_iff.1 h'.2).diag_nonneg (i := i))).1
end GlobalTheory.IsLogBounded
