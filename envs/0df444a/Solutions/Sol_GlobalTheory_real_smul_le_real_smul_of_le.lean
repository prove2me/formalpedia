-- Prove2me | solution 1 for GlobalTheory.real_smul_le_real_smul_of_le
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:32:09.176078+00:00
-- url     : https://prove2.me/submissions/ffb98a0b-6f34-4daf-9471-e09a14f0b681

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open GlobalTheory
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
omit [Fintype n]
theorem _root_.solution {A B : Matrix n n 𝕜} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  first
    | (rw [Matrix.le_iff] at h ⊢
       rw [← smul_sub]
       exact h.smul hc)
    | (open scoped MatrixOrder in
       rw [Matrix.le_iff] at h ⊢
       rw [← smul_sub]
       exact h.smul hc)
    | (exact smul_le_smul_of_nonneg_left h hc)

