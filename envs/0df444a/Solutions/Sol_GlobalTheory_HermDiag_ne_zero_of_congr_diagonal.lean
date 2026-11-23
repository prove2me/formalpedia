-- Prove2me | solution 1 for GlobalTheory.HermDiag.ne_zero_of_congr_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:42.819568+00:00
-- url     : https://prove2.me/submissions/7dd64367-3762-4761-bc5e-a336daf21480

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n]
variable [DecidableEq n]
namespace GlobalTheory.HermDiag
theorem _root_.solution {G P : Matrix n n E} {d : n → E} (hP : P.det ≠ 0)
    (hd : Pᵀ * G * P.map c = Matrix.diagonal d) (hG : G.det ≠ 0) (i : n) : d i ≠ 0 := by
  have h := congrArg Matrix.det hd
  have hm : (P.map c).det = c P.det := (RingHom.map_det c P).symm
  rw [det_mul, det_mul, det_transpose, hm, det_diagonal] at h
  have hne : ∏ i, d i ≠ 0 := by
    rw [← h]
    exact mul_ne_zero (mul_ne_zero hP hG) ((map_ne_zero c).2 hP)
  exact Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ i)
end GlobalTheory.HermDiag
