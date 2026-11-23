-- Prove2me | solution 1 for GlobalTheory.HermDiag.det_of_basis_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:42.215834+00:00
-- url     : https://prove2.me/submissions/8c1856f6-e7d5-4955-9a55-4080dacffa15

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
theorem _root_.solution (v : Basis n E (n → E)) :
    (Matrix.of fun k i => v i k).det ≠ 0 := by
  have h : (Matrix.of fun k i => v i k) = (Pi.basisFun E n).toMatrix v := by
    ext k i
    simp [Basis.toMatrix_apply]
  rw [h]
  letI := (Pi.basisFun E n).invertibleToMatrix v
  exact (Matrix.isUnit_det_of_invertible _).ne_zero
end GlobalTheory.HermDiag
