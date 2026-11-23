-- Prove2me | solution 1 for GlobalTheory.Inertia.congr_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:14.162071+00:00
-- url     : https://prove2.me/submissions/be7b55f3-71f3-4f82-bb26-af6681fbc96a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
namespace GlobalTheory.Inertia
theorem _root_.solution {l : Type*} (G : Matrix n n ℂ) (P : Matrix n m ℂ) (Q : Matrix m l ℂ) :
    (P * Q)ᵀ * G * (P * Q).map conj = Qᵀ * (Pᵀ * G * P.map conj) * Q.map conj := by
  rw [transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
end GlobalTheory.Inertia
