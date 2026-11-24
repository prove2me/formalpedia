-- Prove2me | solution 1 for GlobalTheory.Inertia.dotProduct_congr_mulVec_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:47:56.992799+00:00
-- url     : https://prove2.me/submissions/2fbc4eed-3638-45c1-823e-e8b885099dac

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
theorem _root_.solution (G : Matrix n n ℂ) (P : Matrix n m ℂ) (x y : m → ℂ) :
    x ⬝ᵥ (Pᵀ * G * P.map conj) *ᵥ star y = (P *ᵥ x) ⬝ᵥ G *ᵥ star (P *ᵥ y) := by
  have h : star (P *ᵥ y) = P.map conj *ᵥ star y := by
    ext k
    simp [mulVec, dotProduct]
  rw [h, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x, vecMul_transpose]
end GlobalTheory.Inertia
