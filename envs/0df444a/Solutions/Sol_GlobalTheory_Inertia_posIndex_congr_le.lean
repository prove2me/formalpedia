-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_congr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:05.10057+00:00
-- url     : https://prove2.me/submissions/59b279e3-ea59-48c7-be96-5439fc0d7c8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_isGreatest_posIndex
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_dotProduct_congr_mulVec_star
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
theorem _root_.solution (G : Matrix n n ℂ) {P : Matrix n m ℂ}
    (hP : Function.Injective P.mulVec) : posIndex (Pᵀ * G * P.map conj) ≤ posIndex G := by
  obtain ⟨W, hW, hpos⟩ := (isGreatest_posIndex (Pᵀ * G * P.map conj)).1
  refine (isGreatest_posIndex G).2 ⟨W.map P.mulVecLin, ?_, ?_⟩
  · rw [← hW]
    exact (Submodule.equivMapOfInjective P.mulVecLin hP W).finrank_eq.symm
  · rintro _ ⟨x, hx, rfl⟩ hx0
    have := hpos x hx (by rintro rfl; simp at hx0)
    rwa [dotProduct_congr_mulVec_star] at this
end GlobalTheory.Inertia
