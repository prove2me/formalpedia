-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.posCount_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:47.752797+00:00
-- url     : https://prove2.me/submissions/b89be6b1-5e8f-422a-bea3-ce94c9444a44

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.LocalQuad.HermClass
theorem _root_.solution (τ : E →+* ℂ) {r : ℕ} (g : Fin (r + 1) → E) :
    posCount τ g = (if 0 < (τ (g 0)).re then 1 else 0) + posCount τ fun i : Fin r => g i.succ := by
  simp only [posCount, Finset.card_filter, Fin.sum_univ_succ]
end GlobalTheory.LocalQuad.HermClass
