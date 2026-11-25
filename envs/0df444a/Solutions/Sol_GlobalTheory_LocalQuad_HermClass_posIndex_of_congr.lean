-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.posIndex_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:43.16126+00:00
-- url     : https://prove2.me/submissions/cbc04c09-975c-44d6-87e5-521e77c375ec

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_Inertia_posIndex_map_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LocalQuad.HermClass
theorem _root_.solution (τ : E →+* ℂ) {r : ℕ} {G G' : Matrix (Fin r) (Fin r) E}
    (h : Congr (IsCMField.complexConj E : E →+* E) G G') :
    GlobalTheory.Inertia.posIndex (G'.map τ) = GlobalTheory.Inertia.posIndex (G.map τ) := by
  obtain ⟨P, hP, rfl⟩ := h
  exact GlobalTheory.Inertia.posIndex_map_congr τ G hP
end GlobalTheory.LocalQuad.HermClass
