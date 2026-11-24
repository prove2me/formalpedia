-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.re_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:48:41.763063+00:00
-- url     : https://prove2.me/submissions/58a3bf22-a773-4650-9bb9-ceb265b29258

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_Inertia_embedding_cc
import Theorems.Thm_GlobalTheory_Published_embedding_cc


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
theorem _root_.solution (τ : E →+* ℂ) {x : E} (hx : cc x = x) (h0 : x ≠ 0) : (τ x).re ≠ 0 := by
  intro h
  have h1 := GlobalTheory.Published.embedding_cc τ x
  rw [hx] at h1
  have h2 : (τ x).im = 0 := Complex.conj_eq_iff_im.mp h1.symm
  exact (map_ne_zero τ).mpr h0 (Complex.ext h h2)
end GlobalTheory.LocalQuad.HermClass
