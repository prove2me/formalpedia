-- Prove2me | solution 1 for GlobalTheory.TorsionZero.trdeg_eq_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:00.72985+00:00
-- url     : https://prove2.me/submissions/93a7a03d-eea1-4456-b806-aaca392eff52

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K σ : Type} [Field K]
namespace GlobalTheory.TorsionZero
theorem _root_.solution {A : Type} [CommRing A] [IsDomain A] [Algebra K A]
    (B : Subalgebra K A) [Algebra.IsAlgebraic B A] : Algebra.trdeg K A = Algebra.trdeg K B := by
  haveI : FaithfulSMul K B := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K B).injective
  rw [← trdeg_add_eq K B (A := A), trdeg_eq_zero (R := B) (A := A), add_zero]
end GlobalTheory.TorsionZero
