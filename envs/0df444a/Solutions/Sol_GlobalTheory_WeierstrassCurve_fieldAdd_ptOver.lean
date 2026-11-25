-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.fieldAdd_ptOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:46.551796+00:00
-- url     : https://prove2.me/submissions/68a17f25-2f7a-41a7-b2c0-2d5549556052

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_IsSumTriple_equiv_add
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_ptOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [W.IsElliptic]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {k : Type u} [Field k] [Algebra R k] {P Q T : Fin 3 → k}
    (hP : IsUnimodularSol (W.baseChange k) P) (hQ : IsUnimodularSol (W.baseChange k) Q)
    (hT : IsUnimodularSol (W.baseChange k) T) (h : IsSumTriple (W.baseChange k) P Q T) :
    fieldAdd W k (ptOver W P hP) (ptOver W Q hQ) = ptOver W T hT := by
  rw [fieldAdd, projectivePointEquiv_symm_ptOver, projectivePointEquiv_symm_ptOver]
  obtain ⟨v, hv⟩ := h.equiv_add hP.nonsingular hQ.nonsingular
    (isUnimodularSol_iff_ne_zero.mp hT).right
  exact (ptOver_eq_ptOver_iff W (.of_nonsingular
    (WeierstrassCurve.Projective.nonsingular_add hP.nonsingular hQ.nonsingular)) hT).mpr
    ⟨v, hv.symm⟩
end GlobalTheory.WeierstrassCurve
