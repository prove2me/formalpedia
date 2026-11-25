-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.comp_ptOver_eq_fieldAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:43.942909+00:00
-- url     : https://prove2.me/submissions/1a2c2679-13e1-41fe-b95e-d7f876d769ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_exists_eq_specOverMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_fieldAdd_ptOver
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm


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
theorem _root_.solution {A : Type u} [CommRing A] [Algebra R A] {P Q T : Fin 3 → A}
    (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q)
    (hT : IsUnimodularSol (W.baseChange A) T) (h : IsSumTriple (W.baseChange A) P Q T)
    (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ specOver R A) :
    x ≫ ptOver W T hT = fieldAdd W k (x ≫ ptOver W P hP) (x ≫ ptOver W Q hQ) := by
  obtain ⟨g, rfl⟩ := exists_eq_specOverMap x
  rw [specOverMap_ptOver, specOverMap_ptOver, specOverMap_ptOver]
  exact (fieldAdd_ptOver W _ _ _ (h.baseChange g)).symm
end GlobalTheory.WeierstrassCurve
