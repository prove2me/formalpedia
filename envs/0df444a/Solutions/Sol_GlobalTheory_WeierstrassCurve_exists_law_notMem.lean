-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.exists_law_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:45.244748+00:00
-- url     : https://prove2.me/submissions/9a6cb103-b549-42f1-8c30-3b17f2823277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_AddLaw_addXYZ_ne_zero_or_diagXYZ_ne_zero
import Theorems.Thm_GlobalTheory_AddLaw_map_diagXYZ


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
open AddLaw
variable {A B : Type*} [CommRing A] [CommRing B]
variable {V : WeierstrassCurve A} {P Q T : Fin 3 → A}
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution [V.IsElliptic] (hP : IsUnimodularSol V P) (hQ : IsUnimodularSol V Q)
    (p : Ideal A) [p.IsPrime] :
    (∃ i, V.toProjective.addXYZ P Q i ∉ p) ∨ ∃ i, diagXYZ V.toProjective P Q i ∉ p := by
  let g := algebraMap A p.ResidueField
  have e₁ : (V.map g).toProjective.addXYZ (g ∘ P) (g ∘ Q) = g ∘ V.toProjective.addXYZ P Q :=
    WeierstrassCurve.Projective.map_addXYZ ..
  have e₂ : diagXYZ (V.map g).toProjective (g ∘ P) (g ∘ Q) = g ∘ diagXYZ V.toProjective P Q :=
    map_diagXYZ ..
  have h := addXYZ_ne_zero_or_diagXYZ_ne_zero (hP.map g).nonsingular (hQ.map g).nonsingular
  rw [e₁, e₂] at h
  refine h.imp (fun h => ?_) (fun h => ?_) <;>
    exact (Function.ne_iff.mp h).imp fun i hi hp =>
      hi (Ideal.algebraMap_residueField_eq_zero.mpr hp)
end GlobalTheory.WeierstrassCurve
