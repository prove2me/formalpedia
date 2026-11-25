-- Prove2me | solution 1 for GlobalTheory.SmoothLocusAdd.isSumAt_ptHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:47.086274+00:00
-- url     : https://prove2.me/submissions/508a7b4e-d69b-4f48-8da9-f29510e08af0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
open WeierstrassCurve.Projective
namespace GlobalTheory.SmoothLocusAdd
theorem _root_.solution {k : Type} [Field k] (ρ : R →+* k) {P Q S : Fin 3 → k}
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (hS : IsUnimodularSol (W.map ρ) S) (nP : (W.map ρ).toProjective.Nonsingular P)
    (nQ : (W.map ρ).toProjective.Nonsingular Q)
    (e : S ≈ (W.map ρ).toProjective.add P Q) :
    IsSumAt W (ptHom W ρ P hP) (ptHom W ρ Q hQ) (ptHom W ρ S hS) := by
  intro ρ' P' Q' hP' hQ' eP eQ
  obtain rfl : ρ = ρ' := by
    have := congrArg (· ≫ toSpec W) eP
    simp only [ptHom_toSpec] at this
    exact congrArg (·.hom) (Spec.map_injective this)
  obtain ⟨u, hu⟩ := (ptHom_eq_ptHom_iff W hP' hP).mp eP.symm
  obtain ⟨v, hv⟩ := (ptHom_eq_ptHom_iff W hQ' hQ).mp eQ.symm
  have e₁ : P ≈ P' := ⟨u, hu.symm⟩
  have e₂ : Q ≈ Q' := ⟨v, hv.symm⟩
  have nP' := (nonsingular_of_equiv e₁).mp nP
  have nQ' := (nonsingular_of_equiv e₂).mp nQ
  have hA : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P' Q') :=
    .of_nonsingular (nonsingular_add nP' nQ')
  refine ⟨hA, ?_⟩
  obtain ⟨w, hw⟩ := Setoid.trans e (add_equiv e₁ e₂)
  exact ((ptHom_eq_ptHom_iff W hA hS).mpr ⟨w, hw.symm⟩).symm
end GlobalTheory.SmoothLocusAdd
