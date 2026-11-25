-- Prove2me | solution 1 for GlobalTheory.NodalCubic.exists_splitTorus_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:38:34.900105+00:00
-- url     : https://prove2.me/submissions/d5b1bf23-c822-4b03-9374-b366e834de7b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
import Theorems.Thm_GlobalTheory_NodalCubic_valOf_mul
import Theorems.Thm_GlobalTheory_NodalCubic_valOf_injective
import Theorems.Thm_GlobalTheory_NodalCubic_comp_paramHom
import Theorems.Thm_GlobalTheory_NodalCubic_over_hom_ext_field
import Theorems.Thm_GlobalTheory_NodalCubic_exists_toLocus
import Theorems.Thm_GlobalTheory_NodalCubic_exists_nonsingular
import Theorems.Thm_GlobalTheory_NodalCubic_exists_fromLocus
import Theorems.Thm_GlobalTheory_NodalCubic_isMonHom_of_mul_hom
import Theorems.Thm_GlobalTheory_AddLaw_Represents_ne_zero
import Theorems.Thm_GlobalTheory_NodalCubic_nonsingular_points
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
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_of_isReduced
import Theorems.Thm_GlobalTheory_restrictPoints_val
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
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NodalCubic
open GlobalTheory.WeierstrassCurve
variable (K : Type) [Field K]
variable {K}
namespace GlobalTheory.NodalCubic
theorem _root_.solution : ∀ (K : Type) [Field K] (W : WeierstrassCurve K), W = ⟨1, 0, 0, 0, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : K →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro K _ W hW
  subst hW
  intro U hU hsm _ _ hadd
  obtain ⟨f, hf⟩ := exists_toLocus U hU
  obtain ⟨g, hg⟩ := exists_fromLocus U hU
  have hpt : ∀ (k : Type) [Field k] (ρ : K →+* k)
      (x : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ splitTorus (Spec (.of K)) ℤ),
      (x ≫ f).left ≫ U.ι =
        ptHom (node K) ρ (param (valOf x : k)) (isUnimodularSol_param _ _) := fun k _ ρ x =>
    (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) hf).trans (comp_paramHom x))
  have r1 : IsReduced (splitTorus (Spec (.of K)) ℤ).left :=
    isReduced_of_smooth_of_isReduced (splitTorus (Spec (.of K)) ℤ).hom
  have r2 : IsReduced (Over.mk (U.ι ≫ toSpec (node K))).left :=
    @isReduced_of_smooth_of_isReduced _ _ (U.ι ≫ toSpec (node K)) hsm _
  have s3 : Smooth (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Spec (.of K)) ℤ).hom
      (splitTorus (Spec (.of K)) ℤ).hom ≫ (splitTorus (Spec (.of K)) ℤ).hom))
  have r3 : IsReduced (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).left :=
    isReduced_of_smooth_of_isReduced
      (splitTorus (Spec (.of K)) ℤ ⊗ splitTorus (Spec (.of K)) ℤ).hom
  have sep : IsSeparated (Over.mk (U.ι ≫ toSpec (node K))).hom :=
    inferInstanceAs (IsSeparated (U.ι ≫ toSpec (node K)))
  have ext : ∀ {Z : Over (Spec (.of K))} {a b : Z ⟶ Over.mk (U.ι ≫ toSpec (node K))},
      a.left ≫ U.ι = b.left ≫ U.ι → a = b := fun h =>
    Over.OverMorphism.ext ((cancel_mono U.ι).mp h)
  refine ⟨⟨f, g, ?_, ?_⟩, isMonHom_of_mul_hom f ?_⟩
  · refine over_hom_ext_field fun k _ ρ x => valOf_injective (Units.ext ?_)
    rw [← Category.assoc, hg k ρ _ _ _ (hpt k ρ x), Category.comp_id]
    have := (valOf x).ne_zero
    have e : param (valOf x : k) 0 + param (valOf x : k) 1 = valOf x := by
      simp [param]; ring
    rw [e, div_eq_iff this]
    simp [param, sq]
  · refine over_hom_ext_field fun k _ ρ y => ext ?_
    obtain ⟨P, hP, e, hn⟩ := exists_nonsingular U hU y
    obtain ⟨-, -, c, hc⟩ := (nonsingular_points k).2.2 P hn
    rw [← Category.assoc, hpt, Category.comp_id, e, ptHom_eq_ptHom_iff]
    exact ⟨c, by rw [hg k ρ y P hP e]; exact hc⟩
  · refine over_hom_ext_field fun k _ ρ x => ext ?_
    obtain ⟨h, e⟩ := hadd k ρ _ _ _ _ _ _ (hpt k ρ (x ≫ fst _ _)) (hpt k ρ (x ≫ snd _ _))
    have e1 : x ≫ μ = (x ≫ fst _ _) * (x ≫ snd _ _) := by
      rw [Hom.mul_def, lift_comp_fst_snd]
    have e2 : x ≫ (f ⊗ₘ f) = lift ((x ≫ fst _ _) ≫ f) ((x ≫ snd _ _) ≫ f) := by
      rw [← lift_map, lift_comp_fst_snd]
    obtain ⟨c, hc⟩ := (nonsingular_points k).2.1 (valOf (x ≫ fst _ _)) (valOf (x ≫ snd _ _))
    rw [← Category.assoc, ← Category.assoc, e1, e2, hpt, e, ptHom_eq_ptHom_iff]
    exact ⟨c, by rw [valOf_mul, node_map]; exact hc⟩
end GlobalTheory.NodalCubic
