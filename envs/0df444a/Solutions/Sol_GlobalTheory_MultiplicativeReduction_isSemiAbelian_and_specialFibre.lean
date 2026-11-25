-- Prove2me | solution 1 for GlobalTheory.MultiplicativeReduction.isSemiAbelian_and_specialFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:33.972682+00:00
-- url     : https://prove2.me/submissions/5d449519-92b8-4d4d-93c5-b5e9f91c56f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LiftMulHomPullbackFst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyTorusExtensionSplitTorus
import Theorems.Thm_GlobalTheory_MultiplicativeReduction_isProper_pullback_snd
import Theorems.Thm_GlobalTheory_MultiplicativeReduction_nonempty_torusExtension_splitTorus
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_AddLaw_Represents_ne_zero
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main
import Theorems.Thm_GlobalTheory_NodalCubic_exists_splitTorus_iso
import Theorems.Thm_GlobalTheory_SmoothLocusBaseChange_main
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
open GlobalTheory GlobalTheory.MultiplicativeReduction
open GlobalTheory.WeierstrassCurve
namespace GlobalTheory.MultiplicativeReduction
theorem _root_.solution : ∀ (W : WeierstrassCurve (PowerSeries ℚ)), W = ⟨1, 0, 0, PowerSeries.X, 0⟩ → ∀ (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : (PowerSeries ℚ) →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → QuasiCompact (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∀ [GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))] [IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))], (∀ (k : Type) [Field k] (ρ : (PowerSeries ℚ) →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) → IsSemiAbelian (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ ∃ i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField (PowerSeries ℚ)))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries ℚ))))).obj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsMonHom i.hom := by
  intro W hW U hU hsm hgi hqc _ _ hmul
  have hgc : GeometricallyConnected (U.ι ≫ toSpec W) := by
    refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
    have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    exact inferInstanceAs (ConnectedSpace Z)
  have htor : ∀ (K : Type) [Field K] (f : PowerSeries ℚ →+* K), f PowerSeries.X = 0 →
      ∃ i : splitTorus (Spec (CommRingCat.of K)) ℤ ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)),
        IsMonHom i.hom := by
    intro K _ f hf
    obtain ⟨U', _, e, he, -, hU', hmul'⟩ :=
      GlobalTheory.SmoothLocusBaseChange.main _ K f W U hU hsm hgi hmul
    have hl : U'.ι ≫ toSpec (W.map f) =
        e.hom.left ≫ pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)) :=
      (Over.w e.hom).symm
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    obtain ⟨i, hi⟩ := GlobalTheory.NodalCubic.exists_splitTorus_iso K (W.map f)
      (by subst hW; ext <;> simp [hf]) U' hU' (by rw [hl]; infer_instance)
      (by
        rw [hl]
        exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
          (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨(Category.comp_id _).symm⟩)
          (inferInstanceAs (GeometricallyIntegral
            (pullback.snd (U.ι ≫ toSpec W) (Spec.map (CommRingCat.ofHom f)))))) hmul'
    exact ⟨i ≪≫ e, by rw [Iso.trans_hom]; infer_instance⟩
  refine ⟨⟨inferInstance, hsm, inferInstanceAs (IsSeparated (U.ι ≫ toSpec W)), hqc,
    hgc, fun Ω _ _ p => ?_⟩,
    htor _ _ ?_⟩
  · obtain ⟨g, rfl⟩ := Spec.map_surjective p
    obtain ⟨f, rfl⟩ : ∃ f : PowerSeries ℚ →+* Ω, g = CommRingCat.ofHom f := ⟨g.hom, rfl⟩
    by_cases hf : f PowerSeries.X = 0
    · obtain ⟨i, hi⟩ := htor Ω f hf
      obtain ⟨T⟩ := nonempty_torusExtension_splitTorus Ω
      exact ⟨Geo.Tor.torusExtOfIso i T⟩
    · have hΔ : W.Δ = PowerSeries.X ^ 2 * (1 - 64 * PowerSeries.X) := by
        subst hW
        simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      have hu : IsUnit (1 - 64 * PowerSeries.X : PowerSeries ℚ) := by
        rw [PowerSeries.isUnit_iff_constantCoeff]
        simp
      have hΔ' : f W.Δ ≠ 0 := by
        rw [hΔ, map_mul, map_pow]
        exact mul_ne_zero (pow_ne_zero _ hf) (hu.map f).ne_zero
      refine ⟨GlobalTheory.torusExtensionOfAbelian _ ⟨inferInstance, ?_, ?_, ?_⟩⟩
      · exact inferInstanceAs (Smooth (pullback.snd (U.ι ≫ toSpec W) _))
      · exact isProper_pullback_snd W U hU f hΔ'
      · exact inferInstanceAs (GeometricallyConnected (pullback.snd (U.ι ≫ toSpec W) _))
  · rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff]
    simp
end GlobalTheory.MultiplicativeReduction
