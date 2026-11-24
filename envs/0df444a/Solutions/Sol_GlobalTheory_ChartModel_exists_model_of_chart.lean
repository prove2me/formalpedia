-- Prove2me | solution 1 for GlobalTheory.ChartModel.exists_model_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:00:06.982155+00:00
-- url     : https://prove2.me/submissions/9b515476-8229-4495-a4d6-85a5b922abe7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChart
import Theorems.Thm_GlobalTheory_ChartModel_exists_glue_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.ChartModel
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.ChartModel
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∀ (C : Type) [CommRing C] [Algebra R C], Algebra.Smooth R C → ∀ u : Sp (TensorProduct R K C) ⟶ A.left, IsOpenImmersion u → u ≫ A.hom = spMap (algebraMap K (TensorProduct R K C)) → ∃ (M : Model R A) (g : Sp C ⟶ M.Y.left), IsOpenImmersion g ∧ g ≫ M.Y.hom = spMap (algebraMap R C) ∧ spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom ≫ g = u ≫ M.j ∧ M.sp ⊆ Set.range g := by
  intro R K _ _ _ _ _ _ A hA hs hq C _ _ hC u hu hua
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hloc : IsLocalization.Away π K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (S := K) (M := Submonoid.powers π) (nonZeroDivisors R)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) fun r hr => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hr) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
  have hi : IsOpenImmersion (spMap (algebraMap R K)) := IsOpenImmersion.of_isLocalization π
  have hW : IsPullback (spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom)
      (spMap (algebraMap K (TensorProduct R K C))) (spMap (algebraMap R C)) (spMap (algebraMap R K)) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K C)).flip
  have : Smooth (spMap (algebraMap R C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hC
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨Y, f, g, j, hg, hj, hgf, hp, h1, h2, h3, h4⟩ :=
    exists_glue_chart (spMap (algebraMap R K)) A.hom (spMap (algebraMap R C)) hW u hua
  refine ⟨⟨Over.mk f, Over.isoMk hj.isoPullback.symm hj.isoPullback_inv_snd, h1, h2,
    (inferInstance : QuasiCompact f)⟩, g, hg, hgf, ?_, fun y hy => h4 y ?_⟩
  · exact hp.trans (congrArg (u ≫ ·) hj.isoPullback_hom_fst.symm)
  · rintro ⟨t, ht⟩
    have ht' : spMap (algebraMap R K) t = IsLocalRing.closedPoint R := ht.trans hy
    have h5 : π ∈ (spMap (algebraMap R K) t).asIdeal := by
      rw [ht']; exact hπ.not_isUnit
    exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show algebraMap R K π ∈ t.asIdeal from h5)
      (IsLocalization.Away.algebraMap_isUnit π))
end GlobalTheory.ChartModel
