-- Prove2me | solution 1 for GlobalTheory.SS.HtForm.exists_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:14:18.344619+00:00
-- url     : https://prove2.me/submissions/c222304a-d13d-4d6c-96d2-74d17183ea1b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesOfFgFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.HtForm
namespace GlobalTheory.SS.HtForm
theorem _root_.solution {k : Type} [Field k] (B : Over (Sp k)) [IsIntegral B.left] [LocallyOfFiniteType B.hom] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra k K), (⊤ : IntermediateField k K).FG ∧
      ∃ P : Over.mk (spMap (algebraMap k K)) ⟶ B, IsDominant P.left := by
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let A : Type := Γ(B.left, U)
  letI : Algebra k A := (cstK B U).toAlgebra
  have hft : Algebra.FiniteType k A :=
    (B.hom.finiteType_appLE (isAffineOpen_top _) hU le_top).comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  let K := FractionRing A
  have h1 : Algebra.EssFiniteType A K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors A)
  have h2 : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k A K
  refine ⟨K, inferInstance, inferInstance, IntermediateField.fg_top_iff.2 h2,
    Over.homMk (spMap (algebraMap A K) ≫ hU.fromSpec) ?_, ?_⟩
  · have h := IsAffineOpen.SpecMap_appLE_fromSpec B.hom (isAffineOpen_top _) hU le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    show (spMap (algebraMap A K) ≫ hU.fromSpec) ≫ B.hom = spMap (algebraMap k K)
    rw [Category.assoc, ← h, IsScalarTower.algebraMap_eq k A K, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  · have : IsDominant (spMap (algebraMap A K)) := by
      rw [isDominant_iff]
      show DenseRange (PrimeSpectrum.comap (algebraMap A K))
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective A K)]
      exact bot_le
    have : IsDominant hU.fromSpec := by
      rw [isDominant_iff, DenseRange, hU.range_fromSpec]
      exact U.isOpen.dense ⟨x, hxU⟩
    show IsDominant (spMap (algebraMap A K) ≫ hU.fromSpec)
    infer_instance
end GlobalTheory.SS.HtForm
