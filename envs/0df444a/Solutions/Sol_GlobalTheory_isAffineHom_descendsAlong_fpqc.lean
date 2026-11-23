-- Prove2me | solution 1 for GlobalTheory.isAffineHom_descendsAlong_fpqc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:40.689517+00:00
-- url     : https://prove2.me/submissions/baf68c06-1a9c-4b4b-afdd-ba10e2e4c88e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Theorems.Thm_GlobalTheory_isAffine_of_isPullback_of_flat_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    MorphismProperty.DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_
  · rintro X Y f ⟨hl, hs⟩
    exact ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩
  · intro R S Y φ g hφ hfst
    obtain ⟨hs, hfl⟩ := hφ
    have : Surjective (Spec.map φ) := hs
    have : Flat (Spec.map φ) := hfl
    have : IsAffineHom (pullback.fst (Spec.map φ) g) := hfst
    have : IsAffine (Limits.pullback (Spec.map φ) g) :=
      isAffine_of_isAffineHom (pullback.fst (Spec.map φ) g)
    have : IsAffine Y :=
      _root_.GlobalTheory.isAffine_of_isPullback_of_flat_surjective (IsPullback.of_hasPullback (Spec.map φ) g).flip
    show IsAffineHom g
    infer_instance
end _root_.GlobalTheory
end GlobalTheory
