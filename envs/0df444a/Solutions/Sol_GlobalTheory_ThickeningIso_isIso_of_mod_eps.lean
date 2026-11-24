-- Prove2me | solution 1 for GlobalTheory.ThickeningIso.isIso_of_mod_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:41.690162+00:00
-- url     : https://prove2.me/submissions/efdf0119-e2ec-47bb-a5d5-e58e6c83587e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoThickeningMapOfModEps
import Theorems.Thm_GlobalTheory_ThickeningIso_isIso_of_isAffine
import Theorems.Thm_GlobalTheory_IsNormalScheme_iff_of_iSup_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.ThickeningIso
namespace GlobalTheory.ThickeningIso
theorem _root_.solution : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  rintro Y Y' Z' q _ π' j _ e h h' hf rfl rfl
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
    (iSup_affineOpens_eq_top Z')).mpr fun U => ?_
  have : IsAffine U.1 := U.2
  have p1 := (isPullback_morphismRestrict j (e ⁻¹ᵁ U.1))
  have p2 := (isPullback_morphismRestrict e U.1)
  have hw : e ∣_ U.1 ≫ U.1.ι ≫ π' = (e ⁻¹ᵁ U.1).ι ≫ e ≫ π' := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  refine isIso_of_isAffine (K := ℂ) (π' := U.1.ι ≫ π') (j := j ∣_ (e ⁻¹ᵁ U.1))
    (q := (j ⁻¹ᵁ (e ⁻¹ᵁ U.1)).ι ≫ q) ?_ ?_ ?_
  · rw [hw]
    exact p1.paste_vert h
  · exact (p1.paste_horiz p2).paste_vert h'
  · rw [hw]; infer_instance
end GlobalTheory.ThickeningIso
