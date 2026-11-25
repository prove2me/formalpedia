-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_of_etale_of_mono_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:33.481578+00:00
-- url     : https://prove2.me/submissions/3ce67c8b-5010-47d3-908d-c29a91cb7f6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
import Theorems.Thm_GlobalTheory_isDominant_pullback_fst_of_isOpenMap
import Theorems.Thm_GlobalTheory_isNormalScheme_of_smooth


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X U W : Scheme.{0}}
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsDominant j] (q : W ⟶ X) [Etale q] [IsSeparated q]
    [Mono (pullback.snd q j)] : IsOpenImmersion q := by
  let r : pullback q q ⟶ X := pullback.fst q q ≫ q
  have := isNormalScheme_of_smooth r
  have := isDominant_pullback_fst_of_isOpenMap j r r.isOpenMap
  have h : pullback.lift (f := q) (g := j) (pullback.fst r j ≫ pullback.fst q q) (pullback.snd r j)
        (by rw [Category.assoc]; exact pullback.condition) =
      pullback.lift (pullback.fst r j ≫ pullback.snd q q) (pullback.snd r j)
        (by rw [Category.assoc, ← pullback.condition (f := q) (g := q)]
            exact pullback.condition) := by
    rw [← cancel_mono (pullback.snd q j), pullback.lift_snd, pullback.lift_snd]
  have h' : pullback.fst r j ≫ pullback.fst q q = pullback.fst r j ≫ pullback.snd q q := by
    simpa only [pullback.lift_fst] using congrArg (· ≫ pullback.fst q j) h
  have he : pullback.fst q q = pullback.snd q q :=
    ext_of_isDominant_of_isSeparated q pullback.condition _ h'
  have : Mono q := ⟨fun a b hab => by
    rw [← pullback.lift_fst a b hab, he, pullback.lift_snd]⟩
  exact IsOpenImmersion.of_flat_of_mono q
end GlobalTheory
