-- Prove2me | solution 1 for GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:22.13229+00:00
-- url     : https://prove2.me/submissions/3efe1ceb-11eb-4e0c-bcbb-da7b9bae04e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_SchemeDominantSpecMap_isSchemeTheoreticallyDominant_specMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
namespace GlobalTheory.ExtUnique
theorem _root_.solution {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  first
  | exact @_root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap
  | exact _root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap
  | (apply _root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap <;> assumption)
  | (intros; apply _root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap ..)
end GlobalTheory.ExtUnique
