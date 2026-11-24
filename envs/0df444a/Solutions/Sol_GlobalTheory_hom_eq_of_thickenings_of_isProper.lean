-- Prove2me | solution 1 for GlobalTheory.hom_eq_of_thickenings_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:08.384598+00:00
-- url     : https://prove2.me/submissions/e7ca054a-0bee-40fc-8ca2-d0a89feb0e88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_thickenings_of_isProper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y Z : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] [IsSeparated Z.hom] (f g : Y ⟶ Z), (∀ e, (fstG I e Y).left ≫ f.left = (fstG I e Y).left ≫ g.left) → f = g := by
  intro R _ _ _ I hI Y Z _ _ f g hfg
  have hf : f.left ≫ Z.hom = Y.hom := Over.w f
  have hg : g.left ≫ Z.hom = Y.hom := Over.w g
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.left ⟶ pullback Z.hom Z.hom,
      φ = pullback.lift f.left g.left (hf.trans hg.symm) := ⟨_, rfl⟩
  have hφ1 : φ ≫ pullback.fst Z.hom Z.hom = f.left := by rw [hφ, pullback.lift_fst]
  have hφ2 : φ ≫ pullback.snd Z.hom Z.hom = g.left := by rw [hφ, pullback.lift_snd]
  have hι : IsIso (pullback.fst φ (pullback.diagonal Z.hom)) := by
    refine isIso_of_isClosedImmersion_of_thickenings_of_isProper I hI Y _ fun n => ?_
    refine ⟨pullback.lift (fstG I n Y).left ((fstG I n Y).left ≫ f.left) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [hφ1]
    · simp [hφ2, hfg n]
  have key : φ = inv (pullback.fst φ (pullback.diagonal Z.hom)) ≫
      pullback.snd φ (pullback.diagonal Z.hom) ≫ pullback.diagonal Z.hom := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  apply Over.OverMorphism.ext
  rw [← hφ1, ← hφ2, key]
  simp
end GlobalTheory
