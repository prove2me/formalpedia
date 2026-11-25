-- Prove2me | solution 1 for GlobalTheory.Models.above_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:16.634048+00:00
-- url     : https://prove2.me/submissions/4e36458f-b125-4394-867b-e9edc87aa2c0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsFiniteLiftComp
import Theorems.Thm_GlobalTheory_Models_isFinite_lift_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabComp


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
open GlobalTheory.Models
open GlobalTheory GlobalTheory.Models
namespace GlobalTheory.Models
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (r : U' ⟶ U) (ν : SABMap t' t r) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (ν'' : SABMap t'' t (r' ≫ r)) (a : C'.Above C b r ν) (a' : C''.Above C' b' r' ν'), ν''.φ = ν'.φ ≫ ν.φ → ∃ a'' : C''.Above C (b'.comp b) (r' ≫ r) ν'', a''.π = a'.π ≫ a.π ∧ a''.mu.φ = a'.mu.φ ≫ a.mu.φ := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' r ν r' ν' ν'' a a' hν
  obtain ⟨mu, hmu⟩ := sabComp pullCubComp E H _ _ _ C.t C'.t C''.t a.π a'.π a.mu a'.mu
  have hsp : spMap (b'.comp b) = spMap b' ≫ spMap b := by
    unfold spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hover : (a'.π ≫ a.π) ≫ C.s = C''.s ≫ spMap (b'.comp b) := by
    rw [hsp, Category.assoc, a.π_over, ← Category.assoc, a'.π_over, Category.assoc]
  refine ⟨⟨a'.π ≫ a.π, hover, isFinite_lift_comp hsp a.π_over a'.π_over hover a.fin a'.fin, mu, ?_, ?_⟩, rfl, hmu⟩
  · rw [← Category.assoc, a'.j_comm, Category.assoc, a.j_comm, Category.assoc]
  · rw [hmu, hν, ← Category.assoc, a'.φ_comm, Category.assoc, a.φ_comm, Category.assoc]
end GlobalTheory.Models
