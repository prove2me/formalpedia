-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.isRed_of_away
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:22.483736+00:00
-- url     : https://prove2.me/submissions/38c7ffea-f1b4-4c58-ad3a-1befff1c8632

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Theorems.Thm_GlobalTheory_SecGlue_Red_spMap_comp
import Theorems.Thm_GlobalTheory_SecGlue_Red_away_ext
import Theorems.Thm_GlobalTheory_SecGlue_Red_isUnit_of_away
import Theorems.Thm_GlobalTheory_SecGlue_Red_redPsi_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
variable {R R₀ : Type} [CommRing R] [CommRing R₀]
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) (a : R) (u : Sp (Localization.Away a) ⟶ Y)
    (hu : spMap (Localization.awayMap π a) ≫ u =
      spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀)
    (S : Type) [CommRing S] [Algebra R S] (ρ : Localization.Away a →+* S)
    (hρ : ρ.comp (algebraMap R _) = algebraMap R S) : IsRed π hπ g₀ S (spMap ρ ≫ u) := by
  have hunit : IsUnit (redPsi π hπ S (π a)) := by
    have e : redPsi π hπ S (π a) = Ideal.Quotient.mk (redI π S) (algebraMap R S a) := by
      rw [← RingHom.comp_apply (redPsi π hπ S) π, redPsi_comp, RingHom.comp_apply]
    rw [e]; exact (isUnit_of_away a ρ hρ).map _
  let lam := IsLocalization.Away.lift (S := Localization.Away (π a)) (π a) hunit
  have key : (Ideal.Quotient.mk (redI π S)).comp ρ = lam.comp (Localization.awayMap π a) := by
    apply away_ext a
    rw [RingHom.comp_assoc, hρ, RingHom.comp_assoc]
    have e1 : (Localization.awayMap π a).comp (algebraMap R (Localization.Away a)) =
        (algebraMap R₀ (Localization.Away (π a))).comp π := IsLocalization.map_comp _
    rw [e1, ← RingHom.comp_assoc, IsLocalization.Away.lift_comp, redPsi_comp]
  unfold IsRed
  rw [← Category.assoc, ← spMap_comp, key, spMap_comp, Category.assoc, hu, ← Category.assoc,
    ← spMap_comp, IsLocalization.Away.lift_comp]
end GlobalTheory.SecGlue.Red
