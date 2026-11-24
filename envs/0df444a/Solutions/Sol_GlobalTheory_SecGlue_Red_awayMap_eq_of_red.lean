-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.awayMap_eq_of_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:37:24.421266+00:00
-- url     : https://prove2.me/submissions/258cb736-1d90-461d-8346-5258a4318346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Theorems.Thm_GlobalTheory_SecGlue_Red_spMap_comp

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
theorem _root_.solution (π : R →+* R₀) {Y : Scheme.{0}} (a : R)
    (u v : Sp (Localization.Away a) ⟶ Y)
    (h : spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ u =
      spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ v) :
    spMap (Localization.awayMap π a) ≫ u = spMap (Localization.awayMap π a) ≫ v := by
  have H : ∀ x ∈ redI π (Localization.Away a), Localization.awayMap π a x = 0 := by
    intro x hx
    have hle : redI π (Localization.Away a) ≤ RingHom.ker (Localization.awayMap π a) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
        show (Localization.awayMap π a).comp (algebraMap R (Localization.Away a)) =
          (algebraMap R₀ (Localization.Away (π a))).comp π from IsLocalization.map_comp _,
        RingHom.comp_apply, RingHom.mem_ker.1 hy, map_zero]
    exact hle hx
  have e : Localization.awayMap π a =
      (Ideal.Quotient.lift _ (Localization.awayMap π a) H).comp (Ideal.Quotient.mk _) := by
    ext x; simp
  rw [e, spMap_comp, Category.assoc, Category.assoc, h]
end GlobalTheory.SecGlue.Red
