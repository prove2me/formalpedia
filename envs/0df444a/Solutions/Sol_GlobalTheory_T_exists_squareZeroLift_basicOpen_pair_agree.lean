-- Prove2me | solution 1 for GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:37:14.614736+00:00
-- url     : https://prove2.me/submissions/219d365d-fe31-4fb7-a5bc-fc8c195a9ec2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgreeStatement
import Theorems.Thm_GlobalTheory_SecGlue_exists_pair_lift_comb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  first | exact @GlobalTheory.SecGlue.exists_pair_lift_comb | exact GlobalTheory.SecGlue.exists_pair_lift_comb | (intros; apply GlobalTheory.SecGlue.exists_pair_lift_comb <;> assumption)
end _root_.GlobalTheory.T
