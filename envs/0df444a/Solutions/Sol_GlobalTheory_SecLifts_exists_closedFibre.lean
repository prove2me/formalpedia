-- Prove2me | solution 1 for GlobalTheory.SecLifts.exists_closedFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:52:13.669289+00:00
-- url     : https://prove2.me/submissions/02e6144c-882f-4af9-a8c7-2d196de1cc16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompatibleSections
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_pgen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff


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
open GlobalTheory GlobalTheory.SecLifts
namespace GlobalTheory.SecLifts
theorem _root_.solution (V : Type) [CommRing V] (I : Ideal V)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V I e))
    (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
    (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (e : ℕ) :
    ∃ j : (Y 0).left ⟶ (Y (e + 1)).left,
      IsPullback j (Y 0).hom (Y (e + 1)).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (by omega) : I ^ (e + 1 + 1) ≤ I ^ (0 + 1))))) ∧
      ∃ w : LB.Iso (N 0) ((N (e + 1)).pull j), w.IsGen := by
  induction e with
  | zero => exact ⟨β 0, hβ 0, v 0, (hN 0).2⟩
  | succ e ih =>
    obtain ⟨j, hj, w, hw⟩ := ih
    have g := (isGen_iff _).1 (hN (e + 1)).2
    have g' := (isGen_iff _).1 hw
    obtain ⟨w'', T⟩ := exists_comp (hN (e + 1)).1 (v (e + 1)) w g g' (hN (e + 1 + 1)).1 (hN 0).1
    refine ⟨j ≫ β (e + 1), ?_, w'', (isGen_iff _).2 (T.pgen_comp (hN (e + 1)).1 g g')⟩
    have h := hj.paste_horiz (hβ (e + 1))
    rw [thickTrans, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp] at h
    exact h
end GlobalTheory.SecLifts
