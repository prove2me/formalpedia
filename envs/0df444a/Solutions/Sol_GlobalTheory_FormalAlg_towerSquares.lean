-- Prove2me | solution 1 for GlobalTheory.FormalAlg.towerSquares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:34.087676+00:00
-- url     : https://prove2.me/submissions/7de7ef36-c646-4eca-86b8-5fb6d45a5be8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TowerSquares
import Theorems.Thm_GlobalTheory_FormalAlg_TowerSq_isPullback_id_of_mono
import Theorems.Thm_P2M_GlobalTheory_FormalAlg_TowerSq_mono_thick__4223908ece3e
import Theorems.Thm_P2M_GlobalTheory_FormalAlg_TowerSq_thickTrans_thick__1d9f45897eeb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option autoImplicit false
noncomputable section
open GlobalTheory.FormalAlg.TowerSq
namespace GlobalTheory.FormalAlg
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsPullback (β e) (Y e).hom ((Y (e + 1)).hom ≫ thick R I (e + 1)) (thick R I e)) ∧ ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ e, IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) := by
  intro R _ I Y β hβ
  refine ⟨fun e => ?_, fun γ h0 hγ e => ?_⟩
  · have := mono_thick' R I (e + 1)
    have h := (hβ e).paste_vert (isPullback_id_of_mono (thickTrans R I e) (thick R I (e + 1)))
    rw [thickTrans_thick', Category.comp_id] at h
    exact h
  · have hc : ∀ e, ∃ u : Spec (CommRingCat.of (R ⧸ I ^ (0 + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
        u ≫ thick R I e = thick R I 0 ∧ IsPullback (γ e) (Y 0).hom (Y e).hom u := by
      intro e
      induction e with
      | zero =>
        rw [h0]
        exact ⟨𝟙 _, Category.id_comp _, IsPullback.of_horiz_isIso ⟨by simp⟩⟩
      | succ e ih =>
        obtain ⟨u, hu, hp⟩ := ih
        refine ⟨u ≫ thickTrans R I e, by rw [Category.assoc, thickTrans_thick', hu], ?_⟩
        rw [← hγ e]
        exact hp.paste_horiz (hβ e)
    obtain ⟨u, hu, hp⟩ := hc e
    have := mono_thick' R I e
    have h := hp.paste_vert (isPullback_id_of_mono u (thick R I e))
    rw [hu, Category.comp_id] at h
    exact h
end GlobalTheory.FormalAlg
