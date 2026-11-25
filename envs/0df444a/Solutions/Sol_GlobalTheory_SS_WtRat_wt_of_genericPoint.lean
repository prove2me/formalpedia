-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.wt_of_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:20:39.761328+00:00
-- url     : https://prove2.me/submissions/fa68a52e-0f62-4d43-8415-2b7d3636bd7b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints
import Theorems.Thm_GlobalTheory_SS_WtRat_appLE_wtDefect
import Theorems.Thm_GlobalTheory_SS_WtRat_eq_zero_of_rationalPoints
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_top
import Theorems.Thm_GlobalTheory_SS_WtRat_isUnit_ev
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_splitTorus_properties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
namespace GlobalTheory.SS.WtRat
theorem _root_.solution :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  intro k _ _ G _ hG X _ _ _ i F _ s g hg V u χ H
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp k)).1 X
  have : Smooth (splitTorus (Sp k) X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ X) _
  have : Smooth (splitTorus (Sp k) X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp k) X).hom G.hom ≫
      (splitTorus (Sp k) X).hom))
  have hact : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left = ((t ≫ i) * y).left := by
    intro Z t y
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hsnd : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (snd (splitTorus (Sp k) X) G).left = y.left := by
    intro Z t y
    rw [← Over.comp_left, lift_snd]
  have hfst : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (fst (splitTorus (Sp k) X) G).left = t.left := by
    intro Z t y
    rw [← Over.comp_left, lift_fst]
  have hd : wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val = 0 := by
    refine eq_zero_of_rationalPoints _ fun z x hx => ?_
    set d := wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val with hdd
    let t := z ≫ fst _ _
    let m : G ⟶ splitTorus (Sp k) X ⊗ G := lift (toUnit G ≫ t) (𝟙 G)
    have hz : (z ≫ snd _ _) ≫ m = z := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, t, Category.assoc, lift_fst]
        rw [← Category.assoc (snd _ _), ← Category.assoc z, toUnit_unique (z ≫ _) (𝟙 _),
          Category.id_comp]
      · simp [m]
    have hgm : g ≫ m = lift (toUnit (Over.mk s) ≫ t) g := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, Category.assoc, lift_fst]
        rw [← Category.assoc, toUnit_unique (g ≫ _) (toUnit _)]
      · simp [m]
    have h0 := hg (m.left ⁻¹ᵁ (splitTorus (Sp k) X ⊗ G).left.basicOpen d)
      ⟨(z ≫ snd _ _).left x, by
        have : m.left ((z ≫ snd _ _).left x) = z.left x := congrArg (fun q => q.left x) hz
        show m.left ((z ≫ snd _ _).left x) ∈ (splitTorus (Sp k) X ⊗ G).left.basicOpen d
        rw [this]; exact hx⟩
    have h1 : ⊤ ≤ (lift (toUnit (Over.mk s) ≫ t) g).left ⁻¹ᵁ
        (splitTorus (Sp k) X ⊗ G).left.basicOpen d := by
      rw [← hgm]; exact h0
    have h2 := h1.trans ((lift (toUnit (Over.mk s) ≫ t) g).left.preimage_mono
      ((splitTorus (Sp k) X ⊗ G).left.basicOpen_le d))
    have h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V := by
      rw [← hact]; exact fun y hy => (h2 hy).1
    have h₂ : ⊤ ≤ g.left ⁻¹ᵁ V := by
      rw [← hsnd (toUnit (Over.mk s) ≫ t)]; exact fun y hy => (h2 hy).2
    have hu := isUnit_ev (R := F) _ _ h2 d h1
    have hv := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact _ _) (hsnd _ _) (hfst _ _) h2 h₁ h₂)
    have hH := (H t h₁ h₂).trans (congrArg (· * ev (R := F) g.left V h₂ u)
      (ev_top (R := F) (toUnit (Over.mk s) ≫ t).left le_top (charUnit (Sp k) X χ).val))
    refine hu.ne_zero (hv.trans ?_)
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (hH.trans (map_mul _ _ _).symm))
  intro Z t y h₁ h₂
  have h : ⊤ ≤ (lift t y).left ⁻¹ᵁ (((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left ⁻¹ᵁ V ⊓
      (snd (splitTorus (Sp k) X) G).left ⁻¹ᵁ V) := by
    rw [← hact] at h₁
    rw [← hsnd t] at h₂
    exact fun w hw => ⟨h₁ hw, h₂ hw⟩
  have hv := appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact t y) (hsnd t y) (hfst t y)
    h h₁ h₂
  rw [hd, map_zero] at hv
  exact sub_eq_zero.1 hv.symm
end GlobalTheory.SS.WtRat
