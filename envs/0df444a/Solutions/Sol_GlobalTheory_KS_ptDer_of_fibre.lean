-- Prove2me | solution 1 for GlobalTheory.KS.ptDer_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:37.963702+00:00
-- url     : https://prove2.me/submissions/dacd8f47-faec-4923-a00f-8c4991b21f79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase
import Theorems.Thm_GlobalTheory_KS_VertFib_epsPt_epsStr
import Theorems.Thm_GlobalTheory_KS_VertFib_top_le_of_epsPt
import Theorems.Thm_GlobalTheory_KS_VertFib_top_le_epsPt
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_app
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_congr
import Theorems.Thm_GlobalTheory_KS_VertFib_ringVal_constFn
import Theorems.Thm_GlobalTheory_KS_VertFib_snd_ringVal_const
import Theorems.Thm_GlobalTheory_KS_VertFib_comp_eq_const
import Theorems.Thm_GlobalTheory_T_germDerivation_iff_dualNumberPoint


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory.KS.VertFib
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (Y : Over (Sp ℂ)) (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y.left ⟶ X), IsPullback m Y.hom p (spMap x₀) → ∀ y : Sp ℂ ⟶ Y.left, y ≫ Y.hom = 𝟙 _ → (∀ δ, PtDer (y ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃ δ₀, PtDer y δ₀ ∧ (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) ∧ ∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ W f = δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f)) ∧ ∀ δ₀, PtDer y δ₀ → (∀ a, δ₀ ⊤ (constFn Y.hom ⊤ a) = 0) → (∀ W f, ⊤ ≤ (y ≫ m) ⁻¹ᵁ W → δ₀ (m ⁻¹ᵁ W) ((m.app W).hom f) = 0) → ∀ O f, ⊤ ≤ y ⁻¹ᵁ O → δ₀ O f = 0 := by
  intro Y R _ x₀ X p m hP y hy
  constructor
  · intro δ hδ h0
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint X (y ≫ m)).1 δ hδ
    have hvp : v ≫ p = epsStr ≫ spMap x₀ := by
      refine comp_eq_const x₀ p v ?_ fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rw [← Category.assoc, hv, Category.assoc, hP.w, ← Category.assoc, hy, Category.id_comp]
    have hw₁ := hP.lift_fst v epsStr hvp
    have hw₂ := hP.lift_snd v epsStr hvp
    generalize hP.lift v epsStr hvp = w at hw₁ hw₂
    have hwy : epsPt ≫ w = y := by
      apply hP.hom_ext
      · rw [Category.assoc, hw₁, hv]
      · rw [Category.assoc, hw₂, epsPt_epsStr, hy]
    obtain ⟨δ₀, hδ₀, hw⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint Y.left y).2 w hwy
    refine ⟨δ₀, hδ₀, fun a => ?_, fun W f hW => ?_⟩
    · refine (hw ⊤ le_top _).symm.trans ?_
      exact congrArg TrivSqZeroExt.snd (ringVal_constFn w Y.hom _ hw₂ le_top a)
    · have h1 : ⊤ ≤ v ⁻¹ᵁ W := top_le_of_epsPt v W (by rw [hv]; exact hW)
      have h2 : ⊤ ≤ (w ≫ m) ⁻¹ᵁ W := by rw [hw₁]; exact h1
      refine (hvδ W h1 f).symm.trans (Eq.trans ?_ (hw (m ⁻¹ᵁ W) h2 _))
      exact congrArg TrivSqZeroExt.snd
        ((ringVal_congr hw₁.symm W h1 h2 f).trans (ringVal_app w m W h2 h2 f).symm)
  · intro δ₀ hδ₀ h0 hm O f hO
    obtain ⟨v, ⟨hv, hvδ⟩, -⟩ := (GlobalTheory.T.germDerivation_iff_dualNumberPoint Y.left y).1 δ₀ hδ₀
    have hvp : v ≫ Y.hom = epsStr := by
      have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
      have := comp_eq_const (RingHom.id ℂ) Y.hom v (by rw [← Category.assoc, hv, hy, hid])
        fun r => (hvδ ⊤ le_top _).trans (h0 r)
      rwa [hid, Category.comp_id] at this
    have hz : PtDer (y ≫ m) (fun _ _ => 0) := ⟨by simp, by simp, by simp⟩
    have hvm : v ≫ m = epsStr ≫ y ≫ m := by
      refine ((GlobalTheory.T.germDerivation_iff_dualNumberPoint X (y ≫ m)).1 _ hz).unique ⟨?_, fun W h g => ?_⟩ ⟨?_, fun W h g => ?_⟩
      · rw [← Category.assoc, hv]
      · have hW : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W := by
          have := top_le_epsPt _ W h
          rwa [← Category.assoc, hv] at this
        refine Eq.trans ?_ ((hvδ (m ⁻¹ᵁ W) h _).trans (hm W g hW))
        exact congrArg TrivSqZeroExt.snd (ringVal_app v m W h h g).symm
      · rw [← Category.assoc, epsPt_epsStr, Category.id_comp]
      · exact snd_ringVal_const (y ≫ m) W h g
    have hvc : v = epsStr ≫ y := by
      apply hP.hom_ext
      · rw [hvm, Category.assoc]
      · rw [hvp, Category.assoc, hy, Category.comp_id]
    have h1 : ⊤ ≤ v ⁻¹ᵁ O := top_le_of_epsPt v O (by rw [hv]; exact hO)
    refine (hvδ O h1 f).symm.trans ?_
    have h2 : ⊤ ≤ (epsStr ≫ y) ⁻¹ᵁ O := by rw [← hvc]; exact h1
    exact (congrArg TrivSqZeroExt.snd (ringVal_congr hvc O h1 h2 f)).trans (snd_ringVal_const y O h2 f)
end GlobalTheory.KS
