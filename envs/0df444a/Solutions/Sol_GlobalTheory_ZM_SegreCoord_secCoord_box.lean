-- Prove2me | solution 1 for GlobalTheory.ZM.SegreCoord.secCoord_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:19:40.731602+00:00
-- url     : https://prove2.me/submissions/4349d97d-712c-4649-98a4-9c961bdc65a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SegreCoordinates
import Theorems.Thm_GlobalTheory_ZM_SegreCoord_le_fst
import Theorems.Thm_GlobalTheory_ZM_SegreCoord_le_snd
import Theorems.Thm_GlobalTheory_ZM_SegreCoord_appLE_ap
import Theorems.Thm_GlobalTheory_ZM_RepBC_isGen_val
import Theorems.Thm_GlobalTheory_ZM_RepBC_rr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.SegreCoord
open GlobalTheory.ZM.RepBC GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
namespace GlobalTheory.ZM.SegreCoord
theorem _root_.solution {σ₁ σ₂ : Type} (s : σ₁ → H.Sec) (t : σ₂ → K.Sec) {T : Type} [CommRing T] (x : Sp T ⟶ P)
    (v₁ : σ₁ → T) (v₂ : σ₂ → T) (h₁ : SecCoord H s (x ≫ p) v₁) (h₂ : SecCoord K t (x ≫ q) v₂) :
    SecCoord (box p q H K) (fun i : σ₁ × σ₂ => boxSec p q (s i.1) (t i.2)) x (fun i => v₁ i.1 * v₂ i.2) := by
  obtain ⟨τ₁, g₁, c₁⟩ := h₁
  obtain ⟨τ₂, g₂, c₂⟩ := h₂
  refine ⟨⟨fun J => res (le_fst p q x J) (τ₁.s _) * res (le_snd p q x J) (τ₂.s _)⟩,
    (isGen_val _).2 fun J J' => ?_, fun i J e => ?_⟩
  · have e₁ := inf_le_inf (le_fst p q x J) (le_fst p q x J')
    have e₂ := inf_le_inf (le_snd p q x J) (le_snd p q x J')
    have a₁ := congrArg (resG (Sp T) e₁) ((isGen_val τ₁).1 g₁ _ _)
    have a₂ := congrArg (resG (Sp T) e₂) ((isGen_val τ₂).1 g₂ _ _)
    rw [map_mul, rr, rr, pull_g _ _ _ _ (pull_inf_le _ _ _ _), r_appLE] at a₁ a₂
    erw [pull_g (box p q H K) x J J' (pull_inf_le _ _ _ _)]
    have l : ∀ (J : PUnit → (box p q H K).ι) (W : (Sp T).Opens) (h : W ≤ ((box p q H K).pull x).U J),
        resG (Sp T) h (res (le_fst p q x J) (τ₁.s _) * res (le_snd p q x J) (τ₂.s _)).val =
        resG (Sp T) (h.trans (le_fst p q x J)) (τ₁.s _).val * resG (Sp T) (h.trans (le_snd p q x J)) (τ₂.s _).val := by
      intro J W h
      rw [Units.val_mul, map_mul]
      exact congrArg₂ (· * ·) (rr _ _ _) (rr _ _ _)
    refine (l J _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (appLE_ap p q x _ _ _
      (e₁.trans (pull_inf_le _ _ _ _)) (e₂.trans (pull_inf_le _ _ _ _)) _ _) (l J' _ _)).symm)
    exact (congrArg₂ (· * ·) a₁ a₂).trans (mul_mul_mul_comm _ _ _ _)
  · have a₁ := congrArg (resG (Sp T) (le_fst p q x J)) (c₁ i.1 _ (pull_le _ _ _))
    have a₂ := congrArg (resG (Sp T) (le_snd p q x J)) (c₂ i.2 _ (pull_le _ _ _))
    rw [map_mul, rr, r_appLE] at a₁ a₂
    refine (appLE_ap p q x _ _ e ((le_fst p q x J).trans (pull_le _ _ _))
      ((le_snd p q x J).trans (pull_le _ _ _)) _ _).trans ?_
    refine (congrArg₂ (· * ·) a₁ a₂).trans ((mul_mul_mul_comm _ _ _ _).trans ?_)
    rw [map_mul, map_mul]
    rfl
end GlobalTheory.ZM.SegreCoord
