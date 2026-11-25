-- Prove2me | solution 1 for GlobalTheory.ZM.RepBC.secCoord_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:23:29.100376+00:00
-- url     : https://prove2.me/submissions/b89a0662-fde0-4747-ad41-faca7a140d1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Theorems.Thm_GlobalTheory_ZM_RepBC_rr
import Theorems.Thm_GlobalTheory_ZM_RepBC_appLE_appLE
import Theorems.Thm_GlobalTheory_ZM_RepBC_isGen_val
import Theorems.Thm_P2M_GlobalTheory_ZM_RepBC_le__aa335c156472
import Theorems.Thm_P2M_GlobalTheory_ZM_RepBC_le__8683792fd0d2
import Theorems.Thm_GlobalTheory_ZM_RepBC_pullpull_g
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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.ZM.RepBC
theorem _root_.solution {σ : Type} (M : LB X) (th : σ → M.Sec) (π : Y ⟶ X) {T : Type} [CommRing T] (x : Sp T ⟶ Y)
    (v : σ → T) : SecCoord (M.pull π) (fun i => secPull M π (th i)) x v ↔ SecCoord M th (x ≫ π) v := by
  constructor
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun j => res (le₂ M π x j) (τ.s fun _ => j)⟩, (isGen_val _).2 fun j j' => ?_, fun i j e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₂ M π x j) (le₂ M π x j')))
        ((isGen_val τ).1 hτ (fun _ => j) (fun _ => j'))
      rw [map_mul] at h0
      erw [pullpull_g M π x (fun _ => j) (fun _ => j') ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _)),
        rr, r_appLE] at h0
      erw [pull_g M (x ≫ π) j j' (pull_inf_le _ _ _ _)]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₂ M π x j') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₂ M π x j)) (h i (fun _ => j) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ _ e _).symm.trans h0
  · rintro ⟨τ, hτ, h⟩
    refine ⟨⟨fun J => res (le₁ M π x J) (τ.s (J PUnit.unit))⟩, (isGen_val _).2 fun J J' => ?_, fun i J e => ?_⟩
    · have h0 := congrArg (resG (Sp T) (inf_le_inf (le₁ M π x J) (le₁ M π x J')))
        ((isGen_val τ).1 hτ (J PUnit.unit) (J' PUnit.unit))
      rw [map_mul] at h0
      erw [pull_g M (x ≫ π) (J PUnit.unit) (J' PUnit.unit) (pull_inf_le _ _ _ _), rr, r_appLE] at h0
      erw [pullpull_g M π x J J' ((inf_le_inf (le₁ M π x _) (le₁ M π x _)).trans (pull_inf_le M (x ≫ π) _ _))]
      exact (rr _ _ _).trans (h0.trans (congrArg _ ((rr _ _ _).trans (rr (le₁ M π x J') inf_le_right _).symm)))
    · have h0 := congrArg (resG (Sp T) (le₁ M π x J)) (h i (J PUnit.unit) (pull_le _ _ _))
      rw [map_mul, rr, r_appLE] at h0
      exact (appLE_appLE x π _ e _ _).trans h0
end GlobalTheory.ZM.RepBC
