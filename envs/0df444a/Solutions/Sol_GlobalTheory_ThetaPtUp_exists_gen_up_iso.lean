-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.exists_gen_up_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:53.810829+00:00
-- url     : https://prove2.me/submissions/ff684eee-d6d3-4b0f-a67a-0af1131ee626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_GlobalTheory_VVRank_exists_gen_pullTo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
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
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ThetaPtUp
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ThetaPtMove
namespace GlobalTheory.ThetaPtUp
theorem _root_.solution {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} {χ : Y ⟶ Y'}
    (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (h₁ : h ≫ χ = 𝟙 _) (h₂ : χ ≫ h = 𝟙 _)
    (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L z J → Good L' z J' →
        val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' a ha
  obtain ⟨u, hu, hu'⟩ := VVRank.exists_gen_pullTo (φ' := φ) t ht χ fun k => by
    rw [hψ, ← Category.assoc, h₂, Category.id_comp]
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => (hu' _ _ _ _ hJ).trans ?_⟩
  rw [Category.assoc, h₁, Category.comp_id]
  refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans ?_
  congr 1
end GlobalTheory.ThetaPtUp
