-- Prove2me | solution 1 for GlobalTheory.exists_isLieBasis_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:44.990794+00:00
-- url     : https://prove2.me/submissions/e4f11b08-e148-41f7-99db-a4f27216c289

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Theorems.Thm_GlobalTheory_LieBaseChange_bcVec_left_fst
import Theorems.Thm_GlobalTheory_LieBaseChange_isLieBasis_bcVec
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieBasis_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp IsTan
open TrivSqZeroExt (inl inr)
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (spMap)
namespace GlobalTheory
theorem _root_.solution (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R')
    (G : Over (Sp R)) (G' : Over (Sp R')) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) (hs : Smooth G.hom) (n : ℕ)
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) :
    ∃ v' : Fin n → (epsR R' ⟶ G'), IsLieBasis v' ∧
      ∀ i, (v' i).left ≫ φ = Geo.Tor.spMap (Chart.dualMapR f) ≫ (v i).left := by
  let _ := f.toAlgebra
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G (fB R R'))
  refine ⟨fun i => LieBaseChange.bcVec R' v i ≫ e.inv, isLieBasis_iso e ?_, fun i => ?_⟩
  · simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using
      LieBaseChange.isLieBasis_bcVec (R' := R') hv
  · rw [← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact LieBaseChange.bcVec_left_fst v i
end GlobalTheory
