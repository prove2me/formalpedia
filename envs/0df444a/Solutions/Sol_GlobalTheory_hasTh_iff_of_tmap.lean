-- Prove2me | solution 1 for GlobalTheory.hasTh_iff_of_tmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:36:45.914206+00:00
-- url     : https://prove2.me/submissions/6857c866-02a7-468f-8404-ea784cda6efd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_GlobalTheory_ThetaPtUp_isThetaPt_iff
import Theorems.Thm_GlobalTheory_ThetaPtUp_lab_pow
import Theorems.Thm_GlobalTheory_ThetaPtUp_lab_over
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
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory
theorem _root_.solution : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (S' : Scheme.{0}) (s' : S' ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s') (f : S' ⟶ S) (R : Type) [CommRing R] (x : Sp R ⟶ S') (v : Ix g (N' ^ 2) → R), TMap t' t f → (t'.HasTh x v ↔ t.HasTh (x ≫ f) v) := by
  intro o _ g N' J b S s t S' s' t' f R _ x v ⟨φ, hp, hw, hpt, _⟩
  refine GlobalTheory.ThetaPtUp.isThetaPt_iff (P₀ := t.pol) (P := t'.pol) (T := Over.mk x) hp hw (fun a => ?_) (fun a => ?_) _
  · exact (Category.assoc x f _).trans ((congrArg (x ≫ ·) (GlobalTheory.ThetaPtUp.lab_over hp hpt a)).trans
      (Category.assoc _ _ _).symm)
  · exact (MonObj.comp_pow _ _ _).symm.trans
      ((congrArg (_ ≫ ·) (GlobalTheory.ThetaPtUp.lab_pow t' a)).trans (MonObj.comp_one _))
end GlobalTheory
