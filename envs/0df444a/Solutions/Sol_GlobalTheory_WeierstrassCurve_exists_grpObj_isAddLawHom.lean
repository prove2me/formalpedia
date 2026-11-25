-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.exists_grpObj_isAddLawHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:03:11.11538+00:00
-- url     : https://prove2.me/submissions/f224124e-ab41-48a6-9307-b00aa7619cc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HomExtOfLocalRingPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsEqPtHomOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_ExistsGrpObjIsAddLawHom
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isAddLawHom_mul
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ptHom_grpObj_inv

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)
variable [W.IsElliptic]
omit [W.IsElliptic]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (hΔ : IsUnit W.Δ) :
    ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ η[schemeOver W].left = zero W ∧
      IsAddLawHom W μ[schemeOver W] ∧
      ∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P),
        ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P),
          ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN :=
  haveI : W.IsElliptic := ⟨hΔ⟩
  ⟨grpObj W, isCommMonObj W, one_left W, isAddLawHom_mul W,
    fun _ _ ρ P hP => ⟨hP.neg, ptHom_grpObj_inv W ρ P hP⟩⟩
end GlobalTheory.WeierstrassCurve
