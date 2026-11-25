-- Prove2me | solution 1 for GlobalTheory.ProjCone.awayEquiv_dehom_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:23.336869+00:00
-- url     : https://prove2.me/submissions/b52d1681-aa93-4658-a01a-ca19ddfe3bb3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Theorems.Thm_GlobalTheory_ProjCone_awayEquiv_apply
import Theorems.Thm_ReciprocityTheory_AnForm_R_toSpecZero_appLE_basicOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.ProjCone
variable {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) [GradedAlgebra (quotGrading I)]
namespace GlobalTheory.ProjCone
theorem _root_.solution (c : σ) (a : ℂ) : awayEquiv I c (dehom I c (C a)) = constFn (toSpecC I) (chart I c) a := by
  have hk := toSpecZero_appLE_basicOpen (quotGrading I) (coord_mem I c) one_pos
  have hC : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (toSpecC I).appLE ⊤ (chart I c) le_top =
      CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)) ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (quotGrading I)
          (Submonoid.powers (coord I c))) ≫ Proj.awayToSection (quotGrading I) (coord I c) := by
    have h3 := Scheme.Hom.comp_appLE (Proj.toSpecZero (quotGrading I))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))) ⊤
      (Proj.basicOpen (quotGrading I) (coord I c)) le_top
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Scheme.Hom.appLE (Proj.toSpecZero (quotGrading I) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))) ⊤
      (Proj.basicOpen (quotGrading I) (coord I c)) le_top = _
    have h4 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))
    rw [h3, ← Category.assoc]
    refine (congrArg (· ≫ _) h4.symm).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)) ≫ ·) hk)
  have hl : awayEquiv I c (dehom I c (C a)) =
      (Proj.awayToSection (quotGrading I) (coord I c)).hom
        (HomogeneousLocalization.fromZeroRingHom (quotGrading I) (Submonoid.powers (coord I c))
          (algebraMap ℂ (quotGrading I 0) a)) := by
    rw [awayEquiv_apply]
    simp only [dehom, coe_eval₂Hom, eval₂_C, RingHom.comp_apply]
    rfl
  rw [hl]
  show _ = ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (toSpecC I).appLE ⊤ (chart I c) le_top).hom a
  rw [hC]
  rfl
end GlobalTheory.ProjCone
