-- Prove2me | solution 1 for GlobalTheory.ProjCone.ratio_overlap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:18:03.220121+00:00
-- url     : https://prove2.me/submissions/3624bf1b-9cfa-4a21-aed3-f9b4d506eb40

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Theorems.Thm_GlobalTheory_ProjCone_awayEquiv_apply

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
theorem _root_.solution (c c' q : σ) :
    resG _ (inf_le_left : chart I c ⊓ chart I c' ≤ _) (ratio I c q) *
      resG _ (inf_le_right : chart I c ⊓ chart I c' ≤ _) (ratio I c' c) =
    resG _ (inf_le_right : chart I c ⊓ chart I c' ≤ _) (ratio I c' q) := by
  have key : ∀ (V : (Proj (quotGrading I)).Opens) (h1 : V ≤ chart I c) (h2 : V ≤ chart I c'),
      V = Proj.basicOpen (quotGrading I) (coord I c * coord I c') →
      resG _ h1 (ratio I c q) * resG _ h2 (ratio I c' c) = resG _ h2 (ratio I c' q) := by
    rintro V h1 h2 rfl
    have e1 : ∀ a, resG _ h1 ((Proj.awayToSection (quotGrading I) (coord I c)).hom a) =
        (Proj.awayToSection (quotGrading I) (coord I c * coord I c')).hom
          (HomogeneousLocalization.awayMap (quotGrading I) (coord_mem I c') rfl a) := fun a =>
      (congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (𝒜 := quotGrading I) (f := coord I c)
        (coord_mem I c') (hx := rfl))).symm
    have e2 : ∀ a, resG _ h2 ((Proj.awayToSection (quotGrading I) (coord I c')).hom a) =
        (Proj.awayToSection (quotGrading I) (coord I c * coord I c')).hom
          (HomogeneousLocalization.awayMap (quotGrading I) (coord_mem I c) (mul_comm _ _) a) := fun a =>
      (congrArg (fun φ => φ.hom a) (Proj.awayMap_awayToSection (𝒜 := quotGrading I) (f := coord I c')
        (coord_mem I c) (hx := mul_comm _ _))).symm
    simp only [ratio, awayEquiv_apply]
    rw [e1, e2, e2]
    refine (map_mul (Proj.awayToSection (quotGrading I) (coord I c * coord I c')).hom _ _).symm.trans ?_
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, awayRatio, HomogeneousLocalization.awayMap_mk,
      HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, OneMemClass.coe_one, pow_one, one_mul]
    ring
  exact key _ inf_le_left inf_le_right (Proj.basicOpen_mul _ _ _).symm
end GlobalTheory.ProjCone
