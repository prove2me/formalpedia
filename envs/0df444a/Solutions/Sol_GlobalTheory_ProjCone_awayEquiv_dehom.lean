-- Prove2me | solution 1 for GlobalTheory.ProjCone.awayEquiv_dehom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:59:34.392522+00:00
-- url     : https://prove2.me/submissions/7b2a8f7c-30da-4e63-869b-b79d946a7bb4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Theorems.Thm_GlobalTheory_ProjCone_awayEquiv_dehom_C

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
theorem _root_.solution (c : σ) (F : MvPolynomial σ ℂ) :
    awayEquiv I c (dehom I c F) = eval₂ (RingHom.comp ((toSpecC I).appLE ⊤ (chart I c) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (ratio I c) F := by
  have h : (awayEquiv I c).toRingHom.comp (dehom I c) =
      eval₂Hom (RingHom.comp ((toSpecC I).appLE ⊤ (chart I c) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (ratio I c) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_eval₂Hom,
        eval₂_C]
      exact awayEquiv_dehom_C I c a
    · intro q
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_eval₂Hom,
        eval₂_X, dehom]
      rfl
  exact RingHom.congr_fun h F
end GlobalTheory.ProjCone
