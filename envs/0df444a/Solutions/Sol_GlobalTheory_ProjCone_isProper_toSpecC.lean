-- Prove2me | solution 1 for GlobalTheory.ProjCone.isProper_toSpecC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:03.357923+00:00
-- url     : https://prove2.me/submissions/b24b59cb-b003-4e77-b1f7-12f43d6381b0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Theorems.Thm_GlobalTheory_ProjCone_algebraMap_zero_surjective
import Theorems.Thm_GlobalTheory_ProjCone_adjoin_coord_eq_top

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
theorem _root_.solution [Fintype σ] : IsProper (toSpecC I) := by
  classical
  haveI : Algebra.FiniteType (quotGrading I 0) (MvPolynomial σ ℂ ⧸ I) :=
    ⟨⟨Finset.univ.image (coord I), by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, adjoin_coord_eq_top]⟩⟩
  haveI h2 : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (algebraMap_zero_surjective I)
  exact inferInstanceAs (IsProper (Proj.toSpecZero (quotGrading I) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))))
end GlobalTheory.ProjCone
