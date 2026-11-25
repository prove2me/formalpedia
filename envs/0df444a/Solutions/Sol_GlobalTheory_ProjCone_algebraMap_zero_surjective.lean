-- Prove2me | solution 1 for GlobalTheory.ProjCone.algebraMap_zero_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:59.880968+00:00
-- url     : https://prove2.me/submissions/142a6399-3f7b-4ce5-bc3b-00d0b3978308

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective

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
theorem _root_.solution : Function.Surjective (algebraMap ℂ (quotGrading I 0)) := by
  rintro ⟨a, h, hh, rfl⟩
  have hC := (mem_homogeneousSubmodule 0 h).mp hh
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hC
  refine ⟨coeff 0 h, Subtype.ext ?_⟩
  show algebraMap ℂ (MvPolynomial σ ℂ ⧸ I) (coeff 0 h) = Ideal.Quotient.mkₐ ℂ I h
  conv_rhs => rw [hC]
  rfl
end GlobalTheory.ProjCone
