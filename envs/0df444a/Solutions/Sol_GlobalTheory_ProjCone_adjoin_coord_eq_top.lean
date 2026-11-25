-- Prove2me | solution 1 for GlobalTheory.ProjCone.adjoin_coord_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:17:55.748778+00:00
-- url     : https://prove2.me/submissions/cd66fca1-87cc-49a0-9345-a6a3dc7bbea7

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
theorem _root_.solution : Algebra.adjoin (quotGrading I 0) (Set.range (coord I)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction g using MvPolynomial.induction_on with
  | C a =>
    exact Subalgebra.algebraMap_mem _ (⟨Ideal.Quotient.mk _ (C a),
      ⟨C a, (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ a), rfl⟩⟩ : quotGrading I 0)
  | add g h hg hh => rw [map_add]; exact add_mem hg hh
  | mul_X g q hg => rw [map_mul]; exact mul_mem hg (Algebra.subset_adjoin ⟨q, rfl⟩)
end GlobalTheory.ProjCone
