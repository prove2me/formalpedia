-- Prove2me | solution 1 for GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:32.863014+00:00
-- url     : https://prove2.me/submissions/00a2f992-1ce9-40fb-906d-2cd2ec0bf526

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPolynomialFinrankHomogeneousSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPolynomialFinrankHomogeneousSubmoduleStatement
import Theorems.Thm_GlobalTheory_exists_polynomial_finrank_homogeneousSubmodule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ), ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) = Q.eval (e : ℚ) := by
  first | exact @GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule | exact GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule | (intros; apply GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule <;> assumption)
end _root_.GlobalTheory.T
