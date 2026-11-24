-- Prove2me | solution 1 for GlobalTheory.BoxDetUnique.det_calc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:46.425858+00:00
-- url     : https://prove2.me/submissions/55413563-6078-4b50-82f6-cc50d64f8c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DetKroneckerPower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsBoxSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.BoxDetUnique
theorem _root_.solution {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (Q Q' T : Matrix I I K)
    (c rho rho' : I → K) (n : ℕ) (hQ : ∀ a b, Q (σ a) b = c a * ∑ d, Q' a d * T b d)
    (hr : ∀ a, rho' a = c a ^ n * rho (σ a)) :
    Q.det ^ (2 * n) * ∏ a, rho a ^ 2 = (Q'.det ^ (2 * n) * ∏ a, rho' a ^ 2) * T.det ^ (2 * n) := by
  have h1 : Q.submatrix σ id = Matrix.diagonal c * (Q' * T.transpose) := by
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    exact hQ a b
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_permute, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h2
  have h3 : Q.det ^ 2 = ((∏ a, c a) * (Q'.det * T.det)) ^ 2 := by
    rw [← h2, mul_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h4 : ∏ a, rho' a ^ 2 = (∏ a, c a) ^ (2 * n) * ∏ a, rho a ^ 2 := by
    rw [← Equiv.prod_comp σ (fun a => rho a ^ 2), ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => by rw [hr]; ring
  rw [h4, pow_mul, h3]
  ring
end GlobalTheory.BoxDetUnique
