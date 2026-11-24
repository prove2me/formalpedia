-- Prove2me | solution 1 for GlobalTheory.T.similitude_definite_form_isAlgebraic_on_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:46.64094+00:00
-- url     : https://prove2.me/submissions/65385958-6d43-4096-bf06-eb4e7df77091

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVectorStatement
import Theorems.Thm_GlobalTheory_SimAlg_similitude_algebraic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Λ : Type) [AddCommGroup Λ] (Q : Λ → ℤ) (φ : Module.End ℤ Λ) (e : Λ) (q l r : ℕ), 2 ≤ l → (∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) → (∀ x, 0 ≤ Q x) → (∀ x, Q x = 0 → x = 0) → (∀ x, Q (φ x) = q * Q x) → (∀ n : ℕ, ∃ (χ : Polynomial ℤ) (y : Λ), χ.Monic ∧ χ.natDegree = r ∧ Polynomial.aeval φ χ e = l ^ n • y) → ∃ P : Polynomial ℤ, P ≠ 0 ∧ Polynomial.aeval φ P e = 0 ∧ ∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q := by
  first | exact @GlobalTheory.SimAlg.similitude_algebraic | exact GlobalTheory.SimAlg.similitude_algebraic | (intros; apply GlobalTheory.SimAlg.similitude_algebraic <;> assumption)
end _root_.GlobalTheory.T
