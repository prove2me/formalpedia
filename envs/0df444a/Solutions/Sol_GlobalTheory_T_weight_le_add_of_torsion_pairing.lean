-- Prove2me | solution 1 for GlobalTheory.T.weight_le_add_of_torsion_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:33:59.202492+00:00
-- url     : https://prove2.me/submissions/d3aac1dd-2ca1-462c-9556-49f4249a5303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairingStatement
import Theorems.Thm_GlobalTheory_SS_Weight_le_add_of_torsion


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
theorem _root_.solution : ∀ (M : Type) [CommGroup M] (Ω : Type) [Field Ω] (l q g t a c C : ℕ), l.Prime → 3 ≤ l → (l : Ω) ≠ 0 → 2 ≤ q → 1 ≤ c → (∀ n, Nat.card {x : M // x ^ l ^ n = 1} = l ^ (n * (2 * g))) → ∀ e : ℕ → M → M → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) → ∀ S Φ : M ≃* M, (∀ n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (S x) (S y) = e n x y ∧ e n (Φ x) (Φ y) = e n x y ^ q) → (∀ n x, x ^ l ^ n = 1 → Φ (S x) = S^[q] (Φ x)) → (∀ x, x ^ l = 1 → S x = x) → ∀ (H W : Subgroup M) (P : Polynomial ℤ), (∀ n x, x ^ l ^ n = 1 → S x = x → x ^ c ∈ H) → (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : W // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) → (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) → (∀ n, ∀ x ∈ W, x ^ l ^ n = 1 → Φ x = x ^ q) → (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (P.natDegree + 1), (Φ^[j] x) ^ P.coeff j ∈ W) → g ≤ t + a := by
  first | exact @GlobalTheory.SS.Weight.le_add_of_torsion | exact GlobalTheory.SS.Weight.le_add_of_torsion | (intros; apply GlobalTheory.SS.Weight.le_add_of_torsion <;> assumption)
end _root_.GlobalTheory.T
