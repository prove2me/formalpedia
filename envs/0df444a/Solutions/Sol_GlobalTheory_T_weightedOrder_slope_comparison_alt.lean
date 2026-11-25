-- Prove2me | solution 1 for GlobalTheory.T.weightedOrder_slope_comparison_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:24.297151+00:00
-- url     : https://prove2.me/submissions/169d9876-167c-418f-9f52-7159b8ba3a33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightedOrderSlopeComparison
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightedOrderSlopeComparisonStatement
import Theorems.Thm_GlobalTheory_SS_weightedOrder_slope_comparison


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
theorem _root_.solution : ∀ (k : Type) [Field k] (r : ℕ) (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k), d ≠ 0 → ∀ Q : ℕ → ℕ → Prop, (∀ m n, Q m n ↔ ∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d < MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) → ((∀ i, MvPowerSeries.X 1 ∣ h i) → ¬ MvPowerSeries.X 1 ∣ d → (∃ m n, 1 ≤ m ∧ m ≤ n ∧ ¬ Q m n) → ∃ m n, 1 ≤ m ∧ m ≤ n ∧ (∀ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d ≤ MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ ∃ i, MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) d = MvPowerSeries.weightedOrder (![m, n] : Fin 2 → ℕ) (h i)) ∧ (Q 1 1 → ∃ m₀, ∀ m, m₀ ≤ m → Q m (m + 1)) ∧ (∀ m n l, 1 ≤ l → (Q (l * m) (l * n) ↔ Q m n)) ∧ ((∀ n, 1 ≤ n → Q 1 n) → ∀ i, ∃ u v, ¬ MvPowerSeries.X 1 ∣ v ∧ h i * v = d * u) := by
  first | exact @GlobalTheory.SS.weightedOrder_slope_comparison | exact GlobalTheory.SS.weightedOrder_slope_comparison | (intros; apply GlobalTheory.SS.weightedOrder_slope_comparison <;> assumption)
end _root_.GlobalTheory.T
