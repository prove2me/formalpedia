-- Prove2me | solution 1 for GlobalTheory.T.formalDisc_points_valuationIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:20:31.508814+00:00
-- url     : https://prove2.me/submissions/89045ed4-a819-43c1-88c7-dbd6dcce62a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalDiscPointsValuationIntegers
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalDiscPointsValuationIntegersStatement
import Theorems.Thm_GlobalTheory_ChF_formalDisc_points_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (κ : Type) [Finite κ], (∀ c : κ → O, (∀ q, ¬ IsUnit (c q)) → ∃! Φ : MvPowerSeries κ O →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q) ∧ (∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f)) ∧ ∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (n : ℕ), ∃ N : ℕ, ∀ f ∈ ((Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* MvPowerSeries κ O) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ O))) ^ N, Φ f ∈ Ideal.span {(p : O) ^ n} := by
  first | exact @GlobalTheory.ChF.formalDisc_points_integers | exact GlobalTheory.ChF.formalDisc_points_integers | (intros; apply GlobalTheory.ChF.formalDisc_points_integers <;> assumption)
end _root_.GlobalTheory.T
