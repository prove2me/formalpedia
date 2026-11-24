-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.isPeriod_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:09.320241+00:00
-- url     : https://prove2.me/submissions/ef03c368-3ca3-4bad-9684-d38b9761e4e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_isTypeFn_iff
import Theorems.Thm_GlobalTheory_PeriodCompare_exists_presents
import Theorems.Thm_GlobalTheory_PeriodCompare_isPeriod_of_presents
import Theorems.Thm_GlobalTheory_PeriodCompare_isTypeFn_of_isPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) :
    IsPeriod D ty P ↔ IsPeriodMap D ty P :=
  ⟨fun h => ⟨(isTypeFn_iff D ty).1 (isTypeFn_of_isPeriod h), exists_presents h⟩,
    fun ⟨_, _, hJ, hP⟩ => isPeriod_of_presents hJ hP⟩
end GlobalTheory.PeriodCompare
