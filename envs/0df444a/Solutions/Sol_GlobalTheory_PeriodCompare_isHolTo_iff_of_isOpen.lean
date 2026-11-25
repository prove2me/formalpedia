-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.isHolTo_iff_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:04:29.505802+00:00
-- url     : https://prove2.me/submissions/95f6669f-0b6c-47dc-bc15-13e92de041ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_isHolTo_iff

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution {B : Set V} (hB : IsOpen B) (y : V → (Sp ℂ ⟶ X)) : IsHolTo B y ↔ HolOn B y := by
  rw [isHolTo_iff, and_iff_right hB]
end GlobalTheory.PeriodCompare
