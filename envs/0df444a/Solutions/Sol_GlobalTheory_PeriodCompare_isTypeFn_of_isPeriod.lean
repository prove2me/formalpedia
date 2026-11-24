-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.isTypeFn_of_isPeriod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:05.998599+00:00
-- url     : https://prove2.me/submissions/8e791269-02f3-4181-94c3-747c9f4c76ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_isTypeFn_iff
import Theorems.Thm_GlobalTheory_PeriodCompare_isTypeFn_of_sum
import Theorems.Thm_GlobalTheory_PeriodCompare_trace_of_presents
import Theorems.Thm_GlobalTheory_PeriodCompare_exists_presents

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
theorem _root_.solution {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriod D ty P) : Tor.IsTypeFn H D.p D.q ty := by
  obtain ⟨J, hJ, hP⟩ := exists_presents h
  exact (isTypeFn_iff D ty).2 (isTypeFn_of_sum D ty fun a => (trace_of_presents hP a).symm.trans (hJ.2.2.2.2 a))
end GlobalTheory.PeriodCompare
