-- Prove2me | solution 1 for GlobalTheory.SideCompare.muS_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:20.025146+00:00
-- url     : https://prove2.me/submissions/360f5c90-cbd5-4803-b5b8-be490620c3c9

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_LieMatrixVectors
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DecSmoothAtGapOfDecSmooth
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SideNormalisedGap_measurable_mulP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SideCompare
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open PI.BesselPeriodGGP (IsHaarOn IsQuotMeas)
open Formalism.FourierDecayAlt GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp decConst dimV dimN thrG thrS thrSS propExp DecGap Size Thresholds muS mulP IsSide
  IsSideNormalised KFinDecay wordSeminorm DecKFin DecSmooth)
namespace GlobalTheory.SideCompare
theorem _root_.solution {k r : ℕ} {μW μN : Measure (Mt k r)} [SFinite μN] (hW : μW ≠ 0) (hN : μN ≠ 0) :
    muS μW μN ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero] at *
  unfold muS
  rw [Measure.map_apply SideNormalisedGap.measurable_mulP MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod]
  exact mul_ne_zero hW hN
end GlobalTheory.SideCompare
