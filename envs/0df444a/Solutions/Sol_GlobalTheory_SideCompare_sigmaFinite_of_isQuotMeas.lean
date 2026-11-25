-- Prove2me | solution 1 for GlobalTheory.SideCompare.sigmaFinite_of_isQuotMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:53.389345+00:00
-- url     : https://prove2.me/submissions/adeb9062-388e-4ca5-aa0f-fd428a87f54f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_LieMatrixVectors
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DecSmoothAtGapOfDecSmooth
import Theorems.Thm_GlobalTheory_QuotientMeasureSigmaFinite_sigmaFinite_of_isQuotMeas


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
theorem _root_.solution {k r : ℕ} {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS]
    (hS : μS ≠ 0) (hq : IsQuotMeas μG μS ν) : SigmaFinite ν := by
  first
  | (rename_i h_5 h_6; revert k r μG μS ν h_5 h_6 hS hq; exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas)
  | exact @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
  | (apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas ..)
end GlobalTheory.SideCompare
