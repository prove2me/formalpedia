-- Prove2me | solution 1 for GlobalTheory.SideCompare.decGap_of_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:17:17.164894+00:00
-- url     : https://prove2.me/submissions/ab8106ed-553a-4af4-add8-69d0d2c8769f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_LieMatrixVectors
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DecSmoothAtGapOfDecSmooth
import Theorems.Thm_GlobalTheory_SideCompare_dimV_eq
import Theorems.Thm_GlobalTheory_GapSizeCheck_decay_range


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
theorem _root_.solution (k r : ℕ) (h : ℝ) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) : DecGap k r h := by
  have := GapSizeCheck.decay_range k r h hh
  unfold DecGap
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  rw [← dimV_eq, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hr, Real.rpow_one, ← Real.sqrt_eq_rpow]
  exact this
end GlobalTheory.SideCompare
