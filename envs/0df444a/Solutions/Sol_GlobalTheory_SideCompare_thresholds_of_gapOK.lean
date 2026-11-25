-- Prove2me | solution 1 for GlobalTheory.SideCompare.thresholds_of_gapOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:06.280217+00:00
-- url     : https://prove2.me/submissions/710367f5-39e2-44ac-a561-0ce8f48c5f96

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_LieMatrixVectors
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DecSmoothAtGapOfDecSmooth
import Theorems.Thm_GlobalTheory_SideCompare_aOf_eq
import Theorems.Thm_GlobalTheory_SideCompare_AG_eq
import Theorems.Thm_GlobalTheory_SideCompare_AS_eq
import Theorems.Thm_GlobalTheory_SideCompare_Mexp_eq
import Theorems.Thm_GlobalTheory_SideCompare_decGap_of_cube
import Theorems.Thm_GlobalTheory_GapSizeCheck_thresholds


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
theorem _root_.solution (k r : ℕ) (h : ℝ) (hg : ThreeDimData.GapOK k r h) :
    DecGap k r h ∧ Thresholds k r (decExp r h) ∧ Thresholds k r (decExp r h - 1) := by
  obtain ⟨h1, h2, h3⟩ := GapSizeCheck.thresholds k r h hg
  rw [aOf_eq, AG_eq] at h1
  rw [aOf_eq, AS_eq] at h2
  rw [aOf_eq, AS_eq, AG_eq, Mexp_eq] at h3
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hg.1
  have hG : 4 ≤ thrG k r := by unfold thrG; nlinarith [mul_nonneg hr hr]
  refine ⟨decGap_of_cube k r h hg.2.1, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> (try unfold thrSS) <;> linarith
end GlobalTheory.SideCompare
