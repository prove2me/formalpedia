-- Prove2me | solution 1 for GlobalTheory.SplitFlip.eq_haarVol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:56.314728+00:00
-- url     : https://prove2.me/submissions/62cfcb7d-fa99-41f7-be30-289263a88dbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Theorems.Thm_GlobalTheory_SplitFlip_haarVol_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (μ : Measure (GL n k)) [μ.IsHaarMeasure] {J : Subgroup (GL n k)}
    (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) (h1 : μ J = 1) : μ = haarVol J := by
  have := isHaarMeasure_haarVol ho hK
  have h := Measure.isMulLeftInvariant_eq_smul μ (haarVol J)
  have h2 := congrArg (fun m : Measure (GL n k) => m J) h
  simp only [Measure.coe_nnreal_smul_apply, haarVol_self ho hK, h1, mul_one] at h2
  rw [h, show Measure.haarScalarFactor μ (haarVol J) = 1 by exact_mod_cast h2.symm, one_smul]
end GlobalTheory.SplitFlip
