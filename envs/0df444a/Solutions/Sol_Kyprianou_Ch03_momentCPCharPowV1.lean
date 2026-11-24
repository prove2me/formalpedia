-- Prove2me | solution 1 for Kyprianou.Ch03.momentCPCharPowV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:44:37.012919+00:00
-- url     : https://prove2.me/submissions/1ad4d11f-16ad-4623-b03b-71db9cbc425c

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) (n : ℕ) :
    charFun (KSATSingleFlip.Connect.convPow mu n) xi = (charFun mu xi) ^ n := by
  have hf (k : ℕ) : IsFiniteMeasure (KSATSingleFlip.Connect.convPow mu k) := by
    induction k with
    | zero => simp [KSATSingleFlip.Connect.convPow]; infer_instance
    | succ k ih =>
      letI := ih
      change IsFiniteMeasure (mu ∗ KSATSingleFlip.Connect.convPow mu k)
      infer_instance
  induction n with
  | zero => simp [KSATSingleFlip.Connect.convPow, charFun_apply_real]
  | succ n ih =>
    letI := hf n
    change charFun (mu ∗ KSATSingleFlip.Connect.convPow mu n) xi = _
    rw [charFun_conv, ih, pow_succ, mul_comm]
