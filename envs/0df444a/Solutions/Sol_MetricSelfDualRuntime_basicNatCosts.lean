-- Prove2me | solution 1 for MetricSelfDualRuntime.basicNatCosts
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T19:21:28.047927+00:00
-- url     : https://prove2.me/submissions/8f54debd-58d7-4717-b6fe-57e6f1ce5177

import Mathlib
import Definitions.Def_MetricSelfDualRuntime_CostInterfaces

namespace MetricSelfDualRuntime
open OAI.ThreeMachine.StackCompiler ExactAmpDich.BinaryMachine

theorem basicNatCosts :
    PolynomialRealizer Realizer.add ∧ PolynomialRealizer Realizer.le ∧
      LinearRealizer Realizer.succ ∧ PolynomialRealizer Realizer.eqNat ∧
        LinearRealizer Realizer.pred := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine ⟨10000010,2,?_⟩
    rintro ⟨a,b⟩
    have ht := Realizer.time_add_le a b
    simp only [volume_nat,volume_pair]
    nlinarith
  · refine ⟨1000000010,2,?_⟩
    rintro ⟨a,b⟩
    have ht := Realizer.time_le_le a b
    have hv := volume_bool (decide (a≤b))
    simp only [volume_nat,volume_pair]
    nlinarith [Nat.zero_le (a*b)]
  · refine ⟨300,?_⟩
    intro n
    have ht := Realizer.time_succ_le n
    simp only [volume_nat]
    nlinarith
  · refine ⟨10000000010,2,?_⟩
    rintro ⟨a,b⟩
    have ht := Realizer.time_eqNat_le a b
    have hv := volume_bool (decide (a=b))
    simp only [volume_pair,volume_nat]
    nlinarith [Nat.zero_le (a*b)]
  · refine ⟨2,?_⟩
    intro n
    change volume n.pred+(volume n+2) ≤ 2*(volume n+1)
    simp only [volume_nat]
    have hp := Nat.pred_le n
    omega

end MetricSelfDualRuntime

open OAI.ThreeMachine.StackCompiler ExactAmpDich.BinaryMachine
theorem solution : PolynomialRealizer Realizer.add ∧ PolynomialRealizer Realizer.le ∧ LinearRealizer Realizer.succ ∧ PolynomialRealizer Realizer.eqNat ∧ LinearRealizer Realizer.pred := MetricSelfDualRuntime.basicNatCosts
