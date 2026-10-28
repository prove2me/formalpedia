-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.binaryStackAdder_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T03:52:03.64923+00:00
-- url     : https://prove2.me/submissions/02c09e9d-deb1-4a0c-aa03-5dbad6f4ee5a

import Definitions.Def_OAICommonBasesFPRASBinaryStackAdder
import Theorems.Thm_OAI_CommonBasesFPRAS_binaryStackAdder_correct
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.CommonBasesFPRAS

namespace CostSupport

theorem addBitsPass_length (carry : Bool) (a b : List Bool) :
    (addBitsPass carry a b).1.length = max a.length b.length := by
  induction a generalizing b carry with
  | nil =>
      induction b generalizing carry with
      | nil => simp [addBitsPass]
      | cons b bs ih =>
          cases carry <;> cases b <;> simp [addBitsPass, addColumn, ih]
  | cons a as ih =>
      cases b with
      | nil => cases carry <;> cases a <;> simp [addBitsPass, addColumn, ih]
      | cons b bs =>
          cases carry <;> cases a <;> cases b <;>
            simp [addBitsPass, addColumn, ih, Order.succ_max, Nat.succ_eq_add_one]

theorem addBitsAux_eq_addBitsPass (carry : Bool) (a b : List Bool) :
    addBitsAux carry a b =
      (addBitsPass carry a b).1 ++ (if (addBitsPass carry a b).2 then [true] else []) := by
  induction a generalizing b carry with
  | nil =>
      induction b generalizing carry with
      | nil => cases carry <;> simp [addBitsAux, addBitsPass]
      | cons b bs ih =>
          cases carry <;> cases b <;>
            simp [addBitsAux, addBitsPass, addColumn, ih]
  | cons a as ih =>
      cases b with
      | nil => cases carry <;> cases a <;>
          simp [addBitsAux, addBitsPass, addColumn, ih]
      | cons b bs =>
          cases carry <;> cases a <;> cases b <;>
            simp [addBitsAux, addBitsPass, addColumn, ih]

theorem addBitsAux_length_le (carry : Bool) (a b : List Bool) :
    (addBitsAux carry a b).length ≤ max a.length b.length + 1 := by
  rw [addBitsAux_eq_addBitsPass]
  simp only [List.length_append, List.length_singleton, addBitsPass_length]
  cases (addBitsPass carry a b).2 <;> simp

theorem adderFinalScratch_length_le (a b : List Bool) :
    (adderFinalScratch a b).length ≤ max a.length b.length + 1 := by
  simp only [adderFinalScratch]
  split <;> simp [List.length_reverse, addBitsPass_length]

end CostSupport

theorem binaryStackAdder_cost_le (O : IndependenceOracle 0) (bits : ℕ → Bool)
    (c : MachineConfig 2 21) (a b : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState 0)
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = []) :
    (execution binaryStackAdder O c bits (adderTotalSteps a b)).bitOperations ≤
      c.bitOperations + 6 * max a.length b.length + 10 := by
  rcases OAI.CommonBasesFPRAS.binaryStackAdder_correct O bits c a b
      hout hcontrol hleft hright hscratch with ⟨_, _, _, hcost⟩
  have hcarry : adderCarrySteps a b ≤ 3 := by
    by_cases h : (addBitsPass false a b).2 <;> simp [adderCarrySteps, h]
  have hscratchLen := CostSupport.adderFinalScratch_length_le a b
  have hauxLen := CostSupport.addBitsAux_length_le false a b
  rw [hcost]
  omega

end OAI.CommonBasesFPRAS

abbrev solution := OAI.CommonBasesFPRAS.binaryStackAdder_cost_le
