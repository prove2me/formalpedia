-- Prove2me | solution 1 for OAI.CommonBasesFPRAS.binaryStackAdder_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T03:33:24.407395+00:00
-- url     : https://prove2.me/submissions/6d5fc15e-8a31-4137-aa8d-a158f5b98f7a

import Definitions.Def_OAICommonBasesFPRASBinaryStackAdder
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.CommonBasesFPRAS

/-- Split a deterministic execution into a prefix and a shifted suffix. -/
theorem execution_append {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool)
    (t₀ suffix : ℕ) :
    execution P O c bits (t₀ + suffix) =
      execution P O (execution P O c bits t₀) (fun t => bits (t₀ + t)) suffix := by
  induction suffix with
  | zero => simp [execution]
  | succ suffix ih =>
      calc
        execution P O c bits (t₀ + Nat.succ suffix) =
            machineStep P O (bits (t₀ + suffix))
              (execution P O c bits (t₀ + suffix)) := by rw [Nat.add_succ]; rfl
        _ = machineStep P O (bits (t₀ + suffix))
              (execution P O (execution P O c bits t₀)
                (fun t => bits (t₀ + t)) suffix) := by rw [ih]
        _ = execution P O (execution P O c bits t₀)
              (fun t => bits (t₀ + t)) (Nat.succ suffix) := rfl


@[simp] theorem addColumn_value (a b carry : Bool) :
    (addColumn a b carry).1.toNat + 2 * (addColumn a b carry).2.toNat =
      a.toNat + b.toNat + carry.toNat := by
  cases a <;> cases b <;> cases carry <;> decide

/-- Process corresponding bits, retaining the final carry separately. -/

theorem binaryStackAdder_column (O : IndependenceOracle 0) (bits : ℕ → Bool)
    (c : MachineConfig 2 21) (carry a b : Bool) (as bs : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState (if carry then 4 else 0))
    (hleft : c.registers (adderReg 6) = a :: as)
    (hright : c.registers (adderReg 7) = b :: bs) :
    let out := execution binaryStackAdder O c bits 3
    out.control = adderState (if (addColumn a b carry).2 then 4 else 0) ∧
    out.registers (adderReg 6) = as ∧
    out.registers (adderReg 7) = bs ∧
    out.registers (adderReg 8) = (addColumn a b carry).1 :: c.registers (adderReg 8) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases a <;> cases b <;>
    simp [execution, machineStep, binaryStackAdder, adderState, adderReg,
      addColumn, hleft, hright, Function.update]

/-- The loop also processes a bit when the right input is exhausted. -/
theorem binaryStackAdder_column_rightEmpty (O : IndependenceOracle 0)
    (bits : ℕ → Bool) (c : MachineConfig 2 21) (carry a : Bool) (as : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState (if carry then 4 else 0))
    (hleft : c.registers (adderReg 6) = a :: as)
    (hright : c.registers (adderReg 7) = []) :
    let out := execution binaryStackAdder O c bits 3
    out.control = adderState (if (addColumn a false carry).2 then 4 else 0) ∧
    out.registers (adderReg 6) = as ∧ out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (addColumn a false carry).1 :: c.registers (adderReg 8) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases a <;>
    simp [execution, machineStep, binaryStackAdder, adderState, adderReg,
      addColumn, hleft, hright, Function.update]

/-- Symmetrically, the loop handles an exhausted left input. -/
theorem binaryStackAdder_column_leftEmpty (O : IndependenceOracle 0)
    (bits : ℕ → Bool) (c : MachineConfig 2 21) (carry b : Bool) (bs : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState (if carry then 4 else 0))
    (hleft : c.registers (adderReg 6) = [])
    (hright : c.registers (adderReg 7) = b :: bs) :
    let out := execution binaryStackAdder O c bits 3
    out.control = adderState (if (addColumn false b carry).2 then 4 else 0) ∧
    out.registers (adderReg 6) = [] ∧ out.registers (adderReg 7) = bs ∧
    out.registers (adderReg 8) = (addColumn false b carry).1 :: c.registers (adderReg 8) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright
  subst control
  subst output
  simp [adderReg] at hleft hright
  cases carry <;> cases b <;>
    simp [execution, machineStep, binaryStackAdder, adderState, adderReg,
      addColumn, hleft, hright, Function.update]


/-- The recursively defined result appends a final one exactly when the pass
ends with carry. -/
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
      | nil =>
          cases carry <;> cases a <;>
            simp [addBitsAux, addBitsPass, addColumn, ih]
      | cons b bs =>
          cases carry <;> cases a <;> cases b <;>
            simp [addBitsAux, addBitsPass, addColumn, ih]


private theorem binaryValue_addBitsAux_nil (carry : Bool) (b : List Bool) :
    binaryValue (addBitsAux carry [] b) = binaryValue b + carry.toNat := by
  induction b generalizing carry with
  | nil => cases carry <;> simp [addBitsAux, binaryValue]
  | cons b bs ih =>
    cases b <;> cases carry <;> simp [addBitsAux, addColumn, binaryValue, ih] <;> omega

theorem binaryValue_addBitsAux (carry : Bool) (a b : List Bool) :
    binaryValue (addBitsAux carry a b) =
      binaryValue a + binaryValue b + carry.toNat := by
  induction a generalizing b carry with
  | nil => simpa [binaryValue] using binaryValue_addBitsAux_nil carry b
  | cons a as ih =>
    cases b with
    | nil =>
      cases a <;> cases carry <;> simp [addBitsAux, addColumn, binaryValue, ih] <;> omega
    | cons b bs =>
      cases a <;> cases b <;> cases carry <;>
        simp [addBitsAux, addColumn, binaryValue, ih] <;> omega

/-- After one three-step iteration per input column, both input stacks are
empty and the scratch stack stores the pass bits in reverse order. -/
theorem binaryStackAdder_computeLoop (O : IndependenceOracle 0) (bits : ℕ → Bool)
    (c : MachineConfig 2 21) (carry : Bool) (a b scratch : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState (if carry then 4 else 0))
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = scratch) :
    let out := execution binaryStackAdder O c bits (3 * max a.length b.length)
    out.control = adderState (if (addBitsPass carry a b).2 then 4 else 0) ∧
    out.registers (adderReg 6) = [] ∧ out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (addBitsPass carry a b).1.reverse ++ scratch ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 * max a.length b.length := by
  induction a generalizing b carry c scratch bits with
  | nil =>
      induction b generalizing carry c scratch bits with
      | nil =>
          simp [execution, addBitsPass, hout, hcontrol, hleft, hright, hscratch]
      | cons b bs ih =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdder_column_leftEmpty O bits c carry b bs
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hout', hcalls, hcost⟩
          let c' := execution binaryStackAdder O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn false b carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max 0 (bs.length + 1) = 3 + 3 * max 0 bs.length := by
            simp [Nat.max_def] <;> omega
          rw [hlen, execution_append]
          have htail := ih (carry := (addColumn false b carry).2) (c := c')
            (scratch := (addColumn false b carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, c'] <;> rfl
  | cons a as ih =>
      cases b with
      | nil =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdder_column_rightEmpty O bits c carry a as
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hout', hcalls, hcost⟩
          let c' := execution binaryStackAdder O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn a false carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max (as.length + 1) 0 = 3 + 3 * max as.length 0 := by
            simp [Nat.max_def] <;> omega
          rw [hlen, execution_append]
          have htail := ih (b := []) (carry := (addColumn a false carry).2) (c := c')
            (scratch := (addColumn a false carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, c'] <;> rfl
      | cons b bs =>
          simp only [List.length_cons, List.length_nil] at *
          have hstep := binaryStackAdder_column O bits c carry a b as bs
            hout hcontrol hleft hright
          rcases hstep with ⟨hctl, h6, h7, h8, hout', hcalls, hcost⟩
          let c' := execution binaryStackAdder O c bits 3
          have h8' : c'.registers (adderReg 8) = (addColumn a b carry).1 :: scratch := by
            simpa [c'] using h8.trans (by simpa using hscratch)
          have hlen : 3 * max (as.length + 1) (bs.length + 1) =
              3 + 3 * max as.length bs.length := by
            have hmax : max (as.length + 1) (bs.length + 1) =
                max as.length bs.length + 1 := by
              simpa [Nat.succ_eq_add_one] using
                (Order.succ_max as.length bs.length).symm
            rw [hmax]
            omega
          rw [hlen, execution_append]
          have htail := ih (b := bs) (carry := (addColumn a b carry).2) (c := c')
            (scratch := (addColumn a b carry).1 :: scratch)
            (bits := fun t => bits (3 + t)) hout' hctl h6 h7 h8'
          simp_all [addBitsPass, addColumn, List.reverse_cons, List.append_assoc,
            Nat.add_assoc, c'] <;> rfl


/-- Finish the carry phase and enter the scratch-stack reversal at control 16. -/
theorem binaryStackAdder_finishCarry (O : IndependenceOracle 0) (bits : ℕ → Bool)
    (c : MachineConfig 2 21) (carry : Bool) (scratch : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState (if carry then 4 else 0))
    (hleft : c.registers (adderReg 6) = [])
    (hright : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = scratch) :
    let steps := if carry then 3 else 2
    let out := execution binaryStackAdder O c bits steps
    out.control = adderState 16 ∧ out.registers (adderReg 6) = [] ∧
    out.registers (adderReg 7) = [] ∧
    out.registers (adderReg 8) = (if carry then true :: scratch else scratch) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + steps := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hleft hright hscratch
  subst control
  subst output
  simp [adderReg] at hleft hright hscratch
  cases carry <;>
    simp [execution, machineStep, binaryStackAdder, adderState, adderReg,
      hleft, hright, hscratch, Function.update]

/-- A reversal iteration pops one scratch bit and pushes it onto the output. -/
theorem binaryStackAdder_reverseColumn (O : IndependenceOracle 0)
    (bits : ℕ → Bool) (c : MachineConfig 2 21) (bit : Bool)
    (acc rest : List Bool) (hout : c.output = none)
    (hcontrol : c.control = adderState 16)
    (hnum : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = bit :: rest) :
    let out := execution binaryStackAdder O c bits 2
    out.control = adderState 16 ∧ out.registers (adderReg 6) = bit :: acc ∧
    out.registers (adderReg 7) = [] ∧ out.registers (adderReg 8) = rest ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 := by
  rcases c with ⟨regs, control, output, calls, ops⟩
  simp only at hout hcontrol hnum hden hscratch
  subst control
  subst output
  simp [adderReg] at hnum hden hscratch
  cases bit <;>
    simp [execution, machineStep, binaryStackAdder, adderState, adderReg,
      hnum, hden, hscratch, Function.update]

/-- Reverse the scratch stack and halt, including the machine's output-cost
charge, for any nonempty prefix already accumulated in register 6. -/
theorem binaryStackAdder_reverse (O : IndependenceOracle 0) (bits : ℕ → Bool)
    (c : MachineConfig 2 21) (acc stack : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState 16)
    (hnum : c.registers (adderReg 6) = acc)
    (hden : c.registers (adderReg 7) = [])
    (hscratch : c.registers (adderReg 8) = stack) :
    let out := execution binaryStackAdder O c bits (2 * stack.length + 3)
    out.control = adderState 21 ∧
    out.registers (adderReg 6) = stack.reverse ++ acc ∧
    out.registers (adderReg 7) = [true] ∧ out.registers (adderReg 8) = [] ∧
    out.output = some ((binaryValue (stack.reverse ++ acc) : ℚ) / 1) ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 2 * stack.length +
      (stack.reverse ++ acc).length + 4 := by
  induction stack generalizing acc c bits with
  | nil =>
      rcases c with ⟨regs, control, output, calls, ops⟩
      simp only at hout hcontrol hnum hden hscratch
      subst control
      subst output
      simp [adderReg] at hnum hden hscratch
      simp [execution, machineStep, binaryStackAdder, adderState, adderReg,
        hnum, hden, hscratch, Function.update, binaryValue, Nat.add_assoc] <;> omega
  | cons bit rest ih =>
      simp only [List.length_cons] at *
      have hstep := binaryStackAdder_reverseColumn O bits c bit acc rest
        hout hcontrol hnum hden hscratch
      rcases hstep with ⟨hctl, hnum', hden', hscratch', hout', hcalls, hcost⟩
      let c' := execution binaryStackAdder O c bits 2
      have htail := ih (acc := bit :: acc) (c := c')
        (bits := fun t => bits (2 + t)) hout' hctl hnum' hden' hscratch'
      rw [show 2 * (rest.length + 1) + 3 = 2 + (2 * rest.length + 3) by omega,
        execution_append]
      simp_all [List.reverse_cons, List.append_assoc, Nat.add_assoc, c'] <;> omega

/-- Split an execution into three consecutive deterministic phases. -/
theorem execution_append_three {k s n : ℕ} (P : Program k s)
    (O : IndependenceOracle n) (c : MachineConfig k s) (bits : ℕ → Bool)
    (t₁ t₂ t₃ : ℕ) :
    execution P O c bits (t₁ + (t₂ + t₃)) =
      execution P O
        (execution P O (execution P O c bits t₁) (fun t => bits (t₁ + t)) t₂)
        (fun t => bits (t₁ + t₂ + t)) t₃ := by
  rw [execution_append]
  rw [execution_append]
  congr 1
  funext t
  congr 1
  omega


/-- The stack program adds arbitrary little-endian natural numbers. It consumes
exactly three steps per paired column, handles the last carry, reverses the
scratch result, and charges the actual output write at halt. -/
theorem binaryStackAdder_correct (O : IndependenceOracle 0) (bits : ℕ → Bool)
    (c : MachineConfig 2 21) (a b : List Bool)
    (hout : c.output = none)
    (hcontrol : c.control = adderState 0)
    (hleft : c.registers (adderReg 6) = a)
    (hright : c.registers (adderReg 7) = b)
    (hscratch : c.registers (adderReg 8) = []) :
    let out := execution binaryStackAdder O c bits (adderTotalSteps a b)
    out.control = adderState 21 ∧
    out.output = some (((binaryValue a + binaryValue b : ℕ) : ℚ)) ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + 3 * max a.length b.length +
      adderCarrySteps a b + 2 * (adderFinalScratch a b).length +
      (addBitsAux false a b).length + 4 := by
  let firstSteps := 3 * max a.length b.length
  let carrySteps := adderCarrySteps a b
  let scratch := adderFinalScratch a b
  let lastSteps := 2 * scratch.length + 3
  let pass := addBitsPass false a b
  have hloop := binaryStackAdder_computeLoop O bits c false a b []
    hout hcontrol hleft hright hscratch
  rcases hloop with ⟨hctl₁, h6₁, h7₁, h8₁, hout₁, hcalls₁, hcost₁⟩
  let c₁ := execution binaryStackAdder O c bits firstSteps
  have h8₁' : c₁.registers (adderReg 8) = pass.1.reverse := by
    simpa [c₁, firstSteps, pass] using h8₁
  have hcarry := binaryStackAdder_finishCarry O (fun t => bits (firstSteps + t))
    c₁ pass.2 pass.1.reverse hout₁ hctl₁ h6₁ h7₁ h8₁'
  rcases hcarry with ⟨hctl₂, h6₂, h7₂, h8₂, hout₂, hcalls₂, hcost₂⟩
  let c₂ := execution binaryStackAdder O c₁ (fun t => bits (firstSteps + t)) carrySteps
  have hrev := binaryStackAdder_reverse O
    (fun t => bits (firstSteps + carrySteps + t)) c₂ [] scratch
    hout₂ hctl₂ h6₂ h7₂ h8₂
  rcases hrev with ⟨hctl₃, h6₃, h7₃, h8₃, hout₃, hcalls₃, hcost₃⟩
  have hsum : scratch.reverse = addBitsAux false a b := by
    dsimp [scratch, adderFinalScratch, pass]
    rw [addBitsAux_eq_addBitsPass]
    cases hcarryBit : (addBitsPass false a b).2 <;>
      simp [hcarryBit, List.reverse_cons, List.reverse_reverse]
  have hfinal := execution_append_three binaryStackAdder O c bits
    firstSteps carrySteps lastSteps
  have htotal : adderTotalSteps a b = firstSteps + (carrySteps + lastSteps) := by
    dsimp [adderTotalSteps, adderCarrySteps, firstSteps, carrySteps,
      lastSteps, scratch, adderFinalScratch]
    omega
  have hrun : execution binaryStackAdder O c bits (adderTotalSteps a b) =
      execution binaryStackAdder O c₂
        (fun t => bits (firstSteps + carrySteps + t)) lastSteps := by
    have h := congrArg (fun t => execution binaryStackAdder O c bits t) htotal
    rw [hfinal] at h
    simpa [c₁, c₂, firstSteps, carrySteps] using h
  have hcost₁' : c₁.bitOperations = c.bitOperations + firstSteps := by
    simpa [c₁, firstSteps] using hcost₁
  have hcost₂' : c₂.bitOperations = c₁.bitOperations + carrySteps := by
    simpa [c₂, carrySteps, pass, adderCarrySteps] using hcost₂
  have hcalls₁' : c₁.oracleCalls = c.oracleCalls := by
    simpa [c₁, firstSteps] using hcalls₁
  have hcalls₂' : c₂.oracleCalls = c₁.oracleCalls := by
    simpa [c₂, carrySteps, pass, adderCarrySteps] using hcalls₂
  constructor
  · change (execution binaryStackAdder O c bits (adderTotalSteps a b)).control = _
    rw [hrun]
    exact hctl₃
  constructor
  · change (execution binaryStackAdder O c bits (adderTotalSteps a b)).output = _
    rw [hrun]
    simpa [c₂, hsum, binaryValue_addBitsAux, Nat.cast_add, div_one] using hout₃
  constructor
  · change (execution binaryStackAdder O c bits (adderTotalSteps a b)).oracleCalls = _
    rw [hrun]
    calc
      (execution binaryStackAdder O c₂ (fun t => bits (firstSteps + carrySteps + t)) lastSteps).oracleCalls
          = c₂.oracleCalls := by simpa [lastSteps] using hcalls₃
      _ = c.oracleCalls := hcalls₂'.trans hcalls₁'
  · change (execution binaryStackAdder O c bits (adderTotalSteps a b)).bitOperations = _
    rw [hrun]
    calc
      (execution binaryStackAdder O c₂ (fun t => bits (firstSteps + carrySteps + t)) lastSteps).bitOperations
          = c₂.bitOperations + 2 * scratch.length +
              (scratch.reverse ++ []).length + 4 := by simpa [lastSteps] using hcost₃
      _ = c.bitOperations + 3 * max a.length b.length + carrySteps +
            2 * scratch.length + (addBitsAux false a b).length + 4 := by
          simp [c₂, c₁, hcost₂', hcost₁', hsum, firstSteps, Nat.add_assoc,
            List.length_reverse]


end OAI.CommonBasesFPRAS

abbrev solution := OAI.CommonBasesFPRAS.binaryStackAdder_correct
