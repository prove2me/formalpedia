-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:39:49.502852+00:00
-- url     : https://prove2.me/submissions/081ddd26-bcd1-4497-ab45-d6e7f82544e5

import Mathlib
import Definitions.Def_OAIQ081S065
import Definitions.Def_OAIQ081S117

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DensePolynomialLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed streaming array loop, parameterized by a finite word program
and an actual trace theorem for one word. The concrete modular-word
instantiation is supplied in DensePolynomialPrograms. -/

namespace SubexponentialSAT.DensePolynomialLoop

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

theorem guard_eval (regs : Fin 8 → Bool) (modulus left right width packed : List Bool)
    (frame : Fin 6 → List Bool) :
    Eval guard 3 (ready regs modulus left right width packed frame)
      (ready (guardRegs regs left right) modulus left right width packed frame) := by
  let d := ready regs modulus left right width packed frame
  have h₁ := Eval.base (StructuredProgram.Eval.atom (r := 8) (s := 20) (.peek 8 0 1) d)
  have h₂ := Eval.base (StructuredProgram.Eval.atom (r := 8) (s := 20) (.peek 9 2 3)
    ((StructuredProgram.Atom.peek 8 0 1).eval d))
  have h₃ := Eval.base (StructuredProgram.Eval.atom (r := 8) (s := 20) (.band 4 1 3)
    ((StructuredProgram.Atom.peek 9 2 3).eval ((StructuredProgram.Atom.peek 8 0 1).eval d)))
  exact Eval.seq h₁ (Eval.seq h₂ h₃)

theorem flush_eval (regs : Fin 8 → Bool) (modulus left right width packed : List Bool)
    (frame : Fin 6 → List Bool) :
    Eval flush (6 * left.length + 6 * right.length + 3 * packed.length + 9)
      (ready regs modulus left right width packed frame)
      (ready (readRegs regs 0 1 none) modulus (packed.reverse ++ left ++ right) [] width [] frame) := by
  let d₀ := ready regs modulus left right width packed frame
  let d₁ := ready (readRegs regs 0 1 none) modulus [] right width (left.reverse ++ packed) frame
  let d₂ := ready (readRegs regs 0 1 none) modulus [] [] width
    (right.reverse ++ left.reverse ++ packed) frame
  have h₁ := transfer_eval d₀ 8 13 0 1 (by decide) (by decide)
  have e₁ : afterTransfer d₀ 8 13 0 1 = d₁ := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;>
        simp [afterTransfer, d₀, d₁, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
          StackRoutines.transferStacks]
  have h₂ := transfer_eval d₁ 9 13 0 1 (by decide) (by decide)
  have e₂ : afterTransfer d₁ 9 13 0 1 = d₂ := by
    apply state_ext
    · simp [afterTransfer, d₁, d₂, ready, state, StackRoutines.readRegs_reset]
    · funext i; fin_cases i <;>
        simp [afterTransfer, d₁, d₂, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
          StackRoutines.transferStacks,
          List.append_assoc]
  have h₃ := transfer_eval d₂ 13 8 0 1 (by decide) (by decide)
  have e₃ : afterTransfer d₂ 13 8 0 1 =
      ready (readRegs regs 0 1 none) modulus (packed.reverse ++ left ++ right) [] width [] frame := by
    apply state_ext
    · simp [afterTransfer, d₂, ready, state, StackRoutines.readRegs_reset]
    · funext i; fin_cases i <;>
        simp [afterTransfer, d₂, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod,
          StackRoutines.transferStacks,
          List.reverse_append, List.append_assoc]
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [e₃] at h₃
  have h := Eval.seq h₁ (Eval.seq h₂ h₃)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp [ d₀, d₁, d₂, ready, state, stackArray, Fin.addCases,
    Fin.coe_ofNat_eq_mod, List.length_append]
  omega

theorem flatten_cons_ne_nil {B : ℕ} (hB : 0 < B) (x : Word B) (xs : List (Word B)) :
    flatten (x :: xs) ≠ [] := by
  intro h
  have hh := congrArg List.length h
  rw [flatten_length] at hh
  simp only [List.length_cons, List.length_nil] at hh
  nlinarith

theorem head_isSome_of_ne_nil {α : Type*} {xs : List α} (h : xs ≠ []) : xs.head?.isSome = true := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons a xs => rfl

variable {B : ℕ} (step : WordStep B)

theorem addWords_length (xs ys : List (Word (B))) :
    (addWords step xs ys).length = min xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [addWords]
  | cons x xs ih => cases ys <;> simp [addWords, ih]

theorem addLoop_eval (hB : 0 < B) (regs : Fin 8 → Bool)
    (xs ys : List (Word (B)))
    (width packed : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = B) :
    ∃ n ≤ min xs.length ys.length * (step.cost + 4) + 1, ∃ regs',
      Eval (addLoop step.cmd) n
        (ready (guardRegs regs (flatten xs) (flatten ys)) step.modulus
          (flatten xs) (flatten ys) width packed frame)
        (ready regs' step.modulus (flatten (xs.drop ys.length)) (flatten (ys.drop xs.length)) width
          ((flatten (addWords step xs ys)).reverse ++ packed) frame) := by
  induction xs generalizing ys regs packed with
  | nil =>
      refine ⟨1, by simp, guardRegs regs [] (flatten ys), ?_⟩
      simpa [addLoop, flatten, addWords] using
        (Eval.while_false (test := (4 : Fin 8)) (body := .seq step.cmd guard)
          (a := ready (guardRegs regs [] (flatten ys)) step.modulus [] (flatten ys) width packed frame)
          (by simp [ready, state]))
  | cons x xs ih =>
      cases ys with
      | nil =>
          refine ⟨1, by simp, guardRegs regs (flatten (x :: xs)) [], ?_⟩
          simpa [addLoop, flatten, addWords] using
            (Eval.while_false (test := (4 : Fin 8)) (body := .seq step.cmd guard)
              (a := ready (guardRegs regs (flatten (x :: xs)) []) step.modulus
                (flatten (x :: xs)) [] width packed frame) (by simp [ready, state]))
      | cons y ys =>
          let rg := guardRegs regs (flatten (x :: xs)) (flatten (y :: ys))
          have ht : (ready rg step.modulus (flatten (x :: xs)) (flatten (y :: ys)) width packed frame).regs 4 = true := by
            simp only [ready, state, rg, guardRegs_test,
              head_isSome_of_ne_nil (flatten_cons_ne_nil hB x xs),
              head_isSome_of_ne_nil (flatten_cons_ne_nil hB y ys), Bool.and_self]
          obtain ⟨n, hn, r₁, h₁⟩ := step.run rg x y (flatten xs) (flatten ys)
            width packed frame hwidth
          let packed' := (step.add x y).val.reverse ++ packed
          have hg := guard_eval r₁ step.modulus (flatten xs) (flatten ys) width packed' frame
          obtain ⟨m, hm, r₂, h₂⟩ := ih r₁ ys packed'
          refine ⟨n + 3 + m + 1, ?_, r₂, ?_⟩
          · simp only [List.length_cons]
            rw [show min (xs.length + 1) (ys.length + 1) = min xs.length ys.length + 1 by omega]
            calc
              _ ≤ step.cost + 3 +
                  (min xs.length ys.length * (step.cost + 4) + 1) + 1 := by omega
              _ = _ := by ring
          · have h := Eval.while_true ht (Eval.seq h₁ hg) h₂
            simpa [addLoop, flatten, addWords, rg, packed', List.reverse_append,
              List.append_assoc, Nat.add_assoc] using h

theorem addWordsTotal_decompose (xs ys : List (Word (B))) :
    addWordsTotal step xs ys = addWords step xs ys ++ xs.drop ys.length ++ ys.drop xs.length := by
  induction xs generalizing ys with
  | nil => simp [addWordsTotal, addWords]
  | cons x xs ih => cases ys <;> simp [addWordsTotal, addWords, ih]

theorem addCmd_eval (hB : 0 < B) (regs : Fin 8 → Bool)
    (xs ys : List (Word (B))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = B) :
    ∃ n ≤ (xs.length + ys.length + 1) * (step.cost + 15 * B + 20), ∃ regs',
      Eval (addCmd step.cmd) n (ready regs step.modulus (flatten xs) (flatten ys) width [] frame)
        (ready regs' step.modulus (flatten (addWordsTotal step xs ys)) [] width [] frame) := by
  have hg := guard_eval regs step.modulus (flatten xs) (flatten ys) width [] frame
  obtain ⟨n, hn, r₁, hl⟩ := addLoop_eval step hB regs xs ys width [] frame hwidth
  simp only [List.append_nil] at hl
  let left := flatten (xs.drop ys.length)
  let right := flatten (ys.drop xs.length)
  let packed := (flatten (addWords step xs ys)).reverse
  have hf := flush_eval r₁ step.modulus left right width packed frame
  have h := Eval.seq hg (Eval.seq hl hf)
  have hleft : left.length ≤ (xs.length + ys.length) * B := by
    simp only [left, flatten_length, List.length_drop]
    exact Nat.mul_le_mul_right _ (by omega)
  have hright : right.length ≤ (xs.length + ys.length) * B := by
    simp only [right, flatten_length, List.length_drop]
    exact Nat.mul_le_mul_right _ (by omega)
  have hpacked : packed.length ≤ (xs.length + ys.length) * B := by
    simp only [packed, List.length_reverse, flatten_length, addWords_length]
    exact Nat.mul_le_mul_right _ (by omega)
  have hloop : n ≤ (xs.length + ys.length) * (step.cost + 4) + 1 :=
    hn.trans (by gcongr; omega)
  refine ⟨3 + (n + (6 * left.length + 6 * right.length + 3 * packed.length + 9)), ?_,
    readRegs r₁ 0 1 none, ?_⟩
  · nlinarith
  · simpa only [addCmd, List.append_nil, packed, left, right, List.reverse_reverse,
      addWordsTotal_decompose, flatten_append] using h


end SubexponentialSAT.DensePolynomialLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DensePolynomialPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed streaming program for dense polynomial addition

Quartic coefficients are four consecutive fixed-width base words. The loop
uses the actual modular-word addition program and tests the input stacks.
Its instruction table is independent of the array lengths and the width.
-/

namespace SubexponentialSAT.DensePolynomialPrograms

open BitProgram StructuredCalls DensePolynomialLoop
open SubexpLiftRing SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem addCmd_eval (hB : 0 < baseWidth p μ) (regs : Fin 8 → Bool)
    (xs ys : List (Word (baseWidth p μ))) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p μ) :
    ∃ n ≤ 7000 * (xs.length + ys.length + 1) * (baseWidth p μ + 1) ^ 2, ∃ regs',
      Eval addCmd n (ready regs M.bits (flatten xs) (flatten ys) width [] frame)
        (ready regs' M.bits (flatten (addWordsTotal p μ M xs ys)) [] width [] frame) := by
  obtain ⟨n, hn, rf, hr⟩ := DensePolynomialLoop.addCmd_eval (wordStep p μ M)
    hB regs xs ys width frame hwidth
  have hc : (wordStep p μ M).cost + 15 * baseWidth p μ + 20 ≤
      7000 * (baseWidth p μ + 1) ^ 2 := by
    change SubexpFlatAdd.wordCost (baseWidth p μ) + 15 * baseWidth p μ + 20 ≤ _
    unfold SubexpFlatAdd.wordCost
    ring_nf
    omega
  refine ⟨n, hn.trans ?_, rf, hr⟩
  calc
    _ ≤ (xs.length + ys.length + 1) * (7000 * (baseWidth p μ + 1) ^ 2) :=
      Nat.mul_le_mul_left _ hc
    _ = _ := by ring

end SubexponentialSAT.DensePolynomialPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

private theorem addWords_append {B : ℕ} (step : WordStep B)
    (xs ys as bs : List (Word B)) (hlen : xs.length = ys.length) :
    addWordsTotal step (xs ++ as) (ys ++ bs) =
      List.zipWith step.add xs ys ++ addWordsTotal step as bs := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.cons_append, addWordsTotal, List.zipWith_cons_cons]
          rw [ih ys (by simpa using hlen)]

private theorem zipWith_ofFn {A B C : Type*} (f : A → B → C) {d : ℕ}
    (a : Fin d → A) (b : Fin d → B) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      simp only [List.ofFn_succ, List.zipWith_cons_cons]
      rw [ih]

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

private theorem words_add_block {d : ℕ}
    (a b : Coeff (baseWidth p t) d) (xs ys : List (Word (baseWidth p t))) :
    SubexponentialSAT.DensePolynomialPrograms.addWordsTotal p t M
        (List.ofFn a ++ xs) (List.ofFn b ++ ys) =
      List.ofFn (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1 ++
        SubexponentialSAT.DensePolynomialPrograms.addWordsTotal p t M xs ys := by
  rw [SubexponentialSAT.DensePolynomialPrograms.addWordsTotal,
    addWords_append _ _ _ _ _ (by simp), zipWith_ofFn]
  simp only [SubexponentialSAT.DensePolynomialPrograms.wordStep, RingProgram.addRun,
    RingProgram.tabulateRun_eq, RingProgram.scalarProgram]

private theorem addWordsTotal_nil_right {B : ℕ} (step : WordStep B) (xs : List (Word B)) :
    addWordsTotal step xs [] = xs := by cases xs <;> rfl

theorem words_add {d : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) d)) :
    SubexponentialSAT.DensePolynomialPrograms.addWordsTotal p t M (words P) (words Q) =
      words (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1 := by
  induction P generalizing Q with
  | nil => simp [words, SubexponentialSAT.DensePolynomialPrograms.addWordsTotal,
      addWordsTotal, SubexponentialSAT.SubexpDensePolynomial.addProgram]
  | cons a P ih =>
      cases Q with
      | nil => simp only [SubexponentialSAT.SubexpDensePolynomial.addProgram, words, List.flatMap_nil,
          SubexponentialSAT.DensePolynomialPrograms.addWordsTotal, addWordsTotal_nil_right]
      | cons b Q =>
          simp only [words, List.flatMap_cons, SubexponentialSAT.SubexpDensePolynomial.addProgram]
          change SubexponentialSAT.DensePolynomialPrograms.addWordsTotal p t M
            (List.ofFn a ++ words P) (List.ofFn b ++ words Q) =
            List.ofFn (ops.addRun a b).1 ++ words (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1
          rw [words_add_block p t M cache, hadd, ih]

theorem add_eval {d : ℕ} (hB : 0 < baseWidth p t) (regs : Fin 8 → Bool)
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) d)) (width : List Bool)
    (frame : Fin 6 → List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 7000 * (d * (P.length + Q.length) + 1) * (baseWidth p t + 1)^2,
      ∃ regs', Eval addCmd n
        (ready regs M.bits (encode P) (encode Q) width [] frame)
        (ready regs' M.bits (encode (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1)
          [] width [] frame) := by
  obtain ⟨n, hn, rf, he⟩ := SubexponentialSAT.DensePolynomialPrograms.addCmd_eval p t M hB regs
    (words P) (words Q) width frame hwidth
  rw [words_add p t M cache ops hadd P Q] at he
  refine ⟨n, ?_, rf, ?_⟩
  · simpa only [words_length, show P.length * d + Q.length * d = d * (P.length + Q.length) by ring] using hn
  · simpa only [addCmd, encode_eq_flatten_words] using he

theorem add_trace {d : ℕ} (hB : 0 < baseWidth p t) (regs : Fin 8 → Bool)
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) d)) (width : List Bool)
    (frame : Fin 6 → List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 7000 * (d * (P.length + Q.length) + 1) * (baseWidth p t + 1)^2 + 1,
      ∃ regs', Trace addProgram n
        ((ready regs M.bits (encode P) (encode Q) width [] frame).withPC (some addProgram.entry))
        ((ready regs' M.bits (encode (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1)
          [] width [] frame).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := add_eval p t M cache hB regs ops hadd P Q width frame hwidth
  exact ⟨n + 1, by omega, rf, compiled_halt_trace he 8 8⟩

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetCellProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete addition into one packed jet cell

The persistent jet, unary index, and cell width are on stacks 102, 103, and
104. The array subprogram uses 112--117, and order-preserving moves use 118.
All instruction tables are fixed independently of widths and indices. The
full service reads the old cell, invokes the actual flattened quartic adder,
and writes the sum back. Its endpoint changes only the contribution and jet
stacks; all other caller stacks and registers 8--15 are preserved.
-/

namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem arrayPorts_injective : Function.Injective arrayPorts := by
  decide

theorem copyIndex_eval (d : Data) (htmp : d.stacks 114 = []) :
    Eval copyIndex (7 * (d.stacks 103).length + 5) d (afterCopy d 103 113 0 1) :=
  copy_eval d 103 113 114 0 1 (by decide) (by decide) (by decide) (by decide) htmp

theorem moveForward_eval (d : Data) (src dst : Fin 128)
    (hsd : src ≠ dst) (hst : src ≠ 118) (hdt : dst ≠ 118)
    (htmp : d.stacks 118 = []) :
    Eval (moveForward src dst) (6 * (d.stacks src).length + 6) d (moveOut d src dst) := by
  have h₁ := transfer_eval d src 118 0 1 hst (by decide)
  have h₂ := transfer_eval (afterTransfer d src 118 0 1) 118 dst 0 1 hdt.symm (by decide)
  have hout : afterTransfer (afterTransfer d src 118 0 1) 118 dst 0 1 =
      moveOut d src dst := by
    apply state_ext
    · simp [afterTransfer, moveOut, StackRoutines.readRegs_reset]
    · funext j
      by_cases hd : j = dst
      · subst j
        simp [afterTransfer, moveOut, StackRoutines.transferStacks, htmp,
          hsd.symm, hdt ]
      · by_cases ht : j = 118
        · subst j
          simp [afterTransfer, moveOut, StackRoutines.transferStacks, htmp,
            hd, hst.symm]
        · simp [afterTransfer, moveOut, StackRoutines.transferStacks, hd, ht]
  have hlen : ((afterTransfer d src 118 0 1).stacks 118).length = (d.stacks src).length := by
    simp [afterTransfer, StackRoutines.transferStacks, htmp]
  simpa only [moveForward, hout, hlen, show ∀ n : ℕ, (3*n+3)+(3*n+3)=6*n+6 by omega]
    using Eval.seq h₁ h₂

theorem clear_eval (d : Data) (src : Fin 128) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (clearOut d src) := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks) 2 rfl rfl
  simpa [clearOut, StackRoutines.clearResult, StackRoutines.clearProgram,
    StackRoutines.clearStacks, StructuredProgram.State.withPC, Nat.add_assoc] using h

private theorem embed_array_input (d : Data) :
    embedState id arrayPorts d ⟨d.regs, d.stacks ∘ arrayPorts⟩ = d := by
  apply embedState_eq _ _ Function.injective_id arrayPorts_injective
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

private theorem embed_array_read (d : Data) (record : List Bool) :
    embedState id arrayPorts d
      ⟨readRegs d.regs 0 1 none, ArrayUpdatePrograms.readStacks record (d.stacks ∘ arrayPorts)⟩ =
        readOut d record := by
  apply embedState_eq _ _ Function.injective_id arrayPorts_injective
  · intros; rfl
  · intro i
    fin_cases i <;> simp [readOut, arrayPorts, ArrayUpdatePrograms.readStacks]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have h₁ : j ≠ 112 := fun h => hj ⟨1, by simpa [arrayPorts] using h.symm⟩
    have h₂ : j ≠ 113 := fun h => hj ⟨2, by simpa [arrayPorts] using h.symm⟩
    simp [readOut, h₁, h₂]

private theorem embed_array_replace (d : Data) (earlier : List (List Bool))
    (replacement rest : List Bool) :
    embedState id arrayPorts d
      ⟨readRegs d.regs 0 1 none,
        ArrayUpdatePrograms.replaceStacks earlier replacement rest (d.stacks ∘ arrayPorts)⟩ =
          replaceOut d earlier replacement rest := by
  apply embedState_eq _ _ Function.injective_id arrayPorts_injective
  · intros; rfl
  · intro i
    fin_cases i <;> simp [replaceOut, arrayPorts, ArrayUpdatePrograms.replaceStacks]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have h₁ : j ≠ 102 := fun h => hj ⟨0, by simpa [arrayPorts] using h.symm⟩
    have h₂ : j ≠ 113 := fun h => hj ⟨2, by simpa [arrayPorts] using h.symm⟩
    simp [replaceOut, h₁, h₂]

theorem arrayRead_eval (d : Data) (earlier : List (List Bool))
    (record rest widthWord indexWord : List Bool)
    (hs : d.stacks 102 = earlier.flatten ++ (record ++ rest))
    (hw : d.stacks 104 = widthWord) (hi : d.stacks 113 = indexWord)
    (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length)
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) :
    Eval arrayRead
      (earlier.length * (14 * widthWord.length + 10) + 15 * widthWord.length + 16)
      d (readOut d record) := by
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 16) 1 (by decide)
    earlier record rest widthWord indexWord d.regs (d.stacks ∘ arrayPorts)
    hs hw hi hiLen hrows hlen h114 h115 h116 h117
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 16) 1)
    id arrayPorts d Function.injective_id arrayPorts_injective
    (a := ⟨d.regs, d.stacks ∘ arrayPorts⟩)
    (b := ⟨readRegs d.regs 0 1 none,
      ArrayUpdatePrograms.readStacks record (d.stacks ∘ arrayPorts)⟩) ht
  simpa only [arrayRead, embed_array_input, embed_array_read] using he

theorem arrayReplace_eval (d : Data) (earlier : List (List Bool))
    (record replacement rest widthWord indexWord : List Bool)
    (hs : d.stacks 102 = earlier.flatten ++ (record ++ rest))
    (hn : d.stacks 112 = replacement)
    (hw : d.stacks 104 = widthWord) (hi : d.stacks 113 = indexWord)
    (hiLen : indexWord.length = earlier.length)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hlen : record.length = widthWord.length) (hnew : replacement.length = widthWord.length)
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) :
    Eval arrayReplace
      (earlier.length * (14 * widthWord.length + 10) + 20 * widthWord.length + 21)
      d (replaceOut d earlier replacement rest) := by
  have ht := ArrayUpdatePrograms.replaceProgram_trace (0 : Fin 16) 1 (by decide)
    earlier record replacement rest widthWord indexWord d.regs (d.stacks ∘ arrayPorts)
    hs hn hw hi hiLen hrows hlen hnew h114 h115 h116 h117
  have he := eval_call_lifted (ArrayUpdatePrograms.replaceProgram (0 : Fin 16) 1)
    id arrayPorts d Function.injective_id arrayPorts_injective
    (a := ⟨d.regs, d.stacks ∘ arrayPorts⟩)
    (b := ⟨readRegs d.regs 0 1 none,
      ArrayUpdatePrograms.replaceStacks earlier replacement rest (d.stacks ∘ arrayPorts)⟩) ht
  simpa only [arrayReplace, embed_array_input, embed_array_replace] using he

end SubexponentialSAT.SubexpJetCellProgram
namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

theorem regPorts_injective : Function.Injective regPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem scalarPorts_injective : Function.Injective scalarPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 128 => i.val) h)

theorem updatedState_stacks (d : Data) (regs : Fin 8 → Bool) (old result : List Bool)
    (earlier : List (List Bool)) (rest : List Bool)
    (h9 : d.stacks 9 = []) (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = []) :
    (updatedState d regs old result earlier rest).stacks =
      Function.update (Function.update d.stacks 8 []) 102
        (earlier.flatten ++ (result ++ rest)) := by
  funext j
  by_cases h8j : j = 8 <;> by_cases h9j : j = 9 <;>
    by_cases h102j : j = 102 <;> by_cases h112j : j = 112 <;> by_cases h113j : j = 113 <;>
    simp_all [updatedState, clearOut, replaceOut, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks ]

theorem updatedState_regs (d : Data) (regs : Fin 8 → Bool) (old result : List Bool)
    (earlier : List (List Bool)) (rest : List Bool) (i : Fin 8) :
    (updatedState d regs old result earlier rest).regs (Fin.natAdd 8 i) =
      d.regs (Fin.natAdd 8 i) := by
  have h0 : (Fin.natAdd 8 i : Fin 16) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have h1 : (Fin.natAdd 8 i : Fin 16) ≠ 1 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [updatedState, clearOut, replaceOut, addOut, moveOut, readOut, afterCopy,
    readRegs, h0, h1, Fin.addCases_right, Function.update_apply, -Fin.natAdd_eq_addNat]

end SubexponentialSAT.SubexpJetCellProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native update of one arbitrary-degree ring coefficient in a persistent
flat polynomial array. Every scan, copy, and scalar addition is paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpJetCellProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hB : 0 < baseWidth p t)
    {degree : ℕ} (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)

include cache hB hadd in
theorem addCall_eval (d : Data) (a b : Coeff (baseWidth p t) degree)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p t)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
        (RingProgram.flat a) (RingProgram.flat b) width [] frame).stacks i) :
    ∃ n ≤ addBudget degree (baseWidth p t), ∃ regs',
      Eval addCall n d
        (addOut d regs' (RingProgram.flat (ops.addRun a b).1)) := by
  obtain ⟨n, hn, regs', ht⟩ := DensePolynomialProgram.add_trace p t M cache hB
    (d.regs ∘ regPorts) ops hadd [a] [b] width frame hwidth
  have htrace : Trace DensePolynomialProgram.addProgram n
      ((DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
        (RingProgram.flat a) (RingProgram.flat b) width [] frame).withPC
          (some DensePolynomialProgram.addProgram.entry))
      ((DensePolynomialLoop.ready regs' M.bits
        (RingProgram.flat (ops.addRun a b).1) [] width [] frame).withPC none) := by
    simpa [DensePolynomialProgram.encode, SubexpDensePolynomial.addProgram] using ht
  have hcost : n ≤ addBudget degree (baseWidth p t) := by
    simpa [addBudget, Nat.mul_comm degree 2] using hn
  let left := DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
    (RingProgram.flat a) (RingProgram.flat b) width [] frame
  let right := DensePolynomialLoop.ready regs' M.bits
    (RingProgram.flat (ops.addRun a b).1) [] width [] frame
  have hl : embedState regPorts scalarPorts d left = d := by
    apply embedState_eq _ _ regPorts_injective scalarPorts_injective
    · intros; rfl
    · exact hsmall
    · intros; rfl
    · intros; rfl
  have hr : embedState regPorts scalarPorts d right =
      addOut d regs' (RingProgram.flat (ops.addRun a b).1) := by
    apply embedState_eq _ _ regPorts_injective scalarPorts_injective
    · intro i
      simp [addOut, right, DensePolynomialLoop.ready, DensePolynomialLoop.state, regPorts]
    · intro i
      have hi := hsmall i
      fin_cases i <;>
        simp [addOut, right, scalarPorts, DensePolynomialLoop.ready, DensePolynomialLoop.state,
          DensePolynomialLoop.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod] at hi ⊢ <;> exact hi
    · intro j
      refine Fin.addCases (m := 8) (n := 8) ?_ ?_ j
      · intro i hi
        exact False.elim (hi ⟨i, rfl⟩)
      · intro i _
        simp [addOut, Fin.addCases_right, -Fin.natAdd_eq_addNat]
    · intro j hj
      have h8 : j ≠ 8 := fun h => hj ⟨8, by simpa [scalarPorts] using h.symm⟩
      have h9 : j ≠ 9 := fun h => hj ⟨9, by simpa [scalarPorts] using h.symm⟩
      simp [addOut, h8, h9]
  have he := eval_call_lifted DensePolynomialProgram.addProgram regPorts scalarPorts d
    regPorts_injective scalarPorts_injective (a := left) (b := right) htrace
  exact ⟨n, hcost, regs', by simpa only [addCall, hl, hr] using he⟩

include cache hB hadd in
/-- Exact stack endpoint: only the consumed contribution and selected jet
cell change. The persistent index and all other caller stacks are preserved. -/
theorem updateCell_eval_oai (d : Data) (a b : Coeff (baseWidth p t) degree)
    (earlier : List (List Bool)) (rest widthWord indexWord scalarWidth : List Bool)
    (frame : Fin 6 → List Bool)
    (hs : d.stacks 102 = earlier.flatten ++ (RingProgram.flat b ++ rest))
    (hi : d.stacks 103 = indexWord) (hiLen : indexWord.length = earlier.length)
    (hw : d.stacks 104 = widthWord) (hwLen : widthWord.length = degree * baseWidth p t)
    (hrows : ∀ row ∈ earlier, row.length = widthWord.length)
    (hscalarWidth : scalarWidth.length = baseWidth p t)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (DensePolynomialLoop.ready (d.regs ∘ regPorts) M.bits
        (RingProgram.flat a) [] scalarWidth [] frame).stacks i)
    (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = [])
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) (h118 : d.stacks 118 = []) :
    ∃ n ≤ eventBudget degree (baseWidth p t) indexWord.length, ∃ e : Data,
      Eval updateCell n d e ∧
      e.stacks = Function.update (Function.update d.stacks 8 []) 102
        (earlier.flatten ++
          (RingProgram.flat (ops.addRun a b).1 ++ rest)) ∧
      (∀ i : Fin 8, e.regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i)) := by
  let d₁ := afterCopy d 103 113 0 1
  have h₁ := copyIndex_eval d h114
  let d₂ := readOut d₁ (RingProgram.flat b)
  have h₂ := arrayRead_eval d₁ earlier (RingProgram.flat b) rest widthWord indexWord
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using hs)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using hw)
    (by simp [d₁, afterCopy, StackRoutines.copyStacks, hi, h113]) hiLen hrows
    (by simp [hwLen])
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h114)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h115)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h116)
    (by simpa [d₁, afterCopy, StackRoutines.copyStacks] using h117)
  let d₃ := moveOut d₂ 112 9
  have h₃ := moveForward_eval d₂ 112 9 (by decide) (by decide) (by decide)
    (by simpa [d₂, d₁, readOut, afterCopy, StackRoutines.copyStacks] using h118)
  have hsmall₃ : ∀ i : Fin 20, d₃.stacks (scalarPorts i) =
      (DensePolynomialLoop.ready (d₃.regs ∘ regPorts) M.bits (RingProgram.flat a)
        (RingProgram.flat b) scalarWidth [] frame).stacks i := by
    intro i
    have h := hsmall i
    fin_cases i <;>
      simp [d₃, d₂, d₁, moveOut, readOut, afterCopy, StackRoutines.copyStacks,
        scalarPorts, DensePolynomialLoop.ready, DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
        Fin.addCases, Fin.coe_ofNat_eq_mod, h112] at h ⊢ <;> simp [h]
  obtain ⟨m, hm, regs', h₄⟩ := addCall_eval p t M cache hB ops hadd d₃ a b scalarWidth frame hscalarWidth hsmall₃
  let result := (ops.addRun a b).1
  let d₄ := addOut d₃ regs' (RingProgram.flat result)
  let d₅ := moveOut d₄ 8 112
  have h₅ := moveForward_eval d₄ 8 112 (by decide) (by decide) (by decide)
    (by simpa [d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h118)
  let d₆ := afterCopy d₅ 103 113 0 1
  have h₆ := copyIndex_eval d₅
    (by simpa [d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h114)
  let d₇ := replaceOut d₆ earlier (RingProgram.flat result) rest
  have h₇ := arrayReplace_eval d₆ earlier (RingProgram.flat b)
    (RingProgram.flat result) rest widthWord indexWord
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using hs)
    (by simp [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks])
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using hw)
    (by simp [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks, hi]) hiLen hrows (by simp [hwLen]) (by simp [hwLen])
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h114)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h115)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h116)
    (by simpa [d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut, afterCopy,
      StackRoutines.copyStacks] using h117)
  let d₈ := clearOut d₇ 112
  have h₈ := clear_eval d₇ 112
  have ht : Eval updateCell _ d d₈ :=
    Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄ (Eval.seq h₅
      (Eval.seq h₆ (Eval.seq h₇ h₈))))))
  refine ⟨_, ?_, d₈, ht, ?_, ?_⟩
  · simp [eventBudget, d₇, d₆, d₅, d₄, d₃, d₂, d₁, addOut, moveOut, readOut,
      replaceOut, afterCopy, StackRoutines.copyStacks, hi, h112, hwLen] at ⊢
    rw [hiLen]
    nlinarith [hm]
  · have h9 : d.stacks 9 = [] := by
      simpa [scalarPorts, DensePolynomialLoop.ready, DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
        Fin.addCases, Fin.coe_ofNat_eq_mod]
        using hsmall 9
    exact updatedState_stacks d regs' (RingProgram.flat b)
      (RingProgram.flat result) earlier rest h9 h112 h113
  · exact updatedState_regs d regs' (RingProgram.flat b)
      (RingProgram.flat result) earlier rest


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell_eval_oai
