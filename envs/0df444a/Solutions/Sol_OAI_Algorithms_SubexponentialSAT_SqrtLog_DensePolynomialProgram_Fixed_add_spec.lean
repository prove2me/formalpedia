-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:41:14.055761+00:00
-- url     : https://prove2.me/submissions/b599c78d-7115-48e6-9877-7de0a216ef18

import Mathlib
import Definitions.Def_OAIQ081S065
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialAddService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cached dense addition for the local CRT controller. The fixed service
copies operands 240/241, invokes the actual dense-add instruction table, and
moves its output to 244. All native workspace is restored. -/

namespace SubexponentialSAT.SubexpPolynomialAddService

open BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

private theorem transfer_run (src dst : Fin 256) (s : Store) (hne : src ≠ dst) :
    ExecutesIn (transfer src dst) (3 * (s src).length + 3) s
      (Function.update (Function.update s src []) dst ((s src).reverse ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  simpa [transfer, afterTransfer, StackRoutines.transferStacks] using
    SubexpScanPrimitives.transfer_eval (⟨regs, s⟩ : Data) src dst 0 1 hne (by decide)

theorem finish_run (s : Store) (out : List Bool)
    (h8 : s 8 = []) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn finish (6 * out.length + 6) (Function.update s 8 out)
      (Function.update s 244 out) := by
  let middle := Function.update s 245 out.reverse
  have he₁ : Function.update (Function.update (Function.update s 8 out) 8 []) 245
      (((Function.update s 8 out) 8).reverse ++ (Function.update s 8 out) 245) = middle := by
    funext i
    by_cases h : i = 8 <;> simp [middle, Function.update_apply, h, h8, h245]
  have h₁ : ExecutesIn (transfer 8 245) (3 * out.length + 3) (Function.update s 8 out) middle := by
    have h := transfer_run 8 245 (Function.update s 8 out) (by decide)
    rw [he₁] at h
    simpa using h
  have he₂ : Function.update (Function.update middle 245 []) 244
      ((middle 245).reverse ++ middle 244) = Function.update s 244 out := by
    funext i
    by_cases h : i = 245 <;> simp [middle, Function.update_apply, h, h245, h244]
  have h₂ : ExecutesIn (transfer 245 244) (3 * out.length + 3) middle
      (Function.update s 244 out) := by
    have h := transfer_run 245 244 middle (by decide)
    rw [he₂] at h
    simpa [middle] using h
  convert h₁.seq h₂ using 1
  · rfl
  · omega

end SubexponentialSAT.SubexpPolynomialAddService

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAddService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The arbitrary-degree native adder relocated into a caller, with all
untouched stacks preserved. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

/-- The relocated call changes only its two input/output ports. The complete
bit-level addition trace, including its return instruction, is retained. -/
theorem callAt_eval {degree r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s)
    (hB : 0 < baseWidth p t)
    (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (hadd : ∀ a b, (ops.addRun a b).1 = (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) degree)) (width : List Bool) (frame : Fin 6 → List Bool)
    (hwidth : width.length = baseWidth p t) (d : State r s)
    (hstore : ∀ i, d.stacks (ports i) =
      (ready (fun _ => false) M.bits (encode P) (encode Q) width [] frame).stacks i) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      n ≤ 7000 * (degree * (P.length + Q.length) + 1) * (baseWidth p t + 1)^2 + 1 ∧
      Eval (callAt registers ports) n d
        ⟨Function.extend registers rf d.regs,
          Function.update (Function.update d.stacks (ports 8)
            (encode (SubexpDensePolynomial.addProgram ops P Q).1)) (ports 9) []⟩ := by
  let start := ready (fun i => d.regs (registers i)) M.bits
    (encode P) (encode Q) width [] frame
  obtain ⟨n, hn, rf, ht⟩ := add_trace p t M cache hB (fun i => d.regs (registers i))
    ops hadd P Q width frame hwidth
  have hp : projectState registers ports d = start := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      exact hstore i
  have hc := eval_call_from_state addProgram registers ports d registers.injective ports.injective
    (by simpa only [hp] using ht)
  have hout :
      (ready rf M.bits (encode (SubexpDensePolynomial.addProgram ops P Q).1)
        [] width [] frame).stacks =
      Function.update (Function.update start.stacks 8
        (encode (SubexpDensePolynomial.addProgram ops P Q).1)) 9 [] := by
    funext i
    fin_cases i <;> simp [ready, DensePolynomialLoop.state, stackArray, start,
      Fin.addCases, Fin.coe_ofNat_eq_mod]
  have hi : Function.extend ports start.stacks d.stacks = d.stacks :=
    extend_agree ports start.stacks d.stacks hstore
  have he : embedState registers ports d
      (ready rf M.bits (encode (SubexpDensePolynomial.addProgram ops P Q).1)
        [] width [] frame) =
      (⟨Function.extend registers rf d.regs,
        Function.update (Function.update d.stacks (ports 8)
          (encode (SubexpDensePolynomial.addProgram ops P Q).1)) (ports 9) []⟩ : State r s) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · change Function.extend ports _ d.stacks = _
      rw [hout, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, hi]
  exact ⟨n, rf, hn, by simpa only [he, callAt] using hc⟩


namespace AddService
open SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpPolynomialAddService

theorem command_value {degree : ℕ} (s : Store) (hB : 0 < baseWidth p t)
    (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (hadd : ∀ a b, (ops.addRun a b).1 = (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (P Q : List (Coeff (baseWidth p t) degree))
    (width : List Bool) (frame : Fin 6 → List Bool) (hw : width.length = baseWidth p t)
    (hstore : ∀ i, s (ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hleft : s 240 = encode P)
    (hright : s 241 = encode Q) :
    ExecutesIn command (budget degree (baseWidth p t) P.length Q.length)
      s (Function.update s 244
        (encode (SubexpDensePolynomial.addProgram ops P Q).1)) := by
  let out := encode (SubexpDensePolynomial.addProgram ops P Q).1
  let s₁ := Function.update s 8 (s 240)
  let K := 7000 * (degree * (P.length + Q.length) + 1) * (baseWidth p t + 1)^2 + 1
  have h8 : s 8 = [] := by simpa [ports, DensePolynomialLoop.ready,
    DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
    Fin.addCases, Fin.coe_ofNat_eq_mod] using hstore 8
  have h9 : s 9 = [] := by simpa [ports, DensePolynomialLoop.ready,
    DensePolynomialLoop.state, DensePolynomialLoop.stackArray,
    Fin.addCases, Fin.coe_ofNat_eq_mod] using hstore 9
  have h₁ : ExecutesIn (copy 240 8) (7 * (s 240).length + 5) s s₁ := by
    simpa [s₁, h8] using copy_run 240 8 s (by decide) (by decide) (by decide) h120
  have h₂ : ExecutesIn (copy 241 9) (7 * (s 241).length + 5) s₁ (prepared s) := by
    simpa [s₁, prepared, h9] using copy_run 241 9 s₁
      (by decide) (by decide) (by decide) (by simp [s₁, h120])
  have hs : ∀ i, (prepared s) (ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits
        (encode P) (encode Q)
        width [] frame).stacks i := by
    intro i
    have hi := hstore i
    fin_cases i <;>
      simp [prepared, ports, DensePolynomialLoop.ready, DensePolynomialLoop.state,
        DensePolynomialLoop.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod, hleft, hright] at hi ⊢
      <;> assumption
  have hout : Function.update (Function.update (prepared s) (ports 8) out) (ports 9) [] =
      Function.update s 8 out := by
    funext i
    by_cases h : i = 9 <;> by_cases h' : i = 8 <;>
      simp [ports, prepared, Function.update_apply, h, h', h9]
  have h₃ : ExecutesIn (DensePolynomialProgram.callAt registers ports) K (prepared s) (Function.update s 8 out) := by
    intro regs
    obtain ⟨n, rf, hn, he⟩ := DensePolynomialProgram.callAt_eval p t M cache registers ports
      hB ops hadd P Q width frame hw (⟨regs, prepared s⟩ : SubexponentialSAT.SubexpConvolutionControl.Data) hs
    refine ⟨n, Function.extend registers rf regs, hn, ?_⟩
    simpa only [out, hout] using he
  have h₄ := finish_run s out h8 h244 h245
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  apply h.mono
  rw [hleft, hright, encode_length, encode_length]
  have hlen : out.length ≤ (P.length + Q.length) * (degree * baseWidth p t) := by
    dsimp [out]
    rw [encode_length, addProgram_length]
    exact Nat.mul_le_mul_right _ (by omega)
  change _ ≤ budget degree (baseWidth p t) P.length Q.length
  dsimp [K, budget]
  nlinarith

end AddService
end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-length coefficient-array carriers for the local CRT/Horner loops.
The multiplication service obtains its zero array and length from protected
caches192/193. The relocation is in the finite instruction table, so no tape
copy is charged or hidden by the change of physical port names. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod


variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))


/-- The fixed-length addition instance uses the same restored native frame. -/
theorem add_spec_oai (hB : 0 < baseWidth p t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (base : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table base scalarWidth frame) :
    CRTLocalProgram.ServiceSpec base (encode (J:=J)) AddService.command (add ops)
      (AddService.budget degree (baseWidth p t) J J) := by
  intro s P Q hf hP hQ h244 h245
  have hs : ∀ i, s (SubexponentialSAT.SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] scalarWidth [] frame).stacks i := by
    intro i
    have hi := H.low i
    have hh := hf (SubexponentialSAT.SubexpPolynomialAddService.ports i)
      (by dsimp [SubexponentialSAT.SubexpPolynomialAddService.ports]; omega)
    exact hh.trans hi
  have h := AddService.command_value p t M cache s hB ops hadd P.1 Q.1 scalarWidth frame
    H.scalarWidthLength hs ((hf 120 (by decide)).trans H.scratch) h244 h245 hP hQ
  simpa only [encode, add, P.2, Q.2] using h

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add_spec_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add_spec_oai
