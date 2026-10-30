-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrix_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:37:26.84959+00:00
-- url     : https://prove2.me/submissions/ec89dbd6-7a3c-491f-b095-5f57f114126b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S106

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

theorem words_length (xs : List (List Bool)) (B : ℕ) (h : ∀ x ∈ xs, x.length = B) :
    (words xs).length = xs.length * (2 * B + 1) := by
  induction xs with
  | nil => simp [words]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [words, List.length_append, Encoding.length_frame, hx, hs, List.length_cons]
    ring

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScalarProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Scalar subroutines with the matrix checker's surrounding data preserved

These are calls to the actual finite modular-arithmetic instruction tables.
The eight additional ports carry vector streams, output, and runtime metadata.
-/

namespace SubexponentialSAT.Subexp.MatrixScalarProgram

open BitProgram StructuredCalls BinaryArithmetic ModularRingPrograms
open MatrixProgramSupport

theorem servicePort_injective : Function.Injective servicePort := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin 16 => z.val) h

private theorem outside_service (j : Fin 16) (hj : 8 ≤ j.val) :
    ¬ ∃ i, servicePort i = j := by
  rintro ⟨i, h⟩
  have hv := congrArg Fin.val h
  simp only [servicePort] at hv
  omega

private theorem embed_scalar (regs baseRegs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) :
    embedState id servicePort (state baseRegs [] [] modulus acc left right saved output zero input)
      ⟨regs, extendSeven (scalarInput x y modulus) []⟩ =
      state regs x y modulus acc left right saved output zero input := by
  apply data_ext
  · simp [embedState ]
  · funext j
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      have hi : servicePort i = j := Fin.ext rfl
      rw [← hi, embedState_stack _ _ _ _ servicePort_injective]
      clear_value i
      fin_cases i <;> rfl
    · rw [embedState_stack_frame _ _ _ _ j (outside_service j (by omega))]
      fin_cases j <;> simp_all [ scalarStacks ]

theorem multiply_eval (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) (B : ℕ)
    (hx : x.length = B) (hy : y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ n ≤ 6000 * (B + 1) ^ 2, ∃ regs' result,
      Eval multiply n (state regs x y modulus acc left right saved output zero input)
        (state regs' result [] modulus acc left right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result = (BinaryArithmetic.toNat x * BinaryArithmetic.toNat y) % BinaryArithmetic.toNat modulus := by
  obtain ⟨regs', result, ⟨n, hn, ht⟩, hl, hv⟩ :=
    wordMul_value regs x y modulus B hx hy hml hm hcap
  have he := eval_call_lifted wordMulProgram id servicePort
    (state regs [] [] modulus acc left right saved output zero input)
    Function.injective_id servicePort_injective
    (a := ⟨regs, extendSeven (scalarInput x y modulus) []⟩)
    (b := ⟨regs', extendSeven (scalarInput result [] modulus) []⟩) ht
  change Eval multiply n
    (embedState id servicePort _ ⟨regs, extendSeven (scalarInput x y modulus) []⟩)
    (embedState id servicePort _ ⟨regs', extendSeven (scalarInput result [] modulus) []⟩) at he
  rw [embed_scalar, embed_scalar] at he
  exact ⟨n, hn, regs', result, he, hl, hv⟩

theorem add_eval (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) (B : ℕ)
    (hx : x.length = B) (hy : y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ n ≤ 6000 * (B + 1) ^ 2, ∃ regs' result,
      Eval add n (state regs x y modulus acc left right saved output zero input)
        (state regs' result [] modulus acc left right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result = (BinaryArithmetic.toNat x + BinaryArithmetic.toNat y) % BinaryArithmetic.toNat modulus := by
  obtain ⟨regs', result, ⟨n, hn, ht⟩, hl, hv⟩ :=
    wordAdd_value regs x y modulus B hx hy hml hm hcap
  have he := eval_call_lifted wordAddProgram id servicePort
    (state regs [] [] modulus acc left right saved output zero input)
    Function.injective_id servicePort_injective
    (a := ⟨regs, extendSeven (scalarInput x y modulus) []⟩)
    (b := ⟨regs', extendSeven (scalarInput result [] modulus) []⟩) ht
  change Eval add n
    (embedState id servicePort _ ⟨regs, extendSeven (scalarInput x y modulus) []⟩)
    (embedState id servicePort _ ⟨regs', extendSeven (scalarInput result [] modulus) []⟩) at he
  rw [embed_scalar, embed_scalar] at he
  exact ⟨n, hn, regs', result, he, hl, hv⟩

/-- One genuine modular multiply-add, preserving both vector streams and all
saved caller data. The accumulator is returned on port 8. -/
theorem accumulate_eval (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) (B : ℕ)
    (hx : x.length = B) (hy : y.length = B) (ha : acc.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ n ≤ 12000 * (B + 1) ^ 2 + 12 * B + 12, ∃ regs' result,
      Eval accumulate n (state regs x y modulus acc left right saved output zero input)
        (state regs' [] [] modulus result left right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat x : ZMod (BinaryArithmetic.toNat modulus)) * (BinaryArithmetic.toNat y : ZMod (BinaryArithmetic.toNat modulus)) +
          (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨n₁, hn₁, r₁, product, h₁, hl₁, hv₁⟩ :=
    multiply_eval regs x y modulus acc left right saved output zero input B hx hy hml hm hcap
  obtain ⟨d₂, h₂, hs₂⟩ := move_eval (8 : Fin 16) 1 9 (by decide) (by decide) (by decide)
    (state r₁ product [] modulus acc left right saved output zero input) rfl rfl
  have hd₂ : d₂ = state d₂.regs product acc modulus [] left right saved output zero input := by
    apply data_ext <;> try rfl
    rw [hs₂]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₂] at h₂
  obtain ⟨n₃, hn₃, r₃, result, h₃, hl₃, hv₃⟩ :=
    add_eval d₂.regs product acc modulus [] left right saved output zero input B hl₁ ha hml hm hcap
  obtain ⟨d₄, h₄, hs₄⟩ := move_eval (0 : Fin 16) 8 9 (by decide) (by decide) (by decide)
    (state r₃ result [] modulus [] left right saved output zero input) rfl rfl
  have hd₄ : d₄ = state d₄.regs [] [] modulus result left right saved output zero input := by
    apply data_ext <;> try rfl
    rw [hs₄]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₄] at h₄
  have he := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))
  refine ⟨n₁ + (6 * B + 6 + (n₃ + (6 * B + 6))), by omega,
    d₄.regs, result, ?_, hl₃, ?_, ?_⟩
  · simpa [accumulate, state, scalarStacks, ha, hl₃] using he
  · rw [hv₃]
    exact Nat.mod_lt _ hm
  · rw [hv₃, ZMod.natCast_mod, Nat.cast_add, hv₁, ZMod.natCast_mod, Nat.cast_mul]

end SubexponentialSAT.Subexp.MatrixScalarProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed encoded modular dot products

Vectors are streams of framed, fixed-width little-endian scalar words. The
loop reads the two streams itself and calls the measured multiply-add routine.
Its finite control is independent of the modulus, width, and vector length.
-/

namespace SubexponentialSAT.Subexp.MatrixProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram

theorem term_eval (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) (B : ℕ)
    (hx : x.length = B) (hy : y.length = B) (ha : acc.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ n ≤ termBudget B, ∃ regs' result,
      Eval term n
        (state regs [] [] modulus acc (Encoding.frame x ++ left)
          (Encoding.frame y ++ right) saved output zero input)
        (state regs' [] [] modulus result left right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat x : ZMod (BinaryArithmetic.toNat modulus)) * (BinaryArithmetic.toNat y : ZMod (BinaryArithmetic.toNat modulus)) +
          (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨d₁, h₁, hs₁⟩ := readWord_eval (10 : Fin 16) 0 9
    (by decide) (by decide) (by decide)
    (state regs [] [] modulus acc (Encoding.frame x ++ left)
      (Encoding.frame y ++ right) saved output zero input) x left rfl rfl rfl
  have hd₁ : d₁ = state d₁.regs x [] modulus acc left
      (Encoding.frame y ++ right) saved output zero input := by
    apply data_ext <;> try rfl
    rw [hs₁]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₁] at h₁
  obtain ⟨d₂, h₂, hs₂⟩ := readWord_eval (11 : Fin 16) 1 9
    (by decide) (by decide) (by decide)
    (state d₁.regs x [] modulus acc left (Encoding.frame y ++ right) saved output zero input)
    y right rfl rfl rfl
  have hd₂ : d₂ = state d₂.regs x y modulus acc left right saved output zero input := by
    apply data_ext <;> try rfl
    rw [hs₂]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₂] at h₂
  obtain ⟨n₃, hn₃, r₃, result, h₃, hl₃, hc₃, hv₃⟩ :=
    accumulate_eval d₂.regs x y modulus acc left right saved output zero input B
      hx hy ha hml hm hcap
  refine ⟨(9 * B + 7) + ((9 * B + 7) + n₃), ?_, r₃, result, ?_, hl₃, hc₃, hv₃⟩
  · unfold termBudget
    omega
  · simpa only [term, hx, hy] using Eval.seq h₁ (Eval.seq h₂ h₃)

theorem peekLeft_eval (regs : Fin 8 → Bool) (modulus acc : List Bool)
    (xs : List (List Bool)) (right saved output zero input : List Bool) :
    Eval peekLeft 1 (state regs [] [] modulus acc (words xs) right saved output zero input)
      (ready regs modulus acc xs right saved output zero input) := by
  exact .base (.atom _ _)

theorem ready_nil (regs : Fin 8 → Bool) (modulus acc right saved output zero input : List Bool) :
    (ready regs modulus acc [] right saved output zero input).regs 1 = false := by
  simp [ready, words, state, readRegs]

theorem ready_cons (regs : Fin 8 → Bool) (modulus acc x : List Bool)
    (xs : List (List Bool)) (right saved output zero input : List Bool) :
    (ready regs modulus acc (x :: xs) right saved output zero input).regs 1 = true := by
  cases x <;> simp [ready, words, state, readRegs, Encoding.frame]

theorem dotLoop_eval (xs ys : List (List Bool)) (B : ℕ) (modulus : List Bool)
    (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.length = B) (hy : ∀ y ∈ ys, y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (acc right saved output zero input : List Bool)
    (ha : acc.length = B) (hac : BinaryArithmetic.toNat acc < BinaryArithmetic.toNat modulus) :
    ∃ n ≤ xs.length * (termBudget B + 2) + 1, ∃ regs' result,
      Eval dotLoop n (ready regs modulus acc xs (words ys ++ right) saved output zero input)
        (state regs' [] [] modulus result [] right saved output zero input) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        dotValue (BinaryArithmetic.toNat modulus) xs ys + (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  induction xs generalizing ys regs acc with
  | nil =>
    have hys : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    refine ⟨1, by simp, (ready regs modulus acc [] right saved output zero input).regs,
      acc, ?_, ha, hac, by simp [dotValue]⟩
    simpa [dotLoop, ready, words, state] using
      (Eval.while_false (test := (1 : Fin 8)) (body := dotBody)
        (ready_nil regs modulus acc right saved output zero input))
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hxt := hx x (by simp)
      have hyt := hy y (by simp)
      let rr := (ready regs modulus acc (x :: xs)
        (words (y :: ys) ++ right) saved output zero input).regs
      obtain ⟨nt, hnt, rt, accNext, het, hlt, hct, hvt⟩ := term_eval rr x y modulus acc
        (words xs) (words ys ++ right) saved output zero input B hxt hyt ha hml hm hcap
      have hterm : Eval term nt
          (ready regs modulus acc (x :: xs) (words (y :: ys) ++ right) saved output zero input)
          (state rt [] [] modulus accNext (words xs) (words ys ++ right) saved output zero input) := by
        simpa [ready, rr, words, List.append_assoc] using het
      have hpeek := peekLeft_eval rt modulus accNext xs (words ys ++ right) saved output zero input
      obtain ⟨nr, hnr, rfinal, result, her, hlr, hcr, hvr⟩ := ih ys (by simpa using hlen)
        (fun z hz => hx z (List.mem_cons_of_mem _ hz))
        (fun z hz => hy z (List.mem_cons_of_mem _ hz)) rt accNext hlt hct
      have he := Eval.while_true
        (ready_cons regs modulus acc x xs (words (y :: ys) ++ right) saved output zero input)
        (Eval.seq hterm hpeek) her
      refine ⟨(nt + 1) + nr + 1, ?_, rfinal, result, he, hlr, hcr, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · rw [hvr, hvt]
        simp only [dotValue]
        ring

/-- Actual instruction trace for two independently serialized vectors. The
right-stream suffix is preserved, so the same routine consumes one matrix row. -/
theorem dot_trace (xs ys : List (List Bool)) (B : ℕ) (modulus : List Bool)
    (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.length = B) (hy : ∀ y ∈ ys, y.length = B)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (acc right saved output zero input : List Bool)
    (ha : acc.length = B) (hac : BinaryArithmetic.toNat acc < BinaryArithmetic.toNat modulus) :
    ∃ n ≤ xs.length * (termBudget B + 2) + 3, ∃ regs' result,
      Trace dotProgram n
        ((state regs [] [] modulus acc (words xs) (words ys ++ right)
          saved output zero input).withPC (some dotProgram.entry))
        ((state regs' [] [] modulus result [] right saved output zero input).withPC none) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) =
        dotValue (BinaryArithmetic.toNat modulus) xs ys + (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨n, hn, rf, result, he, hl, hc, hv⟩ := dotLoop_eval xs ys B modulus hlen hx hy hml hm
    hcap regs acc right saved output zero input ha hac
  have hp := peekLeft_eval regs modulus acc xs (words ys ++ right) saved output zero input
  exact ⟨(1 + n) + 1, by omega, rf, result,
    compiled_halt_trace (Eval.seq hp he) 10 8, hl, hc, hv⟩

end SubexponentialSAT.Subexp.MatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixVectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixProgram

/-- One row is read from the right stream. The saved vector, zero word,
modulus, and outer-loop counter are preserved. Its framed result is emitted
in reverse on port 13 for a final linear-time reversal. -/
theorem row_eval (xs ys : List (List Bool)) (B : ℕ) (modulus zero : List Bool)
    (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.length = B) (hy : ∀ y ∈ ys, y.length = B)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (right output count : List Bool) :
    ∃ n ≤ rowBudget xs.length B, ∃ regs' result,
      Eval row n
        (state regs [] [] modulus [] [] (words ys ++ right) (words xs) output zero count)
        (state regs' [] [] modulus [] [] right (words xs)
          ((Encoding.frame result).reverse ++ output) zero count) ∧
      result.length = B ∧ BinaryArithmetic.toNat result < BinaryArithmetic.toNat modulus ∧
      (BinaryArithmetic.toNat result : ZMod (BinaryArithmetic.toNat modulus)) = dotValue (BinaryArithmetic.toNat modulus) xs ys := by
  obtain ⟨d₁, h₁, hs₁⟩ := MatrixProgramSupport.copy_eval (12 : Fin 16) 10 9
    (by decide) (by decide) (by decide)
    (state regs [] [] modulus [] [] (words ys ++ right) (words xs) output zero count) rfl
  have hd₁ : d₁ = state d₁.regs [] [] modulus [] (words xs)
      (words ys ++ right) (words xs) output zero count := by
    apply data_ext <;> try rfl
    rw [hs₁]
    funext j
    fin_cases j <;> simp [ scalarStacks, StackRoutines.copyStacks]
  rw [hd₁] at h₁
  obtain ⟨d₂, h₂, hs₂⟩ := MatrixProgramSupport.copy_eval (14 : Fin 16) 8 9
    (by decide) (by decide) (by decide)
    (state d₁.regs [] [] modulus [] (words xs) (words ys ++ right) (words xs) output zero count) rfl
  have hd₂ : d₂ = state d₂.regs [] [] modulus zero (words xs)
      (words ys ++ right) (words xs) output zero count := by
    apply data_ext <;> try rfl
    rw [hs₂]
    funext j
    fin_cases j <;> simp [ scalarStacks, StackRoutines.copyStacks]
  rw [hd₂] at h₂
  obtain ⟨n₃, hn₃, r₃, result, h₃, hl₃, hc₃, hv₃⟩ :=
    dot_trace xs ys B modulus hlen hx hy hml hm hcap d₂.regs zero right
      (words xs) output zero count hz (by simpa only [hzv] using hm)
  have he₃ : Eval (.call dotProgram) n₃
      (state d₂.regs [] [] modulus zero (words xs) (words ys ++ right) (words xs) output zero count)
      (state r₃ [] [] modulus result [] right (words xs) output zero count) := .call _ h₃
  obtain ⟨d₄, h₄, hs₄⟩ := emitFrame_eval (8 : Fin 16) 0 9
    (by decide) (by decide) (by decide)
    (state r₃ [] [] modulus result [] right (words xs) output zero count) rfl
  have hd₄ : d₄ = state d₄.regs (Encoding.frame result) [] modulus [] []
      right (words xs) output zero count := by
    apply data_ext <;> try rfl
    rw [hs₄]
    funext j
    fin_cases j <;> simp [ scalarStacks]
  rw [hd₄] at h₄
  obtain ⟨d₅, h₅, hs₅⟩ := transfer_eval (0 : Fin 16) 13 (by decide)
    (state d₄.regs (Encoding.frame result) [] modulus [] [] right (words xs) output zero count)
  have hd₅ : d₅ = state d₅.regs [] [] modulus [] [] right (words xs)
      ((Encoding.frame result).reverse ++ output) zero count := by
    apply data_ext <;> try rfl
    rw [hs₅]
    funext j
    fin_cases j <;> simp [ scalarStacks, StackRoutines.transferStacks]
  rw [hd₅] at h₅
  have he := Eval.seq h₁ (Eval.seq h₂ (Eval.seq he₃ (Eval.seq h₄ h₅)))
  refine ⟨(7 * (xs.length * (2 * B + 1)) + 5) + (7 * B + 5 +
      (n₃ + (8 * B + 8 + (3 * (2 * B + 1) + 3)))), ?_, d₅.regs, result, ?_, hl₃, hc₃, ?_⟩
  · unfold rowBudget
    omega
  · simpa [row, state, scalarStacks, words_length xs B hx, hz, hl₃,
      Encoding.length_frame] using he
  · simpa only [hzv, Nat.cast_zero, add_zero] using hv₃

theorem popRow_eval (regs : Fin 8 → Bool) (modulus : List Bool) (xs : List (List Bool))
    (right output zero : List Bool) (m : ℕ) :
    Eval popRow 1
      (state regs [] [] modulus [] [] right (words xs) output zero (List.replicate m true))
      (readyMatrix regs modulus xs right output zero m) := by
  have hfinish : (StructuredProgram.Atom.pop (15 : Fin 16) (0 : Fin 8) 1).eval
      (state regs [] [] modulus [] [] right (words xs) output zero (List.replicate m true)) =
      readyMatrix regs modulus xs right output zero m := by
    apply MatrixProgramSupport.data_ext
    · simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, scalarStacks]
    · funext j
      fin_cases j <;>
        simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr, scalarStacks]
  rw [← hfinish]
  exact .base (.atom _ _)

theorem readyMatrix_zero (regs : Fin 8 → Bool) (modulus : List Bool) (xs : List (List Bool))
    (right output zero : List Bool) :
    (readyMatrix regs modulus xs right output zero 0).regs 1 = false := by
  simp [ readRegs]

theorem readyMatrix_succ (regs : Fin 8 → Bool) (modulus : List Bool) (xs : List (List Bool))
    (right output zero : List Bool) (m : ℕ) :
    (readyMatrix regs modulus xs right output zero (m + 1)).regs 1 = true := by
  simp [ readRegs, List.replicate_succ]

theorem result_widths {p B : ℕ} {xs : List (List Bool)}
    {rows : List (List (List Bool))} {zs : List (List Bool)}
    (h : List.Forall₂ (RowResult p B xs) rows zs) : ∀ z ∈ zs, z.length = B := by
  induction h with
  | nil => simp
  | cons hh ht ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hh.1
    · exact ih z hz

theorem matrixLoop_eval (xs : List (List Bool)) (rows : List (List (List Bool)))
    (B : ℕ) (modulus zero : List Bool)
    (hx : ∀ x ∈ xs, x.length = B)
    (hrows : ∀ ys ∈ rows, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (right output : List Bool) :
    ∃ n ≤ rows.length * (rowBudget xs.length B + 2) + 1, ∃ regs' results,
      Eval matrixLoop n
        (readyMatrix regs modulus xs (matrixWords rows ++ right) output zero rows.length)
        (state regs' [] [] modulus [] [] right (words xs)
          ((words results).reverse ++ output) zero []) ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B xs) rows results := by
  induction rows generalizing regs output with
  | nil =>
    refine ⟨1, by simp, (readyMatrix regs modulus xs right output zero 0).regs,
      [], ?_, .nil⟩
    simpa [matrixLoop, matrixWords, words, readyMatrix, state] using
      (Eval.while_false (test := (1 : Fin 8)) (body := matrixBody)
        (readyMatrix_zero regs modulus xs right output zero))
  | cons ys rows ih =>
    have hy := hrows ys (by simp)
    let rr := (readyMatrix regs modulus xs
      (matrixWords (ys :: rows) ++ right) output zero (ys :: rows).length).regs
    obtain ⟨nr, hnr, r₁, result, her, hlr, hcr, hvr⟩ := row_eval xs ys B modulus zero
      hy.1 hx hy.2 hz hzv hml hm hcap rr (matrixWords rows ++ right) output
      (List.replicate rows.length true)
    have hrow : Eval row nr
        (readyMatrix regs modulus xs (matrixWords (ys :: rows) ++ right) output zero
          (ys :: rows).length)
        (state r₁ [] [] modulus [] [] (matrixWords rows ++ right) (words xs)
          ((Encoding.frame result).reverse ++ output) zero (List.replicate rows.length true)) := by
      simpa only [rr, readyMatrix, matrixWords, List.length_cons, List.replicate_succ,
        List.tail_cons, List.append_assoc] using her
    have hp := popRow_eval r₁ modulus xs (matrixWords rows ++ right)
      ((Encoding.frame result).reverse ++ output) zero rows.length
    obtain ⟨nt, hnt, rf, results, het, hrel⟩ :=
      ih (fun row hr => hrows row (List.mem_cons_of_mem _ hr)) r₁
        ((Encoding.frame result).reverse ++ output)
    have he := Eval.while_true
      (readyMatrix_succ regs modulus xs (matrixWords (ys :: rows) ++ right)
        output zero rows.length) (Eval.seq hrow hp) het
    refine ⟨(nr + 1) + nt + 1, ?_, rf, result :: results, ?_, .cons ⟨hlr, hcr, hvr⟩ hrel⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [matrixLoop, matrixBody, words, List.length_cons, Nat.add_comm,
        List.reverse_append, List.append_assoc] using he

/-- A whole matrix-vector product with actual framing, scalar arithmetic,
row iteration, and output reversal. The unary row count is runtime input;
empty rows and zero-column matrices are handled without an EOF assumption. -/
theorem matrix_trace_oai (xs : List (List Bool)) (rows : List (List (List Bool)))
    (B : ℕ) (modulus zero : List Bool)
    (hx : ∀ x ∈ xs, x.length = B)
    (hrows : ∀ ys ∈ rows, xs.length = ys.length ∧ ∀ y ∈ ys, y.length = B)
    (hz : zero.length = B) (hzv : BinaryArithmetic.toNat zero = 0)
    (hml : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcap : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (regs : Fin 8 → Bool) (right : List Bool) :
    ∃ n ≤ matrixBudget rows.length xs.length B, ∃ regs' results,
      Trace matrixProgram n
        ((state regs [] [] modulus [] [] (matrixWords rows ++ right) (words xs)
          [] zero (List.replicate rows.length true)).withPC (some matrixProgram.entry))
        ((state regs' [] [] modulus (words results) [] right (words xs) [] zero []).withPC none) ∧
      List.Forall₂ (RowResult (BinaryArithmetic.toNat modulus) B xs) rows results := by
  obtain ⟨n, hn, rf, results, he, hrel⟩ := matrixLoop_eval xs rows B modulus zero
    hx hrows hz hzv hml hm hcap regs right []
  have hp := popRow_eval regs modulus xs (matrixWords rows ++ right) [] zero rows.length
  have he' : Eval matrixLoop n
      (readyMatrix regs modulus xs (matrixWords rows ++ right) [] zero rows.length)
      (state rf [] [] modulus [] [] right (words xs) (words results).reverse zero []) := by
    simpa only [List.append_nil] using he
  obtain ⟨d, ht, hst⟩ := transfer_eval (13 : Fin 16) 8 (by decide)
    (state rf [] [] modulus [] [] right (words xs) (words results).reverse zero [])
  have hd : d = state d.regs [] [] modulus (words results) [] right (words xs) [] zero [] := by
    apply data_ext <;> try rfl
    rw [hst]
    funext j
    fin_cases j <;> simp [ scalarStacks, StackRoutines.transferStacks]
  rw [hd] at ht
  have hwidth : (words results).length = rows.length * (2 * B + 1) := by
    rw [words_length results B (result_widths hrel), ← hrel.length_eq]
  have hrun := compiled_halt_trace (Eval.seq hp (Eval.seq he' ht)) 11 8
  refine ⟨1 + (n + (3 * (rows.length * (2 * B + 1)) + 3)) + 1, ?_, d.regs, results, ?_, hrel⟩
  · unfold matrixBudget
    nlinarith only [hn]
  · simpa [matrixProgram, matrixCommand, state, scalarStacks, List.length_reverse, hwidth] using hrun

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrix_trace_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrix_trace_oai
