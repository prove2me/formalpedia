-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.frontend_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:17:25.699055+00:00
-- url     : https://prove2.me/submissions/ab193404-a22d-4107-8331-cd1de71a8c62

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationCorrectness_normalizedBody_length_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationProgram_program_runsIn

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF

universe u

variable {α : Type u} [DecidableEq α]

theorem dedupLiterals_nodup (C : Clause α) : (dedupLiterals C).Nodup := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih
    · simp only [dedupLiterals, ite_eq_right h, List.nodup_cons]
      exact ⟨fun hm => h ((contains_true x xs).mpr ((mem_dedupLiterals x xs).mp hm)), ih⟩

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem dedupClauses_subset (F : Formula α) : dedupClauses F ⊆ F := by
  intro C hC
  induction F with
  | nil => simp [dedupClauses] at hC
  | cons D F ih =>
    by_cases h : F.any (fun E => equivalent D E) = true
    · have htail : C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact List.mem_cons_of_mem D (ih htail)
    · have hsplit : C = D ∨ C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact hsplit.elim (fun h => h ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem D (ih h))

theorem absorb_subset (F : Formula α) : absorb F ⊆ F := by
  intro C hC
  exact dedupClauses_subset F (List.mem_filter.mp hC).1

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem normalize_literal_nodup (neg : α → α) (F : Formula α) :
    ∀ C ∈ normalize neg F, C.Nodup := by
  intro C hC
  have h1 := absorb_subset _ hC
  have h2 := (List.mem_filter.mp h1).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h2
  exact dedupLiterals_nodup D

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

@[simp] theorem dedupLiterals_length (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

end SubexponentialSAT.ExecSunflowerSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecQuantitativeSparsify
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Quantitative bounds for the executable list sparsifier

This module instantiates the actual list search and depth-first worklist at the
arithmetically selected inverse budget. The finite-set view of each output is
used only for SAT semantics. Node visits are counted by the actual worklist;
they are not presented as primitive bit-machine transitions.
-/

namespace SubexponentialSAT.ExecQuantitativeSparsify

open SAT

variable {n : ℕ}

theorem literalList_codes (C : Clause (Fin n)) :
    (literalList C).map Encoding.literalCode = Encoding.clauseNumbers C := by
  let r := fun a b : Literal (Fin n) => Encoding.literalCode a ≤ Encoding.literalCode b
  let _ : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  let _ : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  let _ : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.literalCode_injective (le_antisymm h h')⟩
  unfold literalList Encoding.clauseNumbers
  let e : Literal (Fin n) ↪ ℕ := ⟨Encoding.literalCode, Encoding.literalCode_injective⟩
  have he : C.map e = C.image Encoding.literalCode := Finset.map_eq_image e C
  rw [← he]
  change (C.val.sort _).map Encoding.literalCode = (C.val.map Encoding.literalCode).sort _
  apply Multiset.map_sort
  intro a ha b hb
  rfl

theorem orderedClauses_codes (F : CNF (Fin n)) :
    (orderedClauses F).map Encoding.clauseNumbers = Encoding.cnfNumbers F := by
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  let _ : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  let _ : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  let _ : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  unfold orderedClauses Encoding.cnfNumbers
  let e : Clause (Fin n) ↪ List ℕ :=
    ⟨Encoding.clauseNumbers, Encoding.clauseNumbers_injective⟩
  have he : F.map e = F.image Encoding.clauseNumbers := Finset.map_eq_image e F
  rw [← he]
  change (F.val.sort _).map Encoding.clauseNumbers = (F.val.map Encoding.clauseNumbers).sort _
  apply Multiset.map_sort
  intro a ha b hb
  rfl

/-- The numerical payload of the executable input is exactly the canonical
payload specified by `Encoding`, including both sorting conventions. -/
theorem formulaList_codes (F : CNF (Fin n)) :
    (formulaList F).map (List.map Encoding.literalCode) = Encoding.cnfNumbers F := by
  simp only [formulaList, List.map_map, Function.comp_def, literalList_codes]
  exact orderedClauses_codes F

theorem encode_formulaList (F : CNF (Fin n)) :
    encodeRawFormula (formulaList F) = Encoding.encodeCNFBody F := by
  rw [encodeRawFormula, formulaList_codes]
  rfl

end SubexponentialSAT.ExecQuantitativeSparsify

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Syntactic frontend for the variable-parameter SAT algorithm

The external input declares `n` Boolean coordinates. We first normalize the
finite CNF, then enumerate only its syntactically appearing coordinates in
increasing order. The resulting coordinate set is retained through all later
branching; this frontend is not reapplied at sparsification leaves.

All constructions inspect finite syntax. No satisfiability test, choice of a
satisfying assignment, or noncomputable enumeration is used by `prepare`.
-/

namespace SubexponentialSAT.SubexpFrontend

open SAT

theorem literalCode_negate {n : ℕ} (l : Literal (Fin n)) :
    Encoding.literalCode l.negate = negateCode (Encoding.literalCode l) := by
  rcases l with ⟨v, p⟩
  have hd0 : (2 * v.val) / 2 = v.val := by omega
  have hd1 : (2 * v.val + 1) / 2 = v.val := by omega
  have hm0 : (2 * v.val) % 2 = 0 := by omega
  have hm1 : (2 * v.val + 1) % 2 = 1 := by omega
  cases p <;> simp [Encoding.literalCode, Literal.negate, negateCode,
    hd0, hd1, hm0, hm1]

end SubexponentialSAT.SubexpFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFCodeTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact list transport through literal codes

These equalities preserve clause order and the last-occurrence conventions.
They connect the encoded normalization programs to the typed executable CNF
operations, rather than identifying only their finite-set semantics.
-/

namespace SubexponentialSAT.ExecCNFCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
private theorem filter_map_comm (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (L : List α) :
    (L.map f).filter q = (L.filter p).map f := by
  induction L with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [ h, hx, ih]

@[simp] theorem removeTautologies_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (F : Formula α) : removeTautologies negβ (F.map (List.map f)) =
      (removeTautologies negα F).map (List.map f) := by
  apply filter_map_comm (List.map f)
  intro C
  simp only [tautology_map f hf negα negβ hn]

@[simp] theorem absorb_map (f : α → β) (hf : Function.Injective f)
    (F : Formula α) : absorb (F.map (List.map f)) = (absorb F).map (List.map f) := by
  unfold absorb
  rw [dedupClauses_map f hf]
  apply filter_map_comm (List.map f)
  intro C
  simp only [List.any_map, Function.comp_def, strictSubset_map f hf]

@[simp] theorem normalize_map (f : α → β) (hf : Function.Injective f)
    (negα : α → α) (negβ : β → β) (hn : ∀ x, f (negα x) = negβ (f x))
    (F : Formula α) : ExecCNF.normalize negβ (F.map (List.map f)) =
      (ExecCNF.normalize negα F).map (List.map f) := by
  simp only [ExecCNF.normalize, cleanLiterals_map f hf,
    removeTautologies_map f hf negα negβ hn, absorb_map f hf]

@[simp] theorem eraseClauses_map (f : α → β) (hf : Function.Injective f)
    (F S : Formula α) : eraseClauses (F.map (List.map f)) (S.map (List.map f)) =
      (eraseClauses F S).map (List.map f) := by
  apply filter_map_comm (List.map f)
  intro C
  simp only [List.any_map, Function.comp_def, equivalent_map f hf]

theorem dedupLiterals_eq_of_nodup (C : Clause α) (hC : C.Nodup) : dedupLiterals C = C := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hC
      have h : ¬ contains x xs = true := by simpa only [contains_true] using hx
      simp only [dedupLiterals, ite_eq_right h, ih hxs]

theorem cleanLiterals_eq_of_nodup (F : Formula α) (hF : ∀ C ∈ F, C.Nodup) :
    cleanLiterals F = F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [cleanLiterals, List.map_cons]
      rw [dedupLiterals_eq_of_nodup C (hF C (by simp))]
      congr 1
      exact ih (fun D hD => hF D (by simp [hD]))

@[simp] theorem cleanLiterals_normalize (neg : α → α) (F : Formula α) :
    cleanLiterals (normalize neg F) = normalize neg F :=
  cleanLiterals_eq_of_nodup _ (normalize_literal_nodup neg F)

/-- The extra pass in the typed worklist does not alter order or multiplicity. -/
theorem normalizedInput_eq_normalize {n : ℕ}
    (F : Formula (SAT.Literal (Fin n))) :
    ExecSparsifyWorklist.normalizedInput F = normalize SAT.Literal.negate F := by
  exact cleanLiterals_normalize SAT.Literal.negate F

/-- Exact encoded normalization, including last-occurrence choices and order. -/
theorem normalize_literalCode {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    normalize SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode)) =
      (normalize SAT.Literal.negate F).map (List.map Encoding.literalCode) :=
  normalize_map Encoding.literalCode Encoding.literalCode_injective
    SAT.Literal.negate SubexpFrontend.negateCode SubexpFrontend.literalCode_negate F

/-- This is the list-level interface consumed by the actual normalizer. -/
theorem normalizedInput_literalCode {n : ℕ} (F : Formula (SAT.Literal (Fin n))) :
    (ExecSparsifyWorklist.normalizedInput F).map (List.map Encoding.literalCode) =
      normalize SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode)) := by
  rw [normalizedInput_eq_normalize, normalize_literalCode]

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

theorem nat_pop (b v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 0) v p (b :: input) output) =
      some (cfg (some 1) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem nat_present (v : Bool) (input output : List Bool) :
    step natProgram (cfg (some 1) v true input output) =
      some (cfg (some 2) v true input output) := by
  simp [step, cfg, execInstr]

theorem nat_true (input output : List Bool) :
    step natProgram (cfg (some 2) true true input output) =
      some (cfg (some 3) true true input output) := by
  simp [step, cfg, execInstr]

theorem nat_push (input output : List Bool) :
    step natProgram (cfg (some 3) true true input output) =
      some (cfg (some 0) true true input (true :: output)) := by
  simp [step, cfg, execInstr]

theorem nat_false (input output : List Bool) :
    step natProgram (cfg (some 2) false true input output) =
      some (cfg (some 4) false true input output) := by
  simp [step, cfg, execInstr]

theorem nat_halt (v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 4) v p input output) =
      some (cfg none v p input output) := by
  simp [step, cfg, execInstr]

theorem nat_cycle (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (true :: input) output)
      (cfg (some 0) true true input (true :: output)) :=
  .cons (nat_pop true v p input output)
    (.cons (nat_present true input output)
      (.cons (nat_true input output) (.cons (nat_push input output) (.refl _))))

theorem nat_finish (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (false :: input) output)
      (cfg none false true input output) :=
  .cons (nat_pop false v p input output)
    (.cons (nat_present false input output)
      (.cons (nat_false input output) (.cons (nat_halt false true input output) (.refl _))))

/-- The count is data on stack 1, rather than an input-dependent control state. -/
theorem nat_trace (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace natProgram (4 * n + 4)
      (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output)
      (cfg none false true rest (List.replicate n true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using nat_finish v p rest output
  | succ n ih =>
      have h := (nat_cycle v p (Encoding.encodeNat n ++ rest) output).trans
        (ih (true :: output) true true)
      have ht : 4 + (4 * n + 4) = 4 * (n + 1) + 4 := by omega
      have hin : Encoding.encodeNat (n + 1) ++ rest =
          true :: (Encoding.encodeNat n ++ rest) := by
        simp [Encoding.encodeNat, List.replicate_succ]
      simpa only [ht, hin, List.replicate_succ', List.append_assoc,
        List.singleton_append] using h

/-! ## In-place removal of one escape frame -/

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_FrontendProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual initialization of the canonical SAT input

The nineteen-label program splits the variable-count header and counts its
unary marks into a binary stack word. The untouched encoded CNF body remains
on stack 0. All growing values live on Boolean stacks, not in finite control.
-/

namespace SubexponentialSAT.FrontendProgram

open SubexponentialSAT.BitProgram

theorem extend_parser_regs (b p : Bool) :
    Function.extend (Fin.castSucc : Fin 2 → Fin 3) (ParserProgram.pair b p)
      (CounterPrograms.counterRegs false false false) = CounterPrograms.counterRegs b p false := by
  funext i
  fin_cases i
  · exact (Fin.castSucc_injective 2).extend_apply _ _ 0
  · exact (Fin.castSucc_injective 2).extend_apply _ _ 1
  · have hn : ¬ ∃ j : Fin 2, j.castSucc = (2 : Fin 3) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 2 at hv
      omega
    exact Function.extend_apply' _ _ _ hn

theorem extend_parser_stacks (body unary : List Bool) :
    Function.extend (Fin.castAdd 2 : Fin 2 → Fin 4) (ParserProgram.pair body unary)
      (storage [] [] [] []) = storage body unary [] [] := by
  funext i
  fin_cases i
  · exact (Fin.castAdd_injective 2 2).extend_apply _ _ 0
  · exact (Fin.castAdd_injective 2 2).extend_apply _ _ 1
  · have hn : ¬ ∃ j : Fin 2, j.castAdd 2 = (2 : Fin 4) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 2 at hv
      omega
    exact Function.extend_apply' _ _ _ hn
  · have hn : ¬ ∃ j : Fin 2, j.castAdd 2 = (3 : Fin 4) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 3 at hv
      omega
    exact Function.extend_apply' _ _ _ hn

theorem extend_counter_stacks (body unary binary scratch : List Bool) :
    Function.extend (Fin.succ : Fin 3 → Fin 4)
      (CounterPrograms.lengthStacks unary binary scratch) (storage body [] [] []) =
      storage body unary binary scratch := by
  funext i
  fin_cases i
  · have hn : ¬ ∃ j : Fin 3, j.succ = (0 : Fin 4) := by simp
    exact Function.extend_apply' _ _ _ hn
  · exact (Fin.succ_injective 3).extend_apply _ _ 0
  · exact (Fin.succ_injective 3).extend_apply _ _ 1
  · exact (Fin.succ_injective 3).extend_apply _ _ 2

@[simp] theorem embed_parser (pc : Option (Fin 5)) (b p : Bool) (body unary : List Bool) :
    ProgramLinking.embedCfg Fin.castSucc (Fin.castAdd 2) (Fin.castAdd 14) (some 5)
      emptyFrame (ParserProgram.cfg pc b p body unary) =
      cfg (ProgramLinking.relocatePc (Fin.castAdd 14) (some 5) pc) b p body unary [] [] := by
  simp [ProgramLinking.embedCfg, emptyFrame, cfg, ParserProgram.cfg,
    extend_parser_regs, extend_parser_stacks]

@[simp] theorem embed_counter (pc : Option (Fin 14)) (b p : Bool)
    (body unary binary scratch : List Bool) :
    ProgramLinking.embedCfg id Fin.succ (Fin.natAdd 5) none (bodyFrame body)
      (⟨pc, CounterPrograms.counterRegs b p false,
        CounterPrograms.lengthStacks unary binary scratch⟩ : Cfg 3 3 14) =
      cfg (ProgramLinking.relocatePc (Fin.natAdd 5) none pc) b p body unary binary scratch := by
  simp [ProgramLinking.embedCfg, bodyFrame, cfg, extend_counter_stacks]

theorem counter_terminal_eq (output : List Bool) :
    terminal CounterPrograms.lengthProgram output =
      (⟨none, CounterPrograms.counterRegs false false false,
        CounterPrograms.lengthStacks [] output []⟩ : Cfg 3 3 14) := by
  simp [terminal ]
  constructor
  · funext i
    simp [CounterPrograms.counterRegs]
  · funext i
    fin_cases i <;> simp [CounterPrograms.lengthStacks]

theorem initialize_initial (input : List Bool) :
    initial initializeProgram input = cfg (some 0) false false input [] [] [] := by
  simp [initial, cfg]
  constructor
  · funext i
    simp [CounterPrograms.counterRegs]
  · funext i
    fin_cases i <;> simp [storage]

theorem header_trace (n : ℕ) (body : List Bool) :
    Trace initializeProgram (4 * n + 4)
      (initial initializeProgram (Encoding.encodeNat n ++ body))
      (cfg (some 5) false true body (List.replicate n true) [] []) := by
  have h := ProgramLinking.relocate_trace ParserProgram.natProgram initializeProgram
    Fin.castSucc (Fin.castAdd 2) (Fin.castAdd 14) (some 5) emptyFrame
    (Fin.castSucc_injective 2) (Fin.castAdd_injective 2 2)
    (ProgramLinking.linkInto_leftCode ParserProgram.natProgram CounterPrograms.lengthProgram
      Fin.castSucc (Fin.castAdd 2) id Fin.succ)
    (ParserProgram.nat_trace n body [] false false)
  simpa [embed_parser, ProgramLinking.relocatePc, initialize_initial] using h

/-- Actual raw-input initialization. The formula body is preserved on stack 0,
the binary count is on stack 2, and both work stacks are empty. -/
theorem initialize_raw (n : ℕ) (body : List Bool) :
    ∃ binary : List Bool, CounterPrograms.value binary = n ∧ binary.length ≤ n ∧
      RunsIn initializeProgram (initializeBound n)
        (initial initializeProgram (Encoding.encodeNat n ++ body))
        (cfg none false false body [] binary []) := by
  obtain ⟨binary, hv, hlen, hc⟩ :=
    CounterPrograms.length_correct_from false true (List.replicate n true)
  simp only [List.length_replicate] at hv hlen hc
  have hrel := ProgramLinking.relocate_runsIn CounterPrograms.lengthProgram initializeProgram
    id Fin.succ (Fin.natAdd 5) none (bodyFrame body)
    Function.injective_id (Fin.succ_injective 3)
    (ProgramLinking.linkInto_rightCode ParserProgram.natProgram CounterPrograms.lengthProgram
      Fin.castSucc (Fin.castAdd 2) id Fin.succ) hc
  have hcounter : RunsIn initializeProgram (n * (8 * n + 10) + 3)
      (cfg (some 5) false true body (List.replicate n true) [] [])
      (cfg none false false body [] binary []) := by
    simpa [CounterPrograms.lengthCfg, counter_terminal_eq, embed_counter,
      ProgramLinking.relocatePc] using hrel
  have hheader : RunsIn initializeProgram (4 * n + 4)
      (initial initializeProgram (Encoding.encodeNat n ++ body))
      (cfg (some 5) false true body (List.replicate n true) [] []) :=
    ⟨_, le_rfl, header_trace n body⟩
  exact ⟨binary, hv, hlen, hheader.trans hcounter⟩

end SubexponentialSAT.FrontendProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem clearOutput_eval (port : Fin 1220) (a : State 80 1220) :
    Eval (clearOutput port) (2 * (a.stacks port).length + 3) a
      (clearOutputState port a) :=
  .call _ (ListRegisterProgram.clear_run port 72 73 a.regs a.stacks)

theorem copyInput_eval (input : List Bool) :
    Eval copyInput (7 * input.length + 5) (StructuredProgram.ioState ABI.countStack input)
      (copiedInput input) := by
  have h := ListRegisterProgram.copy_run (r := 80) ABI.countStack
    (1218 : Fin 1220) 1219 72 73 (by decide) (by decide) (by decide) (by decide)
    (fun _ => false) (StructuredProgram.ioState (r := 80) ABI.countStack input).stacks
    (by simp [ABI.countStack])
  apply Eval.call
  simpa [copiedInput, StructuredProgram.ioState, ABI.countStack, readRegs,
    StackRoutines.copyStacks, ListRegisterProgram.Run, StructuredProgram.State.withPC] using h

theorem copiedInput_projection (input : List Bool) :
    (projectState ABI.positivityRegisters headerStacks (copiedInput input)).withPC
      (some FrontendProgram.initializeProgram.entry) =
      initial FrontendProgram.initializeProgram input := by
  rw [FrontendProgram.initialize_initial]
  apply congrArg₂ (Cfg.mk (some 0))
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [projectState, copiedInput, headerStacks,
      ABI.countStack, FrontendProgram.storage]

theorem header_eval (n : ℕ) (body : List Bool) :
    ∃ binary steps, BinaryArithmetic.toNat binary = n ∧ binary.length ≤ n ∧
      steps ≤ 7 * (Encoding.encodeNat n ++ body).length + 5 +
        FrontendProgram.initializeBound n ∧
      Eval headerCommand steps
        (StructuredProgram.ioState ABI.countStack (Encoding.encodeNat n ++ body))
        (headerResult (Encoding.encodeNat n ++ body) body binary) := by
  obtain ⟨binary, hv, hl, steps, hs, ht⟩ := FrontendProgram.initialize_raw n body
  have he := eval_call_from_state FrontendProgram.initializeProgram ABI.positivityRegisters
    headerStacks (copiedInput (Encoding.encodeNat n ++ body))
    ABI.positivityRegisters.injective headerStacks.injective
    (n := steps) (b := StructuredProgram.State.ofCfg
      (FrontendProgram.cfg none false false body [] binary []))
    (by
      rw [copiedInput_projection]
      exact ht)
  refine ⟨binary, (7 * (Encoding.encodeNat n ++ body).length + 5) + steps,
    ?_, hl, by omega, (copyInput_eval _).seq he⟩
  exact (CounterPrograms.value_eq_toNat binary).symm.trans hv

theorem headerResult_input (input body binary : List Bool) :
    (headerResult input body binary).stacks ABI.countStack = input := by
  rw [headerResult, embedState_stack_frame]
  · simp [copiedInput, ABI.countStack]
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [headerStacks, ABI.countStack] at hi

theorem headerResult_binary (input body binary : List Bool) :
    (headerResult input body binary).stacks 267 = binary :=
  embedState_stack ABI.positivityRegisters headerStacks (copiedInput input) _
    headerStacks.injective 2

theorem headerResult_body (input body binary : List Bool) :
    (headerResult input body binary).stacks 1218 = body :=
  embedState_stack ABI.positivityRegisters headerStacks (copiedInput input) _
    headerStacks.injective 0

theorem headerResult_other (input body binary : List Bool) (i : Fin 1220)
    (hc : i ≠ ABI.countStack) (hn : i ≠ 267) (hb : i ≠ 1218) :
    (headerResult input body binary).stacks i = [] := by
  by_cases hi : ∃ j, headerStacks j = i
  · obtain ⟨j, rfl⟩ := hi
    change StructuredProgram.State.stacks
      (embedState ABI.positivityRegisters headerStacks (copiedInput input)
        (StructuredProgram.State.ofCfg (FrontendProgram.cfg none false false body [] binary [])))
      (headerStacks j) = []
    rw [embedState_stack _ _ _ _ headerStacks.injective]
    fin_cases j <;> simp [headerStacks] at hn hb ⊢ <;> rfl
  · rw [headerResult, embedState_stack_frame _ _ _ _ i hi]
    simp [copiedInput, Function.update_of_ne hb, hc]

theorem copyWord_eval (src dst scratch : Fin 1220) (a : State 80 1220)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (htd : scratch ≠ dst)
    (hblank : a.stacks scratch = []) :
    Eval (copyWord src dst scratch) (7 * (a.stacks src).length + 5) a
      (copiedWord src dst a) :=
  Eval.call _ (ListRegisterProgram.copy_run src dst scratch 72 73 hsd hst htd
    (by decide) a.regs a.stacks hblank)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

/-- Exact ordered refinement to the typed worklist's input, including its
redundant final literal-cleanup pass. No finite-set-only equality is used. -/
theorem typed_program_runsIn {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) (d : Data)
    (hsource : d.stacks 13 = formulaCode (F.map (List.map Encoding.literalCode)))
    (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 13 = formulaCode
        ((ExecSparsifyWorklist.normalizedInput F).map (List.map Encoding.literalCode)) ∧
      RunsIn program (3300 * ((formulaCode (F.map (List.map Encoding.literalCode))).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨e, he, hout, hrun⟩ := program_runsIn (F.map (List.map Encoding.literalCode)) d hsource hready
  rw [← ExecCNFCodeTransport.normalizedInput_literalCode F] at hout
  exact ⟨e, he, hout, hrun⟩

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationCorrectness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Canonical-input correctness of the encoded normalizer

The program consumes the body left by the separate header parser. The output
is exactly the typed sparsifier's ordered normalized input. The declared
variable universe is retained, so unused coordinates require no renaming.
-/

namespace SubexponentialSAT.SubexpNormalizationCorrectness

open BitProgram
open SubexpNormalizationProgram (Data Ready formulaCode program)

theorem canonical_body_eq {n : ℕ} (F : SAT.CNF (Fin n)) :
    formulaCode ((ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode)) =
      Encoding.encodeCNFBody F :=
  ExecQuantitativeSparsify.encode_formulaList F

/-- The output is the exact ordered list that initializes the typed worklist. -/
theorem canonical_body_runsIn {n : ℕ} (F : SAT.CNF (Fin n)) (d : Data)
    (hsource : d.stacks 13 = Encoding.encodeCNFBody F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = normalizedBody F ∧
      RunsIn program (3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  have hs : d.stacks 13 =
      formulaCode ((ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode)) := by
    simpa only [canonical_body_eq] using hsource
  obtain ⟨e, he, hout, hrun⟩ := SubexpNormalizationProgram.typed_program_runsIn
    (ExecQuantitativeSparsify.formulaList F) d hs hready
  rw [canonical_body_eq] at hrun
  exact ⟨e, he, hout, hrun⟩

end SubexponentialSAT.SubexpNormalizationCorrectness

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem seedUnary_eval (a : State 80 1220) : Eval seedUnary 2 a (seededUnary a) := by
  apply Eval.base
  simpa [seedUnary, seededUnary, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.withPC,
    StructuredProgram.State.ofCfg, execInstr] using
    (StructuredProgram.Eval.atom (.set (72 : Fin 80) false) a).seq
      (StructuredProgram.Eval.atom (.push (258 : Fin 1220) (72 : Fin 80)) _)

theorem ambient_eval (a : State 80 1220) (n : ℕ) (body : List Bool)
    (hc : a.stacks ABI.countStack = Encoding.encodeNat n ++ body)
    (hu : a.stacks 258 = []) (hw : a.stacks 1218 = []) (hs : a.stacks 1219 = []) :
    Eval ambientCommand (7 * (a.stacks ABI.countStack).length + 4 * n + 2 * body.length + 14)
      a (ambientResult a n body) := by
  let ready := seededUnary (copiedWord ABI.countStack 1218 a)
  have hc' : a.stacks 256 = Encoding.encodeNat n ++ body := hc
  have hprojection : (projectState unaryRegisters unaryStacks ready).withPC
      (some ParserProgram.natProgram.entry) =
      ParserProgram.cfg (some 0) (ready.regs (unaryRegisters 0))
        (ready.regs (unaryRegisters 1)) (Encoding.encodeNat n ++ body) [false] := by
    apply congrArg₂ (Cfg.mk (some 0))
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;>
        simp [projectState, unaryStacks, ready, seededUnary, copiedWord,
          StackRoutines.copyStacks, ParserProgram.pair, hc', hu, hw, ABI.countStack]
  have hparse := eval_call_from_state ParserProgram.natProgram unaryRegisters unaryStacks
    ready unaryRegisters.injective unaryStacks.injective
    (n := 4 * n + 4) (b := StructuredProgram.State.ofCfg
      (ParserProgram.cfg (l := 5) none false true body (Encoding.encodeNat n)))
    (by
      rw [hprojection]
      simpa [Encoding.encodeNat, StructuredProgram.State.ofCfg,
        StructuredProgram.State.withPC, ParserProgram.cfg] using
        (ParserProgram.nat_trace n body [false] (ready.regs (unaryRegisters 0))
          (ready.regs (unaryRegisters 1))))
  have hbody : (parsedAmbient a n body).stacks 1218 = body :=
    embedState_stack unaryRegisters unaryStacks ready _ unaryStacks.injective 0
  convert (copyWord_eval ABI.countStack 1218 1219 a (by decide) (by decide)
    (by decide) hs).seq ((seedUnary_eval _).seq (hparse.seq
      (clearOutput_eval 1218 (parsedAmbient a n body)))) using 1
  · rfl
  · rw [hbody]
    omega
  · rfl

theorem ambientResult_stacks (a : State 80 1220) (n : ℕ) (body : List Bool)
    (hw : a.stacks 1218 = []) :
    (ambientResult a n body).stacks = Function.update a.stacks 258 (Encoding.encodeNat n) := by
  funext i
  by_cases hi : i = 1218
  · subst i; simp [ambientResult, clearOutputState, hw]
  by_cases hu : i = 258
  · subst i
    change (parsedAmbient a n body).stacks 258 = Encoding.encodeNat n
    exact embedState_stack _ unaryStacks _ _ unaryStacks.injective 1
  have hoff : ¬ ∃ j, unaryStacks j = i := by
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [unaryStacks] at hj <;> omega
  simp only [ambientResult, clearOutputState, Function.update_of_ne hi]
  rw [parsedAmbient, embedState_stack_frame _ _ _ _ i hoff]
  simp [seededUnary, copiedWord, StackRoutines.copyStacks, hi, hu]

theorem placeBody_eval (a : State 80 1220) (hs : a.stacks 1219 = []) :
    Eval placeBodyCommand (9 * (a.stacks 1218).length + 8) a (placedBody a) := by
  convert (copyWord_eval 1218 265 1219 a (by decide) (by decide) (by decide) hs).seq
    (clearOutput_eval 1218 (copiedWord 1218 265 a)) using 1
  · rfl
  · simp [copiedWord, StackRoutines.copyStacks]
    omega
  · rfl

theorem placedBody_stacks (a : State 80 1220) :
    (placedBody a).stacks =
      Function.update (Function.update a.stacks 265 (a.stacks 1218 ++ a.stacks 265)) 1218 [] := rfl


theorem normalization_after_header {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool) :
    ∃ steps b, steps ≤ 3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2 ∧
      Eval normalizationCommand steps
        (headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary) b ∧
      b.stacks 1218 = SubexpNormalizationCorrectness.normalizedBody F ∧
      (∀ i : Fin 16, i ≠ 13 → b.stacks (normalizationStacks i) = []) ∧
      (∀ i, (¬ ∃ j, normalizationStacks j = i) → b.stacks i =
        (headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary).stacks i) := by
  let a := headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary
  let localData := projectState normalizationRegisters normalizationStacks a
  have hsource : localData.stacks 13 = Encoding.encodeCNFBody F :=
    headerResult_body _ _ _
  have hready : SubexpNormalizationProgram.Ready localData := by
    intro i hi
    fin_cases i <;> first | contradiction |
      exact headerResult_other _ _ _ _ (by decide) (by decide) (by decide)
  obtain ⟨b, hb, hout, steps, hs, ht⟩ :=
    SubexpNormalizationCorrectness.canonical_body_runsIn F localData hsource hready
  refine ⟨steps, embedState normalizationRegisters normalizationStacks a b, hs,
    eval_call_from_state _ _ _ a normalizationRegisters.injective normalizationStacks.injective ht,
    ?_, ?_, ?_⟩
  · exact (embedState_stack _ _ _ _ normalizationStacks.injective 13).trans hout
  · intro i hi
    exact (embedState_stack _ _ _ _ normalizationStacks.injective i).trans (hb i hi)
  · intro i hi
    exact embedState_stack_frame _ _ _ _ i hi

theorem normalization_after_header_frame {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool) :
    ∃ steps b, steps ≤ 3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2 ∧
      Eval normalizationCommand steps
        (headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary) b ∧
      b.stacks 1218 = SubexpNormalizationCorrectness.normalizedBody F ∧
      b.stacks ABI.countStack = Encoding.encodeCNF F ∧ b.stacks 267 = binary ∧
      (∀ i, i ≠ ABI.countStack → i ≠ 267 → i ≠ 1218 → b.stacks i = []) := by
  obtain ⟨steps, b, hs, he, ho, hr, hf⟩ := normalization_after_header F binary
  have hframe (i : Fin 1220) (hi : ¬ ∃ j, normalizationStacks j = i) :
      b.stacks i = (headerResult (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) binary).stacks i :=
    hf i hi
  refine ⟨steps, b, hs, he, ho, ?_, ?_, ?_⟩
  · rw [hframe _ (by rintro ⟨j, hj⟩; fin_cases j <;> simp [normalizationStacks, ABI.countStack] at hj)]
    exact headerResult_input _ _ _
  · rw [hframe _ (by rintro ⟨j, hj⟩; fin_cases j <;> simp [normalizationStacks] at hj)]
    exact headerResult_binary _ _ _
  · intro i hc hn hb
    by_cases hi : ∃ j, normalizationStacks j = i
    · obtain ⟨j, rfl⟩ := hi
      apply hr j
      intro hj
      subst j
      exact hb rfl
    · rw [hframe i hi]
      exact headerResult_other _ _ _ i hc hn hb

theorem frontend_eval_oai {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ binary steps b, BinaryArithmetic.toNat binary = n ∧ binary.length ≤ n ∧
      steps ≤ frontendBound F ∧ Eval frontendCommand steps
        (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b ∧
      FrontendReady F binary b := by
  obtain ⟨binary, headerSteps, hv, hl, hh, he⟩ := header_eval n (Encoding.encodeCNFBody F)
  obtain ⟨normalSteps, a, hn, hnormal, hbody, hinput, hbinary, hblank⟩ :=
    normalization_after_header_frame F binary
  have ha265 : a.stacks 265 = [] := hblank 265 (by decide) (by decide) (by decide)
  have ha1219 : a.stacks 1219 = [] := hblank 1219 (by decide) (by decide) (by decide)
  have hp := placeBody_eval a ha1219
  have hplaced (i : Fin 1220) (hi : i ≠ 265) (hw : i ≠ 1218) :
      (placedBody a).stacks i = a.stacks i := by
    simp [placedBody_stacks, hi, hw]
  have hpc : (placedBody a).stacks ABI.countStack = Encoding.encodeCNF F :=
    (hplaced _ (by decide) (by decide)).trans hinput
  have hpu : (placedBody a).stacks 258 = [] :=
    (hplaced _ (by decide) (by decide)).trans (hblank _ (by decide) (by decide) (by decide))
  have hpw : (placedBody a).stacks 1218 = [] := by simp [placedBody_stacks]
  have hps : (placedBody a).stacks 1219 = [] :=
    (hplaced _ (by decide) (by decide)).trans ha1219
  have ham := ambient_eval (placedBody a) n (Encoding.encodeCNFBody F) hpc hpu hpw hps
  have hfinal := ambientResult_stacks (placedBody a) n (Encoding.encodeCNFBody F) hpw
  refine ⟨binary, headerSteps + (normalSteps + (9 * (a.stacks 1218).length + 8 +
    (7 * ((placedBody a).stacks ABI.countStack).length + 4 * n +
      2 * (Encoding.encodeCNFBody F).length + 14))),
    ambientResult (placedBody a) n (Encoding.encodeCNFBody F), hv, hl, ?_,
    he.seq (hnormal.seq (hp.seq ham)), ?_⟩
  · have hlen := SubexpNormalizationCorrectness.normalizedBody_length_le F
    rw [hbody, hpc]
    change headerSteps + (normalSteps +
      (9 * (SubexpNormalizationCorrectness.normalizedBody F).length + 8 +
        (7 * Encoding.formulaBitLength F + 4 * n +
          2 * (Encoding.encodeCNFBody F).length + 14))) ≤ frontendBound F
    change headerSteps ≤ 7 * Encoding.formulaBitLength F + 5 +
      FrontendProgram.initializeBound n at hh
    dsimp [frontendBound]
    omega
  · constructor
    · rw [hfinal, Function.update_of_ne (by decide : ABI.countStack ≠ 258)]
      exact hpc
    · rw [hfinal, Function.update_self]
    · rw [hfinal, Function.update_of_ne (by decide : (265 : Fin 1220) ≠ 258)]
      simp [placedBody_stacks, ha265, hbody]
    · rw [hfinal, Function.update_of_ne (by decide : (267 : Fin 1220) ≠ 258),
        hplaced _ (by decide) (by decide)]
      exact hbinary
    · intro i hc hu hb hn
      rw [hfinal, Function.update_of_ne hu]
      by_cases hw : i = 1218
      · subst i; exact hpw
      · rw [hplaced i hb hw]
        exact hblank i hc hn hw


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.frontend_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.frontend_eval_oai
