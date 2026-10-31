-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:08:08.274573+00:00
-- url     : https://prove2.me/submissions/9dfecd2d-1569-485e-a75b-1ac8fbd6cb17

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S097
import Definitions.Def_OAIQ081S157
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixAnchorReadProgram_readFour_typed
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_Subexp_MatrixInputTypes_program_runsIn

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Three physical byte comparisons for the selected joint coordinate. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

open BitProgram StructuredCalls StackRoutines

theorem eqRegs_injective : Function.Injective eqRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 10 => k.val) h)
theorem eqStacks_injective : Function.Injective eqStacks := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 42 => k.val) h)

theorem equality_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 20,
      Eval equality n a (compared a (decide (a.stacks 1 = a.stacks 12))) := by
  let x : State 5 13 := ⟨fun j => a.regs (eqRegs j), fun j => a.stacks (eqStacks j)⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval x
  have hin : embedState eqRegs eqStacks a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqStacks_injective <;> intros <;> rfl
  have hout : embedState eqRegs eqStacks a
      (CollisionStreamProgram.sealed x (decide (x.stacks 1 = x.stacks 12))) =
      compared a (decide (a.stacks 1 = a.stacks 12)) := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqStacks_injective
    · intro j; fin_cases j <;> simp +decide [compared, CollisionStreamProgram.sealed, eqRegs]
    · intro j hj
      have hn : ¬ j.val < 5 := by
        intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [compared, hn]
    · intro j
      fin_cases j <;>
        simp +decide [compared, CollisionStreamProgram.sealed, x, eqStacks] ; rfl
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      have h12 : j ≠ 12 := fun h => hj ⟨12, h.symm⟩
      simp [compared, h1, h11, h12]
  have he := eval_call_lifted MatrixPositionProgram.equalityInner eqRegs eqStacks a
    eqRegs_injective eqStacks_injective (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · change n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 19 at hn
    omega
  · simpa only [hin, hout, equality] using he

theorem copy_eval (a : Data) (src dst : Fin 42) (hsd : src ≠ dst)
    (hs0 : src ≠ 0) (h0d : (0 : Fin 42) ≠ dst) (h0 : a.stacks 0 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 0 (0 : Fin 10) 1 hsd hs0 h0d (by decide) a h0

theorem pop_eval (a : Data) : Eval pop 1 a (popped a) := .base (.atom _ _)

theorem accept_eval (a : Data) (expected : Bool) :
    ∃ n ≤ 2, Eval (accept expected) n a (accepted a expected) := by
  have ht : Eval setFalse 1 a ⟨Function.update a.regs 9 false, a.stacks⟩ := .base (.atom _ _)
  cases expected <;> cases ha : a.regs 3
  · refine ⟨1, by decide, ?_⟩
    simpa [accept, accepted, ha] using Eval.ite_false (yes := setFalse) ha
      (Eval.base (StructuredProgram.Eval.skip a))
  · refine ⟨2, by decide, ?_⟩
    simpa [accept, accepted, ha] using Eval.ite_true (no := .base .skip) ha ht
  · refine ⟨2, by decide, ?_⟩
    simpa [accept, accepted, ha] using Eval.ite_false (yes := .base .skip) ha ht
  · refine ⟨1, by decide, ?_⟩
    simpa [accept, accepted, ha] using Eval.ite_true (no := setFalse) ha
      (Eval.base (StructuredProgram.Eval.skip a))

theorem check_eval (a : Data) (left right : Fin 4) (expected : Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ 18 * (a.stacks (slot left)).length + 9 * (a.stacks (slot right)).length + 35,
      ∃ b : Data, Eval (check left right expected) n a b ∧ b.stacks = a.stacks ∧
        b.regs 9 = (a.regs 9 && (decide (a.stacks (slot left) = a.stacks (slot right)) == expected)) := by
  let a1 := copied a (slot left) 1
  let a2 := copied a1 (slot right) 12
  let answer := decide (a.stacks (slot left) = a.stacks (slot right))
  let a3 := compared a2 answer
  let a4 := popped a3
  let a5 := accepted a4 expected
  have t0 := copy_eval a (slot left) 1
    (by fin_cases left <;> decide) (by fin_cases left <;> decide) (by decide) h0
  have t1 := copy_eval a1 (slot right) 12
    (by fin_cases right <;> decide) (by fin_cases right <;> decide) (by decide)
    (by simp [a1, copied, copyStacks, h0])
  obtain ⟨ne, hne, te⟩ := equality_eval a2
  have hans : decide (a2.stacks 1 = a2.stacks 12) = answer := by
    fin_cases left <;> fin_cases right <;>
      simp +decide [a2, a1, copied, copyStacks, slot, h1, h12, answer] <;> rfl
  rw [hans] at te
  have tp := pop_eval a3
  obtain ⟨na, hna, ta⟩ := accept_eval a4 expected
  have he := t0.seq (t1.seq (te.seq (tp.seq ta)))
  refine ⟨_, ?_, a5, he, ?_, ?_⟩
  · fin_cases left <;> fin_cases right <;>
      simp +decide [a2, a1, copied, copyStacks, slot, h1, h12] at hne ⊢ <;> omega
  · funext j
    fin_cases j <;>
      simp +decide [a5, a4, a3, a2, a1, accepted, popped, compared, copied,
        copyStacks, h1, h11, h12]
  · simp +decide [a5, a4, a3, a2, a1, accepted, popped, compared, copied,
      readRegs, copyStacks, h11, answer]

theorem command_eval (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ cost a, ∃ b : Data, Eval command n a b ∧ b.stacks = a.stacks ∧ b.regs 9 = valid a := by
  let a0 : Data := ⟨Function.update a.regs 9 true, a.stacks⟩
  have ts : Eval (.base (.atom (.set 9 true))) 1 a a0 := .base (.atom _ _)
  obtain ⟨n1, hn1, a1, t1, hs1, hr1⟩ := check_eval a0 0 2 true h0 h1 h11 h12
  obtain ⟨n2, hn2, a2, t2, hs2, hr2⟩ := check_eval a1 1 2 false
    (by simpa [hs1, a0] using h0) (by simpa [hs1, a0] using h1)
    (by simpa [hs1, a0] using h11) (by simpa [hs1, a0] using h12)
  obtain ⟨n3, hn3, a3, t3, hs3, hr3⟩ := check_eval a2 3 2 false
    (by simpa [hs2, hs1, a0] using h0) (by simpa [hs2, hs1, a0] using h1)
    (by simpa [hs2, hs1, a0] using h11) (by simpa [hs2, hs1, a0] using h12)
  refine ⟨1 + (n1 + (n2 + n3)), ?_, a3, ts.seq (t1.seq (t2.seq t3)), ?_, ?_⟩
  · simp +decide [hs2, hs1, a0, slot, cost] at hn1 hn2 hn3 ⊢
    omega
  · exact hs3.trans (hs2.trans hs1)
  · rw [hr3, hr2, hr1, hs2, hs1]
    simp +decide [a0, slot, valid, Bool.and_assoc]
    rfl

theorem program_runsIn (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ b : Data, RunsIn program (cost a + 1)
      (a.withPC (some program.entry)) (b.withPC none) ∧ b.stacks = a.stacks ∧ b.regs 9 = valid a := by
  obtain ⟨n, hn, b, ht, hs, hr⟩ := command_eval a h0 h1 h11 h12
  exact ⟨b, ⟨n + 1, by omega, compiled_halt_trace ht 38 38⟩, hs, hr⟩

end SubexponentialSAT.Subexp.MatrixAnchorGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixAnchorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical one-hot color reads for the explicit joint-membership guard. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

theorem colorWord_injective : Function.Injective (@colorWord r) := by
  intro a b h
  have hh := congrFun (List.ofFn_injective h) a
  simp only [decide_true] at hh
  exact (of_decide_eq_true hh.symm).symm

@[simp] theorem colorWord_eq_iff (a b : Fin r) : colorWord a = colorWord b ↔ a = b :=
  colorWord_injective.eq_iff

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for the zero-extended joint entry on arbitrary universal
types. The unary position cursor is preserved on37. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes

variable {r Q Δ : ℕ}

theorem castLE_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (Fin.castLE h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun k : Fin n => k.val) hij)

theorem embed_install {k s : ℕ} (hk : k ≤ 10) (hs : s ≤ 42) (a : Data) (b : State k s) :
    embedState (Fin.castLE hk) (Fin.castLE hs) a b = install a b := by
  apply embedState_eq_of_ports _ _ _ _ _ (castLE_injective hk) (castLE_injective hs)
  · intro j; simp [install, j.isLt]
  · intro j hj
    have hn : ¬ j.val < k := by
      intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [install, hn]
  · intro j; simp [install, j.isLt]
  · intro j hj
    have hn : ¬ j.val < s := by
      intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [install, hn]

theorem install_project {k s : ℕ} (hk : k ≤ 10) (hs : s ≤ 42) (a : Data) :
    install a (project hk hs a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases h : j.val < k <;> simp [ project, h]
  · funext j
    by_cases h : j.val < s <;> simp [ project, h]

theorem liftCall_eval {k s l : ℕ} (p : Program k s l) (hk : k ≤ 10) (hs : s ≤ 42)
    (a : Data) (b : State k s) {n : ℕ}
    (ht : Trace p n ((project hk hs a).withPC (some p.entry)) (b.withPC none)) :
    Eval (liftCall p hk hs) n a (install a b) := by
  have he := eval_call_lifted p (Fin.castLE hk) (Fin.castLE hs) a
    (castLE_injective hk) (castLE_injective hs) ht
  rw [embed_install, embed_install, install_project] at he
  exact he

theorem clear_eval (a : Data) (src : Fin 42) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  TupleProgram.clear_eval src (0 : Fin 10) 1 a

open BitProgram StructuredCalls StackRoutines

theorem clearColors_eval (a : Data) :
    Eval clearColors (clearColorsCost a) a (colorsCleared a) := by
  let a1 := cleared a 17
  let a2 := cleared a1 18
  let a3 := cleared a2 19
  let a4 := cleared a3 20
  let a5 := cleared a4 38
  let a6 := cleared a5 39
  let a7 := cleared a6 40
  have he := (clear_eval a 17).seq ((clear_eval a1 18).seq ((clear_eval a2 19).seq
    ((clear_eval a3 20).seq ((clear_eval a4 38).seq ((clear_eval a5 39).seq
      ((clear_eval a6 40).seq (clear_eval a7 41)))))))
  convert he using 1
  · rfl
  · simp +decide [clearColorsCost, a7, a6, a5, a4, a3, a2, a1, cleared, clearStacks]
    ring
  · rfl

theorem colorsCleared_reg9 (a : Data) : (colorsCleared a).regs 9 = a.regs 9 := by
  simp +decide [colorsCleared, cleared, readRegs]

theorem colorsCleared_stacks (a : Data) :
    (colorsCleared a).stacks = fun j =>
      if j ∈ ([17, 18, 19, 20, 38, 39, 40, 41] : List (Fin 42)) then [] else a.stacks j := by
  funext j
  fin_cases j <;> simp +decide [colorsCleared, cleared, clearStacks]

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes


end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid joint-membership guard on actual type bytes. The four integer cache
words are arbitrary retained bytes; no finite-field numerator is invoked. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Guard

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.Subexp.MatrixWordEncoding SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q Δ : ℕ}

theorem guardStage_eval (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 10 → Bool) :
    ∃ n ≤ guardStageCost r Q Δ i.val t.val, ∃ b : Data,
      Eval guardStage n (guardInput i t u y cache0 cache1 cache2 cache3 regs) b ∧
      b.stacks = (guardInput i t u y cache0 cache1 cache2 cache3 regs).stacks ∧
      b.regs 9 = decide (anchorValid i t u y) := by
  let base := guardInput i t u y cache0 cache1 cache2 cache3 regs
  let lr : Fin 8 → Bool := fun j => regs (j.castLE (by decide : 8 ≤ 10))
  let a1 := install base (MatrixInputTypes.output i u y lr)
  let ws : Fin 4 → Word r Q := ![u.head, u.slot i, y.head, y.slot i]
  let colors := fun j => MatrixAnchorReadProgram.colorWord (ws j t)
  let a2 := MatrixAnchorReadProgram.fourReadResult a1 colors
  have hin : project (by decide : 8 ≤ 10) (by decide : 29 ≤ 42) base =
      MatrixInputTypes.input i u y lr := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp +decide [ base, guardInput, Scan.scanInput,
          MatrixEntryProgram.input]
  obtain ⟨ne, hne, he⟩ := MatrixInputTypes.program_runsIn i u y lr
  rw [← hin] at he
  have te := liftCall_eval MatrixInputProgram.program (by decide) (by decide) base
    (MatrixInputTypes.output i u y lr) he
  have hwork : ∀ j : Fin 42, j.val < 9 → a1.stacks j = [] := by
    intro j hj
    fin_cases j <;>
      simp +decide [a1, install, MatrixInputTypes.output,
        MatrixInputProgram.outputState, MatrixInputProgram.inputState] at hj ⊢
  have hd : ∀ j, a1.stacks (MatrixAnchorReadProgram.target j) = [] := by
    intro j
    fin_cases j <;>
      simp +decide [a1, install, MatrixAnchorReadProgram.target, base, guardInput]
  have hs : ∀ j, a1.stacks (MatrixAnchorReadProgram.source j) = ReadPlan.encodeWord (ws j) := by
    intro j
    fin_cases j <;>
      simp +decide [a1, install, MatrixAnchorReadProgram.source, ws,
        MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  have hi : (a1.stacks 37).length = t.val := by
    simp +decide [a1, install, base, guardInput]
  have hw : (a1.stacks 21).length = r := by
    simp +decide [a1, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  have hr := MatrixAnchorReadProgram.readFour_typed a1 ws t hwork hd hs hi hw
  have tr : Eval (.call readProgram)
      (4 * (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43) + 1) a1 a2 :=
    .call _ (compiled_halt_trace hr 17 38)
  have hb0 : a2.stacks 0 = [] := by
    simpa +decide [a2, MatrixAnchorReadProgram.fourReadResult,
      MatrixAnchorReadProgram.readOneResult, MatrixAnchorReadProgram.target] using hwork 0 (by decide)
  have hb1 : a2.stacks 1 = [] := by
    simpa +decide [a2, MatrixAnchorReadProgram.fourReadResult,
      MatrixAnchorReadProgram.readOneResult, MatrixAnchorReadProgram.target] using hwork 1 (by decide)
  have hb11 : a2.stacks 11 = [] := by
    simp +decide [a2, MatrixAnchorReadProgram.fourReadResult, MatrixAnchorReadProgram.readOneResult,
      MatrixAnchorReadProgram.target, a1, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  have hb12 : a2.stacks 12 = [] := by
    simp +decide [a2, MatrixAnchorReadProgram.fourReadResult, MatrixAnchorReadProgram.readOneResult,
      MatrixAnchorReadProgram.target, a1, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, MatrixInputProgram.inputState]
  obtain ⟨a3, ⟨ng, hng, hg⟩, hs3, hf3⟩ := MatrixAnchorGuardProgram.program_runsIn a2 hb0 hb1 hb11 hb12
  have tg : Eval (.call MatrixAnchorGuardProgram.program) ng a2 a3 := .call _ hg
  let a4 := colorsCleared a3
  have tc := clearColors_eval a3
  have hbaseLow (j : Fin 42) (hj : j.val < 29) :
      base.stacks j = (MatrixInputTypes.input i u y lr).stacks ⟨j.val, hj⟩ := by
    have h := congrFun (congrArg StructuredProgram.State.stacks hin) ⟨j.val, hj⟩
    have heq : Fin.castLE (by decide : 29 ≤ 42) ⟨j.val, hj⟩ = j := Fin.ext rfl
    simpa only [project, heq] using h
  have ha1 (j : Fin 42) :
      (if j ∈ ([17, 18, 19, 20, 38, 39, 40, 41] : List (Fin 42)) then []
        else a1.stacks j) = base.stacks j := by
    by_cases hmem : j ∈ ([17, 18, 19, 20, 38, 39, 40, 41] : List (Fin 42))
    · simp only [ite_eq_left hmem]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h | h | h <;> subst j <;>
        simp +decide [base, guardInput, Scan.scanInput, MatrixEntryProgram.input]
    · simp only [ite_eq_right hmem]
      by_cases hj : j.val < 29
      · have h17 : j.val ≠ 17 := by
          intro h
          apply hmem
          have : j = (17 : Fin 42) := Fin.ext h
          subst j
          simp
        have h18 : j.val ≠ 18 := by
          intro h
          apply hmem
          have : j = (18 : Fin 42) := Fin.ext h
          subst j
          simp
        have h19 : j.val ≠ 19 := by
          intro h
          apply hmem
          have : j = (19 : Fin 42) := Fin.ext h
          subst j
          simp
        have h20 : j.val ≠ 20 := by
          intro h
          apply hmem
          have : j = (20 : Fin 42) := Fin.ext h
          subst j
          simp
        rw [hbaseLow j hj]
        simp +decide [a1, install, hj, MatrixInputTypes.output, MatrixInputTypes.input,
          MatrixInputProgram.outputState, MatrixInputProgram.inputState, Fin.ext_iff,
          h17, h18, h19, h20]
      · simp +decide [a1, install, hj]
  have hfinal : a4.stacks = base.stacks := by
    rw [show a4 = colorsCleared a3 from rfl, colorsCleared_stacks, hs3]
    funext j
    by_cases hmem : j ∈ ([17, 18, 19, 20, 38, 39, 40, 41] : List (Fin 42))
    · simpa only [ite_eq_left hmem] using ha1 j
    · have h38 : j ≠ 38 := by intro h; subst j; exact hmem (by simp)
      have h39 : j ≠ 39 := by intro h; subst j; exact hmem (by simp)
      have h40 : j ≠ 40 := by intro h; subst j; exact hmem (by simp)
      have h41 : j ≠ 41 := by intro h; subst j; exact hmem (by simp)
      simpa +decide [a2, MatrixAnchorReadProgram.fourReadResult,
        MatrixAnchorReadProgram.readOneResult, MatrixAnchorReadProgram.target,
        hmem, h38, h39, h40, h41] using ha1 j
  have hc38 : a2.stacks 38 = MatrixAnchorReadProgram.colorWord (u.head t) := rfl
  have hc39 : a2.stacks 39 = MatrixAnchorReadProgram.colorWord (u.slot i t) := rfl
  have hc40 : a2.stacks 40 = MatrixAnchorReadProgram.colorWord (y.head t) := rfl
  have hc41 : a2.stacks 41 = MatrixAnchorReadProgram.colorWord (y.slot i t) := rfl
  have hflag : a4.regs 9 = decide (anchorValid i t u y) := by
    rw [show a4 = colorsCleared a3 from rfl, colorsCleared_reg9, hf3]
    simp only [MatrixAnchorGuardProgram.valid, hc38, hc39, hc40, hc41,
      ne_eq, MatrixAnchorReadProgram.colorWord_eq_iff, anchorValid]
    rfl
  have hcostg : MatrixAnchorGuardProgram.cost a2 + 1 = 81 * r + 107 := by
    simp only [MatrixAnchorGuardProgram.cost, hc38, hc39, hc40, hc41,
      MatrixAnchorReadProgram.colorWord_length]
    ring
  have hcostc : clearColorsCost a3 = 8 * (Q * r) + 8 * r + 24 := by
    simp only [clearColorsCost, hs3, hc38, hc39, hc40, hc41]
    simp +decide [a2,
      MatrixAnchorReadProgram.fourReadResult, MatrixAnchorReadProgram.readOneResult,
      MatrixAnchorReadProgram.target, colors, a1, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, ReadPlan.wordWidth]
    ring
  refine ⟨ne + ((4 * (9 * (Q * r) + t.val * (14 * r + 17) + 30 * r + 43) + 1) +
    (ng + clearColorsCost a3)), ?_, a4, te.seq (tr.seq (tg.seq tc)), hfinal, hflag⟩
  rw [hcostg] at hng
  rw [hcostc]
  dsimp [guardStageCost]
  omega


end SubexponentialSAT.SqrtLog.LayoutProgram.Guard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for one universal integer constraint entry. The concrete
local stages are lifted into one bank; subsequent lemmas compose their traces.
No ring inversion or field-valued matrix is used in this integer procedure. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.MulticolorTypes

theorem guardPorts_inj : Function.Injective guardPorts := Fin.castAdd_injective _ _

variable {r Q : ℕ}

theorem guard_eval_oai (t : Fin Q) (u y : UniversalType r Q 1) (a : Data)
    (ha : projectState id guardPorts a = Guard.guardInput (0 : Fin 1) t u y
      [] [] [] [] a.regs) :
    ∃ n ≤ MatrixExtendedEntryProgram.guardStageCost r Q 1 0 t.val+1,
      ∃ e : Data, Eval guard n a e ∧ e.stacks=a.stacks ∧
      e.regs 9=decide (MatrixExtendedEntryProgram.anchorValid (0 : Fin 1) t u y) := by
  obtain ⟨n,hn,b,hb,hs,hflag⟩ := Guard.guardStage_eval (0 : Fin 1) t u y [] [] [] [] a.regs
  rw [← ha] at hb
  let e := embedState id guardPorts a b
  have he := eval_liftCommand_from_state MatrixExtendedEntryProgram.guardStage 23 0 id guardPorts a
    Function.injective_id guardPorts_inj hb
  have hstacks : e.stacks=a.stacks := by
    change Function.extend guardPorts b.stacks a.stacks = a.stacks
    rw [hs]
    have hh := congrArg StructuredProgram.State.stacks
      (embedState_project id guardPorts a Function.injective_id guardPorts_inj)
    rw [ha] at hh
    exact hh
  have h9 : e.regs 9 = b.regs 9 :=
    embedState_register id guardPorts a b Function.injective_id 9
  have hn' : n ≤ MatrixExtendedEntryProgram.guardStageCost r Q 1 0 t.val := by simpa using hn
  exact ⟨n+1,by omega,e,he,hstacks,h9.trans hflag⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry.guard_eval_oai
