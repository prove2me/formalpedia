-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:32:17.006979+00:00
-- url     : https://prove2.me/submissions/eb5235a0-f791-49eb-a134-317ddee46f32

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S173
import Definitions.Def_OAIQ081S176

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Different finite execution derivations of the same structured command
must have the same final data. The existing source port supplies a concrete
compiled machine, and determinism is inherited from its actual transition. -/
theorem Eval.final_unique {r s : ℕ} (port : Fin s) {c : Cmd r s}
    {n m : ℕ} {a b d : State r s} (h : Eval c n a b) (g : Eval c m a d) : b = d := by
  have hb := compiled_halt_trace h port port
  have hd := compiled_halt_trace g port port
  have heq := Computation.RunsIn.terminal_unique
    (show RunsIn (compiled c port port) (n + 1)
      (a.withPC (some (compiled c port port).entry)) (b.withPC none) from
      ⟨n + 1, le_rfl, hb⟩)
    (show RunsIn (compiled c port port) (m + 1)
      (a.withPC (some (compiled c port port).entry)) (d.withPC none) from
      ⟨m + 1, le_rfl, hd⟩)
    (by simp [step, StructuredProgram.State.withPC])
    (by simp [step, StructuredProgram.State.withPC])
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpExponentArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Growing-parameter exponent arithmetic

All factors in this module are actual real powers. The bounds expose the
growing parameters; they assert no program-running-time fact.
-/

namespace SubexponentialSAT.SubexpExponentArithmetic

noncomputable section
open Filter
open scoped Topology

theorem logb_lt_natLog2_add_one (n : ℕ) :
    Real.logb 2 (n : ℝ) < (Nat.log2 n : ℝ) + 1 := by
  have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Real.natFloor_logb_natCast 2 n
  simpa only [hf] using
    (Nat.lt_floor_add_one (Real.logb 2 (n : ℝ)))

end
end SubexponentialSAT.SubexpExponentArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticSchedule
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact, computable square-root-log scheduling. No algorithmic assertion is
hidden in these numerical lemmas. Small inputs may have schedule zero. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem s_le_L (n : ℕ) : s n ≤ L n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem four_le_logSize (n : ℕ) : 4 ≤ logSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (n : ℝ) + 16)).mpr
  norm_num

theorem logSize_lt_L (n : ℕ) : logSize n < (L n : ℝ) := by
  simpa [logSize, L, Nat.cast_add, Nat.cast_ofNat] using
    SubexpExponentArithmetic.logb_lt_natLog2_add_one (n + 16)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem layoutR_le_L (n : ℕ) : layoutR n ≤ L n := by
  have h : (4 : ℝ) < L n := (four_le_logSize n).trans_lt (logSize_lt_L n)
  have hnat : 4 < L n := by exact_mod_cast h
  exact max_le (by omega) (s_le_L n)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCrudeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

open Asymptotic

theorem magnitude_ge (x : Input) :
    16 ≤ magnitude x ∧ x.freeCount ≤ magnitude x ∧ x.occurrence ≤ magnitude x := by
  dsimp [magnitude]
  omega

theorem L_le_magnitude (x : Input) : L x.freeCount ≤ 2*magnitude x := by
  have h := Nat.log2_le_self (x.freeCount+16)
  dsimp [L, magnitude]
  omega

theorem energy_le_magnitude (x : Input) :
    layoutEnergy x.freeCount x.occurrence ≤ 513*(magnitude x)^4 := by
  let H := magnitude x
  have hH : 1 ≤ H := by dsimp [H]; have := magnitude_ge x; omega
  have hL := L_le_magnitude x
  have hr := (layoutR_le_L x.freeCount).trans hL
  have hb := (magnitude_ge x).2.2
  have hlog := Nat.log2_le_self (64*x.occurrence*layoutR x.freeCount*(L x.freeCount)^2)
  have hprod : 64*x.occurrence*layoutR x.freeCount*(L x.freeCount)^2 ≤ 512*H^4 := by
    calc
      _ ≤ 64*H*(2*H)*(2*H)^2 := by gcongr
      _ = _ := by ring
  have hpow : 1 ≤ H^4 := one_le_pow₀ hH
  dsimp [layoutEnergy]
  change Nat.log2 _+1 ≤ 513*H^4
  omega

theorem loop_operands_le_cap (x : Input) :
    16 ≤ loopCap x ∧ L x.freeCount ≤ loopCap x ∧
    2*layoutQ x.freeCount ≤ loopCap x ∧
    128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ loopCap x ∧
    Nat.log2 (layoutQ x.freeCount)+2 ≤ loopCap x := by
  let H := magnitude x
  have hH : 16 ≤ H := (magnitude_ge x).1
  have hL := L_le_magnitude x
  have hQ : layoutQ x.freeCount ≤ 2*H := (Nat.div_le_self _ _).trans hL
  have hE := energy_le_magnitude x
  have hlog := Nat.log2_le_self (layoutQ x.freeCount)
  have hp1 : H ≤ H^6 := Nat.le_self_pow (by decide) _
  have hp5 : H^5 ≤ H^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp0 : 1 ≤ H^6 := one_le_pow₀ (by omega)
  have hroot : 128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ 131328*H^5 := by
    calc
      _ ≤ 128*(2*H)*(513*H^4) := by gcongr
      _ = _ := by ring
  change 16 ≤ 1000000*H^6 ∧ _ ∧ _ ∧ _ ∧ _
  dsimp [loopCap]
  change 16 ≤ 1000000*H^6 ∧ L x.freeCount ≤ 1000000*H^6 ∧
    2*layoutQ x.freeCount ≤ 1000000*H^6 ∧
    128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ 1000000*H^6 ∧
    Nat.log2 (layoutQ x.freeCount)+2 ≤ 1000000*H^6
  omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

open BitProgram StructuredCalls StructuredProgram BinaryArithmetic

theorem regs_injective : Function.Injective regs := Fin.castAdd_injective _ _
theorem pair_injective (j : Fin 10) : Function.Injective (pair j) := by
  intro a b h; apply Fin.ext; have := congrArg Fin.val h; dsimp [pair] at this; omega

theorem pair_separate {j k : Fin 10} (hjk : j ≠ k) (i : Fin 2) :
    ¬ ∃ h, pair j h = pair k i := by
  rintro ⟨h,he⟩
  have hv := congrArg Fin.val he
  apply hjk
  apply Fin.ext
  dsimp [pair] at hv
  have := h.isLt
  have := i.isLt
  omega

theorem check_eval (j : Fin 10) (a : Data) :
    ∃ b, StructuredCalls.Eval (check j) (cost j a) a b ∧
      b.regs 8 = (a.regs 8 && pass j a) ∧
      (∀ i, (¬ ∃ h, pair j h = i) → b.stacks i = a.stacks i) ∧
      (∀ h, b.stacks (pair j h) = []) := by
  obtain ⟨mid,hr,hcmp,hregs,hframe,hclear⟩ :=
    SubexpGuardProgram.compare_call regs (pair j) regs_injective (pair_injective j) a
  let inv := (Atom.bnot (0 : Fin 9) 0).eval mid
  let b := (Atom.band (8 : Fin 9) 8 0).eval inv
  have hb : StructuredProgram.Eval (.seq (.atom (.bnot 0 0)) (.atom (.band 8 8 0))) 2 mid b :=
    .seq (.atom _ _) (.atom _ _)
  have hnot : ¬ ∃ i, regs i = (8 : Fin 9) := by
    rintro ⟨i,hi⟩; have := congrArg Fin.val hi; have := i.isLt; dsimp [regs] at *; omega
  have hacc := hregs 8 hnot
  have hbool : (!mid.regs 0) = pass j a := by
    change mid.regs 0 = true ↔ _ at hcmp
    cases hm : mid.regs 0 with
    | false =>
      have hle : BinaryArithmetic.toNat (a.stacks (pair j 1))  ≤  BinaryArithmetic.toNat (a.stacks (pair j 0)) := by
        have hn : ¬ BinaryArithmetic.toNat (a.stacks (pair j 0)) < BinaryArithmetic.toNat (a.stacks (pair j 1)) := by
          simpa [hm] using hcmp.symm
        omega
      simp [pass,hle]
    | true =>
      have hle : ¬ BinaryArithmetic.toNat (a.stacks (pair j 1))  ≤  BinaryArithmetic.toNat (a.stacks (pair j 0)) := by
        have := hcmp.mp hm; omega
      simp [pass,hle]
  refine ⟨b,?_,?_,hframe,hclear⟩
  · simpa only [check,cost,Nat.add_assoc] using hr.seq (StructuredCalls.Eval.base hb)
  · simp [b,inv,Atom.eval,Atom.instr,StructuredProgram.State.ofCfg,execInstr,hacc,hbool]

theorem checks_eval (js : List (Fin 10)) (hn : js.Nodup) (a : Data) :
    ∃ b, StructuredCalls.Eval (checks js) (checksCost js a) a b ∧
      b.regs 8 = (a.regs 8 && checksPass js a) ∧
      (∀ j, j ∉ js → ∀ h, b.stacks (pair j h) = a.stacks (pair j h)) ∧
      (∀ j, j ∈ js → ∀ h, b.stacks (pair j h) = []) := by
  induction js generalizing a with
  | nil => exact ⟨a,.base (.skip _),by simp [checksPass],by simp,by simp⟩
  | cons j js ih =>
    obtain ⟨mid,he,hacc,hframe,hclear⟩ := check_eval j a
    obtain ⟨b,her,hracc,hrframe,hrclear⟩ := ih (List.nodup_cons.mp hn).2 mid
    have hv (k : Fin 10) (hk : k ∈ js) :
        cost k mid = cost k a ∧ pass k mid = pass k a := by
      have hjk : j ≠ k := by intro h; subst k; exact (List.nodup_cons.mp hn).1 hk
      have h0 := hframe (pair k 0) (pair_separate hjk 0)
      have h1 := hframe (pair k 1) (pair_separate hjk 1)
      simp only [cost,pass,h0,h1,and_self]
    have hc : checksCost js mid = checksCost js a := by
      unfold checksCost
      congr 1
      apply List.map_congr_left
      intro k hk
      exact (hv k hk).1
    have hp : checksPass js mid = checksPass js a := by
      unfold checksPass
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor
      · intro hh k hk
        rw [← (hv k hk).2]
        exact hh k hk
      · intro hh k hk
        rw [(hv k hk).2]
        exact hh k hk
    refine ⟨b,?_,?_,?_,?_⟩
    · rw [hc] at her
      simpa only [checks,checksCost,List.map_cons,List.sum_cons] using he.seq her
    · rw [hracc,hacc,hp]
      simp [checksPass,Bool.and_assoc]
    · intro k hk h
      have hkj : k ≠ j := by intro he; subst k; exact hk (by simp)
      have hkjs : k ∉ js := by intro h; exact hk (List.mem_cons_of_mem j h)
      exact (hrframe k hkjs h).trans (hframe _ (pair_separate hkj.symm h))
    · intro k hk h
      rcases List.mem_cons.mp hk with rfl|hk
      · exact (hrframe k (List.nodup_cons.mp hn).1 h).trans (hclear h)
      · exact hrclear k hk h

theorem command_eval (a : Data) :
    ∃ b, StructuredCalls.Eval command (1+checksCost allChecks a) a b ∧
      b.regs 8 = checksPass allChecks a := by
  let a0 := (Atom.set (8 : Fin 9) true).eval a
  obtain ⟨b,he,hacc,hframe,hclear⟩ := checks_eval allChecks (List.nodup_finRange 10) a0
  refine ⟨b,?_,?_⟩
  · exact (StructuredCalls.Eval.base (.atom _ _)).seq he
  · simpa [a0,Atom.eval,Atom.instr,StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,
      checksPass,pass] using hacc

private theorem forall_ten (P : Fin 10 → Prop) :
    (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 ∧ P 6 ∧ P 7 ∧ P 8 ∧ P 9 := by
  constructor
  · intro h
    exact ⟨h 0,h 1,h 2,h 3,h 4,h 5,h 6,h 7,h 8,h 9⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9

private theorem numeric_guard_for (x : Input) (p : Parameters) :
    (∀ j : Fin 10, lowerFor x p j  ≤  upperFor x p j) ↔
      (0 < x.freeCount ∧ x.freeCount ≤ x.ambient ∧ 0 < x.clauses ∧
       0 < x.occurrence ∧ 0 < x.arity ∧ x.freeCount ≤ x.incidences ∧
       2 ≤ p.Q ∧ 4*p.R ≤ p.Q ∧
       4*(x.occurrence+x.arity)*p.N^2*p.epsilonDen^2 ≤ x.incidences ∧
       16*p.Q*p.r^2 ≤ x.freeCount) := by
  rw [forall_ten]
  change (1 ≤ x.freeCount ∧ x.freeCount ≤ x.ambient ∧ 1 ≤ x.clauses ∧
    1 ≤ x.occurrence ∧ 1 ≤ x.arity ∧ x.freeCount ≤ x.incidences ∧
    2 ≤ p.Q ∧ 4*p.R ≤ p.Q ∧
    4*(x.occurrence+x.arity)*p.N^2*p.epsilonDen^2 ≤ x.incidences ∧
    16*p.Q*p.r^2 ≤ x.freeCount) ↔ _
  exact and_congr Nat.succ_le_iff (and_congr Iff.rfl
    (and_congr Nat.succ_le_iff (and_congr Nat.succ_le_iff
      (and_congr Nat.succ_le_iff Iff.rfl))))

theorem numeric_guard_iff (x : Input) :
    (∀ j : Fin 10, lower x j  ≤  upper x j) ↔ Guard x :=
  numeric_guard_for x (produce x)

theorem checksPass_numeric (x : Input) (a : Data) (h : Encodes x a) :
    checksPass allChecks a = true ↔ ∀ j : Fin 10, lower x j  ≤  upper x j := by
  simp only [checksPass,List.all_eq_true,allChecks,List.mem_finRange,forall_true_left,pass,
    decide_eq_true_eq]
  exact forall_congr' (fun j => by rw [(h j).1,(h j).2])

theorem checksPass_iff (x : Input) (a : Data) (h : Encodes x a) :
    checksPass allChecks a = true ↔ Guard x :=
  (checksPass_numeric x a h).trans (numeric_guard_iff x)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

/-- Every output is fresh and every division denominator is positive for all
inputs. The final safe divisor is max(1,Q); the fast-path guard later implies
Q>=2 and hence identifies it with Q. -/
theorem admissible (x : Input) (inputLengths : Fin 8 → ℕ) :
    AdmissibleCode code (initialModel x inputLengths) := by
  simp [code,coreCode,tailCode,AdmissibleCode,Admissible,next,output,value,lengthBound,initialModel,
    initialValues,BinaryArithmetic.toNat,bitVal,Fin.coe_ofNat_eq_mod]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutValues -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem admissible (m : Model) : AdmissibleCode code m := by
  rw [code, admissibleCode_append]
  constructor
  · simp [preparation, AdmissibleCode, Admissible, next, output, value, lengthBound]
  · simp [emissions, AdmissibleCode, Admissible, next, output, value, lengthBound]

theorem values (m : Model) (j : Fin 10) :
    (Circuit.result code m).val (pair j 0)=upper m j ∧
    (Circuit.result code m).val (pair j 1)=lower m j := by
  rw [code, result_append]
  fin_cases j <;>
    simp [emissions, Circuit.result, next, value, output, upper, lower, pair, pow_two] <;>
    simp [preparation, Circuit.result, next, value, output,
      BinaryArithmetic.toNat, bitVal, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.GuardSetup


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPrepared -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem command_eval (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Regs)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t rf w', Eval command t (state r w) (state rf w') ∧
      Shape (finalModel x l) w' ∧ t ≤ runtimeBound x l := by
  have ha : AdmissibleCode code (Layout.initialModel x l) := by
    rw [code,admissibleCode_append]
    exact ⟨Layout.admissible x l,GuardSetup.admissible _⟩
  simpa only [command,code,result_append,budget_append,finalModel,runtimeBound,
    Layout.model,Layout.runtimeBound] using
    Circuit.program_eval code (Layout.initialModel x l) w r hs ha

private theorem operand_bridge (m : Model) (x : Input) (p : Parameters)
    (h0 : m.val 0=x.ambient) (h1 : m.val 1=x.freeCount) (h2 : m.val 2=x.clauses)
    (h3 : m.val 3=x.occurrence) (h4 : m.val 4=x.arity) (h7 : m.val 7=x.incidences)
    (hr : m.val 18=p.r) (hQ : m.val 21=p.Q) (he : m.val 25=p.epsilonDen)
    (hR : m.val 29=p.R) (hN : m.val 31=p.N) (j : Fin 10) :
    GuardSetup.upper m j=BitGuard.upperFor x p j ∧ GuardSetup.lower m j=BitGuard.lowerFor x p j := by
  fin_cases j <;> simp [GuardSetup.upper,GuardSetup.lower,BitGuard.upperFor,BitGuard.lowerFor,
    h0,h1,h2,h3,h4,h7,hr,hQ,he,hR,hN]

theorem operand_values (x : Input) (l : Fin 8 → ℕ) (j : Fin 10) :
    (finalModel x l).val (GuardSetup.pair j 0)=BitGuard.upper x j ∧
    (finalModel x l).val (GuardSetup.pair j 1)=BitGuard.lower x j := by
  have hg := GuardSetup.values (Layout.model x l) j
  rcases Layout.model_core_values x l with ⟨hL,hw,hs,hr,hQ,he,hR,hN⟩
  have hb := operand_bridge (Layout.model x l) x (produce x)
    (Layout.model_inputs x l 0) (Layout.model_inputs x l 1) (Layout.model_inputs x l 2)
    (Layout.model_inputs x l 3) (Layout.model_inputs x l 4) (Layout.model_inputs x l 7)
    hr hQ he hR hN j
  exact ⟨hg.1.trans hb.1,hg.2.trans hb.2⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramExecute -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem guardStacks_injective : Function.Injective guardStacks := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [guardStacks] at this
  omega

theorem guardStacks_pair (j : Fin 10) (h : Fin 2) :
    guardStacks (BitGuard.pair j h)=Bank.port (GuardSetup.pair j h) := by
  apply Fin.ext
  simp [guardStacks,BitGuard.pair,Bank.port,GuardSetup.pair,Nat.add_assoc]

theorem numeric_eval (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t rf w', Eval numeric t (state r w) (state rf w') ∧
      Shape (Prepared.finalModel x l) w' ∧ t ≤ Prepared.runtimeBound x l+1 := by
  obtain ⟨t,rf,w',he,hs',ht⟩ := Prepared.command_eval x l w (r ∘ registers) hs
  let e := embedState registers id (state r w) (Bank.state rf w')
  have hrun : Eval numeric (t+1) (state r w) e :=
    eval_liftCommand_from_state Prepared.command (Bank.port 0) (Bank.port 42)
      registers id (state r w) (Fin.castAdd_injective 8 1) Function.injective_id he
  have heq : e=state e.regs w' := by
    apply CounterForPrograms.data_ext (a := e) (b := state e.regs w') rfl
    funext i
    exact embedState_stack registers id (state r w) (Bank.state rf w') Function.injective_id i
  refine ⟨t+1,e.regs,w',?_,hs',Nat.add_le_add_right ht 1⟩
  rw [← heq]
  exact hrun

theorem guard_encodes (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Prepared.finalModel x l) w) :
    BitGuard.Encodes x (projectState id guardStacks (state r w)) := by
  intro j
  have hv := Prepared.operand_values x l j
  constructor
  · change BinaryArithmetic.toNat ((state r w).stacks (guardStacks (BitGuard.pair j 0)))=_
    rw [guardStacks_pair]
    rw [state_port]
    exact (hs.1 _).trans hv.1
  · change BinaryArithmetic.toNat ((state r w).stacks (guardStacks (BitGuard.pair j 1)))=_
    rw [guardStacks_pair]
    rw [state_port]
    exact (hs.1 _).trans hv.2

/-- A native setup-and-test trace. The operand words are produced by the
numeric program itself before the ten bit comparisons are executed. -/
theorem setup_eval (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t mid final,
      Eval setup t (state r w) final ∧
      (final.regs 8=true ↔ Guard x) ∧
      (∃ rm wm, mid=state rm wm ∧ Shape (Prepared.finalModel x l) wm) ∧
      (∀ a : Fin 64, a.val < 44 → final.stacks (Bank.port a)=mid.stacks (Bank.port a)) ∧
      t ≤ Prepared.runtimeBound x l+BitGuard.checksCost BitGuard.allChecks
        (projectState id guardStacks mid)+3 := by
  obtain ⟨t,rf,w',he,hs',ht⟩ := numeric_eval x l w r hs
  let mid := state rf w'
  let a0 :=  projectState id guardStacks mid
  have hc : BitGuard.Encodes x a0 := guard_encodes x l w' rf hs'
  obtain ⟨b,hb,hflag⟩ := BitGuard.command_eval a0
  let final := embedState id guardStacks mid b
  have hcheck : Eval check ((1+BitGuard.checksCost BitGuard.allChecks a0)+1) mid final :=
    eval_liftCommand_from_state BitGuard.command 0 0 id guardStacks mid
      Function.injective_id guardStacks_injective hb
  refine ⟨t+((1+BitGuard.checksCost BitGuard.allChecks a0)+1),mid,final,
    he.seq hcheck,?_,⟨rf,w',rfl,hs'⟩,?_,by dsimp only [a0]; omega⟩
  · have hreg : final.regs 8=b.regs 8 :=
      embedState_register id guardStacks mid b Function.injective_id 8
    rw [hreg,hflag]
    exact BitGuard.checksPass_iff x a0 hc
  · intro a ha
    apply embedState_stack_frame id guardStacks mid b (Bank.port a)
    rintro ⟨i,hi⟩
    have hv := congrArg Fin.val hi
    dsimp [guardStacks,Bank.port] at hv
    omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitBudget -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

theorem le_majorant (B : ℕ) : B ≤ majorant B := by
  have hp : B+2 ≤ (B+2)^6 := Nat.le_self_pow (by decide) _
  dsimp [majorant]
  omega

private theorem power_bounds (B : ℕ) :
    1 ≤ (B+2)^6 ∧ B ≤ (B+2)^6 ∧ B^2 ≤ (B+2)^6 ∧
      B^3 ≤ (B+2)^6 ∧ B^4 ≤ (B+2)^6 := by
  have h1 : 1 ≤ B+2 := by omega
  have hp (k : ℕ) (hk : k ≤ 6) : B^k ≤ (B+2)^6 :=
    (Nat.pow_le_pow_left (show B ≤ B+2 by omega) k).trans (Nat.pow_le_pow_right h1 hk)
  exact ⟨one_le_pow₀ h1,(by simpa using hp 1 (by decide)),hp 2 (by decide),hp 3 (by decide),hp 4 (by decide)⟩

theorem length_cost_majorant (m : Model) (i : Instr) (B : ℕ)
    (hl : ∀ a, m.len a ≤ B) (hs : scale m i ≤ B) :
    lengthBound m.val m.len i ≤ majorant B ∧ cost m.val m.len i ≤ majorant B := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := power_bounds B
  have hM := le_majorant B
  cases i with
  | clear a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  0 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  2*B+3 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | load o bits =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  2*B := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | copy a o h =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  7*B+5 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | add a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | mul a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | pow a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  1+B*B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  B*(50*(B+1)*(2+(B+1)*B))+(B+1)*(16*B+16)+3+9*B+8 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | quot a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  150*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | sqrt a o h =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  200001*(B+B+2)^3 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | logSucc a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  32*(B+1)^2+4 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | addConst a k =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  8*B*(B+B+1)+4 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | pred a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  20*(B+1) := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | maxTwo a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+2 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+3) := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]

theorem le_iterMajorant (n B : ℕ) : B ≤ iterMajorant n B := by
  induction n generalizing B with
  | zero => exact le_rfl
  | succ n ih => exact (le_majorant B).trans (ih (majorant B))

theorem scaleBound_mono (B C : ℕ) (hBC : B ≤ C) (is : List Instr) (m : Model)
    (h : ScaleBound B is m) : ScaleBound C is m := by
  induction is generalizing m with
  | nil => trivial
  | cons i is ih => exact ⟨h.1.trans hBC,ih (next m i) h.2⟩

/-- A single global bound on numeric loop parameters yields a polynomial
bound for every fixed instruction table, regardless of large output values. -/
theorem budget_majorant (is : List Instr) (m : Model) (B : ℕ)
    (hl : ∀ a, m.len a ≤ B) (hs : ScaleBound B is m) :
    (∀ a, (result is m).len a ≤ iterMajorant is.length B) ∧
      budget is m ≤ is.length*iterMajorant is.length B := by
  induction is generalizing m B with
  | nil => exact ⟨hl,by simp [budget]⟩
  | cons i is ih =>
    have hi := length_cost_majorant m i B hl hs.1
    have hn : ∀ a, (next m i).len a ≤ majorant B := by
      intro a
      by_cases ha : a=output i
      · simpa [next,ha] using hi.1
      · simpa [next,ha] using (hl a).trans (le_majorant B)
    have ht := ih (next m i) (majorant B) hn
      (scaleBound_mono B (majorant B) (le_majorant B) is (next m i) hs.2)
    refine ⟨ht.1,?_⟩
    have hm := le_iterMajorant is.length (majorant B)
    simp only [budget,List.length_cons,iterMajorant]
    nlinarith [hi.2,ht.2]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutCost -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic Asymptotic

/-- The only input values entering loop costs are precisely the four small
operands bounded in CrudeBounds. All power outputs affect later work through
binary word lengths alone. -/
theorem scaleBound (x : Input) (l : Fin 8 → ℕ) :
    ScaleBound (loopCap x) code (initialModel x l) := by
  obtain ⟨h16,hL,hQ,hR,hd⟩ := loop_operands_le_cap x
  have hL' : (x.freeCount + 16).log2 + 1 ≤ loopCap x := by
    simpa [L] using hL
  have hR' : 128 * (layoutQ x.freeCount *
      layoutEnergy x.freeCount x.occurrence) ≤ loopCap x := by
    simpa only [Nat.mul_assoc] using hR
  have henergy :
      Nat.log2 (64 * (x.occurrence *
        (layoutR x.freeCount * (L x.freeCount * L x.freeCount)))) + 1 =
        layoutEnergy x.freeCount x.occurrence := by
    simp [layoutEnergy,pow_two,Nat.mul_assoc]
  have hRcomputed : 128 * (layoutQ x.freeCount *
      (Nat.log2 (64 * (x.occurrence *
        (layoutR x.freeCount * (L x.freeCount * L x.freeCount)))) + 1)) ≤ loopCap x := by
    rw [henergy]
    exact hR'
  simp only [layoutQ,layoutDen,layoutR,s,w,L,pow_two] at hRcomputed
  have hQcomputed := hQ
  simp only [layoutQ,layoutDen,layoutR,s,w,L,pow_two] at hQcomputed
  rw [code,scaleBound_append]
  constructor
  · simp [coreCode,ScaleBound,scale,next,output,value,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal,Nat.mul_assoc]
    omega
  · have hQ' : (result coreCode (initialModel x l)).val 21 = layoutQ x.freeCount := by
      rw [coreCode,result_append]
      rw [result_value_frame finishCode _ 21]
      · exact (prefix_values x l).2.2
      · decide
    simp [tailCode,ScaleBound,scale,next,output,value,hQ']
    omega

theorem guard_scaleBound (m : Model) (B : ℕ) (hB : 16 ≤ B) :
    ScaleBound B GuardSetup.code m := by
  rw [GuardSetup.code, scaleBound_append]
  constructor
  · simp [GuardSetup.preparation, ScaleBound, scale]
    omega
  · simp [GuardSetup.emissions, ScaleBound, scale]
    omega

theorem initial_lengths_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ a, (initialModel x l).len a ≤ setupScale x l := by
  intro a
  dsimp [initialModel]
  split_ifs with h
  · have hs : l ⟨a.val,h⟩ ≤ ∑ i, l i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    dsimp [setupScale]
    omega
  · exact Nat.zero_le _

theorem guarded_scaleBound (x : Input) (l : Fin 8 → ℕ) :
    ScaleBound (setupScale x l) guardedCode (initialModel x l) := by
  rw [guardedCode,scaleBound_append]
  constructor
  · exact scaleBound_mono _ _ (by dsimp [setupScale]; omega) _ _ (scaleBound x l)
  · exact guard_scaleBound _ _ (by have := (loop_operands_le_cap x).1; dsimp [setupScale]; omega)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatchCost -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

theorem checksCost_le (js : List (Fin 10)) (d : Data) (B : ℕ)
    (h : ∀ j b, (d.stacks (pair j b)).length ≤ B) :
    checksCost js d ≤ js.length*(10*B+8) := by
  induction js with
  | nil => simp [checksCost]
  | cons j js ih =>
    have hc : cost j d ≤ 10*B+8 := by
      dsimp [cost]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 10 (max_le (h j 0) (h j 1))) 8
    simp only [checksCost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

theorem allChecksCost_le (d : Data) (B : ℕ)
    (h : ∀ j b, (d.stacks (pair j b)).length ≤ B) :
    checksCost allChecks d ≤ 100*B+80 := by
  have hh := checksCost_le allChecks d B h
  simp [allChecks] at hh ⊢
  omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramExecuteCost -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem final_lengths_le (x : Input) (l : Fin 8 → ℕ) (a : Fin 64) :
    (Prepared.finalModel x l).len a ≤ bitBound x l := by
  have h := (budget_majorant Layout.guardedCode (Layout.initialModel x l)
    (Layout.setupScale x l) (Layout.initial_lengths_le x l) (Layout.guarded_scaleBound x l)).1 a
  simpa only [Layout.guardedCode,result_append,Layout.model,Prepared.finalModel,bitBound] using h

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPublic -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem prepared_encodes (x : Input) (l : Fin 8 → ℕ) (w : Words)
    (hs : Shape (Prepared.finalModel x l) w) (hm : x.clauses≠0) (hq : (produce x).Q≠0) :
    Layout.EncodesParameters (produce x) w := by
  have hv (i : Fin 12) : BinaryArithmetic.toNat (w (publicSlot i))=(Layout.model x l).val (publicSlot i) :=
    (hs.1 _).trans (guard_preserves_public (Layout.model x l) i)
  rcases Layout.model_core_values x l with ⟨hL,hw,hs',hr,hQ,he,hR,hN⟩
  exact ⟨(hv 0).trans hL,(hv 1).trans hw,(hv 2).trans hs',
    (hv 3).trans hr,(hv 4).trans hQ,(hv 5).trans he,
    (hv 6).trans hR,(hv 7).trans hN,
    (hv 8).trans (Layout.model_precision x l hm),
    (hv 9).trans (Layout.model_degree x l hq),
    (hv 10).trans (Layout.model_fieldCard x l hq),
    (hv 11).trans (Layout.model_jet x l hm hq)⟩

theorem encodes_congr (p : Parameters) (w w' : Words)
    (h : ∀ i, w (publicSlot i)=w' (publicSlot i)) :
    Layout.EncodesParameters p w ↔ Layout.EncodesParameters p w' := by
  unfold Layout.EncodesParameters
  have h0 : w 13=w' 13 := h 0
  have h1 : w 14=w' 14 := h 1
  have h2 : w 17=w' 17 := h 2
  have h3 : w 18=w' 18 := h 3
  have h4 : w 21=w' 21 := h 4
  have h5 : w 25=w' 25 := h 5
  have h6 : w 29=w' 29 := h 6
  have h7 : w 31=w' 31 := h 7
  have h8 : w 33=w' 33 := h 8
  have h9 : w 34=w' 34 := h 9
  have h10 : w 35=w' 35 := h 10
  have h11 : w 42=w' 42 := h 11
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

/-- Native end-to-end parameter production and guard testing. On a successful
fast path every public output word encodes its exact specified parameter. -/
theorem setup_output (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t final, Eval setup t (state r w) final ∧ (final.regs 8=true ↔ Guard x) ∧
      (Guard x → Layout.EncodesParameters (produce x) (fun a => final.stacks (Bank.port a))) ∧
      t ≤ runtimeBound x l := by
  obtain ⟨t,mid,final,he,hg,⟨rm,wm,hm,hshape⟩,hframe,ht⟩ := setup_eval x l w r hs
  have hlen (j : Fin 10) (b : Fin 2) :
      ((projectState id guardStacks mid).stacks (BitGuard.pair j b)).length ≤ bitBound x l := by
    rw [hm]
    change ((state rm wm).stacks (guardStacks (BitGuard.pair j b))).length ≤ _
    rw [guardStacks_pair]
    rw [state_port]
    exact (hshape.2 _).trans (final_lengths_le x l _)
  have hc := BitGuard.allChecksCost_le (projectState id guardStacks mid) (bitBound x l) hlen
  refine ⟨t,final,he,hg,?_,by dsimp [runtimeBound]; omega⟩
  intro hg'
  have hm' : x.clauses≠0 := Nat.ne_of_gt hg'.2.2.1
  have hq' : (produce x).Q≠0 := by have hh := hg'.2.2.2.2.2.2.1; omega
  have hp := prepared_encodes x l wm hshape hm' hq'
  apply (encodes_congr (produce x) (fun a => final.stacks (Bank.port a)) wm ?_).mpr hp
  intro i
  rw [hframe (publicSlot i) (publicSlot_lt i),hm,state_port]


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramSerialization -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBanked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


open BitProgram StructuredCalls StructuredProgram

theorem command_clears (a : Data) :
    ∃ b, Eval command (1+checksCost allChecks a) a b ∧ ∀ i, b.stacks i=[] := by
  let a0 := (Atom.set (8 : Fin 9) true).eval a
  obtain ⟨b,he,hacc,hframe,hclear⟩ := checks_eval allChecks (List.nodup_finRange 10) a0
  refine ⟨b,(Eval.base (.atom _ _)).seq he,?_⟩
  intro i
  let j : Fin 10 := ⟨i.val/2,by omega⟩
  let bit : Fin 2 := ⟨i.val%2,Nat.mod_lt _ (by decide)⟩
  have hi : pair j bit=i := by
    apply Fin.ext
    dsimp [pair,j,bit]
    omega
  rw [← hi]
  exact hclear j (by simp [allChecks]) bit

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

private theorem guard_frame (r : Fin 9 → Bool) (w : Words) (b : BitGuard.Data)
    (hb : ∀ i, b.stacks i=[]) :
    embedState id guardStacks (state r w) b=state b.regs (guardedWords w) := by
  apply embedState_eq_of_ports id guardStacks (state r w) _ b
    Function.injective_id guardStacks_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    rw [hb]
    simp [state,Bank.state,guardedWords,guardStacks]
  · intro i hi
    by_cases hlo : i.val < 44
    · simp [state,Bank.state,guardedWords,show i.val < 64 by omega,hlo]
    · have hhigh : 64 ≤ i.val := by
        by_contra hn
        have hlt : i.val < 64 := by omega
        let j : Fin 20 := ⟨i.val-44,by omega⟩
        apply hi
        refine ⟨j,?_⟩
        apply Fin.ext
        dsimp [guardStacks,j]
        omega
      simp [state,Bank.state,show ¬i.val < 64 by omega]

private theorem banked_trace (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t rf wf, Eval setup t (state r w) (state rf wf) ∧
      Shape (guardedModel x l) wf := by
  obtain ⟨t,rf,w',he,hs',ht⟩ := numeric_eval x l w r hs
  let mid := state rf w'
  obtain ⟨b,hb,hclear⟩ := BitGuard.command_clears (projectState id guardStacks mid)
  have hc := eval_liftCommand_from_state BitGuard.command 0 0 id guardStacks mid
    Function.injective_id guardStacks_injective hb
  rw [guard_frame rf w' b hclear] at hc
  refine ⟨t+((1+BitGuard.checksCost BitGuard.allChecks (projectState id guardStacks mid))+1),
    b.regs,guardedWords w',he.seq hc,?_⟩
  constructor
  · intro a
    by_cases ha : a.val < 44
    · simpa [guardedModel,guardedWords,ha] using hs'.1 a
    · simp [guardedModel,guardedWords,ha]
  · intro a
    by_cases ha : a.val < 44
    · simpa [guardedModel,guardedWords,ha] using hs'.2 a
    · simp [guardedModel,guardedWords,ha]

/-- The actual post-guard endpoint has an empty physical work bank. Its low
table keeps all input and parameter words and clears the comparison operands.
The separate ninth register retains the guard result. -/
theorem setup_banked_output (x : Input) (l : Fin 8 → ℕ) (w : Words) (r : Fin 9 → Bool)
    (hs : Shape (Layout.initialModel x l) w) :
    ∃ t rf wf, Eval setup t (state r w) (state rf wf) ∧
      (rf 8=true ↔ Guard x) ∧ Shape (guardedModel x l) wf ∧
      (Guard x → Layout.EncodesParameters (produce x) wf) ∧ t ≤ runtimeBound x l := by
  obtain ⟨u,rf,wf,he,hshape⟩ := banked_trace x l w r hs
  obtain ⟨t,final,ht,hguard,hparameters,hbound⟩ := setup_output x l w r hs
  have hf := ht.final_unique (Bank.port 0) he
  subst final
  refine ⟨t,rf,wf,ht,hguard,hshape,?_,hbound⟩
  simpa only [state_port] using hparameters

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem registers_injective (n : ℕ) (hn : n ≤ 40) : Function.Injective (registers n hn) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun z : Fin 40 => z.val) h
theorem block_injective (base n : ℕ) (hn : base+n ≤ 768) : Function.Injective (block base n hn) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [block] at this; omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendParameterCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
open LeafParametersProgram

theorem parameterCall_eval_oai (a : Data) (x : Input) (l : Fin 8 → ℕ) (w : Bank.Words)
    (hs : Circuit.Shape (Layout.initialModel x l) w)
    (hp : projectState r9 bank a = Execute.state (a.regs ∘ r9) w) :
    ∃ n ≤ Execute.runtimeBound x l+1, ∃ rf wf,
      Eval parameterCall n a (embedState r9 bank a (Execute.state rf wf)) ∧
      (rf 8=true ↔ Guard x) ∧ Circuit.Shape (Execute.guardedModel x l) wf ∧
      (Guard x → Layout.EncodesParameters (produce x) wf) := by
  obtain ⟨n,rf,wf,he,hg,hshape,hparams,hn⟩ := Execute.setup_banked_output x l w (a.regs ∘ r9) hs
  have ht := compiled_halt_trace he (Bank.port 0) (Bank.port 42)
  rw [←hp] at ht
  exact ⟨n+1,by omega,rf,wf,
    eval_call_from_state Execute.program r9 bank a (registers_injective ..) (block_injective ..) ht,
    hg,hshape,hparams⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.parameterCall_eval_oai
