-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:23:07.517442+00:00
-- url     : https://prove2.me/submissions/a7e7c6c3-0f24-4410-9a48-fcad028d8944

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S080
import Definitions.Def_OAIQ081S100
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LiftRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The finite free ring used for prime-power counting

This file constructs the quotient by a monic polynomial, proves that a
positive-degree quotient retains the base ring, and constructs coefficient
reduction maps between these polynomial quotient rings.
-/

namespace SubexponentialSAT.LiftRing

noncomputable section

open Polynomial

theorem decodeCount_natCast (p μ : ℕ) {F : (Base p μ)[X]}
    (hF : F.Monic) (hdeg : 0 < F.natDegree) (n : ℕ) (hn : n < p ^ μ) :
    decodeCount p μ hF (n : Lambda p μ F) = n := by
  have hcast : (n : Lambda p μ F) = of F (n : Base p μ) := by
    simp only [map_natCast]
  simp only [decodeCount, hcast, remainder_of hF hdeg, coeff_C_zero]
  exact ZMod.val_natCast_of_lt hn

end

end SubexponentialSAT.LiftRing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFlatCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Count decisions from the actual flat coefficient representation

Coefficients are stored constant-first, with four consecutive little-endian
words per coefficient. Width and modulus are runtime data. This adapter reads
the first word, discards the unused polynomial suffix, and executes the checked
remainder-and-positivity program. It does not serialize the array into records.
-/

namespace SubexponentialSAT.SubexpFlatCount

open BitProgram StructuredCalls ProgramLinking

theorem peek_eval (d : Data) : Eval peekCmd 1 d (peekState d) :=
  .base (.atom _ _)

theorem decoderPorts_injective : Function.Injective decoderPorts := Fin.castSucc_injective 7

end SubexponentialSAT.SubexpFlatCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramReadback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-degree readback of a reconstructed scalar count. The original
fixed program already reads a runtime B-bit first word and discards a suffix;
this theorem removes the old four-coordinate type restriction. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Readback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

/-- Physical first-coordinate extraction, with arbitrary remaining dimension. -/
theorem extract_eval {B : ℕ} (hB : 0 < B)
    (word suffix : List Bool) (hword : word.length = B)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    Eval extractCmd (14 * B + 2 * suffix.length + 16)
      (start regs modulus width (word ++ suffix))
      (finish (reset regs) modulus width word) := by
  let d₀ := start regs modulus width (word ++ suffix)
  let d₁ := peekState d₀
  let d₂ := SubexpScanPrimitives.afterTake d₁ 0 6 0 1 word suffix
  have hw : word ≠ [] := by intro h; simp [h] at hword; omega
  have hp : d₁.regs 1 = true := by
    cases he : word with
    | nil => exact False.elim (hw he)
    | cons b bs => simp [d₁, d₀, peekState, start, store, he]
  have ht := SubexpScanPrimitives.takeWord_eval d₁ 7 1 2 0 6 0 1
    (by decide) (by decide) word suffix
    (by simp [d₁, d₀, peekState, start, store])
    (by rfl) (by rfl) (by simp [d₁, d₀, peekState, start, store, hwidth, hword])
  have hc₀ := ListRegisterProgram.clear_run (0 : Fin 8) (0 : Fin 8) 1 d₂.regs d₂.stacks
  have hregs : reset d₂.regs = reset regs := by
    simp [reset, d₂, d₁, d₀, SubexpScanPrimitives.afterTake, peekState, start,
      StackRoutines.readRegs_reset]
  change readRegs d₂.regs 0 1 none = reset regs at hregs
  have hsource : d₂.stacks 0 = suffix := by simp [d₂, SubexpScanPrimitives.afterTake]
  have hstacks : StackRoutines.clearStacks 0 d₂.stacks = store [] modulus word width := by
    funext i
    fin_cases i <;> simp [d₂, d₁, d₀, SubexpScanPrimitives.afterTake, peekState,
      start, store, StackRoutines.clearStacks]
  have hc : Eval clearCmd (2 * suffix.length + 3) d₂
      (finish (reset regs) modulus width word) := by
    apply Eval.call
    simpa only [ListRegisterProgram.Run, hsource, hregs, hstacks, finish,
      StructuredProgram.State.withPC] using hc₀
  have ht' : Eval takeCmd (14 * B + 11) d₁ d₂ := by simpa only [takeCmd, hword] using ht
  have htotal : Eval extractCmd (1 + ((14 * B + 11 + (2 * suffix.length + 3)) + 1)) d₀
      (finish (reset regs) modulus width word) :=
    (peek_eval d₀).seq (Eval.ite_true (no := .base .skip) hp (ht'.seq hc))
  convert htotal using 1 ; omega

end SubexponentialSAT.SqrtLog.LeafProgram.Readback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

theorem decodeCount_natCast (ht : 0 < t) (hd : d ≠ 0) (n : ℕ) (hn : n < 3 ^ t) :
    a.decodeCount t ht (n : a.O t) = n :=
  LiftRing.decodeCount_natCast 3 t (a.F_monic t ht) (by rw [a.F_degree t ht]; omega) n hn

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete ternary coefficient input and the executable represented arithmetic
for the supplied-polynomial unramified ring model. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

theorem modelRing_readBase (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) :
    a.readBase t ht ((modelRing t ht hd a M cache).decode x) =
      wordValue 3 t (x ⟨0, hd⟩) := by
  have h := congrFun (modelRing_coordinates t ht hd a M cache x) ⟨0, hd⟩
  simpa only [RingModel.Data.coordinates_apply, RingModel.Data.readBase] using h

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramReadbackReduce
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The count reader reduces the extracted scalar word before returning it.
It therefore works for arbitrary valid coefficient codes, including codes
with noncanonical representatives of zero. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Readback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ProgramLinking SubexponentialSAT.SubexpFlatCount

private theorem embed_remainder (pc : Option (Fin 89)) (regs frameRegs : Fin 8 → Bool)
    (input modulus word width : List Bool) :
    embedCfg id decoderPorts id none
      (⟨none, frameRegs, store [] modulus [] width⟩ : Cfg 8 8 89)
      ⟨pc, regs, ModularDivisionPrograms.resting input modulus word⟩ =
      ⟨pc, regs, store input modulus word width⟩ := by
  apply embedCfg_eq_of_ports id decoderPorts id none _ _ _
    Function.injective_id decoderPorts_injective
  · cases pc <;> rfl
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · exact False.elim (hi ⟨6, rfl⟩)
    · rfl

theorem remainder_eval (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    ∃ n finalRegs, n ≤ 100 * (modulus.length + word.length + 1)^2 ∧
      Eval (.call remainderProgram) n (finish regs modulus width word)
        ⟨finalRegs, store (ModularArithmetic.reduce modulus word) modulus [] width⟩ := by
  obtain ⟨finalRegs, n, hn, ht⟩ := ModularDivisionPrograms.remainder_correct regs modulus word
  have h := liftProgram_trace ModularDivisionPrograms.remainderProgram id decoderPorts
    (⟨none, regs, store [] modulus [] width⟩ : Cfg 8 8 89)
    Function.injective_id decoderPorts_injective ht
  rw [embed_remainder, embed_remainder] at h
  exact ⟨n, finalRegs, hn, .call _ h⟩

theorem countProgram_run {B : ℕ} (hB : 0 < B)
    (word suffix : List Bool) (hword : word.length = B)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    ∃ finalRegs, RunsIn countProgram (budget B modulus (word ++ suffix))
      ((start regs modulus width (word ++ suffix)).withPC (some countProgram.entry))
      (⟨none, finalRegs, store (ModularArithmetic.reduce modulus word) modulus [] width⟩ : Cfg 8 8 _) := by
  have he := extract_eval hB word suffix hword regs modulus width hwidth
  obtain ⟨n, finalRegs, hn, ht⟩ := remainder_eval (reset regs) modulus width word
  refine ⟨finalRegs, 14 * B + 2 * suffix.length + 16 + n + 1, ?_,
    compiled_halt_trace (he.seq ht) 0 0⟩
  dsimp [budget]
  simp only [List.length_append, hword] at *
  nlinarith

open RingProgram SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

theorem firstWord_mod_eq (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (modelRing t ht hd a M cache).decode x = (z : a.O t)) :
    BinaryArithmetic.toNat (x ⟨0, hd⟩).val % 3^t = z := by
  have h := congrArg (a.decodeCount t ht) hx
  rw [a.decodeCount_natCast t ht (Nat.ne_of_gt hd) z hz] at h
  unfold RingModel.Data.decodeCount at h
  rw [modelRing_readBase] at h
  simpa [wordValue, ZMod.val_natCast] using h

theorem reduced_firstWord_value (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : Code (ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (modelRing t ht hd a M cache).decode x = (z : a.O t))
    (modulus : List Bool) (hm : BinaryArithmetic.toNat modulus = 3^t) :
    BinaryArithmetic.toNat (ModularArithmetic.reduce modulus (x ⟨0, hd⟩).val) = z := by
  rw [ModularArithmetic.reduce_correct _ _ (by rw [hm]; positivity), hm]
  exact firstWord_mod_eq t ht hd a M cache x z hz hx

end SubexponentialSAT.SqrtLog.LeafProgram.Readback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramReadbackModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical count readback for the supplied irreducible model.
The dimension and scalar width occur only in data and bounds. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Readback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount
open RingProgram SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpLiftRing SubexponentialSAT.BinaryArithmetic

theorem flat_firstWord {d B : ℕ} (hd : 0 < d) (x : RingProgram.Code (Word B) d) :
    ∃ suffix, flat x = (x ⟨0, hd⟩).val ++ suffix ∧ suffix.length = (d - 1) * B := by
  cases d with
  | zero => omega
  | succ d =>
      refine ⟨flat (fun i : Fin d => x i.succ), ?_, ?_⟩
      · simp [flat, List.ofFn_succ]
      · simp

theorem model_countProgram_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (x : RingProgram.Code (ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (modelRing t ht hd a M cache).decode x = (z : a.O t))
    (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t) (hwidth : width.length = baseWidth 3 t) :
    ∃ finalRegs word, BinaryArithmetic.toNat word = z ∧
      word.length = modulus.length + baseWidth 3 t ∧
      RunsIn countProgram (budget (baseWidth 3 t) modulus (flat x))
        ((start regs modulus width (flat x)).withPC (some countProgram.entry))
        (⟨none, finalRegs, store word modulus [] width⟩ : Cfg 8 8 _) := by
  have hB : 0 < baseWidth 3 t := by rw [ternary_baseWidth]; omega
  obtain ⟨suffix, hs, _⟩ := flat_firstWord hd x
  obtain ⟨finalRegs, hr⟩ := countProgram_run hB (x ⟨0, hd⟩).val suffix
    (x ⟨0, hd⟩).property regs modulus width hwidth
  refine ⟨finalRegs, ModularArithmetic.reduce modulus (x ⟨0, hd⟩).val,
    reduced_firstWord_value t ht hd a M cache x z hz hx modulus hm, ?_, ?_⟩
  · simp [ModularArithmetic.reduce_length, (x ⟨0, hd⟩).property]
  · simpa only [hs] using hr

end SubexponentialSAT.SqrtLog.LeafProgram.Readback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete CRT reconstruction and full-word modular readback. The same actual
native traces satisfy correctness, polynomial local time, and every-prefix
bounds on all source stacks, including the persistent caller frame. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace

open OAI BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram ReconstructionProgram.Native


/-- Modular reduction and extraction remain polynomial even when the residue
vector contains noncanonical representatives. -/
theorem readback_budget_le (B S : ℕ) (modulus input : List Bool)
    (hB : B ≤ S) (hmodulus : modulus.length ≤ S) (hinput : input.length ≤ S) :
    SubexpFlatCount.budget B modulus input ≤ 500*(S+1)^2 := by
  unfold SubexpFlatCount.budget
  nlinarith [Nat.mul_self_le_mul_self
    (show modulus.length + B + 1 ≤ 2*S+1 by omega)]

/-- The actual reader produces a complete little-endian count word; its Boolean
head is not used as a satisfiability answer. The caller later normalizes this
word and computes positivity on the separate answer stack. -/
theorem readback_run_space_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (count : ℕ)
    (hcount : count < 3^t)
    (hx : (RingProgram.modelRing t ht hd a M cache).decode x = (count : a.O t))
    (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t)
    (hw : width.length = baseWidth 3 t)
    (S : ℕ) (hB : baseWidth 3 t ≤ S) (hmodulus : modulus.length ≤ S)
    (hinput : (RingProgram.flat x).length ≤ S) :
    ∃ finalRegs word steps, BinaryArithmetic.toNat word = count ∧
      word.length = modulus.length + baseWidth 3 t ∧ steps ≤ 500*(S+1)^2 ∧
      Trace LeafProgram.Readback.countProgram steps
        ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
          (some LeafProgram.Readback.countProgram.entry))
        (⟨none, finalRegs, SubexpFlatCount.store word modulus [] width⟩ : Cfg 8 8 _) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace LeafProgram.Readback.countProgram prefixSteps
          ((SubexpFlatCount.start regs modulus width (RingProgram.flat x)).withPC
            (some LeafProgram.Readback.countProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits (SubexpFlatCount.start regs modulus width (RingProgram.flat x)).stacks +
            500*(S+1)^2 := by
  obtain ⟨finalRegs, word, hvalue, hlength, steps, hsteps, htrace⟩ :=
    LeafProgram.Readback.model_countProgram_run t ht hd a M cache x count hcount hx
      regs modulus width hm hw
  have hbudget : steps ≤ 500*(S+1)^2 := hsteps.trans
    (readback_budget_le (baseWidth 3 t) S modulus (RingProgram.flat x) hB hmodulus hinput)
  refine ⟨finalRegs, word, steps, hvalue, hlength, hbudget, htrace, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _ (steps := 500*(S+1)^2)
    (by rfl) prefixSteps intermediate (hprefix.trans hbudget) hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space_oai
