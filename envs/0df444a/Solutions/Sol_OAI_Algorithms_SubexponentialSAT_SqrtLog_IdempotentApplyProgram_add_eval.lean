-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:59:19.782242+00:00
-- url     : https://prove2.me/submissions/ccbc989f-460a-4e7f-b281-2c73e17721ce

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S146
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Normalize_program_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed record-control code for sparse-hash evaluation. This module fixes
all parsing and traversal code. Arithmetic components below are finite native
commands, to be instantiated by the separate dictionary modules; no semantic
function is called by the machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem copy_eval (d : Machine) (src dst tmp : Fin 96)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7*(d.stacks src).length+5) d (copied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd
    (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [copied,StackRoutines.copyResult,StructuredProgram.State.withPC,
    StackRoutines.copyProgram,Nat.add_assoc] using hh

theorem clear_eval (d : Machine) (src : Fin 96) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [cleared,StackRoutines.clearResult,StructuredProgram.State.withPC,
    StackRoutines.clearProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Split-memory rules for composing the actual low arithmetic workspace with
persistent high interpreter data. All movement lemmas retain primitive costs. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem low_injective : Function.Injective lowPort := Fin.castAdd_injective _ _
theorem high_injective : Function.Injective highPort := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change 56+i.val = 56+j.val at hh
  omega

theorem low_ne_high (i : Fin 56) (j : Fin 40) : lowPort i ≠ highPort j := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = 56+j.val at hh
  omega

theorem update_low (low high) (i : Fin 56) (word : List Bool) :
    Function.update (tapes low high) (lowPort i) word = tapes (Function.update low i word) high := by
  funext j
  induction j using (Fin.addCases (m := 56) (n := 40)) with
  | left j =>
    change (Function.update (tapes low high) (lowPort i) word) (lowPort j) =
      tapes (Function.update low i word) high (lowPort j)
    by_cases hj : j = i
    · subst j; simp
    · have hh : lowPort j ≠ lowPort i := fun h => hj (low_injective h)
      simp [hh,hj]
  | right j =>
    change (Function.update (tapes low high) (lowPort i) word) (highPort j) =
      tapes (Function.update low i word) high (highPort j)
    simp [(low_ne_high i j).symm]

theorem update_high (low high) (i : Fin 40) (word : List Bool) :
    Function.update (tapes low high) (highPort i) word = tapes low (Function.update high i word) := by
  funext j
  induction j using (Fin.addCases (m := 56) (n := 40)) with
  | left j =>
    change (Function.update (tapes low high) (highPort i) word) (lowPort j) =
      tapes low (Function.update high i word) (lowPort j)
    simp [low_ne_high j i]
  | right j =>
    change (Function.update (tapes low high) (highPort i) word) (highPort j) =
      tapes low (Function.update high i word) (highPort j)
    by_cases hj : j = i
    · subst j; simp
    · have hh : highPort j ≠ highPort i := fun h => hj (high_injective h)
      simp [hh,hj]

theorem embed_low (regs rr : Fin 8 → Bool) (low next : Fin 56 → List Bool) (high : Fin 40 → List Bool) :
    embedState id lowPort (state regs low high) (⟨rr,next⟩ : State 8 56) = state rr next high := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; simp [state]
  · intro i hi
    induction i using (Fin.addCases (m := 56) (n := 40)) with
    | left i => exact False.elim (hi ⟨i,rfl⟩)
    | right i => simp [state,tapes]

/-- A preserving copy from high persistent memory into arithmetic workspace. -/
theorem copy_high_low (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src tmp : Fin 40) (dst : Fin 56) (hne : src ≠ tmp) (htmp : high tmp = []) :
    Eval (copy (highPort src) (lowPort dst) (highPort tmp)) (7*(high src).length+5)
      (state regs low high)
      (state (readRegs regs 0 1 none) (Function.update low dst (high src ++ low dst)) high) := by
  have h := Native.copy_eval (state regs low high) (highPort src) (lowPort dst) (highPort tmp)
    (low_ne_high dst src).symm (fun he => hne (high_injective he))
    (low_ne_high dst tmp).symm (by simpa [state] using htmp)
  simpa only [state,copied,StackRoutines.copyStacks,tapes_high,tapes_low,update_low] using h

/-- A preserving copy of a result back into persistent high memory. -/
theorem copy_low_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src : Fin 56) (dst tmp : Fin 40) (hne : tmp ≠ dst) (htmp : high tmp = []) :
    Eval (copy (lowPort src) (highPort dst) (highPort tmp)) (7*(low src).length+5)
      (state regs low high)
      (state (readRegs regs 0 1 none) low (Function.update high dst (low src ++ high dst))) := by
  have h := Native.copy_eval (state regs low high) (lowPort src) (highPort dst) (highPort tmp)
    (low_ne_high src dst) (low_ne_high src tmp) (fun he => hne (high_injective he))
    (by simpa [state] using htmp)
  simpa only [state,copied,StackRoutines.copyStacks,tapes_high,tapes_low,update_high] using h

theorem clear_low (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src : Fin 56) :
    Eval (clear (lowPort src)) (2*(low src).length+3) (state regs low high)
      (state (readRegs regs 0 1 none) (Function.update low src []) high) := by
  simpa only [state,cleared,StackRoutines.clearStacks,tapes_low,update_low] using
    Native.clear_eval (state regs low high) (lowPort src)

theorem clear_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src : Fin 40) :
    Eval (clear (highPort src)) (2*(high src).length+3) (state regs low high)
      (state (readRegs regs 0 1 none) low (Function.update high src [])) := by
  simpa only [state,cleared,StackRoutines.clearStacks,tapes_high,update_high] using
    Native.clear_eval (state regs low high) (highPort src)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem normalizePorts_injective : Function.Injective normalizePorts := by decide

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_eval (d : Data) (src dst : Fin 56)
    (hsd : src ≠ dst) (hst : src ≠ 47) (htd : (47 : Fin 56) ≠ dst) (htmp : d.stacks 47 = []) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (afterCopy d src dst) := by
  exact .call _ (ListRegisterProgram.copy_run src dst 47 0 1 hsd hst htd (by decide) d.regs d.stacks htmp)

theorem clear_eval (d : Data) (src : Fin 56) :
    Eval (clear src) (2*(d.stacks src).length+3) d (afterClear d src) := by
  apply Eval.call
  have h := clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  simpa only [clearResult,afterClear,StructuredProgram.State.withPC,Nat.add_assoc] using hh

theorem copy_state (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 56)
    (hsd : src ≠ dst) (hst : src ≠ 47) (htd : (47 : Fin 56) ≠ dst)
    (hs : copyStacks src dst (tapes a) = tapes b) :
    Eval (copy src dst) (7*(tapes a src).length+5) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterCopy,state,hs] using copy_eval (state regs a) src dst hsd hst htd rfl

theorem clear_state (regs : Fin 8 → Bool) (a b : Store) (src : Fin 56)
    (hs : clearStacks src (tapes a) = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterClear,state,hs] using clear_eval (state regs a) src


end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copyMapped_eval (regs : Fin 8 → Bool) (a : Store) (he : a.normalSource = []) :
    Eval (copy 4 27) (7*a.mapped.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with normalSource := a.mapped }) := by
  apply copy_state regs a _ 4 27 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem copyDegree_eval (regs : Fin 8 → Bool) (a : Store) (he : a.normalCount = []) :
    Eval (copy 39 51) (7*a.degree.length+5) (state regs a)
      (state (readRegs regs 0 1 none) { a with normalCount := a.degree }) := by
  apply copy_state regs a _ 39 51 (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [copyStacks,tapes,he]

theorem clearMapped_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 4) (2*a.mapped.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with mapped := [] }) := by
  apply clear_state regs a _ 4
  funext i; fin_cases i <;> simp [clearStacks,tapes]

theorem clearNormalCount_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval (clear 51) (2*a.normalCount.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with normalCount := [] }) := by
  apply clear_state regs a _ 51
  funext i; fin_cases i <;> simp [clearStacks,tapes]

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem embed_normalize (regs rr : Fin 8 → Bool) (a : Store) (dict source count : List Bool)
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) :
    embedState id normalizePorts (state regs a)
      (Normalize.state rr a.modulus a.width count dict source) =
    state rr { a with acc := dict, normalSource := source, normalCount := count } := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id normalizePorts_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> simp [normalizePorts,state,tapes,Normalize.state,Normalize.extend,
      Dictionary.machine,Dictionary.tapes,Dictionary.outputTape,h0,h1,h2,h3,h4,Fin.snoc]
    all_goals first | rfl
  · intro i hi
    fin_cases i <;> first | rfl | (exfalso; apply hi; decide)

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

theorem normalize_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Store)
    (hm : a.modulus = M.bits) (hw : a.width.length = baseWidth p t) (hd : a.normalCount.length = d)
    (hsource : a.normalSource = Normalize.bytes key source) (hseed : a.acc = Normalize.bytes key seed)
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) :
    ∃ n ≤ Normalize.work p t M cache key source seed + 2, ∃ rr,
      Eval normalize n (state regs a)
        (state rr { a with normalSource := [], acc := Normalize.bytes key (Normalize.run p t M cache source seed) }) := by
  obtain ⟨rr,n,hn,ht⟩ := Normalize.program_run p t M cache key hk source seed regs a.width a.normalCount hd hw
  have hh := eval_call_lifted Normalize.program id normalizePorts (state regs a)
    Function.injective_id normalizePorts_injective ht
  rw [←hm,←hsource,←hseed,embed_normalize _ _ _ _ _ _ h0 h1 h2 h3 h4,
    embed_normalize _ _ _ _ _ _ h0 h1 h2 h3 h4] at hh
  have ha : { a with acc := a.acc, normalSource := a.normalSource, normalCount := a.normalCount } = a := by cases a; rfl
  rw [ha] at hh
  exact ⟨n,hn,rr,hh⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

theorem normalizePhase_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Store)
    (hm : a.modulus = M.bits) (hw : a.width.length = baseWidth p t) (hd : a.degree.length = d)
    (hsource : a.mapped = Normalize.bytes key source) (hseed : a.acc = Normalize.bytes key seed)
    (hs : a.normalSource = []) (hc : a.normalCount = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = []) (h3 : a.keyZCap = []) :
    ∃ n ≤ 9*a.mapped.length+9*a.degree.length+Normalize.work p t M cache key source seed+18,
    ∃ rr, Eval normalizePhase n (state regs a)
      (state rr {a with mapped := [], acc := Normalize.bytes key (Normalize.run p t M cache source seed)}) := by
  let b : Store := {a with normalSource := a.mapped}
  let c : Store := {b with mapped := []}
  let f : Store := {c with normalCount := c.degree}
  let g : Store := {f with normalSource := [], acc := Normalize.bytes key (Normalize.run p t M cache source seed)}
  have hcopy := copyMapped_eval regs a hs
  have hclear := clearMapped_eval (readRegs regs 0 1 none) b
  have hcount := copyDegree_eval (readRegs (readRegs regs 0 1 none) 0 1 none) c hc
  obtain ⟨n,hn,rr,hN⟩ := normalize_eval p t M cache key hk source seed
    (readRegs (readRegs (readRegs regs 0 1 none) 0 1 none) 0 1 none) f
    hm hw hd hsource hseed h0 h1 h2 h3 rfl
  have hclean := clearNormalCount_eval rr g
  have hrun := hcopy.seq (hclear.seq (hcount.seq (hN.seq hclean)))
  refine ⟨_,?_,readRegs rr 0 1 none,(by
    convert hrun using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (state (readRegs rr 0 1 none))
    cases a
    simp_all [b,c,f,g])⟩
  dsimp [b,c,f,g] at hn ⊢
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native normalized addition for the persistent polynomial registers used
by the indicator Horner loop. Both operand copies and result storage are paid. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

private theorem update_mapped (s : Product.Store) (w : List Bool) :
    Function.update (Product.tapes s) 4 w=Product.tapes {s with mapped:=w} := by
  funext i
  fin_cases i <;> simp [Product.tapes]

theorem add_eval_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    {K : Type*} [DecidableEq K] {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (table : List Bool) (degree width uCap zCap : List Bool)
    (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 11=Normalize.bytes key source)
    (hb : high 5=Normalize.bytes key seed) (htmp : high 14=[]) :
    let e:=Product.idle M.bits width cache.zero.val table degree uCap zCap
    let result:=Normalize.bytes key (Normalize.run p t M cache source seed)
    ∃ cost ≤ 18*(Normalize.bytes key source).length+9*(Normalize.bytes key seed).length+
      9*result.length+9*degree.length+Normalize.work p t M cache key source seed+43,
      ∃ rr, Eval add cost (Memory.state regs (Product.tapes e) high)
        (Memory.state rr (Product.tapes e) (binaryResult high result)) := by
  dsimp only
  let e:=Product.idle M.bits width cache.zero.val table degree uCap zCap
  let a:=Normalize.bytes key source
  let b:=Normalize.bytes key seed
  let result:=Normalize.bytes key (Normalize.run p t M cache source seed)
  let r1:=readRegs regs 0 1 none
  let r2:=readRegs r1 0 1 none
  have h1:=Memory.copy_high_low regs (Product.tapes e) high 11 14 4 (by decide) htmp
  have he4 : Product.tapes e 4=[]:=rfl
  simp only [ha,he4,List.append_nil,update_mapped] at h1
  have h2:=Memory.copy_high_low r1 (Product.tapes {e with mapped:=a}) high 5 14 42
    (by decide) htmp
  have he42 : Product.tapes {e with mapped:=a} 42=[]:=rfl
  simp only [hb,he42,List.append_nil,Memory.update_product_acc] at h2
  obtain ⟨k,hkCost,r3,hcore⟩:=Product.normalizePhase_eval p t M cache key hk source seed r2
    {e with mapped:=a,acc:=b} rfl hw hd rfl rfl rfl rfl rfl rfl rfl rfl
  have h3:=eval_liftCommand hcore 4 42 id Memory.lowPort
    (Memory.state r2 (Product.tapes {e with mapped:=a,acc:=b}) high)
    Function.injective_id Memory.low_injective
  simp only [Product.state,Memory.embed_low] at h3
  change Eval addCore (k+1)
    (Memory.state r2 (Product.tapes {e with mapped:=a,acc:=b}) high)
    (Memory.state r3 (Product.tapes {e with acc:=result}) high) at h3
  have h4:=Memory.clear_high r3 (Product.tapes {e with acc:=result}) high 11
  simp only [ha] at h4
  let r4:=readRegs r3 0 1 none
  let high1:=Function.update high (11:Fin 40) []
  have h5:=Memory.clear_high r4 (Product.tapes {e with acc:=result}) high1 5
  have hb1 : high1 5=b:=by simpa [high1,b] using hb
  simp only [hb1] at h5
  let r5:=readRegs r4 0 1 none
  let high2:=Function.update high1 (5:Fin 40) []
  have htmp2 : high2 14=[]:=by simpa [high2,high1] using htmp
  have h6:=Memory.copy_low_high r5 (Product.tapes {e with acc:=result}) high2 42 11 14
    (by decide) htmp2
  have hres : Product.tapes {e with acc:=result} 42=result:=rfl
  have hhigh2 : high2 11=[]:=by simp [high2,high1]
  simp only [hres,hhigh2,List.append_nil] at h6
  let r6:=readRegs r5 0 1 none
  let high3:=Function.update high2 (11:Fin 40) result
  have h7:=Memory.clear_low r6 (Product.tapes {e with acc:=result}) high3 42
  simp only [hres,Memory.update_product_acc] at h7
  have he:=h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))
  refine ⟨(7*a.length+5)+(7*b.length+5)+(k+1)+(2*a.length+3)+(2*b.length+3)+
    (7*result.length+5)+(2*result.length+3),?_,readRegs r6 0 1 none,?_⟩
  · dsimp [a,b,e,result,Product.idle] at hkCost ⊢
    omega
  · convert he using 1 <;> first | rfl | (dsimp [a,b,result]; omega)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval_oai.{u_1}
