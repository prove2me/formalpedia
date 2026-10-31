-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:21:23.619336+00:00
-- url     : https://prove2.me/submissions/777c95e0-afdd-4dd4-8c21-d84deff5ae9e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S146
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Normalize_program_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Product_keyPhase_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Product_scalePhase_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem frameReadRegs_injective : Function.Injective frameReadRegs := Fin.castAdd_injective _ _
theorem frameReadPorts_injective {s : ℕ} (src dst : Fin s) (h : src ≠ dst) :
    Function.Injective (frameReadPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [frameReadPorts, ParserProgram.pair]

theorem readFrame8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst)
    (bits : List Bool) (rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (readFrame8 src dst) (6 * bits.length + 4) d (afterFrame8 d src dst bits rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : embedState frameReadRegs (frameReadPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
  have hb : embedState frameReadRegs (frameReadPorts src dst) d b = afterFrame8 d src dst bits rest := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadRegs, readRegs, b, ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [frameReadRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [frameReadRegs] using h.symm⟩
      simp [afterFrame8, readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [frameReadPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [frameReadPorts] using h.symm⟩
      simp [afterFrame8, hsrc, hdst]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.frameProgram frameReadRegs
    (frameReadPorts src dst) d frameReadRegs_injective (frameReadPorts_injective src dst hsd) ht
  simpa only [ha,hb,readFrame8] using h

theorem transfer8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst) :
    Eval (transfer8 src dst) (3*(d.stacks src).length+3) d (afterTransfer8 d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [afterTransfer8,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_injective {n : ℕ} :
    Function.Injective (encodeMask (n := n)) := by
  intro a b h
  have hf : (fun i : Fin n => decide (i ∈ a)) =
      (fun i : Fin n => decide (i ∈ b)) := List.ofFn_injective h
  ext i
  have hi := congrFun hf i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all

theorem encodeIndex_injective {n : ℕ} :
    Function.Injective (encodeIndex (n := n)) := by
  intro a b h
  have hfirst : a.u = b.u ∧
      Encoding.encodeNat a.z ++ encodeMask a.vars =
        Encoding.encodeNat b.z ++ encodeMask b.vars := by
    simpa [encodeIndex, List.append_assoc] using congrArg Encoding.readNat h
  have hsecond : a.z = b.z ∧ encodeMask a.vars = encodeMask b.vars := by
    simpa using congrArg Encoding.readNat hfirst.2
  have hs := encodeMask_injective hsecond.2
  cases a
  cases b
  cases hfirst.1
  cases hsecond.1
  cases hs
  rfl

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem transfer_eval (d : Data) (src dst : Fin 56) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (afterTransfer d src dst) := by
  exact Squarefree.Program.transfer8_eval d src dst hsd

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

theorem transfer_state (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 56)
    (hsd : src ≠ dst) (hs : transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterTransfer,state,hs] using transfer_eval (state regs a) src dst hsd

theorem clear_state (regs : Fin 8 → Bool) (a b : Store) (src : Fin 56)
    (hs : clearStacks src (tapes a) = tapes b) :
    Eval (clear src) (2*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  simpa only [afterClear,state,hs] using clear_eval (state regs a) src


theorem read_state (regs : Fin 8 → Bool) (a b : Store) (src dst : Fin 56)
    (hsd : src ≠ dst) (bits tail : List Bool)
    (hin : tapes a src = Encoding.frame bits ++ tail)
    (hs : Function.update (Function.update (tapes a) src tail) dst
      (bits.reverse ++ tapes a dst) = tapes b) :
    Eval (Squarefree.Program.readFrame8 src dst) (6*bits.length+4) (state regs a)
      (state (readRegs regs 0 1 (some false)) b) := by
  simpa only [state,Squarefree.Program.afterFrame8,hs] using
    Squarefree.Program.readFrame8_eval (state regs a) src dst hsd bits tail hin

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

theorem transferCoefficient_eval (regs : Fin 8 → Bool) (a : Store) (he : a.coeff = []) :
    Eval (transfer 48 44) (3*a.reversedCoeff.length+3) (state regs a)
      (state (readRegs regs 0 1 none) { a with reversedCoeff := [], coeff := a.reversedCoeff.reverse }) := by
  apply transfer_state regs a _ 48 44 (by decide)
  funext i; fin_cases i <;> simp [transferStacks,tapes,he]

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

theorem read_eval (regs : Fin 8 → Bool) (a : Store) (key coeff tail : List Bool)
    (hin : a.left = Encoding.frame key ++ Encoding.frame coeff ++ tail)
    (hk : a.key = []) (hc : a.coeff = []) (hr : a.reversedCoeff = []) :
    Eval read (6*key.length+9*coeff.length+11) (state regs a)
      (state (readRegs regs 0 1 none) {a with left := tail, key := key.reverse, coeff := coeff}) := by
  let b : Store := {a with left := Encoding.frame coeff ++ tail, key := key.reverse}
  let c : Store := {b with left := tail, reversedCoeff := coeff.reverse}
  have h1 := read_state regs a b 40 43 (by decide) key (Encoding.frame coeff ++ tail)
    (by simpa [tapes, List.append_assoc] using hin)
    (by funext i; fin_cases i <;> first | rfl | simp [tapes,b,hk])
  have h2 := read_state (readRegs regs 0 1 (some false)) b c 40 48 (by decide) coeff tail rfl
    (by funext i; fin_cases i <;> first | rfl | simp [tapes,c,b,hr])
  have h3 := transferCoefficient_eval (readRegs (readRegs regs 0 1 (some false)) 0 1 (some false)) c hc
  have he := h1.seq (h2.seq h3)
  convert he using 1
  · simp only [c,List.length_reverse]
    omega
  · simp only [b,c,List.reverse_reverse,readRegs_reset]
    apply congrArg (state (readRegs regs 0 1 none))
    cases a
    simp_all

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


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem coefficientBytes_join {n B d : ℕ} (left : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) :
    Squarefree.KeyMapProgram.mapped left u J (coefficientBytes entries) =
      coefficientBytes (keptJoin left u J entries) := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
    rcases a with ⟨b,c⟩
    simp only [coefficientBytes] at ih
    by_cases h : (left.join b).Kept u J <;>
      simp [coefficientBytes,keptJoin,Squarefree.KeyMapProgram.mapped,h,ih]

theorem coefficientBytes_reverse {n B d : ℕ} (entries : List (Entry n B d)) :
    (coefficientBytes entries).reverse = coefficientBytes entries.reverse := by
  simp [coefficientBytes]

theorem encoded_coefficientBytes {n B d : ℕ} (entries : List (Entry n B d)) :
    Squarefree.KeyMapProgram.encoded (coefficientBytes entries) =
      Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries := by
  simp [coefficientBytes,Squarefree.KeyMapProgram.encoded,Squarefree.Program.encodeDictionary,
    List.map_map,Function.comp_def]

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem block_bytes (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded
      (Squarefree.KeyMapProgram.mapped a.1 u J
        (coefficientBytes (Squarefree.ScaleProgram.scaled p t M cache table a.2 right))).reverse) =
      bytes (block p t M cache table u J a right) := by
  rw [coefficientBytes_join,coefficientBytes_reverse,encoded_coefficientBytes]
  rfl

theorem step_eval_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (a : Entry n (baseWidth p t) d)
    (left right seed : List (Entry n (baseWidth p t) d)) (regs : Fin 8 → Bool) :
    ∃ k ≤ stepBudget p t M cache table u J a right seed, ∃ rr,
      Eval step k (state regs (working (environment p t M cache table degree width u J) (a::left) right seed))
        (state rr (working (environment p t M cache table degree width u J) left right
          (Normalize.run p t M cache (block p t M cache table u J a right) seed))) := by
  let e := environment p t M cache table degree width u J
  let start := working e (a::left) right seed
  let b : Store := {start with left := bytes left, key := (Squarefree.encodeIndex a.1).reverse, coeff := RingProgram.flat a.2}
  let scaled := Squarefree.ScaleProgram.scaled p t M cache table a.2 right
  let c : Store := {b with coeff := [], scaled := bytes scaled}
  let source := block p t M cache table u J a right
  let f : Store := {c with scaled := [], key := [], mapped := bytes source}
  have hr := read_eval regs start (Squarefree.encodeIndex a.1) (RingProgram.flat a.2) (bytes left) rfl rfl rfl rfl
  obtain ⟨k1,hk1,r1,hs⟩ := scalePhase_eval p t M cache hz table a.2 degree width hd hw
    Squarefree.encodeIndex right (readRegs regs 0 1 none) b rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨k2,hk2,r2,hk⟩ := keyPhase_eval a.1 u J (coefficientBytes scaled) r1 c rfl rfl rfl
    (by rw [encoded_coefficientBytes]; rfl) rfl rfl rfl rfl rfl
  rw [block_bytes p t M cache table u J a right] at hk
  obtain ⟨k3,hk3,r3,hn⟩ := normalizePhase_eval p t M cache Squarefree.encodeIndex
    Squarefree.encodeIndex_injective source seed r2 f rfl hw hd rfl rfl rfl rfl rfl rfl rfl rfl
  have hrun := hr.seq (hs.seq (hk.seq hn))
  refine ⟨6*(Squarefree.encodeIndex a.1).length+9*(RingProgram.flat a.2).length+11+(k1+(k2+k3)),?_,r3,?_⟩
  · dsimp [b,c,f,start,e,working,environment,idle,scaled,source] at hk1 hk2 hk3
    simp only [List.length_reverse,List.length_replicate] at hk2
    rw [hd] at hk3
    dsimp [stepBudget]
    simp only [bytes] at hk1 hk2 hk3 ⊢
    omega
  · exact hrun

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval_oai
