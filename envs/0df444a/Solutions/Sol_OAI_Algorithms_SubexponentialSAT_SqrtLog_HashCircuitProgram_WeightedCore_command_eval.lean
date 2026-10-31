-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:49:26.638095+00:00
-- url     : https://prove2.me/submissions/a71c915f-d741-4e7d-af03-abb7dd2368c7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S146
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Normalize_program_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Product_scalePhase_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

theorem encode_scaled_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (key : K → List Bool) (entries) :
    (encode key (scaled p t M cache table scalar entries)).length = (encode key entries).length := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
      simp only [scaled,List.map_cons,encode_cons,List.length_append,Encoding.length_frame,
        RingProgram.flat_length]
      simpa only [scaled] using congrArg (fun n => (2*(key a.1).length+1)+(2*(d*baseWidth p t)+1)+n) ih

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Cost stage. -/

/-! Semantics stage. -/

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramWeightedCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native weighted sparse accumulation. This local56-stack core is
used by hash rows and head moments. It retains the source dictionary41,
consumes the flat coefficient44, and replaces accumulator42 by the normalized
weighted sum. Its output restores all temporary work used by these phases. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem copyScaled_eval (regs : Fin 8 → Bool) (a : Product.Store) (h : a.mapped = []) :
    Eval (Product.copy 38 4) (7*a.scaled.length+5) (Product.state regs a)
      (Product.state (readRegs regs 0 1 none) {a with mapped := a.scaled}) := by
  apply Product.copy_state regs a {a with mapped := a.scaled} 38 4
    (by decide) (by decide) (by decide)
  funext i; fin_cases i <;> simp [Product.tapes,StackRoutines.copyStacks,h]

theorem clearScaled_eval (regs : Fin 8 → Bool) (a : Product.Store) :
    Eval (Product.clear 38) (2*a.scaled.length+3) (Product.state regs a)
      (Product.state (readRegs regs 0 1 none) {a with scaled := []}) := by
  apply Product.clear_state regs a {a with scaled := []} 38
  funext i; fin_cases i <;> simp [Product.tapes,StackRoutines.clearStacks]

variable {K : Type*} [DecidableEq K]

theorem command_eval_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (hk : Function.Injective key)
    (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (a : Product.Store)
    (he : Product.scaleEnvironment a a.coeff = Squarefree.ScaleProgram.environment p t M cache table scalar degree width)
    (hm : a.modulus = M.bits) (hwidth : a.width = width) (hdegree : a.degree = degree)
    (hr : a.right = Squarefree.ScaleProgram.encode key entries)
    (hseed : a.acc = Normalize.bytes key seed)
    (hs : a.scaleSource = []) (hc : a.scalar = []) (ho : a.scaled = [])
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) (h27 : a.normalSource = [])
    (h51 : a.normalCount = []) :
    let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
    ∃ n ≤ 25*a.right.length+11*a.coeff.length+9*a.degree.length+
      Squarefree.ScaleProgram.budget key entries + Normalize.work p t M cache key weighted seed+43,
      ∃ rr, Eval command n (Product.state regs a)
        (Product.state rr {a with coeff := [], acc := Normalize.bytes key (Normalize.run p t M cache weighted seed)}) := by
  dsimp only
  let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
  let output := Squarefree.ScaleProgram.encode key weighted
  let b : Product.Store := {a with coeff := [],scaled := output}
  let c : Product.Store := {b with mapped := output}
  let e : Product.Store := {c with scaled := []}
  obtain ⟨n,hn,r1,hscale⟩ := Product.scalePhase_eval p t M cache hz table scalar degree width hd hw
    key entries regs a he hr hs hc ho h0 h1 h2 h3 h4 h27
  have hcopy := copyScaled_eval r1 b (by simpa [b] using h4)
  have hclear := clearScaled_eval (readRegs r1 0 1 none) c
  obtain ⟨m,hmb,r2,hnorm⟩ := Product.normalizePhase_eval p t M cache key hk weighted seed
    (readRegs (readRegs r1 0 1 none) 0 1 none) e
    (by simpa [e,c,b] using hm)
    (by simpa [e,c,b,hwidth] using hw)
    (by simpa [e,c,b,hdegree] using hd)
    (by rfl) (by simpa [e,c,b] using hseed)
    (by simpa [e,c,b] using h27) (by simpa [e,c,b] using h51)
    (by simpa [e,c,b] using h0) (by simpa [e,c,b] using h1)
    (by simpa [e,c,b] using h2) (by simpa [e,c,b] using h3)
  have hlen : output.length = a.right.length := by
    rw [hr]
    exact Squarefree.ScaleProgram.encode_scaled_length p t M cache table scalar key entries
  have hrun := hscale.seq (hcopy.seq (hclear.seq hnorm))
  refine ⟨n+(7*output.length+5)+ (2*output.length+3)+m,?_,r2,?_⟩
  · dsimp only [b,c,e,weighted] at hn hmb ⊢
    rw [hlen] at hmb ⊢
    omega
  · convert hrun using 1
    · dsimp only [b,c]
      omega
    · apply congrArg (Product.state r2)
      cases a
      simp_all [b,c,e,weighted]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval_oai.{u_1}
