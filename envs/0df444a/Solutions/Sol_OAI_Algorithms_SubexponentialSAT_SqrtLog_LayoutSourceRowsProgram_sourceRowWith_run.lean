-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:06:01.41442+00:00
-- url     : https://prove2.me/submissions/bb04a254-4f79-4859-b96b-7e0d6fa06fe4

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_evaluateModel_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceForOwner_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

variable {R : Type*}

theorem serialize_append (encode : R → List Bool) (a b : List (Algorithm.Instr R)) :
    SubexpPostfixControl.serializeCode encode (a++b)=
      SubexpPostfixControl.serializeCode encode a++SubexpPostfixControl.serializeCode encode b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [SubexpPostfixControl.serializeCode,ih,List.append_assoc]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
variable {R : Type*}

theorem foldSources_code (encode : R → List Bool) (seed : Algorithm.Expr R)
    (sources : List (Algorithm.Expr R)) :
    SubexpPostfixControl.serializeCode encode (foldSources seed sources).compile=
      SubexpPostfixControl.serializeCode encode seed.compile++
        emittedBytes (fun e : Algorithm.Expr R =>
          SubexpPostfixControl.serializeCode encode e.compile) sources := by
  induction sources generalizing seed with
  | nil => simp [foldSources,emittedBytes]
  | cons e es ih =>
      change SubexpPostfixControl.serializeCode encode (foldSources (.add seed e) es).compile=_
      rw [ih]
      simp [Algorithm.Expr.compile,serialize_append,SubexpPostfixControl.serializeCode,
        SubexpPostfixControl.serializeInstr,emittedBytes,List.append_assoc]

theorem foldSources_zero_code (encode : R → List Bool) (z : R) (hz : encode z=[])
    (sources : List (Algorithm.Expr R)) :
    SubexpPostfixControl.serializeCode encode (foldSources (.lit z) sources).compile=
      [false,false]++emittedBytes (fun e : Algorithm.Expr R =>
          SubexpPostfixControl.serializeCode encode e.compile) sources := by
  rw [foldSources_code]
  simp [Algorithm.Expr.compile,SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr,hz,Encoding.frame]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

/-- Semantic values are added in the same order as the emitted sources. -/
theorem foldSources_map_eval {C A : Type*} [AddMonoid A] [Mul A]
    (decode : C → A) (seed : Algorithm.Expr C) (sources : List (Algorithm.Expr C)) :
    ((foldSources seed sources).map decode).eval=
      (seed.map decode).eval+(sources.map (fun e => (e.map decode).eval)).sum := by
  induction sources generalizing seed with
  | nil => simp [foldSources]
  | cons e es ih =>
      change ((foldSources (.add seed e) es).map decode).eval=_
      rw [ih]
      simp [Algorithm.Expr.map,Algorithm.Expr.eval,add_assoc]

theorem related_sources_sum {C A : Type*} [AddMonoid A] [Mul A]
    (decode : C → A) (value : ℕ → A) (ids : List ℕ) (sources : List (Algorithm.Expr C))
    (h : List.Forall₂ (fun i e => (e.map decode).eval=value i) ids sources) :
    (sources.map (fun e => (e.map decode).eval)).sum=(ids.map value).sum := by
  induction h with
  | nil => rfl
  | cons h hs ih => simp [h,ih]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem emittedBytes_length_le {W : Type*} (encode : W → List Bool)
    (R : ℕ → W → Prop) (L : ℕ)
    (hbound : ∀ i w, R i w → (encode w).length ≤ L)
    (ids : List ℕ) (ws : List W) (h : List.Forall₂ R ids ws) :
    (emittedBytes encode ws).length ≤ ids.length*(L+2) := by
  induction h with
  | nil => simp [emittedBytes]
  | @cons i w ids ws hr hrs ih =>
      have hw := hbound i w hr
      change ((encode w++[true,false])++emittedBytes encode ws).length ≤ _
      simp only [List.length_append,List.length_cons,List.length_nil] at *
      calc
        (encode w).length+2+(emittedBytes encode ws).length ≤ L+2+ids.length*(L+2) := by omega
        _ = (ids.length+1)*(L+2) := by ring

theorem fullSource_length_le {C : Type*} (encode : C → List Bool)
    (R : ℕ → Algorithm.Expr C → Prop) (L : ℕ)
    (hbound : ∀ i e, R i e →
      (SubexpPostfixControl.serializeCode encode e.compile).length ≤ L)
    (ids : List ℕ) (ws : List (Algorithm.Expr C)) (h : List.Forall₂ R ids ws)
    (z : C) (hz : encode z=[]) :
    (SubexpPostfixControl.serializeCode encode (foldSources (.lit z) ws).compile).length ≤
      2+ids.length*(L+2) := by
  rw [foldSources_zero_code encode z hz ws]
  have hb := emittedBytes_length_le (fun e : Algorithm.Expr C =>
    SubexpPostfixControl.serializeCode encode e.compile) R L hbound ids ws h
  simpa only [List.length_append,List.length_cons,List.length_nil] using Nat.add_le_add_left hb 2

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact extraction of the native executor context from the source worker.
The four dispatcher ports are excluded from this context. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore)
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The executor context discards its source and saved controls. Thus a new
postfix source on333 does not change any arithmetic readiness premise. -/
theorem executionContext_evaluation (s : Store) :
    executionContext (evaluationInput s)=executionContext (Function.update s 21 []) := by
  funext i
  let p := executorPorts (ports (Fin.natAdd 4 i))
  have hp : p.val < 256 := (ports (Fin.natAdd 4 i)).isLt
  have h26 : p≠26 := by
    intro h
    have he : ports (Fin.natAdd 4 i)=26 := by
      apply Fin.ext
      have hh := congrArg (fun k : Fin 340 => k.val) h
      change (ports (Fin.natAdd 4 i)).val=26 at hh
      exact hh
    have hi : Fin.natAdd 4 i=(0 : Fin 256) := by
      simpa using congrArg ports.symm he
    have hh := congrArg Fin.val hi
    simp at hh
  have h333 : p≠333 := by intro h; rw [h] at hp; norm_num at hp
  have h335 : p≠335 := by intro h; rw [h] at hp; norm_num at hp
  have h336 : p≠336 := by intro h; rw [h] at hp; norm_num at hp
  change evaluationInput s p=Function.update s 21 [] p
  simp [evaluationInput,Function.update_apply,h26,h333,h335,h336]

theorem executionContext_evaluation_update333 (s : Store) (bits : List Bool) :
    executionContext (evaluationInput (Function.update s 333 bits))=
      executionContext (evaluationInput s) := by
  rw [executionContext_evaluation,executionContext_evaluation]
  funext i
  have hp : (executorPorts (ports (Fin.natAdd 4 i))).val < 256 :=
    (ports (Fin.natAdd 4 i)).isLt
  have h333 : executorPorts (ports (Fin.natAdd 4 i))≠333 := by
    intro h
    rw [h] at hp
    norm_num at hp
  simp [executionContext,Function.update_apply,h333]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramTyped
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The paid owner-fiber scan emits the actual compiler bytes of one typed
sum expression. No precomputed polynomial values enter the executable. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem sourceForOwner_typed {C A : Type*} [AddMonoid A] [Mul A]
    (encode : C → List Bool) (decode : C → A) (value : ℕ → A)
    (z : C) (hz : encode z=[]) (hzero : decode z=0)
    (source : Code) (base : Store) (I K L : ℕ)
    (spec : RelSourceSpec source base
      (fun e : Algorithm.Expr C => SubexpPostfixControl.serializeCode encode e.compile)
      (TypedSourceRel encode decode value L) I K L)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : base 320=LayoutOwnerFiberProgram.unary query)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (hclean : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (h305 : base 305=[]) (h287 : base 287=[]) (h333 : base 333=[])
    (hI : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ I)
    (regs : Fin 16 → Bool) :
    ∃ e : Algorithm.Expr C, ∃ n rf,
      (e.map decode).eval=ownerSum ps query value ∧
      (SubexpPostfixControl.serializeCode encode e.compile).length ≤
        2+(LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(L+2) ∧
      n ≤ LayoutOwnerFiberProgram.budget query ps+
        (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(K+5*I+3*L+15)+6 ∧
      Eval (sourceForOwner source) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 333
          (SubexpPostfixControl.serializeCode encode e.compile).reverse⟩ : Data) := by
  obtain ⟨ws,n,rf,hr,hn,he⟩ := sourceForOwner_run source base _
    (TypedSourceRel encode decode value L) I K L spec query ps hq hs hclean
    h305 h287 h333 hI regs
  refine ⟨foldSources (.lit z) ws,n,rf,?_,?_,hn,?_⟩
  · rw [foldSources_map_eval]
    have hmean : List.Forall₂ (fun i e => (e.map decode).eval=value i)
        (LayoutOwnerFiberProgram.fiberIndices query 0 ps) ws := by
      exact List.Forall₂.imp (fun _ _ h => h.1) hr
    rw [related_sources_sum decode value _ ws hmean]
    simp [Algorithm.Expr.map,Algorithm.Expr.eval,hzero,ownerSum]
  · exact fullSource_length_le encode (TypedSourceRel encode decode value L) L
      (fun _ _ h => h.2) _ ws hr z hz
  · simpa only [foldSources_zero_code encode z hz ws] using he

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One source row: actual owner scan, native per-incidence source generation,
postfix summation, and native polynomial evaluation. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem sourceRowWith_run_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (source : Code) (base : Store) (I K L : ℕ)
    (value : ℕ → Polynomial (a.O t))
    (spec : RelSourceSpec source base
      (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)) =>
        SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
      (TypedSourceRel DensePolynomialProgram.encode
        (PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)) value L) I K L)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : base 320=LayoutOwnerFiberProgram.unary query)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (hclean : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (h305 : base 305=[]) (h287 : base 287=[]) (h333 : base 333=[])
    (hI : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ I)
    (h27 : base 27=[]) (h28 : base 28=[]) (h29 : base 29=[])
    (h335 : base 335=[]) (h336 : base 336=[])
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput base)))
    (regs : Fin 16 → Bool) :
    ∃ out : List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d), ∃ n rf,
      out.length=D ∧
      PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc D (ownerSum ps query value) ∧
      n ≤ sourceRowBudget query ps I K L D d (baseWidth 3 t) (base 21).length (base 26).length ∧
      Eval (sourceRowWith source) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 240 (DensePolynomialProgram.encode out)⟩ : Data) := by
  let decode := PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)
  obtain ⟨e,n1,r1,hevalue,helen,hn1,he1⟩ := sourceForOwner_typed
    DensePolynomialProgram.encode decode value [] rfl
    (by simp [decode,PolynomialExecutorProgram.meaning])
    source base I K L spec query ps hq hs hclean h305 h287 h333 hI regs
  let bits := SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile
  let s1 := Function.update base 333 bits.reverse
  have H1 : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput s1)) := by
    simpa only [s1,executionContext_evaluation_update333] using H
  obtain ⟨out,hlen,hmeaning,hr⟩ := evaluateModel_run t ht hd a M cache hz D width frame s1 H1 e
    (by simp [s1,bits]) (by simp [s1,h27]) (by simp [s1,h28]) (by simp [s1,h29])
    (by simp [s1,h335]) (by simp [s1,h336])
  obtain ⟨n2,r2,hn2,he2⟩ := hr r1
  have hfinish : Function.update (Function.update s1 333 []) 240
      (DensePolynomialProgram.encode out)=Function.update base 240 (DensePolynomialProgram.encode out) := by
    funext i
    by_cases hi : i=333 <;>
      simp [s1,Function.update_apply,hi,h333]
  rw [hfinish] at he2
  refine ⟨out,n1+n2,r2,hlen,?_,?_,he1.seq he2⟩
  · dsimp only [decode] at hevalue
    simpa only [hevalue] using hmeaning
  · have hlen1 : (s1 333).length ≤
        2+(LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(L+2) := by
      simpa [s1,bits] using helen
    have hpoly : 300000*((s1 333).length+1)*(D+1)^3*(d+1)^3*(baseWidth 3 t+1)^2 ≤
        300000*(2+(LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(L+2)+1)*
          (D+1)^3*(d+1)^3*(baseWidth 3 t+1)^2 := by
      gcongr
    have hc21 : s1 21=base 21 := by simp [s1]
    have hc26 : s1 26=base 26 := by simp [s1]
    rw [hc21,hc26] at hn2
    dsimp only [sourceRowBudget]
    omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith_run_oai
