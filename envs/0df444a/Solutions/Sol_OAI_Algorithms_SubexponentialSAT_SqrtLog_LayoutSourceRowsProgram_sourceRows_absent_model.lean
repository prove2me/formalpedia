-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:08:42.673429+00:00
-- url     : https://prove2.me/submissions/60846c6a-aa8a-402a-a2bc-eca5dc8880e2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_absent

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact zero bytes for the native padded-polynomial constructors. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem toNat_false (n : ℕ) :
    SubexponentialSAT.BinaryArithmetic.toNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

theorem zero_cache_bits (p t : ℕ) [Fact p.Prime] (cache : RingProgram.ScalarCache p t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t) :
    cache.zero.val = List.replicate (baseWidth p t) false := by
  apply SubexponentialSAT.SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp [cache.zero.property]
  · have hv := congrArg ZMod.val cache.zero_correct
    have hnum : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val = 0 := by
      simpa only [wordValue,ZMod.val_natCast,Nat.mod_eq_of_lt hz,ZMod.val_zero] using hv
    rw [hnum,toNat_false]

private theorem flatten_replicate_false (d B : ℕ) :
    (List.replicate d (List.replicate B false)).flatten = List.replicate (d*B) false := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.replicate_succ,List.flatten_cons,ih,← List.replicate_add]
      congr 1
      ring

theorem flat_constant_zero {B : ℕ} (z : Word B)
    (hz : z.val = List.replicate B false) (d : ℕ) :
    RingProgram.flat (fun _ : Fin d => z) = List.replicate (d*B) false := by
  simp only [RingProgram.flat,hz,List.ofFn_const]
  exact flatten_replicate_false d B

theorem model_zero_bits (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < 3^t) :
    RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1 =
      List.replicate (d*baseWidth 3 t) false := by
  change RingProgram.flat (fun _ : Fin d => cache.zero) = _
  exact flat_constant_zero cache.zero (zero_cache_bits 3 t cache hz) d

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed, width-generic initialization for the source-row executor. All
zero-array construction and copies are paid; only four output stacks change. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram

theorem encode_zero_array {B d : ℕ} (zero : Coeff B d)
    (hz : RingProgram.flat zero = List.replicate (d*B) false) (D : ℕ) :
    encode (List.replicate D zero) = List.replicate (D*(d*B)) false := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [List.replicate_succ, encode_cons, hz, ih, ← List.replicate_add]
      congr 1
      ring

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Coordinatewise meaning and serialization facts for the completed source
table. The row order is the original ambient order. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem encodeList_replicate {Wit : Type*} (encode : Wit → List Bool) (w : Wit) (N : ℕ) :
    Encoding.encodeList id (List.replicate N (encode w))=
      Encoding.encodeList encode (List.replicate N w) := by
  induction N with
  | zero => rfl
  | succ N ih => simp [List.replicate_succ,Encoding.encodeList,ih]

theorem RowProperty.replicate {Wit : Type*} (encode : Wit → List Bool)
    (R : ℕ → Wit → Prop) (W : ℕ) (w : Wit)
    (hR : ∀ j, R j w) (hW : (encode w).length=W) (j N : ℕ) :
    RowProperty encode R W j (List.replicate N w) := by
  induction N generalizing j with
  | zero => trivial
  | succ N ih => exact ⟨hR j,hW,ih (j+1)⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramAbsent
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem sourceRows_absent_model_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (source : Code) (s : Store) (D v N f : ℕ) (ps : List (ℕ × ℕ))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D (d*baseWidth 3 t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∉ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s D (d*baseWidth 3 t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s D (d*baseWidth 3 t) ps v N f))
    (regs : Fin 16 → Bool) :
    ∃ rows n rf,
      RowProperty DensePolynomialProgram.encode
        (fun _ out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=0)
        (D*(d*baseWidth 3 t)) 0 rows ∧ rows.length=N ∧
      n ≤ LayoutSourceRowsProgramInitialize.budget D (d*baseWidth 3 t)+
        LayoutSourcePlanLookup.pairBudget v N f ps+N*(26*(D*(d*baseWidth 3 t))+44)+
        2*(ps.idxOf (v,N+f))+23 ∧
      Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s D (d*baseWidth 3 t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data) := by
  let z := (RingProgram.modelProgram t a M cache).zeroRun.1
  let zs := List.replicate D z
  let rows := List.replicate N zs
  have hb : DensePolynomialProgram.encode zs=List.replicate (D*(d*baseWidth 3 t)) false :=
    LayoutSourceRowsProgramInitialize.encode_zero_array z
      (DensePolynomialProgram.model_zero_bits t a M cache hz) D
  have hzvalue : (RingProgram.modelRing t ht hd a M cache).decode z=0 :=
    (RingProgram.modelRing t ht hd a M cache).zero_correct
  have hm : PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) zs=0 := by
    dsimp only [zs]
    induction D with
    | zero => simp [PolynomialExecutorProgram.meaning]
    | succ D ih =>
        simp only [PolynomialExecutorProgram.meaning] at ih ⊢
        simp [List.replicate_succ,hzvalue]
  have hp : RowProperty DensePolynomialProgram.encode
      (fun _ out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=0)
      (D*(d*baseWidth 3 t)) 0 rows :=
    RowProperty.replicate _ _ _ zs (fun _ => hm) (by simp [hb]) 0 N
  obtain ⟨n,rf,hn,he⟩ := sourceRows_absent source s D (d*baseWidth 3 t) v N f ps
    hinit hv hN hf hplan hmem hlookup hclean regs
  refine ⟨rows,n,rf,hp,by simp [rows],hn,?_⟩
  have heq : Encoding.encodeList id (List.replicate N (List.replicate (D*(d*baseWidth 3 t)) false))=
      Encoding.encodeList DensePolynomialProgram.encode rows := by
    rw [←hb]
    exact encodeList_replicate _ zs N
  simpa only [heq] using he

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model_oai
