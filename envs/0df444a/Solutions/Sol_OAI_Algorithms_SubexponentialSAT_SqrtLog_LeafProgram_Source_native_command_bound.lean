-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:54:24.072503+00:00
-- url     : https://prove2.me/submissions/f634efff-f495-44e5-bb63-ef284089b0de

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_nativeRowsBudget_le_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Source_native_command_eval

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

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {Witness : Type*}

theorem records_length (encode : Witness → List Bool) (R : ℕ → Witness → Prop)
    (W j : ℕ) (ws : List Witness) (h : RowProperty encode R W j ws) :
    (records encode ws).length=ws.length*(2*W+2) := by
  induction ws generalizing j with
  | nil => simp [records]
  | cons w ws ih =>
      obtain ⟨_,hw,ht⟩ := h
      change (rowRecord (encode w)++records encode ws).length=(w::ws).length*(2*W+2)
      rw [List.length_append,ih (j+1) ht]
      simp only [rowRecord,List.length_cons,Encoding.length_frame,hw]
      ring

theorem records_encoding (encode : Witness → List Bool) (ws : List Witness) :
    records encode ws++[false]=Encoding.encodeList encode ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simpa [records,rowRecord,Encoding.encodeList,List.append_assoc] using
        (congrArg (fun b => rowRecord (encode w)++b) ih)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramOutputSize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

theorem RowProperty.serialized_length {Wit : Type*} (encode : Wit → List Bool)
    (R : ℕ → Wit → Prop) (W j : ℕ) (rows : List Wit)
    (h : RowProperty encode R W j rows) :
    (Encoding.encodeList encode rows).length=rows.length*(2*W+2)+1 := by
  rw [←records_encoding, List.length_append, records_length encode R W j rows h]
  rfl

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem embedState_wordBound {r s S : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin S) (frame : Data S) (out : State r s) (B : ℕ)
    (hs : Function.Injective stack) (hf : WordBound B frame) (ho : WordBound B out) :
    WordBound B (embedState register stack frame out) := by
  intro i
  by_cases hm : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hm
    rw [embedState_stack register stack frame out hs j]
    exact ho j
  · rw [embedState_stack_frame register stack frame out i hm]
    exact hf i

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem delta_stacks (a : Data) :
    (deltaState a).stacks = Function.update a.stacks 365 (true :: a.stacks 365) := by
  rfl

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source callback used by the actual incidence-table loop. The fixed
command stages source controls, protects all four target caches, invokes the
concrete source-row instruction table, restores the target caches, and clears
source-only controls. The local source correctness theorem is joined below
through its actual execution, never through a supplied polynomial oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
theorem workerPort_injective : Function.Injective workerPort := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 340+i.val=340+j.val at hv
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Every source-wrapper copy and cleanup is charged against actual word
lengths. The fixed finite allocation makes this overhead linear even without
assuming that intermediate destinations were empty. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem copy_bound {S : ℕ} (src dst : Fin S) (a : SubexpSetupStorage.Data S)
    (B : ℕ) (ha : WordBound B a) : WordBound (2*B) (copyState src dst a) := by
  intro i
  rw [copyState_stack]
  by_cases hi : i=dst
  · subst i
    simp only [Function.update_same,List.length_append]
    have hs:=ha src
    have hd:=ha dst
    omega
  · rw [Function.update_of_ne hi]
    exact (ha i).trans (by omega)

private theorem copyMany_bound {S : ℕ} (ps : List (Fin S × Fin S))
    (a : SubexpSetupStorage.Data S) (B : ℕ) (ha : WordBound B a) :
    WordBound (2^ps.length*B) (copyManyState ps a) := by
  induction ps generalizing a B with
  | nil => simpa [copyManyState] using ha
  | cons p ps ih =>
    have h := ih (copyState p.1 p.2 a) (2*B) (copy_bound _ _ _ _ ha)
    simpa only [copyManyState,List.length_cons,pow_succ,Nat.mul_assoc] using h

private theorem copyMany_cost_bound {S : ℕ} (ps : List (Fin S × Fin S))
    (a : SubexpSetupStorage.Data S) (B : ℕ) (ha : WordBound B a) :
    copyManyCost ps a ≤ ps.length*(7*(2^ps.length*B)+5) := by
  induction ps generalizing a B with
  | nil => simp [copyManyCost]
  | cons p ps ih =>
    have h := ih (copyState p.1 p.2 a) (2*B) (copy_bound _ _ _ _ ha)
    have hp := ha p.1
    have hpow : 1 ≤ 2^ps.length := Nat.one_le_pow _ _ (by decide)
    have hb : B ≤ 2^(ps.length+1)*B := by
      calc
        B = 1*B := by omega
        _ ≤ 2^(ps.length+1)*B := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ (by decide))
    calc
      copyManyCost (p::ps) a = (7*(a.stacks p.1).length+5)+
          copyManyCost ps (copyState p.1 p.2 a) := rfl
      _ ≤ (7*(2^ps.length*(2*B))+5)+ps.length*(7*(2^ps.length*(2*B))+5) := by
        apply Nat.add_le_add _ h
        simp only [pow_succ,Nat.mul_assoc] at hb
        omega
      _ = (p::ps).length*(7*(2^(p::ps).length*B)+5) := by
        simp only [List.length_cons,pow_succ]
        ring

/-- Coarse bound for a copy list of statically known size, including any
appending to its destinations. -/
theorem saved_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound (16*B) (SourceStaging.saved a) := by
  apply clearMany_wordBound
  simpa [SourceStaging.savePairs] using copyMany_bound SourceStaging.savePairs a B ha

theorem prepared_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound (67108864*B+1) (prepared a) := by
  have h := copyMany_bound SourceControls.pairs (SourceStaging.saved a) (16*B)
    (saved_bound a B ha)
  have h' : WordBound (67108864*B)
      (copyManyState SourceControls.pairs (SourceStaging.saved a)) := by
    have he : 2^SourceControls.pairs.length*(16*B)=67108864*B := by
      norm_num [SourceControls.pairs]
      ring
    rw [he] at h
    exact h
  intro i
  change ((SourceControls.deltaState _).stacks i).length ≤ _
  rw [SourceControls.delta_stacks]
  by_cases hi : i=365
  · subst i
    simpa only [Function.update_same,List.length_cons] using Nat.add_le_add_right (h' 365) 1
  · rw [Function.update_of_ne hi]
    exact (h' i).trans (by omega)

private theorem before_cost_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    SourceStaging.beforeCost a ≤ 576*B+32 := by
  have h0 := copyMany_cost_bound SourceStaging.savePairs a B ha
  have h1 := clearManyCost_le SourceStaging.cachePorts _ (16*B)
    (by simpa [SourceStaging.savePairs] using copyMany_bound SourceStaging.savePairs a B ha)
  norm_num [SourceStaging.savePairs,SourceStaging.cachePorts] at h0 h1
  dsimp only [SourceStaging.beforeCost,SourceStaging.savePairs,SourceStaging.cachePorts]
  omega

private theorem prepare_cost_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    SourceControls.prepareCost (SourceStaging.saved a) ≤ 10334765056*B+112 := by
  have h := copyMany_cost_bound SourceControls.pairs (SourceStaging.saved a) (16*B)
    (saved_bound a B ha)
  norm_num [SourceControls.pairs] at h
  dsimp only [SourceControls.prepareCost,SourceControls.pairs]
  omega

private theorem after_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound (16*B) (SourceStaging.finished a) := by
  apply clearMany_wordBound
  apply clearMany_wordBound
  simpa [SourceStaging.restorePairs] using copyMany_bound SourceStaging.restorePairs
    (clearManyState SourceStaging.cachePorts a) B
    (clearMany_wordBound _ _ B ha)

private theorem after_cost_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    SourceStaging.afterCost a ≤ 7144*B+659 := by
  have h0 := clearManyCost_le SourceStaging.cachePorts a B ha
  have hc := clearMany_wordBound SourceStaging.cachePorts a B ha
  have h1 := copyMany_cost_bound SourceStaging.restorePairs _ B hc
  have hh : WordBound (16*B) (copyManyState SourceStaging.restorePairs
      (clearManyState SourceStaging.cachePorts a)) := by
    simpa [SourceStaging.restorePairs] using copyMany_bound SourceStaging.restorePairs _ B hc
  have h2 := clearManyCost_le SourceStaging.backupPorts _ (16*B) hh
  have h3 := clearManyCost_le SourceStaging.lowClearPorts _ (16*B)
    (clearMany_wordBound SourceStaging.backupPorts _ (16*B) hh)
  have hl : SourceStaging.lowClearPorts.length ≤ 205 := by
    unfold SourceStaging.lowClearPorts
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange)
  have h3' : clearManyCost SourceStaging.lowClearPorts (SourceStaging.restored a) ≤
      205*(2*(16*B)+3) := h3.trans (Nat.mul_le_mul_right _ hl)
  norm_num [SourceStaging.cachePorts,SourceStaging.restorePairs,SourceStaging.backupPorts] at h0 h1 h2
  dsimp only [SourceStaging.afterCost,SourceStaging.cachePorts,SourceStaging.restorePairs,SourceStaging.backupPorts]
  omega

/-- Full wrapper overhead, including source-private and arithmetic cleanup.
The core invocation is accounted for separately by its actual step count. -/
theorem cost_bound (a : Data) (b : State 16 340) (n A B : ℕ)
    (ha : WordBound A a) (hb : WordBound B b) :
    cost a b n ≤ n+1000000000000*(A+B+1) := by
  let C := 67108864*A+1+B
  have hp := prepared_bound a A ha
  have he : WordBound C (coreOutput a b) := by
    apply embedState_wordBound id workerPort (prepared a) b C workerPort_injective
    · intro i
      exact (hp i).trans (by dsimp [C]; omega)
    · intro i
      exact (hb i).trans (by dsimp [C]; omega)
  have h0 := before_cost_bound a A ha
  have h1 := prepare_cost_bound a A ha
  have h2 := after_cost_bound (coreOutput a b) C he
  have h3 := clearManyCost_le SourceControls.extraPorts _ (16*C)
    (after_bound (coreOutput a b) C he)
  have hl : SourceControls.extraPorts.length=88 := by simp [SourceControls.extraPorts]
  rw [hl] at h3
  unfold cost
  dsimp [C] at h2 h3
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceNativeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform cost for the actual source invocation, including its global
staging, four-cache save/restore, and cleanup. The size assumption includes the
live incidence-table accumulator rather than quantifying over unbounded data. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpSetupStorage
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

private theorem encode_fixed_map {B d D : ℕ}
    (rows : List (DensePolynomialProgram.Fixed.Array B d D)) :
    Encoding.encodeList DensePolynomialProgram.Fixed.encode rows =
      Encoding.encodeList DensePolynomialProgram.encode (rows.map Subtype.val) := by
  induction rows with
  | nil => rfl
  | cons w ws ih => simp [Encoding.encodeList,DensePolynomialProgram.Fixed.encode,ih]

private theorem result_bound {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a : Source.Data) (N S : ℕ) (ha : WordBound S a)
    (raw : List (List (DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)))
    (regs : Fin 16 → Bool)
    (hlen : (Encoding.encodeList DensePolynomialProgram.encode raw).length =
      N*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1) :
    WordBound (nativeOutputBound p N S) (nativeResult p (nativeStore a) raw regs) := by
  have hp := prepared_bound a S ha
  intro i
  have hi := hp (workerPort i)
  by_cases h205 : i=205
  · subst i
    simpa only [nativeResult,Function.update_same,hlen] using
      (show N*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1 ≤ nativeOutputBound p N S by
        unfold nativeOutputBound; omega)
  by_cases h193 : i=193
  · subst i
    simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
      Function.update_same,List.length_replicate]
    unfold nativeOutputBound
    omega
  by_cases h192 : i=192
  · subst i
    simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
      Function.update_of_ne (by decide : (192 : Fin 340) ≠ 193),
      Function.update_same,List.length_replicate]
    unfold nativeOutputBound
    omega
  by_cases h242 : i=242
  · subst i
    simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
      Function.update_of_ne (by decide : (242 : Fin 340) ≠ 193),
      Function.update_of_ne (by decide : (242 : Fin 340) ≠ 192),
      Function.update_same,List.length_replicate]
    unfold nativeOutputBound
    omega
  by_cases h243 : i=243
  · subst i
    simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
      Function.update_of_ne (by decide : (243 : Fin 340) ≠ 193),
      Function.update_of_ne (by decide : (243 : Fin 340) ≠ 192),
      Function.update_of_ne (by decide : (243 : Fin 340) ≠ 242),
      Function.update_same,List.length_replicate]
    unfold nativeOutputBound
    omega
  simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
    Function.update_of_ne h193,Function.update_of_ne h192,
    Function.update_of_ne h242,Function.update_of_ne h243]
  exact hi.trans (by unfold nativeOutputBound; omega)

/-- The returned arrays and the time bound belong to the same executed call.
Every size premise refers to an actual input word or finite runtime index. -/
theorem native_command_bound_oai {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : Source.Data) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (h : NativeInput p ps P a v N f S width frame)
    (ha : WordBound S a) (hv : v ≤ S) (hN : N ≤ S) (hf : f ≤ S)
    (hps : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h21 : (nativeStore a 21).length ≤ S) (h26 : (nativeStore a 26).length ≤ S) :
    ∃ (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
      (k : ℕ) (rr : Fin 16 → Bool),
      rows.length=N ∧
      RowProperty DensePolynomialProgram.Fixed.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out.val =
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧
      k ≤ nativeSourceWorkPolynomial p S ∧
      Eval Source.command k a
        (⟨rr,Function.update a.stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : Source.Data) := by
  obtain ⟨rows,raw,n,rf,rr,hmap,hlen,hrows,hn,he⟩ :=
    native_command_eval p ps P a v N f S width frame h
  have hbytes := encode_fixed_map rows
  rw [hmap] at hbytes
  have hrawlen : (Encoding.encodeList DensePolynomialProgram.encode raw).length =
      N*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1 := by
    rw [←hbytes,RowProperty.serialized_length _ _ _ _ _ hrows,hlen]
  have hb := result_bound p a N S ha raw rf hrawlen
  have hc := cost_bound a (nativeResult p (nativeStore a) raw rf) n S
    (nativeOutputBound p N S) ha hb
  have hn' := nativeRowsBudget_le_polynomial p (nativeStore a) v N f S ps
    hv hN hf h.incidenceBound hps h21 h26
  have hmono : nativeOutputBound p N S ≤ nativeOutputBound p S S := by
    unfold nativeOutputBound
    gcongr
  refine ⟨rows,_,rr,hlen,hrows,?_,he⟩
  have hnpoly : n ≤ nativeRowsPolynomial p S := hn.trans hn'
  have hoverhead : 1000000000000*(S+nativeOutputBound p N S+1) ≤
      1000000000000*(S+nativeOutputBound p S S+1) := by
    exact Nat.mul_le_mul_left _ (by omega)
  exact hc.trans (Nat.add_le_add hnpoly hoverhead)

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.native_command_bound_oai
