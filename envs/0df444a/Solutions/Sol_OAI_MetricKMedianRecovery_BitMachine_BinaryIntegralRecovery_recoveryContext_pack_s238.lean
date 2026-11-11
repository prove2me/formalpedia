-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:15.853208+00:00
-- url     : https://prove2.me/submissions/897698c3-5769-4b42-bf64-ed179535a1b2

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K031
import Definitions.Def_Q238K034
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NumAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryRational

lemma natWords_bits (n : ℕ) : natWords n.bits=encode (n:ℚ) := by
  simp only [natWords,value_bits,castIntWords_encode,Int.cast_natCast]
end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma member_length {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>exact False.elim (List.not_mem_nil hw)
  | cons v vs ih=>
    rw [encode,length_cons]
    rcases List.mem_cons.mp hw with rfl|hw
    · omega
    · have h:=ih hw
      omega
end MetricKMedianRecovery.BitMachine.WordList

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawDrop
open WordOperations BinaryArithmetic

lemma step_zero (ws : List Bool) : step (pairBits (Nat.bits 0,ws))=pairBits (Nat.bits 0,ws) := by
  simp only [step,extractPrefix_pairBits,value_bits,ite_true, if_true]
lemma step_succ (i : ℕ) (ws : List Bool) :
    step (pairBits ((i+1).bits,ws))=pairBits (i.bits,ws.tail) := by
  simp only [step,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,Nat.add_sub_cancel,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false, if_false]
lemma drop_iterate (n i : ℕ) (ws : List Bool) (hn : ws.length≤n) :
    discardPrefix (step^[n] (pairBits (i.bits,ws)))=ws.drop i := by
  induction n generalizing i ws with
  | zero=>
    have hw : ws=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ws
    simp only [Function.iterate_zero_apply,discardPrefix_pairBits,List.drop_nil]
  | succ n ih=>
    cases i with
    | zero=>rw [Function.iterate_fixed (step_zero ws),discardPrefix_pairBits,List.drop_zero]
    | succ i=>
      rw [Function.iterate_succ_apply,step_succ]
      have hl : ws.tail.length≤n := by simp only [List.length_tail]; omega
      rw [ih i ws.tail hl]
      cases ws with
      | nil=>simp only [List.tail_nil,List.drop_nil]
      | cons w ws=>rfl
lemma run_encode (i : ℕ) (ws : List Bool) :
    run (pairBits (i.bits,ws))=ws.drop i := by
  apply drop_iterate
  rw [pairBits_length]
  dsimp only
  omega
end MetricKMedianRecovery.BitMachine.RawDrop
namespace MetricKMedianRecovery.BitMachine.RawTake
open WordOperations BinaryArithmetic
attribute [local irreducible] number RawDrop.run
lemma run_pack (n : ℕ) (ws : List Bool) : run (pairBits (n.bits,ws))=ws.take n := by
  simp only [run,number,extractPrefix_pairBits,discardPrefix_pairBits,UnaryResources.lengthBits_eq,value_bits,
    RawDrop.run_encode,List.reverse_drop,List.reverse_reverse,List.length_reverse]
  rw [show ws.length-(ws.length-n)=min n ws.length by omega]
  exact List.take_eq_take_min.symm
end MetricKMedianRecovery.BitMachine.RawTake

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma values_sort (S : Finset (Fin n)) : (values S).sort (·≤·)=(S.sort (·≤·)).map Fin.val := by
  let f : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hh := Finset.map_sort f S (·≤·) (·≤·) (fun a _ b _=>show a≤b↔a.val≤b.val from Iff.rfl)
  simpa only [f,Finset.map_eq_image,values,Function.Embedding.coeFn_mk] using hh.symm
lemma encode_eq (S : Finset (Fin n)) : encode S=WordList.encode ((S.sort (·≤·)).map (fun i=>i.val.bits)) := by
  rw [encode,BinaryNatSet.encode,BinaryNatSet.pack,values_sort,List.map_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_BoundedNatWord
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BoundedNatWord
open WordOperations
attribute [local irreducible] RawTake.run RawUnary.run counter
lemma run_pack (P : Polynomial ℕ) (n : ℕ) (w : List Bool) :
    run P (pairBits (n.bits,w))=List.replicate (min n (P.eval w.length)) true := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,RawTake.run_pack,RawUnary.run,
    List.length_take,(counter P).word_length]
lemma run_exact (P : Polynomial ℕ) (n : ℕ) (w : List Bool) (hn : n≤P.eval w.length) :
    run P (pairBits (n.bits,w))=List.replicate n true := by
  rw [run_pack,min_eq_left hn]
end MetricKMedianRecovery.BitMachine.BoundedNatWord

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PolynomialProduct
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.GlobalAssembly

open LocalSearch Sampling FiniteSampling IntegralAssembly IndexedCopies

lemma cap_polynomial (n N : ℕ) (h : n ≤ N) :
    Rounding.cap n (gamma/16) ≤ (⌈20/(gamma/16)⌉₊+2)*(N+2)^2 := by
  have he : 0 < gamma/16 := div_pos gamma_pos_s238 (by norm_num)
  have hn : (n:ℝ)^2 ≤ ((N:ℝ)+2)^2 := by
    have h' : (n:ℝ) ≤ N := by exact_mod_cast h
    nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) N]
  have hc : ⌈20*(n:ℝ)^2/(gamma/16)⌉₊ ≤ ⌈20/(gamma/16)⌉₊*(N+2)^2 := by
    apply Nat.ceil_le.mpr
    push_cast
    calc
      _ = (20/(gamma/16))*(n:ℝ)^2 := by ring
      _ ≤ (20/(gamma/16))*((N:ℝ)+2)^2 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (sq_nonneg _)
  have hb : 1 ≤ (N+2)^2 := one_le_pow₀ (by omega)
  unfold Rounding.cap
  nlinarith

end MetricKMedianRecovery.GlobalAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Parameters
open WordOperations WordList BinaryArithmetic Polynomial RadiusMenus Sampling Sampling.Comparison
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BoundedNatWord.run bound
variable {n : ℕ}
lemma pack_resources (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    m≤bound.eval (pack δ D F S Δ P m).length ∧ Δ≤bound.eval (pack δ D F S Δ P m).length := by
  let L := (pack δ D F S Δ P m).length
  have hn : n≤L := by
    have hh:=member_length (show List.replicate n true∈[RationalMatrix.encode δ,List.replicate n true,
      BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,Δ.bits,BinaryRational.encode P,m.bits] by simp)
    simpa only [L,pack,List.length_replicate] using hh
  have hd : D.card≤L := (Finset.card_le_univ D).trans (by simpa only [Finset.card_univ,Fintype.card_fin] using hn)
  have hc:=GlobalAssembly.cap_polynomial D.card L hd
  simp only [bound,eval_add,eval_X,eval_mul,eval_C,eval_pow,eval_ofNat]
  exact ⟨(hm.trans hn).trans (Nat.le_add_right _ _),(hΔ.trans hc).trans (Nat.le_add_left _ _)⟩
lemma unary_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    unary 7 (pack δ D F S Δ P m)=List.replicate m true ∧
    unary 5 (pack δ D F S Δ P m)=List.replicate Δ true := by
  obtain ⟨hm',hd'⟩:=pack_resources δ D F S Δ P m hm hΔ
  constructor
  · simpa only [unary,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      using BoundedNatWord.run_exact bound m (pack δ D F S Δ P m) hm'
  · simpa only [unary,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      using BoundedNatWord.run_exact bound Δ (pack δ D F S Δ P m) hd'
end MetricKMedianRecovery.BitMachine.BinarySampler.Parameters

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] params cfg mword precision sampleRaw completeRaw extra src
  BinarySampler.Parameters.run BinarySampler.Parameters.precision BinarySampler.Parameters.unary
variable {n b : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
  (g : List Bool) (seed : Fin (2*m)→Fin b→Bool) (complete : List Bool)
lemma params_pack : params (pack δ D F S Δ P m g seed complete)=BinarySampler.Parameters.pack δ D F S Δ P m := by
  simp only [params,pack,extractPrefix_pairBits]
lemma data_pack : extra (pack δ D F S Δ P m g seed complete)=g ∧
    sampleRaw (pack δ D F S Δ P m g seed complete)=BinarySeed.raw (ds:=[2*m]) seed ∧
    completeRaw (pack δ D F S Δ P m g seed complete)=complete := by
  simp only [extra,sampleRaw,completeRaw,pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,and_self]
lemma src_pack (j : ℕ) : src j (pack δ D F S Δ P m g seed complete)=
    field j (BinarySampler.Parameters.pack δ D F S Δ P m) := by
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits]
lemma mword_pack (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    mword (pack δ D F S Δ P m g seed complete)=List.replicate m true := by
  rw [mword,Function.comp_apply,params_pack]
  exact (BinarySampler.Parameters.unary_pack δ D F S Δ P m hm hΔ).1
lemma recoveryContext_pack_s238_oai (hm : m≤n) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    recoveryContext (pack δ D F S Δ P m g seed complete)=
      BinaryRecovery.pack δ D F S Δ RationalSampling.State.initial m g complete := by
  rw [recoveryContext,mword_pack δ D F S Δ P m g seed complete hm hΔ,
    (data_pack δ D F S Δ P m g seed complete).1,(data_pack δ D F S Δ P m g seed complete).2.2]
  simp only [src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryRational.natWords_bits,BinaryRecovery.pack]
  congr 1
  simp only [BinarySamplingState.encode,RationalSampling.State.initial,BinaryFinSet.encode_eq,
    Finset.sort_empty,List.map_nil,BinaryNearestLeaf.leavesBits,WordList.encode]
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.recoveryContext_pack_s238_oai
