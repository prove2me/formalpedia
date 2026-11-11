-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:17:24.268194+00:00
-- url     : https://prove2.me/submissions/d10caef0-9426-47a6-a20f-655ea0e1c15f

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K053
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInputParser_Stream_run_code_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalization_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalizeInput_P_clients_bits_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalizeInput_facilities_bits_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalizeInput_prep_bits_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

lemma decode_encode (x : ℚ) : decode (encode x)=x := by
  simp only [decode,numerator,denominator,encode,pairBits,extractPrefix_pair,discardPrefix_pair,
    Signed.encode_decode,value_bits,Rat.mkRat_self]

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

namespace WordList

lemma cons_ne_nil (w ws : List Bool) : cons w ws≠[] := List.cons_ne_nil _ _

namespace ReverseMap

lemma next_nil (f : List Bool → List Bool) (d o : List Bool) :
    next f (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (f : List Bool → List Bool) (w ws d o : List Bool) :
    next f (pack true (cons w ws) d o)=pack true ws d (cons (f (pairBits (d,w))) o) := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,cons_ne_nil,ite_false, if_false,
    data_pack,output_pack,tail_cons,head_cons]
lemma loop_exact (f : List Bool → List Bool) (ws : List (List Bool)) (d : List Bool) (os : List (List Bool)) :
    (next f)^[ws.length+1] (pack true (encode ws) d (encode os))=
      pack false [] d (encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse++os)) := by
  induction ws generalizing os with
  | nil => simp only [encode,List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,
      List.map_nil,List.reverse_nil,List.nil_append]
  | cons w ws ih =>
    rw [List.length_cons,Function.iterate_succ_apply,encode,next_cons]
    change (next f)^[ws.length+1] (pack true (encode ws) d (encode (f (pairBits (d,w))::os)))=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
lemma loop_spec (f : List Bool → List Bool) (ws : List (List Bool)) (d : List Bool) :
    (next f)^[(encode ws).length+1] (pack true (encode ws) d [])=
      pack false [] d (encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse)) := by
  have hl := length_le_encode ws
  have hlen : (encode ws).length+1=((encode ws).length-ws.length)+(ws.length+1) := by omega
  rw [hlen,Function.iterate_add_apply]
  change (next f)^[_] ((next f)^[ws.length+1] (pack true (encode ws) d (encode [])))=_
  rw [loop_exact,List.append_nil]
  apply While.next_fixed
  exact (by decide : (some false:Option Bool)≠some true)

lemma run_encode (f : List Bool → List Bool) (d : List Bool) (ws : List (List Bool)) :
    run f (pairBits (d,encode ws))=encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse) := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,rank,head_pack,ite_true, if_true,counter_pack,
    loop_spec,output_pack]
end ReverseMap

lemma reverse_encode (ws : List (List Bool)) : reverse (encode ws)=encode ws.reverse := by
  simp only [reverse,ReverseMap.run_encode,discardPrefix_pairBits,List.map_id']
lemma mapWith_encode (f : List Bool → List Bool) (d : List Bool) (ws : List (List Bool)) :
    mapWith f (pairBits (d,encode ws))=encode (ws.map (fun w=>f (pairBits (d,w)))) := by
  simp only [mapWith,Function.comp_apply,ReverseMap.run_encode,reverse_encode,List.reverse_reverse]

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
lemma length_encode_append (xs ys : List (List Bool)) :
    (encode (xs++ys)).length=(encode xs).length+(encode ys).length := by
  induction xs with
  | nil => simp only [List.nil_append,encode,List.length_nil,Nat.zero_add]
  | cons x xs ih => simp only [List.cons_append,encode,length_cons,ih]; omega
lemma length_encode_drop (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.drop n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
namespace Fold

lemma length_pack (ws ctx a : List Bool) : (pack ws ctx a).length=2*ws.length+2*ctx.length+a.length+2 := by
  simp only [pack,pairBits_length]; omega
lemma step_nil (f : List Bool → List Bool) (ctx a : List Bool) :
    step f (pack (encode []) ctx a)=pack (encode []) ctx a := by
  simp only [step,items_pack,encode,ite_true, if_true]
lemma step_cons (f : List Bool → List Bool) (ctx a w : List Bool) (ws : List (List Bool)) :
    step f (pack (encode (w::ws)) ctx a)=pack (encode ws) ctx (operation f ctx a w) := by
  simp only [step,items_pack,encode,cons_ne_nil,ite_false, if_false,context_pack,head_cons,tail_cons,accum_pack,operation]
lemma iterate_pack (f : List Bool → List Bool) (ctx a : List Bool) (ws : List (List Bool)) (n : ℕ) :
    (step f)^[n] (pack (encode ws) ctx a)=
      pack (encode (ws.drop n)) ctx ((ws.take n).foldl (operation f ctx) a) := by
  induction n generalizing ws a with
  | zero => simp only [Function.iterate_zero_apply,List.drop_zero,List.take_zero,List.foldl_nil]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases ws with
    | nil =>
      rw [step_nil,Function.iterate_fixed (step_nil f ctx a)]
      rfl
    | cons w ws =>
      rw [step_cons,ih]
      simp only [List.drop_succ_cons,List.take_succ_cons,List.foldl_cons]

lemma run_encode (f : List Bool → List Bool) (R : Polynomial ℕ) (ctx a : List Bool)
    (ws : List (List Bool)) (B : ℕ)
    (hB : ∀ n,((ws.take n).foldl (operation f ctx) a).length ≤ B)
    (hR : 2*(encode ws).length+2*ctx.length+B+2 ≤ R.eval (pack (encode ws) ctx a).length) :
    run f R (pack (encode ws) ctx a)=ws.foldl (operation f ctx) a := by
  have he := BoundedIteration.polynomialRun_eq (step f) Polynomial.X R (pack (encode ws) ctx a) (by
    intro j _
    rw [iterate_pack,length_pack]
    have hd := length_encode_drop ws j
    have hb := hB j
    omega)
  simp only [run,Function.comp_apply,he,Polynomial.eval_X,iterate_pack,accum_pack]
  rw [List.take_of_length_le]
  have hw := length_le_encode ws
  rw [length_pack]
  omega
end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords 
open WordOperations BinaryArithmetic
namespace WordList
lemma length_member_le_encode {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) :
    w.length≤(encode ws).length := by
  induction ws with
  | nil => simp only [List.not_mem_nil] at hw
  | cons v vs ih =>
    simp only [List.mem_cons] at hw
    rw [encode,length_cons]
    rcases hw with rfl|hv
    · omega
    · have hh := ih hv
      omega
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
namespace Count
lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=true::a := by
  simp only [Fold.operation,op,Function.comp_apply,Fold.accum,discardPrefix_pairBits]
lemma fold_op (ws : List (List Bool)) (a : List Bool) (ctx : List Bool) :
    ws.foldl (Fold.operation op ctx) a=List.replicate ws.length true++a := by
  induction ws generalizing a with
  | nil => simp only [List.foldl_nil,List.length_nil,List.replicate_zero,List.nil_append]
  | cons w ws ih =>
    simp only [List.foldl_cons,operation_eq,ih,List.length_cons]
    rw [←List.singleton_append,←List.append_assoc,←List.replicate_succ',List.replicate_succ]
lemma run_encode (ws : List (List Bool)) : run (encode ws)=List.replicate ws.length true := by
  unfold run
  rw [Fold.run_encode op (4*Polynomial.X+4) [] [] ws (encode ws).length]
  · simp only [fold_op,List.append_nil]
  · intro n
    simp only [fold_op,List.append_nil,List.length_replicate]
    have ht : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    exact ht.trans (length_le_encode ws)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
end Count
end WordList
end MetricKMedianRecovery.BitMachine

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UnaryParser
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.UnaryParser
open WordOperations UnaryTake

lemma next_stop (c d : List Bool) : next (pack false c d [])=pack false c d [] := by
  simp only [next,While.next,head_pack,Option.some.injEq,Bool.false_eq_true,ite_false, if_false]
lemma next_false (c d : List Bool) : next (pack true c (false::d) [])=pack false c d [] := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,data_pack,counter_pack,List.head?_cons,
    Option.getD_some,Bool.false_eq_true,ite_false, if_false,List.tail_cons]
lemma next_true (c d : List Bool) : next (pack true c (true::d) [])=pack true (true::c) d [] := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,data_pack,counter_pack,List.head?_cons,
    Option.getD_some,List.tail_cons]
lemma exact_prefix (n : ℕ) (c d : List Bool) :
    next^[n+1] (pack true c (List.replicate n true++false::d) [])=
      pack false (List.replicate n true++c) d [] := by
  induction n generalizing c with
  | zero=>simp only [Nat.zero_add,List.replicate_zero,List.nil_append,Function.iterate_one,next_false]
  | succ n ih=>
    rw [List.replicate_succ,List.cons_append,Function.iterate_succ_apply,next_true,ih]
    rw [show List.replicate n true++true::c=(List.replicate (n+1) true)++c by
      rw [List.replicate_succ',List.append_assoc,List.singleton_append]]
    simp only [List.replicate_succ,List.cons_append]
lemma run_code (n : ℕ) (d : List Bool) :
    run (List.replicate n true++false::d)=pairBits (List.replicate n true,d) := by
  dsimp only [run,loop]
  have hl : n+1≤(pack true [] (List.replicate n true++false::d) []).length := by
    simp only [length_pack,List.length_nil,List.length_append,List.length_replicate,List.length_cons]; omega
  rw [show (pack true [] (List.replicate n true++false::d) []).length=
    (pack true [] (List.replicate n true++false::d) []).length-(n+1)+(n+1) by omega]
  rw [Function.iterate_add_apply,exact_prefix,List.append_nil,Function.iterate_fixed (next_stop _ _),
    counter_pack,data_pack]
end MetricKMedianRecovery.BitMachine.UnaryParser

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser
open WordOperations
attribute [local irreducible] UnaryParser.run UnaryTake.takeWords UnaryTake.dropWords
lemma nat_code (n : ℕ) (tail : List Bool) :
    nat (RationalMetricInput.natBits n++tail)=pairBits (n.bits,tail) := by
  simp only [RationalMetricInput.natBits,List.append_assoc,List.cons_append,List.nil_append,nat,
    UnaryParser.run_code,UnaryTake.takeWords,UnaryTake.dropWords,extractPrefix_pairBits,
    discardPrefix_pairBits,List.length_replicate,List.take_left,List.drop_left]
attribute [local irreducible] nat
attribute [local irreducible] numerator denominator
end MetricKMedianRecovery.BitMachine.BinaryInputParser

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricParser
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric
open WordOperations WordList
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run Rows.run RawUnary.run
attribute [local irreducible] header count tailHeader budget masks clients afterClients facilities rawMatrix
attribute [local irreducible] matrix
lemma bits_eq (I : RationalMetricInput) : I.bits=RationalMetricInput.natBits I.pointCount++RationalMetricInput.natBits I.budget++
    mask I.clients++mask I.facilities++Stream.raw (flat I) := by
  unfold RationalMetricInput.bits mask Stream.raw flat
  congr 1
  rw [List.map_flatten,List.flatten_flatten]
  simp only [List.map_ofFn,Function.comp_def]
lemma header_bits (I : RationalMetricInput) : header I.bits=pairBits (I.pointCount.bits,
    RationalMetricInput.natBits I.budget++mask I.clients++mask I.facilities++Stream.raw (flat I)) := by
  rw [header,bits_eq]
  simp only [List.append_assoc,nat_code]
lemma count_bits (I : RationalMetricInput) : count I.bits=I.pointCount.bits := by rw [count,header_bits,extractPrefix_pairBits]
lemma tailHeader_bits (I : RationalMetricInput) : tailHeader I.bits=pairBits (I.budget.bits,
    mask I.clients++mask I.facilities++Stream.raw (flat I)) := by
  rw [tailHeader,header_bits,discardPrefix_pairBits]
  simp only [List.append_assoc,nat_code]
lemma budget_bits (I : RationalMetricInput) : budget I.bits=I.budget.bits := by rw [budget,tailHeader_bits,extractPrefix_pairBits]
lemma masks_bits (I : RationalMetricInput) : masks I.bits=mask I.clients++mask I.facilities++Stream.raw (flat I) := by
  rw [masks,tailHeader_bits,discardPrefix_pairBits]
lemma mask_length {n : ℕ} (S : Finset (Fin n)) : (mask S).length=n := List.length_ofFn
lemma clients_bits (I : RationalMetricInput) : clients I.bits=mask I.clients := by
  rw [clients,count_bits,masks_bits,RawTake.run_pack,List.append_assoc]
  simpa only [mask_length] using (show (mask I.clients++(mask I.facilities++Stream.raw (flat I))).take (mask I.clients).length=mask I.clients from List.take_left)
lemma afterClients_bits (I : RationalMetricInput) : afterClients I.bits=mask I.facilities++Stream.raw (flat I) := by
  rw [afterClients,count_bits,masks_bits,RawDrop.run_encode,List.append_assoc]
  simpa only [mask_length] using (show (mask I.clients++(mask I.facilities++Stream.raw (flat I))).drop (mask I.clients).length=mask I.facilities++Stream.raw (flat I) from List.drop_left)
lemma rawMatrix_bits (I : RationalMetricInput) : rawMatrix I.bits=Stream.raw (flat I) := by
  rw [rawMatrix,count_bits,afterClients_bits,RawDrop.run_encode]
  simpa only [mask_length] using (show (mask I.facilities++Stream.raw (flat I)).drop (mask I.facilities).length=Stream.raw (flat I) from List.drop_left)
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
lemma left_encode (S : Finset (Fin n)) : BinaryFinSet.encode (S.image left)=BinaryFinSet.encode S := by
  simp only [BinaryFinSet.encode,BinaryFinSet.values,Finset.image_image]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalConstants
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
lemma countRat_cast : (countRat:ℝ)=Anchoring.countConstant (1/100) := by
  simp only [countRat,Anchoring.countConstant,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one]
lemma gapRat_cast : (gapRat:ℝ)=strictnessGap (200*Anchoring.countConstant (1/100)) := by
  simp only [gapRat,strictnessGap,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_one,countRat_cast]
lemma gammaRat_cast : (gammaRat:ℝ)=gamma := by
  simp only [gammaRat,gamma,Rat.cast_min,Rat.cast_div,Rat.cast_ofNat,gapRat_cast]
lemma cap_rat (n : ℕ) : Rounding.cap n (gamma/16)=⌈20*(n:ℚ)^2/(gammaRat/16)⌉₊+1 := by
  unfold Rounding.cap
  congr 1
  rw [←gammaRat_cast]
  norm_cast
  rw [←Int.ceil_toNat,←Int.ceil_toNat,Rat.ceil_cast]
end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_NormalizationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open IntegralAssembly (gammaRat)
lemma count_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) : count (pack δ d M)=d.bits := by
  simp only [count,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    UnaryResources.lengthBits_eq,List.length_replicate]
lemma mesh_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    mesh (pack δ d M)=BinaryRational.encode ((gammaRat/16)*M/d) := by
  rw [mesh,count_pack,value_bits]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryRational.decode_encode]
lemma cap_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    cap (pack δ d M)=(Rounding.cap d (IntegralAssembly.gamma/16)).bits := by
  simp only [cap,capArgument,count_pack,value_bits,BinaryRational.decode_encode,IntegralAssembly.cap_rat]
  congr 3
  ring
end MetricKMedianRecovery.BitMachine.BinaryNormalization

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NormalizeInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalizeInput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
namespace P
lemma points_bits (I : RationalMetricInput) : points I.bits=List.replicate I.pointCount true := by
  rw [points,Function.comp_apply,BinaryInputParser.Metric.clients_bits,RawUnary.run,BinaryInputParser.Metric.mask_length]
end P
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.matrix BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
lemma run_bits (I : RationalMetricInput) (M : ℚ) :
    run (pairBits (I.bits,BinaryRational.encode M))=encode
      [RationalMatrix.encode (BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate I.distance)
          ((IntegralAssembly.gammaRat/16)*M/I.clients.card) (Rounding.cap I.clients.card (IntegralAssembly.gamma/16))),
        List.replicate (I.pointCount+I.pointCount) true,BinaryFinSet.encode (I.clients.image BinaryTaggedSets.left),
        BinaryFinSet.encode (I.facilities.image BinaryTaggedSets.right),I.budget.bits,
        BinaryRational.encode ((IntegralAssembly.gammaRat/16)*M/I.clients.card),
        (Rounding.cap I.clients.card (IntegralAssembly.gamma/16)).bits] := by
  rw [run,rounded,twice,mesh,cap,prep_bits_s238,BinaryNormalization.run_pack_s238,BinaryNormalization.mesh_pack,BinaryNormalization.cap_pack,facilities_bits_s238]
  simp only [clients,points,budget,raw,extractPrefix_pairBits,P.points_bits,P.clients_bits_s238,BinaryInputParser.Metric.budget_bits,
    BinaryDuplicateMatrix.twice,←List.replicate_add,BinaryTaggedSets.left_encode]
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] counter demand base RawTake.run UnaryResources.lengthBits
attribute [local irreducible] call BinaryIntegralAll.run BinaryIntegralDispatch.budget ready norm src clamp BinaryInputParser.Metric.count
lemma norm_pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    norm (pack I M raw)=BinaryNormalizeInput.run (pairBits (I.bits,BinaryRational.encode M)) := by
  simp only [norm,normInput,pack,Function.comp_apply,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma right_card (I : RationalMetricInput) : (I.facilities.image BinaryTaggedSets.right).card=I.facilities.card := by
  apply Finset.card_image_of_injective
  intro a b h
  have hh:=congrArg Fin.val h
  simp only [BinaryTaggedSets.right,Fin.val_natAdd] at hh
  exact Fin.ext (by omega)
lemma clamp_pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    clamp (pack I M raw)=(min I.budget I.facilities.card).bits := by
  simp only [clamp,fcount,src,Function.comp_apply,norm_pack,BinaryNormalizeInput.run_bits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.encode_eq,Count.run_encode,
    List.length_map,Finset.length_sort,UnaryResources.lengthBits_eq,List.length_replicate,value_bits,right_card]
lemma base_pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) : base (pack I M raw)=integralPack I M [] := by
  rw [base,clamp_pack]
  simp only [src,Function.comp_apply,norm_pack]
  simp only [BinaryNormalizeInput.run_bits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,integralPack,A.pack,BinaryIntegralDispatch.pack,matrix]
lemma demand_length (Q : Polynomial ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    (demand Q (pack I M raw)).length=(A.budget Q).eval (integralPack I M []).length := by
  rw [demand,Function.comp_apply,(counter Q).word_length,base_pack]
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
lemma scales_bits (I : RationalMetricInput) : scales I.bits=encode ((BinaryInputParser.Metric.flat I).map BinaryRational.encode) := by
  rw [scales,Function.comp_apply,BinaryInputParser.Metric.rawMatrix_bits,BinaryInputParser.Stream.run_code_s238]
lemma callInput_pack (I : RationalMetricInput) (raw : List Bool) (M : ℚ) :
    callInput (pairBits (pairBits (I.bits,raw),BinaryRational.encode M))=BinaryGlobalCall.pack I M raw := by
  simp only [callInput,extractPrefix_pairBits,discardPrefix_pairBits,BinaryGlobalCall.pack]
attribute [local irreducible] BinaryInputParser.Metric.matrix BinaryNormalizeInput.P.clients
  BinaryNormalizeInput.P.facilities BinaryInputParser.Metric.budget fallback candidates
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList LocalSearch Completion
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryGlobalCall.run BinaryGlobalCall.demand budget select BinarySanitizedBest.output
lemma demand_bound_s238_oai (Q : Polynomial ℕ) (I : RationalMetricInput) (M : ℚ) (hM : M∈BinaryInputParser.Metric.flat I) :
    (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length≤(budget Q).eval I.bits.length := by
  have hm : demand Q (pairBits (pairBits (I.bits,[]),BinaryRational.encode M))∈
      (BinaryInputParser.Metric.flat I).map (fun r=>demand Q (pairBits (pairBits (I.bits,[]),BinaryRational.encode r))) :=
    List.mem_map.mpr ⟨M,hM,rfl⟩
  have hb:=length_member_le_encode hm
  have hl : (demand Q (pairBits (pairBits (I.bits,[]),BinaryRational.encode M))).length=
      (BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length := by
    rw [demand,Function.comp_apply,callInput_pack,BinaryGlobalCall.demand_length]
  rw [hl] at hb
  have he : demands Q I.bits=encode ((BinaryInputParser.Metric.flat I).map
      (fun r=>demand Q (pairBits (pairBits (I.bits,[]),BinaryRational.encode r)))) := by
    rw [demands,scales_bits,mapWith_encode,List.map_map];rfl
  rw [←he] at hb
  exact hb.trans (by simpa only [budget] using (demands_computes Q).length_bound I.bits)
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238_oai
