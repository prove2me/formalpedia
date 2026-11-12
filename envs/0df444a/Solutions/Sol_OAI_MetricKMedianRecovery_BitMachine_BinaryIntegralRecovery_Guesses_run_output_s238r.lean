-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:08:00.425315+00:00
-- url     : https://prove2.me/submissions/e20c6120-5c01-4c51-abd2-8158889be678

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L031
import Definitions.Def_Q238L040
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_ranges_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricBest_run_pack_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma length_encode_take (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.take n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
namespace Flatten

lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=a++w := by
  simp only [Fold.operation,op,Fold.accum,Find.item,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_eq (ws : List (List Bool)) (ctx a : List Bool) :
    ws.foldl (Fold.operation op ctx) a=a++ws.flatten := by
  induction ws generalizing a with
  | nil=>simp only [List.foldl_nil,List.flatten_nil,List.append_nil]
  | cons w ws ih=>simp only [List.foldl_cons,operation_eq,ih,List.flatten_cons,List.append_assoc]
lemma length_flatten_le (ws : List (List Bool)) : ws.flatten.length≤(encode ws).length := by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>simp only [List.flatten_cons,List.length_append,encode,length_cons]; omega
lemma run_encode (ws : List (List Bool)) : run (encode ws)=ws.flatten := by
  unfold run
  rw [Fold.run_encode op (3*Polynomial.X+3) [] [] ws (encode ws).length]
  · simp only [fold_eq,List.nil_append]
  · intro n
    simp only [fold_eq,List.nil_append]
    exact (length_flatten_le _).trans (length_encode_take ws n)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
lemma encode_flatMap {α : Type*} (ws : List α) (f : α → List (List Bool)) :
    encode (ws.flatMap f)=(ws.map (fun x=>encode (f x))).flatten := by
  induction ws with
  | nil=>rfl
  | cons a ws ih=>simp only [List.flatMap_cons,encode_append,List.map_cons,List.flatten_cons,ih]
end Flatten
lemma flatMapWith_encode (f : List Bool → List Bool) (ctx : List Bool) (ws : List (List Bool))
    (g : List Bool → List (List Bool)) (h : ∀ w∈ws, f (pairBits (ctx,w))=encode (g w)) :
    flatMapWith f (pairBits (ctx,encode ws))=encode (ws.flatMap g) := by
  simp only [flatMapWith,Function.comp_apply,mapWith_encode,Flatten.run_encode,Flatten.encode_flatMap]
  congr 1
  apply List.map_congr_left
  exact h
end WordList
end MetricKMedianRecovery.BitMachine
namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
lemma crossWith_encode (f : List Bool → List Bool) (xs ys : List (List Bool)) :
    crossWith f (pairBits (encode xs,encode ys))=
      encode (xs.flatMap (fun x=>ys.map (fun y=>f (pairBits (x,y))))) := by
  unfold crossWith
  simp only [extractPrefix_pairBits,discardPrefix_pairBits]
  apply flatMapWith_encode
  intro w _
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,mapWith_encode]
lemma cross_encode (xs ys : List (List Bool)) :
    cross (pairBits (encode xs,encode ys))=encode (xs.flatMap (fun x=>ys.map (fun y=>pairBits (x,y)))) :=
  crossWith_encode id xs ys
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma flatMap_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : α → List β) :
    (List.ofFn f).flatMap g=(List.ofFn (fun j=>g (f j))).flatten := by
  change ((List.ofFn f).map g).flatten=_
  rw [List.map_ofFn]
  rfl
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FilterItem
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma filterWith_encode (p : List Bool → Bool) (ctx : List Bool) (ws : List (List Bool)) :
    filterWith p (pairBits (ctx,encode ws))=encode (ws.filter (fun w=>p (pairBits (ctx,w)))) := by
  unfold filterWith
  rw [flatMapWith_encode (filterItem p) ctx ws (fun w=>if p (pairBits (ctx,w)) then [w] else []) (by
    intro w _; simp only [filterItem,discardPrefix_pairBits]; split <;> rfl)]
  congr 1
  induction ws with
  | nil=>rfl
  | cons w ws ih=>cases h : p (pairBits (ctx,w)) <;> simp [h,ih]
end WordList
end MetricKMedianRecovery.BitMachine

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
lemma filter_sort {n : ℕ} (F : Finset (Fin n)) (p : Fin n→Prop) [DecidablePred p] :
    (F.sort (·≤·)).filter (fun v=>decide (p v))=(F.filter p).sort (·≤·) := by
  have hn := (Finset.sort_nodup F (·≤·)).filter (fun v=>decide (p v))
  have hp := (Finset.pairwise_sort F (·≤·)).filter (fun v=>decide (p v))
  have hh := (List.toFinset_sort (r:=(·≤·)) hn).mpr hp
  simpa only [List.toFinset_filter,Finset.sort_toFinset,decide_eq_true_eq] using hh.symm
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma clip_pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) :
    clip (pack F S k raw)=BinaryFinSet.encode (clipped F raw) := by
  simp only [clip,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFinSet.encode_eq,filterWith_encode,List.filter_map,Function.comp_def,keep,
    extractPrefix_pairBits,discardPrefix_pairBits,clipped]
  congr 2
  simpa only [Bool.decide_coe] using BinaryFinSet.filter_sort F (fun i=>BinaryNatSet.contains (pairBits (i.val.bits,raw))=true)
lemma size_pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) :
    size (pack F S k raw)=(clipped F raw).card.bits := by
  simp only [size,Function.comp_apply,clip_pack,BinaryFinSet.encode_eq,Count.run_encode,List.length_map,Finset.length_sort,
    UnaryResources.lengthBits_eq,List.length_replicate]
lemma run_pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) :
    run (pack F S k raw)=BinaryFinSet.encode (output F S k raw) := by
  rw [run,size_pack,clip_pack]
  simp only [value_bits,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,output,Finset.card_pos]
  split_ifs <;> simp_all
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma atRaw_pack (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool) :
    atRaw (pairBits (encode [BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits],raw))=
      BinaryFinSet.encode (BinaryCandidateSanitize.output F S k raw) := by
  simp only [atRaw,Function.comp_apply,atRawInput,extractPrefix_pairBits,discardPrefix_pairBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact BinaryCandidateSanitize.run_pack F S k raw
lemma candidates_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) :
    candidates (pack δ D F S k xs)=encode (xs.map (fun raw=>BinaryFinSet.encode (BinaryCandidateSanitize.output F S k raw))) := by
  simp only [candidates,sanitizeContext,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,mapWith_encode,atRaw_pack]
lemma run_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) :
    run (pack δ D F S k xs)=BinaryFinSet.encode (output δ D F S k xs) := by
  rw [run,candidates_pack]
  have hm : metricContext (pack δ D F S k xs)=BinaryMetricBest.context δ D := by
    simp only [metricContext,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,BinaryMetricBest.context]
  have hs : field 3 (pack δ D F S k xs)=BinaryFinSet.encode S := by simp only [pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hm,hs]
  have hh:=BinaryMetricBest.run_pack_s238r δ D S (xs.map (BinaryCandidateSanitize.output F S k))
  simpa only [BinaryRationalBest.pack,List.map_map,Function.comp_def,output] using hh
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Repeat.FiniteTape.run BinarySanitizedBest.run BinaryFinSet.encode BinarySampler.Parameters.unary Count.run src
attribute [local irreducible] mapWith
attribute [local irreducible] sizeWord candidateWords
variable {n : ℕ}
lemma src_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) (j : ℕ) :
    src j (pack δ D F S Δ g raw)=field j (BinarySampler.Parameters.pack δ D F S Δ 0 0) := by
  simp only [src,pack,Fair.pack,Function.comp_apply,extractPrefix_pairBits]
lemma atInput_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool) (p m : ℕ) :
    atInput (pairBits (pack δ D F S Δ g raw,pairBits (p.bits,m.bits)))=Fair.pack δ D F S Δ p m g raw := by
  simp only [atInput,atParams,source,price,count,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    src,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.natWords_bits,extra,Fair.raw,pack,Fair.pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
lemma candidateWords_pack (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g raw : List Bool) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    candidateWords Q d (pack δ D F S Δ g raw)=encode (words Q d δ D F S Δ g raw) := by
  rw [candidateWords,choices,(ranges_pack_s238r δ D F S Δ g raw hΔ).1,(ranges_pack_s238r δ D F S Δ g raw hΔ).2,
    cross_encode,mapWith_encode]
  simp only [flatMap_ofFn,List.map_flatten,List.map_ofFn,Function.comp_def,atChoice,
    atInput_pack,words]
lemma run_pack (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (g raw : List Bool) (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    run Q d (pack δ D F S Δ g raw)=BinaryFinSet.encode
      (BinarySanitizedBest.output δ D F S S.card (words Q d δ D F S Δ g raw)) := by
  rw [run,Function.comp_apply,runInput,candidateWords_pack Q d δ D F S Δ g raw hΔ]
  have hs : sizeWord (pack δ D F S Δ g raw)=S.card.bits := by
    simp only [sizeWord,src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.encode_eq,Count.run_encode,List.length_map,
      Finset.length_sort,UnaryResources.lengthBits_eq,List.length_replicate]
  rw [hs]
  simp only [src_pack,BinarySampler.Parameters.pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  exact BinarySanitizedBest.run_pack δ D F S S.card _
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
lemma run_output_s238r_oai (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (g raw : List Bool)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    run Q d (pack δ D F S Δ g raw)=BinaryFinSet.encode (output Q d δ D F S Δ g raw) :=
  run_pack Q d δ D F S Δ g raw hΔ
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238r_oai
