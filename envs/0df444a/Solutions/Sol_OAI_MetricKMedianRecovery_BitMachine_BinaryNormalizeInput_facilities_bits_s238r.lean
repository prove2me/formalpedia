-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_bits_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:59:22.428904+00:00
-- url     : https://prove2.me/submissions/a54e11ee-1d40-4b25-b195-216ea055c791

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L035
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalizeInput_P_facilities_bits_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SortMath
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSort
variable {α : Type*} [LinearOrder α]

lemma insert_sort (a : α) (S : Finset α) :
    insert a (S.sort (·≤·))=(Insert.insert a S).sort (·≤·) := by
  apply List.Pairwise.eq_of_mem_iff (r:= (·<·))
  · rw [insert,List.pairwise_append]
    refine ⟨(Finset.sortedLT_sort S).pairwise.filter _,?_,?_⟩
    · rw [List.pairwise_cons]
      exact ⟨fun b hb=>of_decide_eq_true (List.mem_filter.mp hb).2,(Finset.sortedLT_sort S).pairwise.filter _⟩
    · intro b hb c hc
      have hb' : b<a := of_decide_eq_true (List.mem_filter.mp hb).2
      rcases List.mem_cons.mp hc with rfl|hc
      · exact hb'
      · exact hb'.trans (of_decide_eq_true (List.mem_filter.mp hc).2)
  · exact (Finset.sortedLT_sort _).pairwise
  · intro b
    simp only [insert,List.mem_append,List.mem_filter,List.mem_cons,Finset.mem_sort,Finset.mem_insert,decide_eq_true_eq]
    constructor
    · rintro (⟨hb,_⟩|h|⟨hb,_⟩) <;> tauto
    · rintro (rfl|hb)
      · exact Or.inr (Or.inl rfl)
      · rcases lt_trichotomy b a with h|h|h
        · exact Or.inl ⟨hb,h⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨hb,h⟩)

lemma fold_sort (xs : List α) (S : Finset α) :
    xs.foldl (fun acc a=>insert a acc) (S.sort (·≤·))=(S∪xs.toFinset).sort (·≤·) := by
  induction xs generalizing S with
  | nil=>simp
  | cons a xs ih=>
    rw [List.foldl_cons,insert_sort,ih]
    congr 1
    ext b
    simp only [List.toFinset_cons,Finset.mem_union,Finset.mem_insert]
    tauto

lemma run_sort (xs : List α) : xs.foldl (fun acc a=>insert a acc) []=xs.toFinset.sort (·≤·) := by
  simpa only [Finset.sort_empty,Finset.empty_union] using fold_sort xs ∅
end MetricKMedianRecovery.CanonicalSort

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList.Sort

variable {α : Type*} [LinearOrder α]
lemma insert_encode (E : α → List Bool) (p : List Bool → Bool)
    (hp : ∀ a b,p (pairBits (E a,E b))=decide (a<b)) (a : α) (xs : List α) :
    insert p (pairBits (E a,encode (xs.map E)))=
      encode ((CanonicalSort.insert a xs).map E) := by
  simp only [insert,filterWith_encode,reverseTest,extractPrefix_pairBits,discardPrefix_pairBits,
    List.filter_map,Function.comp_def,hp,CanonicalSort.insert,List.map_append,List.map_cons,encode_append,encode]

lemma length_filter_pair (E : α → List Bool) (a : α) (xs : List α) :
    (encode ((xs.filter (·<a)).map E)).length+(encode ((xs.filter (a<·)).map E)).length ≤
    (encode (xs.map E)).length := by
  induction xs with
  | nil=>rfl
  | cons b xs ih=>
    by_cases hba : b<a
    · have hab : ¬a<b := not_lt_of_gt hba
      simp only [List.filter_cons,decide_eq_true hba,decide_eq_false hab,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,
        List.map_cons,encode,length_cons]
      omega
    · by_cases hab : a<b
      · simp only [List.filter_cons,decide_eq_false hba,decide_eq_true hab,ite_true, if_true,Bool.false_eq_true,ite_false, if_false,
          List.map_cons,encode,length_cons]
        omega
      · simp only [List.filter_cons,decide_eq_false hba,decide_eq_false hab,Bool.false_eq_true,ite_false, if_false,
          List.map_cons,encode,length_cons]
        omega

lemma insert_length (E : α → List Bool) (a : α) (xs : List α) :
    (encode ((CanonicalSort.insert a xs).map E)).length ≤
      (encode (xs.map E)).length+2*(E a).length+2 := by
  have h:=length_filter_pair E a xs
  simp only [CanonicalSort.insert,List.map_append,List.map_cons,length_encode_append,encode,length_cons]
  omega

lemma fold_length (E : α → List Bool) (xs acc : List α) :
    (encode ((xs.foldl (fun ac a=>CanonicalSort.insert a ac) acc).map E)).length ≤
      (encode (acc.map E)).length+(encode (xs.map E)).length := by
  induction xs generalizing acc with
  | nil=>simp
  | cons a xs ih=>
    simp only [List.foldl_cons,List.map_cons,encode,length_cons]
    have h:=ih (CanonicalSort.insert a acc)
    have h':=insert_length E a acc
    omega

lemma operation_encode (E : α → List Bool) (p : List Bool → Bool)
    (hp : ∀ a b,p (pairBits (E a,E b))=decide (a<b)) (ctx : List Bool) (a : α) (xs : List α) :
    Fold.operation (op p) ctx (encode (xs.map E)) (E a)=encode ((CanonicalSort.insert a xs).map E) := by
  simp only [Fold.operation,op,Find.item,Fold.accum,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,insert_encode E p hp]
lemma fold_encode (E : α → List Bool) (p : List Bool → Bool)
    (hp : ∀ a b,p (pairBits (E a,E b))=decide (a<b)) (ctx : List Bool) (xs acc : List α) :
    (xs.map E).foldl (Fold.operation (op p) ctx) (encode (acc.map E))=
      encode ((xs.foldl (fun ac a=>CanonicalSort.insert a ac) acc).map E) := by
  induction xs generalizing acc with
  | nil=>rfl
  | cons a xs ih=>simp only [List.map_cons,List.foldl_cons,operation_encode E p hp,ih]

lemma run_encode (E : α → List Bool) (p : List Bool → Bool)
    (hp : ∀ a b,p (pairBits (E a,E b))=decide (a<b)) (xs : List α) :
    run p (encode (xs.map E))=encode ((xs.toFinset.sort (·≤·)).map E) := by
  unfold run
  rw [Fold.run_encode (op p) (3*Polynomial.X+3) [] [] (xs.map E) (encode (xs.map E)).length]
  · change (xs.map E).foldl _ (encode (List.map E []))=_
    rw [fold_encode E p hp,CanonicalSort.run_sort]
  · intro j
    rw [←List.map_take]
    change ((xs.take j).map E |>.foldl _ (encode (List.map E []))).length≤_
    rw [fold_encode E p hp]
    have h:=fold_length E (xs.take j) []
    simp only [List.map_nil,encode,List.length_nil,Nat.zero_add] at h
    exact h.trans (by simpa only [List.map_take] using length_encode_take (xs.map E) j)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
end WordList.Sort
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
lemma lt_pack (a b : ℕ) : lt (pairBits (a.bits,b.bits))=decide (a<b) := by
  simp only [lt,extractPrefix_pairBits,discardPrefix_pairBits,value_bits]
lemma sort_pack (xs : List ℕ) : sort (pack xs)=encode xs.toFinset := Sort.run_encode _ _ lt_pack _
end MetricKMedianRecovery.BitMachine.BinaryNatSet

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Metric
open WordOperations WordList
attribute [local irreducible] nat RawTake.run RawDrop.run Stream.run RawUnary.run
attribute [local irreducible] header count tailHeader budget masks clients afterClients facilities rawMatrix
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

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {m n : ℕ}
lemma sort_list (xs : List (Fin n)) :
    BinaryNatSet.sort (WordList.encode (xs.map (fun i=>i.val.bits)))=encode xs.toFinset := by
  have hh:=BinaryNatSet.sort_pack (xs.map Fin.val)
  simp only [BinaryNatSet.pack,List.map_map,Function.comp_def] at hh
  rw [hh,encode]
  congr 1
  ext i
  simp only [List.mem_toFinset,List.mem_map,values,Finset.mem_image,List.mem_toFinset]
end MetricKMedianRecovery.BitMachine.BinaryFinSet

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
lemma shift_encode (S : Finset (Fin n)) :
    shift (pairBits (n.bits,BinaryFinSet.encode S))=BinaryFinSet.encode (S.image right) := by
  rw [shift,Function.comp_apply,BinaryFinSet.encode_eq,mapWith_encode,List.map_map]
  simp only [Function.comp_def]
  have he : ((S.sort (·≤·)).map (fun i=>plus (pairBits (n.bits,i.val.bits))))=
      ((S.sort (·≤·)).map right).map (fun i=>i.val.bits) := by
    simp only [List.map_map,Function.comp_def,plus,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,right,Fin.val_natAdd]
  rw [he,BinaryFinSet.sort_list]
  congr 1
  ext i
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_image]
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

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
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
lemma facilities_bits_s238r_oai (I : RationalMetricInput) (M : ℚ) :
    facilities (pairBits (I.bits,BinaryRational.encode M))=BinaryFinSet.encode (I.facilities.image BinaryTaggedSets.right) := by
  simp only [facilities,facilitiesInput,count,plainFacilities,raw,extractPrefix_pairBits,BinaryInputParser.Metric.count_bits,P.facilities_bits_s238r,BinaryTaggedSets.shift_encode]
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_bits_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.facilities_bits_s238r_oai
