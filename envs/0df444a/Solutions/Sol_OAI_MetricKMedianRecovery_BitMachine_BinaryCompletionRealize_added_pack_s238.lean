-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:48:59.671861+00:00
-- url     : https://prove2.me/submissions/1971c89f-544a-4a1b-a5e1-506f2b1ce25e

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K030

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList
lemma length_encode_reverse (xs : List (List Bool)) : (encode xs.reverse).length=(encode xs).length := by
  simp only [length_encode,List.map_reverse,List.sum_reverse,List.length_reverse]
end WordList
end
open WordOperations BinaryArithmetic
namespace WordList
lemma encode_le_bound (ws : List (List Bool)) (B : ℕ) (hB : ∀ w∈ws,w.length ≤ B) :
    (encode ws).length ≤ ws.length*(2*B+2) := by
  induction ws with
  | nil => simp only [encode,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons w ws ih =>
    have hw := hB w (List.mem_cons_self ..)
    have ht := ih (fun x hx=>hB x (List.mem_cons_of_mem _ hx))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
namespace Indices

lemma op_pair (w : List Bool) (a : ℕ) (os : List (List Bool)) :
    Fold.operation op [] (pairBits (a.bits,encode os)) w=
      pairBits ((a+1).bits,encode (a.bits::os)) := by
  simp only [Fold.operation,op,discardPrefix_pairBits,extractPrefix_pairBits,value_bits,encode]
lemma fold_eq (ws os : List (List Bool)) (a : ℕ) :
    ws.foldl (Fold.operation op []) (pairBits (a.bits,encode os))=
      pairBits ((a+ws.length).bits,encode ((List.range' a ws.length |>.map Nat.bits).reverse++os)) := by
  induction ws generalizing a os with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero,List.range'_zero,List.map_nil,
      List.reverse_nil,List.nil_append]
  | cons w ws ih =>
    rw [List.foldl_cons,op_pair,ih]
    simp only [List.length_cons,List.range'_succ,List.map_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm 1]
lemma range_length (n : ℕ) : (encode ((List.range' 0 n).map Nat.bits)).length ≤ n*(2*n+2) := by
  have hh := encode_le_bound ((List.range' 0 n).map Nat.bits) n (by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have hh := (List.mem_range'_1.mp hi).2
    exact (bits_length_le i).trans (by omega))
  simpa only [List.length_map,List.length_range'] using hh

lemma run_encode (ws : List (List Bool)) : run (encode ws)=encode ((List.range ws.length).map Nat.bits) := by
  unfold run
  rw [Fold.run_encode op (20*(Polynomial.X+1)^2) [] (pairBits (Nat.bits 0,encode [])) ws
    (2*ws.length+1+ws.length*(2*ws.length+2))]
  · rw [fold_eq,discardPrefix_pairBits,List.append_nil,reverse_encode,List.reverse_reverse,List.range_eq_range']
  · intro n
    rw [fold_eq,Nat.zero_add,List.append_nil,pairBits_length]
    dsimp only
    rw [length_encode_reverse]
    have hb := bits_length_le (ws.take n).length
    have hr := range_length (ws.take n).length
    have hl : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    nlinarith
  · simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    have hw := length_le_encode ws
    have hsq := Nat.mul_le_mul hw hw
    nlinarith [Nat.zero_le ((pairBits (Nat.bits 0, encode [])).length)]
end Indices
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RowEncode
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
lemma lookup_ofFn {n : ℕ} (i : Fin n) (f : Fin n → List Bool) :
    Lookup.run (pairBits (i.val.bits,encode (List.ofFn f)))=f i := by
  rw [Lookup.run_encode]
  simp only [List.getElem?_ofFn,i.isLt,dite_eq_left,Option.getD_some]
lemma mapWith_ofFn {n : ℕ} (f : List Bool → List Bool) (d : List Bool) (g : Fin n → List Bool) :
    mapWith f (pairBits (d,encode (List.ofFn g)))=encode (List.ofFn (fun i=>f (pairBits (d,g i)))) := by
  rw [mapWith_encode,List.map_ofFn]
  rfl
lemma indices_ofFn {n : ℕ} (f : Fin n → List Bool) :
    Indices.run (encode (List.ofFn f))=encode (List.ofFn (fun i : Fin n=>i.val.bits)) := by
  rw [Indices.run_encode,List.length_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
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
lemma union_pack (xs ys : List ℕ) : union (pairBits (pack xs,pack ys))=encode (xs.toFinset∪ys.toFinset) := by
  simp only [union,extractPrefix_pairBits,discardPrefix_pairBits,←WordList.encode_append,←List.map_append,
    sort_pack,List.toFinset_append]
lemma union_encode (S T : Finset ℕ) : union (pairBits (encode S,encode T))=encode (S∪T) := by
  simpa only [Finset.sort_toFinset] using union_pack (S.sort (·≤·)) (T.sort (·≤·))
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionFill
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {q a : ℕ}
attribute [local irreducible] options
lemma options_pack (part : Fin q→Fin a) (o : Fin a→Fin q) (xs : List (Fin q)) (j : Fin a) :
    options (pairBits (pack part o xs,j.val.bits))=encode ((xs.filter (fun e=>part e=j)).map elemBits) := by
  simp only [options,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    extractPrefix_pairBits,discardPrefix_pairBits,filterWith_encode,List.filter_map,Function.comp_def,
    test,elemBits,lookup_ofFn,value_bits,Fin.ext_iff]
lemma pick_pack (part : Fin q→Fin a) (o : Fin a→Fin q) (xs : List (Fin q)) (j : Fin a) :
    pick (pairBits (pack part o xs,j.val.bits))=elemBits (Completion.Canonical.pick part o xs j) := by
  rw [pick,options_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn,Completion.Canonical.pick]
  cases h : xs.filter (fun e=>part e=j) with
  | nil=>rfl
  | cons e es=>
    simp only [List.map_cons,encode]
    have hn : cons (elemBits e) (encode (es.map elemBits))≠[] := by
      unfold cons; exact List.cons_ne_nil _ _
    rw [ite_eq_right hn]
    simp only [head,cons,List.tail_cons,extractPrefix_pairBits,List.head?_cons,Option.getD_some]

lemma run_pack (part : Fin q→Fin a) (o : Fin a→Fin q) (xs : List (Fin q)) :
    run (pack part o xs)=encode (List.ofFn (fun j=>elemBits (Completion.Canonical.pick part o xs j))) := by
  rw [run]
  have hi : field 1 (pack part o xs)=encode (List.ofFn (fun j=>(o j).val.bits)) := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hi,indices_ofFn,mapWith_ofFn]
  apply congrArg encode
  apply congrArg List.ofFn
  funext j
  exact pick_pack part o xs j
end MetricKMedianRecovery.BitMachine.BinaryCompletionFill

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma values_union (S T : Finset (Fin n)) : values (S∪T)=values S∪values T := Finset.image_union _ _
lemma union_pack (S T : Finset (Fin n)) : BinaryNatSet.union (pairBits (encode S,encode T))=encode (S∪T) := by
  rw [encode,encode,BinaryNatSet.union_encode,encode,values_union]
end MetricKMedianRecovery.BitMachine.BinaryFinSet

namespace MetricKMedianRecovery.BitMachine.BinaryIndexMap
open WordOperations WordList
lemma run_pack {α : Type*} {n : ℕ} (E : α→List Bool) (f : Fin n→α) (xs : List (Fin n)) :
    run (pairBits (encode (List.ofFn (fun i=>E (f i))),encode (xs.map (fun i=>i.val.bits))))=
      encode ((xs.map f).map E) := by
  simp only [run,mapWith_encode,item,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn,
    List.map_map,Function.comp_def]
end MetricKMedianRecovery.BitMachine.BinaryIndexMap

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
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
lemma sort_table (f : Fin m→Fin n) : BinaryNatSet.sort (table f)=encode (Finset.univ.image f) := by
  have hh:=sort_list (List.ofFn f)
  simp only [List.map_ofFn,Function.comp_def] at hh
  rw [table,hh]
  congr 1
  ext i
  simp
lemma image_list (f : Fin m→Fin n) (xs : List (Fin m)) :
    image (pairBits (table f,WordList.encode (xs.map (fun i=>i.val.bits))))=encode (xs.toFinset.image f) := by
  unfold image table
  rw [Function.comp_apply,BinaryIndexMap.run_pack]
  have hh:=sort_list (xs.map f)
  simp only [List.map_map,Function.comp_def] at hh ⊢
  rw [hh]
  congr 1
  ext i
  simp
lemma image_ofFn {l : ℕ} (f : Fin m→Fin n) (g : Fin l→Fin m) :
    image (pairBits (table f,WordList.encode (List.ofFn (fun j=>(g j).val.bits))))=
      encode (Finset.univ.image (f ∘ g)) := by
  have hh:=image_list f (List.ofFn g)
  simp only [List.map_ofFn,Function.comp_def] at hh
  rw [hh]
  congr 1
  ext i
  simp
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionRealize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionRealize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n q a p r b : ℕ}
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
attribute [local irreducible] redValues BinaryNatSet.sort
attribute [local irreducible] blue dest BinaryNatSet.union
attribute [local irreducible] BinaryNatSet.diff
attribute [local irreducible] filled
attribute [local irreducible] added
section Correct
variable (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (o : Fin a→Fin q) (loc : Fin q→Fin n)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n) (k : ℕ)
    (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ) (weight redBase : Fin r→ℚ)
    (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q))
local notation "data" => pack F S Q part o loc redLoc blueLoc blueDest k base distance weight redBase redDistance xs
lemma fillInput_pack : fillInput data=BinaryCompletionFill.pack part o xs := by
  simp only [fillInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rfl
lemma filled_pack : filled data=BinaryFinSet.encode (Completion.Canonical.filled part o loc xs) := by
  rw [filled,fillInput_pack,BinaryCompletionFill.run_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryCompletionFill.elemBits]
  exact BinaryFinSet.image_ofFn loc (Completion.Canonical.pick part o xs)
lemma dest_pack : dest data=BinaryFinSet.encode (Finset.univ.image blueDest) := by
  simp only [dest,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.sort_table]
lemma added_pack_s238_oai : added data=BinaryFinSet.encode (Completion.Canonical.filled part o loc xs∪Finset.univ.image blueDest) := by
  rw [added,filled_pack,dest_pack,BinaryFinSet.union_pack]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238_oai
