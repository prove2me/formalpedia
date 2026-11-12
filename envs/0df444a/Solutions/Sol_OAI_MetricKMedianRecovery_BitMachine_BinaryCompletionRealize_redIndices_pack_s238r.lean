-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:57:32.457278+00:00
-- url     : https://prove2.me/submissions/fa63dd16-31ab-44c2-9665-4f274cd1baf7

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L026
import Definitions.Def_Q238L034
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRationalSort_ranked_pack_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace RationalMin
open WordList
lemma operation_pair (ctx a w : List Bool) :
    Fold.operation choose ctx a w=if BinaryRational.decode w≤BinaryRational.decode a then w else a := by
  simp only [Fold.operation,choose,Find.item,Fold.accum,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_encode (qs : List ℚ) (a : ℚ) (ctx : List Bool) :
    (qs.map BinaryRational.encode).foldl (Fold.operation choose ctx) (BinaryRational.encode a)=
      BinaryRational.encode (qs.foldl min a) := by
  induction qs generalizing a with
  | nil=>rfl
  | cons q qs ih=>
    simp only [List.map_cons,List.foldl_cons,operation_pair,BinaryRational.decode_encode]
    by_cases h : q≤a
    · simp only [h,ite_true, if_true,min_eq_right h,ih]
    · have ha : a≤q := le_of_lt (lt_of_not_ge h)
      simp only [h,ite_false, if_false,min_eq_left ha,ih]
lemma fold_length (ws : List (List Bool)) (a ctx : List Bool) :
    (ws.foldl (Fold.operation choose ctx) a).length≤a.length+(encode ws).length := by
  induction ws generalizing a with
  | nil=>simp only [List.foldl_nil,encode,List.length_nil,Nat.add_zero,Nat.le_refl]
  | cons w ws ih=>
    rw [List.foldl_cons,operation_pair]
    simp only [encode,length_cons]
    split_ifs
    · have hh := ih w; omega
    · have hh := ih a; omega

lemma seed_encode (qs : List ℚ) : seed (RationalArray.encode qs)=BinaryRational.encode (qs.head?.getD 0) := by
  cases qs with
  | nil=>rfl
  | cons q qs=>simp only [seed,RationalArray.encode,List.map_cons,encode,cons_ne_nil,
      ite_false, if_false,head_cons,List.head?_cons,Option.getD_some]
lemma run_encode (qs : List ℚ) : run (RationalArray.encode qs)=BinaryRational.encode (minimum qs) := by
  unfold run
  rw [show RationalArray.encode qs=encode (qs.map BinaryRational.encode) from rfl]
  rw [Fold.run_encode choose (3*Polynomial.X+3) [] (seed (encode (qs.map BinaryRational.encode)))
    (qs.map BinaryRational.encode)
    ((seed (encode (qs.map BinaryRational.encode))).length+(encode (qs.map BinaryRational.encode)).length)]
  · rw [show seed (encode (qs.map BinaryRational.encode))=BinaryRational.encode (qs.head?.getD 0) from seed_encode qs,
      fold_encode]
    rfl
  · intro j
    have hh := fold_length ((qs.map BinaryRational.encode).take j)
      (seed (encode (qs.map BinaryRational.encode))) []
    exact hh.trans (Nat.add_le_add_left (length_encode_take _ _) _)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil]
    omega

end RationalMin
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
namespace Drop
open Lookup (step step_computes iterate_bounds step_zero step_succ)
lemma drop_iterate (n i : ℕ) (ws : List (List Bool)) (hn : ws.length≤n) :
    discardPrefix (step^[n] (pairBits (i.bits,encode ws)))=encode (ws.drop i) := by
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
lemma run_encode (i : ℕ) (ws : List (List Bool)) :
    run (pairBits (i.bits,encode ws))=encode (ws.drop i) := by
  apply drop_iterate
  have h:=length_le_encode ws
  rw [pairBits_length]
  dsimp only
  omega
end Drop
lemma lengthBits_encode (ws : List (List Bool)) : lengthBits (encode ws)=ws.length.bits := by
  simp only [lengthBits,Function.comp_apply,Count.run_encode,UnaryResources.lengthBits_eq,List.length_replicate]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordTake
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Take
open WordOperations BinaryArithmetic
attribute [local irreducible] number reverse Drop.run
lemma run_encode (n : ℕ) (ws : List (List Bool)) :
    run (pairBits (n.bits,encode ws))=encode (ws.take n) := by
  simp only [run,number,extractPrefix_pairBits,discardPrefix_pairBits,lengthBits_encode,value_bits,
    reverse_encode,Drop.run_encode,List.reverse_drop,List.reverse_reverse,List.length_reverse]
  congr 1
  rw [show ws.length-(ws.length-n)=min n ws.length by omega]
  exact List.take_eq_take_min.symm
end MetricKMedianRecovery.BitMachine.WordList.Take

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

lemma lt_pack (a b : ℚ ×ₗ ℕ) : lt (pairBits (entryBits a,entryBits b))=decide (a<b) := by
  simp only [lt,entryBits,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode,
    value_bits,Prod.Lex.lt_iff,Bool.decide_or,Bool.decide_and]
lemma sort_pack (xs : List (ℚ ×ₗ ℕ)) :
    sort (encode (xs.map entryBits))=encode ((xs.toFinset.sort (·≤·)).map entryBits) :=
  Sort.run_encode entryBits lt lt_pack xs
attribute [local irreducible] sort ranked Take.run
lemma bottom_pack {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    bottom (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))) )=
      encode ((((Finset.univ.image (ranking v)).sort (·≤·)).take k).map entryBits) := by
  simp only [bottom,extractPrefix_pairBits,discardPrefix_pairBits,ranked_pack_s238r]
  rw [show List.ofFn (fun i=>entryBits (ranking v i))=(List.ofFn (ranking v)).map entryBits by rw [List.map_ofFn]; rfl]
  rw [sort_pack,Take.run_encode,←Fin.univ_image_def,←List.map_take]
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

namespace MetricKMedianRecovery.BitMachine.BinaryNatSet
open WordOperations WordList BinaryArithmetic
lemma lt_pack (a b : ℕ) : lt (pairBits (a.bits,b.bits))=decide (a<b) := by
  simp only [lt,extractPrefix_pairBits,discardPrefix_pairBits,value_bits]
lemma sort_pack (xs : List ℕ) : sort (pack xs)=encode xs.toFinset := Sort.run_encode _ _ lt_pack _
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BottomMath
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {α : Type*} [LinearOrder α]
lemma bottomSet_subset (U : Finset α) (k : ℕ) : bottomSet U k⊆U := by
  intro x hx
  exact (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))
end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalBottomIndices
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic
lemma indexSet_image {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    (indexSet v k).image (ranking v)=Completion.bottomSet (Finset.univ.image (ranking v)) k := by
  classical
  ext p
  simp only [Finset.mem_image,indexSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact hi
  · intro hp
    obtain ⟨i,_,he⟩:=Finset.mem_image.mp (Completion.bottomSet_subset _ _ hp)
    exact ⟨i,he ▸ hp,he⟩
lemma bottomIndices_finset {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    (bottomIndices v k).toFinset=(indexSet v k).image Fin.val := by
  classical
  have hm (xs : List (ℚ ×ₗ ℕ)) : (xs.map (fun p=>(ofLex p).2)).toFinset=xs.toFinset.image (fun p=>(ofLex p).2) := by
    ext i; simp
  rw [bottomIndices,hm,show (((Finset.univ.image (ranking v)).sort (·≤·)).take k).toFinset=
    (indexSet v k).image (ranking v) from (indexSet_image v k).symm,Finset.image_image]
  rfl
lemma rawIndices_pack {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    rawIndices (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))))=
      encode ((bottomIndices v k).map Nat.bits) := by
  simp only [rawIndices,bottom_pack,mapWith_encode,List.map_map,Function.comp_def,
    discardPrefix_pairBits,entryBits,bottomIndices]
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {m n : ℕ}
lemma bottom_pack (v : Fin m→ℚ) (k : ℕ) :
    BinaryNatSet.sort (BinaryRationalSort.rawIndices
      (pairBits (k.bits,WordList.encode (List.ofFn (fun i=>BinaryRational.encode (v i))))))=
      encode (BinaryRationalSort.indexSet v k) := by
  rw [BinaryRationalSort.rawIndices_pack,BinaryNatSet.sort_pack,BinaryRationalSort.bottomIndices_finset]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalCap
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)

lemma minimum_capped {E : Type*} [DecidableEq E] (b : ℚ) (d : E→ℚ) (xs : List E) :
    RationalMin.minimum (b::xs.map d)=capped b d xs.toFinset := by
  simp only [RationalMin.minimum,List.head?_cons,Option.getD_some,List.foldl_cons,min_self]
  rw [List.foldl_eq_foldr]
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.map_cons,List.foldr_cons,List.toFinset_cons,capped,Finset.fold_insert_idem] at *
    rw [ih]
attribute [local irreducible] mapWith
lemma offers_pack {q : ℕ} (b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    offers (pairBits (encode (xs.map BinaryCategorical.elemBits),rowBits b d))=
      encode (xs.map (fun e=>BinaryRational.encode (d e))) := by
  simp only [offers,rowBits,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mapWith_encode,List.map_map,
    Function.comp_def,look,BinaryCategorical.elemBits,lookup_ofFn]
attribute [local irreducible] RationalMin.run
lemma cap_pack {q : ℕ} (b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    cap (pairBits (encode (xs.map BinaryCategorical.elemBits),rowBits b d))=
      BinaryRational.encode (capped b d xs.toFinset) := by
  unfold cap
  rw [offers_pack]
  simp only [discardPrefix_pairBits,rowBits,field_encode,List.getElem?_cons_zero,Option.getD_some]
  rw [show cons (BinaryRational.encode b) (encode (xs.map (fun e=>BinaryRational.encode (d e))))=
    RationalArray.encode (b::xs.map d) by
      simp only [RationalArray.encode,List.map_cons,List.map_map,Function.comp_def,encode]]
  rw [RationalMin.run_encode,minimum_capped]

lemma weightedCap_pack {q : ℕ} (w b : ℚ) (d : Fin q→ℚ) (xs : List (Fin q)) :
    weightedCap (pairBits (encode (xs.map BinaryCategorical.elemBits),weightedRowBits w b d))=
      BinaryRational.encode (w*capped b d xs.toFinset) := by
  simp only [weightedCap,weightedRowBits,extractPrefix_pairBits,discardPrefix_pairBits,cap_pack,
    BinaryRational.decode_encode]
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalSurrogate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {q p r : ℕ}
lemma redValues_pack (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    redValues (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      encode (List.ofFn (fun i=>BinaryRational.encode (weight i*capped (redBase i) (redDistance i) xs.toFinset))) := by
  simp only [redValues,contextBits,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,mapWith_ofFn,weightedCap_pack]

end MetricKMedianRecovery.BitMachine.BinaryCompletion

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
open BinaryOpeningPayment (field field_computes field_encode)
variable {n q a p r b : ℕ}
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
attribute [local irreducible] redValues BinaryNatSet.sort BinaryRationalSort.rawIndices
attribute [local irreducible] redIndices
attribute [local irreducible] red blue dest BinaryNatSet.union
attribute [local irreducible] removed BinaryNatSet.diff
attribute [local irreducible] filled
attribute [local irreducible] remain added
attribute [local irreducible] core
section Correct
variable (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (o : Fin a→Fin q) (loc : Fin q→Fin n)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n) (k : ℕ)
    (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ) (weight redBase : Fin r→ℚ)
    (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q))
local notation "data" => pack F S Q part o loc redLoc blueLoc blueDest k base distance weight redBase redDistance xs
local notation "v" => (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset)
lemma redValues_pack : redValues data=encode (List.ofFn (fun i=>BinaryRational.encode (v i))) := by
  simp only [redValues,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryCompletion.redValues_pack]
lemma redIndices_pack_s238r_oai : redIndices data=BinaryFinSet.encode (BinaryRationalSort.indexSet v k) := by
  rw [redIndices,redValues_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryCompletion.contextBits,BinaryFinSet.bottom_pack]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238r_oai
