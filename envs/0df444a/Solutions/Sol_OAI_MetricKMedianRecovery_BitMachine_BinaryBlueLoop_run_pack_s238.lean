-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:46:51.326186+00:00
-- url     : https://prove2.me/submissions/2a686726-0885-4b04-90d0-85d0b5b29d48

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K029
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBlueSize_tableRun_best_bound_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBlueSize_table_length_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBlueTable_next_pack_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList.Find

lemma operation_pack (p : List Bool → Bool) (ctx a w : List Bool) :
    Fold.operation (operation p) ctx a w=
      if a=[] then if p (pairBits (ctx,w)) then true::w else [] else a := by
  simp only [Fold.operation,operation,accum,item,context,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_result (p : List Bool → Bool) (ctx a : List Bool) (ws : List (List Bool)) :
    ws.foldl (Fold.operation (operation p) ctx) a=
      if a=[] then optionEncode (ws.find? (fun w=>p (pairBits (ctx,w)))) else a := by
  induction ws generalizing a with
  | nil => simp only [List.foldl_nil,List.find?_nil,optionEncode]; split_ifs with h <;> simp_all
  | cons w ws ih =>
    rw [List.foldl_cons,operation_pack,ih]
    by_cases ha : a=[]
    · subst a
      simp only [ite_true, if_true]
      cases hp : p (pairBits (ctx,w)) <;> simp [hp,optionEncode]
    · simp only [ha,ite_false, if_false]

lemma optionEncode_bound {ws : List (List Bool)} {p : List Bool → Bool} :
    (optionEncode (ws.find? p)).length≤(encode ws).length+1 := by
  cases h : ws.find? p with
  | none => simp only [optionEncode,List.length_nil]; omega
  | some w =>
    have hw : w∈ws := List.mem_of_find?_eq_some h
    have hh := length_member_le_encode hw
    simpa only [optionEncode,List.length_cons] using Nat.add_le_add_right hh 1
lemma run_encode (p : List Bool → Bool) (ctx : List Bool) (ws : List (List Bool)) :
    run p (pairBits (ctx,encode ws))=optionEncode (ws.find? (fun w=>p (pairBits (ctx,w)))) := by
  unfold run
  simp only [Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [Fold.run_encode (operation p) (3*Polynomial.X+3) ctx [] ws ((encode ws).length+1)]
  · simp only [fold_result,ite_true, if_true]
  · intro j
    rw [fold_result,ite_eq_left rfl]
    have hb : (optionEncode ((ws.take j).find? (fun w=>p (pairBits (ctx,w))))).length≤
        (encode (ws.take j)).length+1 := optionEncode_bound
    have he := length_encode_append (ws.take j) (ws.drop j)
    rw [List.take_append_drop] at he
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Fold.length_pack,List.length_nil]
    omega
end WordList.Find
end
open WordOperations BinaryArithmetic RationalLinearFeasibility
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
open WordOperations WordList BinaryArithmetic
variable {A : Type*}
lemma run_pack (enc : A→List Bool) (x y : BlueDP.Candidate A) :
    run (pairBits (encode enc x,encode enc y))=encode enc (BlueDP.choose x y) := by
  rw [run,extractPrefix_pairBits,discardPrefix_pairBits]
  cases x with
  | none=>rw [show encode enc none=[] from rfl,ite_eq_left rfl];rfl
  | some x=>
    cases x with
    | mk q a=>
      have hx : encode enc (some (q,a))≠[] := by simp [encode,WordList.encode,WordList.cons,pairBits]
      rw [ite_eq_right hx]
      cases y with
      | none=>rw [show encode enc none=[] from rfl,ite_eq_left rfl];rfl
      | some y=>
        cases y with
        | mk r b=>
          have hy : encode enc (some (r,b))≠[] := by simp [encode,WordList.encode,WordList.cons,pairBits]
          rw [ite_eq_right hy]
          simp only [score,encode,WordList.encode,head_cons,extractPrefix_pairBits,BinaryRational.decode_encode,BlueDP.choose]
          split_ifs <;> rfl

end MetricKMedianRecovery.BitMachine.BinaryBlueChoice

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
namespace WordEq
lemma eq_pair (xs ys : List Bool) : eq (pairBits (xs,ys))=decide (xs=ys) := by
  simp only [eq,extractPrefix_pairBits,discardPrefix_pairBits]
end WordEq
namespace WordList
lemma encode_injective : Function.Injective encode := by
  intro xs
  induction xs with
  | nil=>
    intro ys he
    cases ys with
    | nil=>rfl
    | cons y ys=>exact (cons_ne_nil y (encode ys) he.symm).elim
  | cons x xs ih=>
    intro ys he
    cases ys with
    | nil=>exact (cons_ne_nil x (encode xs) he).elim
    | cons y ys=>
      have hh:=congrArg head he
      have ht:=congrArg tail he
      simp only [encode,head_cons] at hh
      simp only [encode,tail_cons] at ht
      exact congrArg₂ List.cons hh (ih ht)
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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
lemma lookup_map (vs : List (Finset L)) (f : Finset L→Candidate (List A)) (U : Finset L) (h : U∈vs) :
    lookup U (vs.map (fun V=>(V,f V)))=f U := by
  induction vs with
  | nil=>simp at h
  | cons V vs ih=>
    simp only [List.map_cons,lookup]
    by_cases he : U=V
    · simp [he]
    · rw [ite_eq_right he]
      exact ih (List.mem_cons.mp h |>.resolve_left he)
lemma mem_states (U V : Finset L) : V∈states U ↔ V⊆U := by
  simp only [states,List.mem_map,List.mem_sublists]
  constructor
  · rintro ⟨xs,hxs,rfl⟩
    intro l hl
    exact (Finset.mem_sort (·≤·)).mp (hxs.subset (List.mem_toFinset.mp hl))
  · intro h
    refine ⟨(U.sort (·≤·)).filter (fun l=>l∈V),List.filter_sublist,?_⟩
    ext l
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨And.right,fun hv=>⟨h hv,hv⟩⟩
lemma tables_eq (C : Finset L→Candidate (List A)) (U : Finset L) (t : ℕ) :
    tables C U t=(states U).map (fun V=>(V,recurrence C t V)) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    simp only [tables,nextTable,ih]
    apply List.map_congr_left
    intro W hW
    have hWU := (mem_states U W).mp hW
    congr 1
    conv_rhs => rw [recurrence]
    congr 1
    apply List.map_congr_left
    intro V _
    rw [lookup_map _ _ _ ((mem_states U (W\V)).mpr ((Finset.sdiff_subset).trans hWU))]
lemma lookup_tables (C : Finset L→Candidate (List A)) (U W : Finset L) (t : ℕ) (hW : W⊆U) :
    lookup W (tables C U t)=recurrence C t W := by
  rw [tables_eq,lookup_map _ _ _ ((mem_states U W).mpr hW)]
lemma tableRun_spec (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) :
    tableRun C U c=(tables C U c,select ((List.range c).map (fun t=>recurrence C (t+1) U))) := by
  induction c with
  | zero=>rfl
  | succ c ih=>
    rw [tableRun,Function.iterate_succ_apply']
    change tableStep C U (tableRun C U c)=_
    rw [ih]
    simp only [tableStep,show nextTable C U (tables C U c)=tables C U (c+1) from rfl,
      lookup_tables C U U (c+1) le_rfl,List.range_succ,List.map_append,
      List.map_singleton,select,List.foldl_append,List.foldl_cons,List.foldl_nil]
lemma tableBest_eq (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) : tableBest C U c=best C c U := by
  simp only [tableBest,tableRun_spec,best]
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
variable {n : ℕ}
lemma key_empty (U : Finset (Fin n)) : BinaryFinSet.encode U=[] ↔ U=∅ := by
  constructor
  · intro he
    have hh:=WordList.length_le_encode ((U.sort (·≤·)).map (fun i=>i.val.bits))
    rw [←BinaryFinSet.encode_eq,he] at hh
    simp only [List.length_map,Finset.length_sort,List.length_nil] at hh
    exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
  · rintro rfl
    simp [BinaryFinSet.encode_eq,WordList.encode]
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLookup
open WordOperations WordList
variable {L A : Type*} [LinearOrder L]
lemma run_pack (key : Finset L→List Bool) (enc : A→List Bool) (hk : Function.Injective key)
    (T : BlueDP.Table L A) (U : Finset L) : run (pairBits (key U,encode key enc T))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) (BlueDP.lookup U T) := by
  simp only [run,encode,Find.run_encode]
  induction T with
  | nil=>simp [Find.optionEncode,BlueDP.lookup,BinaryBlueChoice.encode,List.tail,discardPrefix]
  | cons z T ih=>
    rcases z with ⟨V,c⟩
    simp only [List.map_cons,List.find?_cons,matchKey,extractPrefix_pairBits,discardPrefix_pairBits,WordEq.eq_pair,
      hk.eq_iff,BlueDP.lookup]
    split_ifs with h
    · simp [h,Find.optionEncode,List.tail]
    · simp only [h,decide_false]
      simpa only [matchKey,extractPrefix_pairBits,discardPrefix_pairBits,WordEq.eq_pair] using ih
end MetricKMedianRecovery.BitMachine.BinaryBlueLookup
namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
lemma encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro S T he
  rw [encode_eq,encode_eq] at he
  have hh:=WordList.encode_injective he
  have hin : Function.Injective (fun i : Fin n=>i.val.bits) := by
    intro i j hij
    apply Fin.val_injective
    have h:=congrArg BinaryArithmetic.value hij
    simpa only [BinaryArithmetic.value_bits] using h
  have hh' := List.map_injective_iff.mpr hin hh
  simpa only [Finset.sort_toFinset] using congrArg List.toFinset hh'
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueNextTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueTable
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
omit [LinearOrder R] in
lemma initial_pack (er : R→List Bool) (U : Finset (Fin m)) :
    initial (encode ((BlueDP.states U).map BinaryFinSet.encode))=
      BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueCell.atomEnc (n:=n) (m:=m) er) (BlueDP.initialTable U) := by
  simp only [initial,mapWith_encode,List.map_map,Function.comp_def,initRow,discardPrefix_pairBits,
    BinaryBlueStates.key_empty,BinaryBlueLookup.encode,BlueDP.initialTable]
  congr 1
  apply List.map_congr_left
  intro W _
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryBlueTable

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTableSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLoop
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
lemma step_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) (s : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))×BlueDP.Candidate (List (BlueDP.Atom (Fin m) R (Fin n)))) :
    step (statePack er (pack er B F label q U c) s)=
      statePack er (pack er B F label q U c) (BlueDP.tableStep (BlueDP.block B F label q) U s) := by
  have hc : nextCtx (statePack er (pack er B F label q U c) s)=BinaryBlueCell.ctxPack er B F label q U s.1 := by
    simp only [nextCtx,statePack,oldTable,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryBlueCell.ctxPack]
  have hn : newTable (statePack er (pack er B F label q U c) s)=
      BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueCell.atomEnc er) (BlueDP.nextTable (BlueDP.block B F label q) U s.1) := by
    rw [newTable,hc,BinaryBlueTable.next_pack_s238]
  unfold step newBest
  rw [hn]
  simp only [statePack,oldBest,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [BinaryBlueLookup.run_pack _ _ BinaryFinSet.encode_injective,BinaryBlueChoice.run_pack]
  rfl
lemma iterate_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c t : ℕ) :
    step^[t] (statePack (n:=n) (m:=m) er (pack er B F label q U c) (BlueDP.initialTable U,none))=
      statePack er (pack er B F label q U c) (BlueDP.tableRun (BlueDP.block B F label q) U t) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    rw [Function.iterate_succ_apply',ih,step_pack]
    simp only [BlueDP.tableRun,Function.iterate_succ_apply']
lemma initial_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : initial (pack er B F label q U c)=statePack (n:=n) (m:=m) er (pack er B F label q U c) (BlueDP.initialTable U,none) := by
  simp only [initial,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryBlueTable.initial_pack (n:=n) er,statePack,BinaryBlueChoice.encode]
lemma iterate_length (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c t : ℕ) :
    (step^[t] (initial (pack er B F label q U c))).length≤(cap.word (pack er B F label q U c)).length := by
  rw [initial_pack,iterate_pack,cap.word_length]
  have hr : (BinaryBlueItem.records (fun i=>i.val.bits) er B label q).length≤(pack er B F label q U c).length := member_length (by simp)
  have hs : (encode ((BlueDP.states U).map BinaryFinSet.encode)).length≤(pack er B F label q U c).length := member_length (by simp)
  have ht:=BinaryBlueSize.table_length_s238 er B F label q U t _ hr hs
  have hb:=BinaryBlueSize.tableRun_best_bound_s238 er B F label q U t _ hr hs
  simp only [statePack,pairBits_length,BlueDP.tableRun_spec] at ⊢
  simp only [BlueDP.tableRun_spec] at hb
  simp only [capPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith
lemma loop_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : loop (pack er B F label q U c)=
      statePack er (pack er B F label q U c) (BlueDP.tableRun (BlueDP.block B F label q) U c) := by
  unfold loop
  rw [BoundedIteration.run_eq]
  · rw [show field 4 (pack er B F label q U c)=List.replicate c true by
      simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some],List.length_replicate,
      initial_pack,iterate_pack]
  · intro t _
    exact iterate_length er B F label q U c t
lemma run_pack_s238_oai (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : run (pack er B F label q U c)=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) (BlueDP.best (BlueDP.block B F label q) c U) := by
  rw [run,show field 3 (pack er B F label q U c)=BinaryFinSet.encode U by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]]
  simp only [BinaryBlueStates.key_empty]
  rw [←BlueDP.tableBest_eq,BlueDP.tableBest]
  split_ifs
  · rfl
  · rw [loop_pack]
    simp only [oldBest,statePack,discardPrefix_pairBits]
end MetricKMedianRecovery.BitMachine.BinaryBlueLoop

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238_oai.{u_1}
