-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:02:06.016231+00:00
-- url     : https://prove2.me/submissions/685e0c44-d732-48f1-b3bc-3918895efdba

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBlueLoop_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchCheck_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_bluePack_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_plan_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_run_pack_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.CappedFold
open WordOperations
lemma run_pack (f : List Bool → List Bool) (cap ctx a : List Bool) (ws : List (List Bool))
    (hB : ∀ n, ((ws.take n).foldl (Fold.operation f ctx) a).length ≤ cap.length) :
    run f (pairBits (cap,Fold.pack (encode ws) ctx a))=ws.foldl (Fold.operation f ctx) a := by
  unfold run
  rw [discardPrefix_pairBits,Fold.items_pack,Count.run_encode,BoundedIteration.run_eq]
  · simp only [List.length_replicate,Fold.iterate_pack,Fold.accum_pack,List.take_length]
  · intro j _
    rw [Fold.iterate_pack,Fold.length_pack,RepeatedAppend.length_copies,pairBits_length,Fold.length_pack]
    dsimp only at *
    have hws:=length_encode_drop ws j
    have hb:=hB j
    omega

lemma fold_encode {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) :
    (xs.map encA).foldl (Fold.operation f ctx) (encS s)=encS (xs.foldl g s) := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.map_cons,List.foldl_cons,Fold.operation,hf]
    exact ih (g s a)
lemma run_typed {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx cap : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) (hB : ∀ n,(encS ((xs.take n).foldl g s)).length ≤ cap.length) :
    run f (pairBits (cap,Fold.pack (encode (xs.map encA)) ctx (encS s)))=encS (xs.foldl g s) := by
  rw [run_pack]
  · exact fold_encode encS encA g f ctx hf s xs
  · intro n
    rw [←List.map_take,fold_encode encS encA g f ctx hf]
    exact hB n
end MetricKMedianRecovery.BitMachine.WordList.CappedFold

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Subsets
open WordOperations
variable {A : Type*}
lemma fold_from (p xs : List A) : xs.foldl update p.sublists=(p++xs).sublists := by
  induction xs generalizing p with
  | nil=>simp
  | cons a xs ih=>
    rw [List.foldl_cons]
    change xs.foldl update (p.sublists++p.sublists.map (fun s=>s++[a]))=_
    rw [←List.sublists_concat,ih]
    simp only [List.append_assoc,List.singleton_append]
lemma fold_empty (xs : List A) : xs.foldl update [[]]=xs.sublists := by simpa using fold_from [] xs
lemma op_pack (ss : List (List (List Bool))) (a : List Bool) :
    op (pairBits ([],pairBits (a,encode (ss.map encode))))=encode ((update ss a).map encode) := by
  simp only [op,added,Fold.accum,Find.item,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    mapWith_encode,List.map_map,Function.comp_def,addLast,encode_append,update,List.map_append]
lemma length_encode_sublist (xs ys : List (List Bool)) (h : xs.Sublist ys) : (encode xs).length≤(encode ys).length := by
  induction h with
  | slnil=>rfl
  | @cons a xs ys h ih=>simp only [encode,length_cons];omega
  | @cons_cons a xs ys h ih=>simp only [encode,length_cons];omega
lemma encode_bound (ws : List (List Bool)) (B : ℕ) (h : ∀ w∈ws,w.length≤B) :
    (encode ws).length≤ws.length*(2*B+2) := by
  induction ws with
  | nil=>simp [encode]
  | cons w ws ih=>
    have hw:=h w (by simp)
    have ht:=ih (fun x hx=>h x (by simp [hx]))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
lemma subset_bound (ws : List (List Bool)) :
    (encode (ws.sublists.map encode)).length≤2^ws.length*(2*(encode ws).length+2) := by
  have h:=encode_bound (ws.sublists.map encode) (encode ws).length (by
    intro w hw
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hw
    exact length_encode_sublist s ws (List.mem_sublists.mp hs))
  simpa only [List.length_map,List.length_sublists] using h
lemma prefix_bound (ws : List (List Bool)) (j : ℕ) :
    (encode ((ws.take j).sublists.map encode)).length≤2^ws.length*(2*(encode ws).length+2) := by
  apply (subset_bound (ws.take j)).trans
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (by omega) (by simp only [List.length_take]; exact Nat.min_le_right ..)
  · have h:=length_encode_take ws j
    omega
lemma run_pack (d : ℕ) (ctx : List Bool) (ws : List (List Bool))
    (h : 2^ws.length*(2*(encode ws).length+2)≤((pairBits (ctx,encode ws)).length+1)^d) :
    run d (pairBits (ctx,encode ws))=encode (ws.sublists.map encode) := by
  unfold run
  rw [discardPrefix_pairBits]
  have hb (j : ℕ) : (encode (((ws.take j).foldl update [[]]).map encode)).length ≤ ((cap d).word (pairBits (ctx,encode ws))).length := by
    rw [fold_empty,(cap d).word_length]
    simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    exact (prefix_bound ws j).trans h
  have hh := CappedFold.run_typed (fun ss : List (List (List Bool))=>encode (ss.map encode)) id update op [] ((cap d).word (pairBits (ctx,encode ws))) op_pack [[]] ws hb
  simpa only [List.map_id,fold_empty,List.map_cons,List.map_nil,show encode ([] : List (List Bool))=[] from rfl] using hh
end MetricKMedianRecovery.BitMachine.WordList.Subsets

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

namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
variable {n : ℕ}
lemma key_sublist (U : Finset (Fin n)) (xs : List (Fin n)) (h : xs.Sublist (U.sort (·≤·))) :
    BinaryFinSet.encode xs.toFinset=WordList.encode (xs.map (fun i=>i.val.bits)) := by
  rw [BinaryFinSet.encode_eq,(List.toFinset_sort (r:=(·≤·)) (List.Nodup.sublist h (Finset.sort_nodup U (·≤·)))).mpr
    (List.Pairwise.sublist h (Finset.pairwise_sort U (·≤·)))]
lemma states_encode (U : Finset (Fin n)) :
    WordList.encode ((BlueDP.states U).map BinaryFinSet.encode)=
      WordList.encode (((U.sort (·≤·)).map (fun i=>i.val.bits)).sublists.map WordList.encode) := by
  simp only [BlueDP.states,List.sublists_map,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro xs hx
  exact key_sublist U xs (List.mem_sublists.mp hx)
lemma run_pack (d : ℕ) (ctx : List Bool) (U : Finset (Fin n))
    (hb : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤((pairBits (ctx,BinaryFinSet.encode U)).length+1)^d) :
    run d (pairBits (ctx,BinaryFinSet.encode U))=WordList.encode ((BlueDP.states U).map BinaryFinSet.encode) := by
  rw [run,BinaryFinSet.encode_eq,Subsets.run_pack]
  · exact (states_encode U).symm
  · simpa only [List.length_map,Finset.length_sort,←BinaryFinSet.encode_eq] using hb
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueProgram
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
lemma prepare_pack (d : ℕ) (extra : List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→Fin m) (q : R→Fin n→ℚ) (U : Finset (Fin m)) (c : ℕ)
    (h : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤
      ((pairBits (pack extra er B F label q U c,BinaryFinSet.encode U)).length+1)^d) :
    prepare d (pack extra er B F label q U c)=BinaryBlueLoop.pack er B F label q U c := by
  have hs : states d (pack extra er B F label q U c)=encode ((BlueDP.states U).map BinaryFinSet.encode) := by
    unfold states
    rw [show field 2 (pack extra er B F label q U c)=BinaryFinSet.encode U by
      simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some],BinaryBlueStates.run_pack d _ U h]
  unfold prepare
  rw [hs]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryBlueLoop.pack]
lemma run_pack (d : ℕ) (extra : List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→Fin m) (q : R→Fin n→ℚ) (U : Finset (Fin m)) (c : ℕ)
    (h : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤
      ((pairBits (pack extra er B F label q U c,BinaryFinSet.encode U)).length+1)^d) :
    run d (pack extra er B F label q U c)=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) (BlueDP.best (BlueDP.block B F label q) c U) := by
  rw [run,Function.comp_apply,prepare_pack d extra er B F label q U c h,BinaryBlueLoop.run_pack_s238]
end MetricKMedianRecovery.BitMachine.BinaryBlueProgram

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
section Output
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n)
    (hr : BinaryBranchCheck.Ready δ F S s colors q c m)
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\s.deleted)
local notation "score" => rationalScore δ D S Δ s
include hr in
lemma output_none (hb : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=none) (bits) :
    output δ D F S Δ s colors label q c r0 y0 bits=S := by
  classical
  unfold output
  rw [dite_eq_left hr]
  split
  · rfl
  · rename_i v xs he
    rw [hb] at he
    contradiction
lemma output_some (v : ℚ) (xs : List (BlueDP.Atom (Fin m) (Fin n) (Fin n)))
    (hb : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs)) (bits) :
    output δ D F S Δ s colors label q c r0 y0 bits=
      result δ D F S Δ s colors hr.2.1 (BlueDP.makePlan blue F label score c r0 y0 v xs hb).sel
        (BlueDP.makePlan blue F label score c r0 y0 v xs hb).dst q bits := by
  classical
  unfold output
  rw [dite_eq_left hr]
  split
  · rename_i he
    rw [hb] at he
    contradiction
  · rename_i v' xs' he
    have hh : (v',xs')=(v,xs) := Option.some.inj (he.symm.trans hb)
    cases hh
    rfl
end Output
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (q c : ℕ) (extra : List Bool) (d : ℕ)
local notation "data" => BinaryBranchContext.pack δ D F S Δ s colors label q c extra
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\RationalSampling.State.deleted s)
local notation "score" => rationalScore δ D S Δ s
lemma best_pack (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
      (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
        BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d) :
    best d data=BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc (fun i : Fin n=>i.val.bits)))
      (BlueDP.best (BlueDP.block blue F label score) c Finset.univ) := by
  rw [best,bluePack_pack_s238]
  exact BinaryBlueProgram.run_pack d extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c (by simpa using hcap)
lemma run_pack_s238_oai (r0 y0 : Fin n)
    (hcap : 2^m*(2*(BinaryFinSet.encode (Finset.univ : Finset (Fin m))).length+2)≤
      (pairBits (BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c,
        BinaryFinSet.encode (Finset.univ : Finset (Fin m)))).length.succ^d)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) :
    run d (pairBits (data,BinaryCategorical.Tape.raw (s.leaves.length*n) s.leaves.length
      (Categorical.Explicit.exponent s.leaves.length) (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length) bits))=
      BinaryFinSet.encode (output δ D F S Δ s colors label q c r0 y0 bits) := by
  classical
  rw [run,extractPrefix_pairBits,BinaryBranchCheck.run_pack_s238]
  simp only [decide_eq_true_eq]
  by_cases hr : BinaryBranchCheck.Ready δ F S s colors q c m
  · rw [ite_eq_left hr,best_pack δ D F S Δ s colors label q c extra d hcap]
    have hx : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=none ∨
        ∃ v xs,BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs) := by
      cases ht : BlueDP.best (BlueDP.block blue F label score) c Finset.univ with
      | none=>exact Or.inl rfl
      | some x=>exact Or.inr ⟨x.1,x.2,rfl⟩
    rcases hx with hb | ⟨v,xs,hb⟩
    ·
      rw [output_none δ D F S Δ s colors label q c r0 y0 hr hb]
      simp only [hb,BinaryBlueChoice.encode,ite_true, if_true]
      simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
    ·
      have hn : BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc (fun i : Fin n=>i.val.bits))) (some (v,xs))≠[] := by
        simp [BinaryBlueChoice.encode,WordList.encode,WordList.cons,pairBits]
      rw [output_some δ D F S Δ s colors label q c r0 y0 hr v xs hb]
      simp only [hb,ite_eq_right hn]
      have hp:=plan_pack_s238 δ D F S Δ s colors label q c extra d r0 y0 v xs hb hcap
      exact BinaryBranchProgram.run_pack_s238 δ D F S Δ s colors label q c extra hr.2.1 d _ _ hp bits
  · rw [ite_eq_right hr]
    rw [output,dite_eq_right hr]
    simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238_oai
