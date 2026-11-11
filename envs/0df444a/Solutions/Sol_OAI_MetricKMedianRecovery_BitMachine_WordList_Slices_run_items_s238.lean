-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:59.191243+00:00
-- url     : https://prove2.me/submissions/00f7db5e-5c27-4e07-a236-bd2a10b22b74

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SliceFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSlices
open CanonicalMergeRefinement
variable {X : Type*}
lemma fold_result (C U : List X) (V : List (List X × X × List X)) :
    U.foldl step ⟨C,U,V⟩=⟨C++U,[],V++(cuts U).map (addFront C)⟩ := by
  induction U generalizing C V with
  | nil=>simp only [List.foldl_nil,cuts,List.map_nil,List.append_nil]
  | cons a U ih=>
    simp only [List.foldl_cons,step,List.tail_cons]
    rw [ih]
    simp only [cuts,List.map_cons,List.map_map,addFront,List.append_assoc,List.singleton_append,
      Function.comp_def,List.append_nil]
    have he : addFront (C++[a])=(fun p : List X × X × List X => (C++a::p.1,p.2.1,p.2.2)) := by
      funext p
      simp only [addFront,List.append_assoc,List.singleton_append]
    rw [he]
lemma addFront_nil (p : List X × X × List X) : addFront [] p=p := by
  rcases p with ⟨C,a,T⟩
  rfl
end MetricKMedianRecovery.CanonicalSlices

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
open WordOperations CanonicalSlices
open BinaryOpeningPayment (field field_encode)

lemma itemsBits_append {X : Type*} (enc : X → List Bool) (xs ys : List X) :
    itemsBits enc (xs++ys)=itemsBits enc xs++itemsBits enc ys := by simp only [itemsBits,List.map_append,encode_append]
lemma itemsBits_cons {X : Type*} (enc : X → List Bool) (x : X) (xs : List X) :
    itemsBits enc (x::xs)=cons (enc x) (itemsBits enc xs) := rfl
lemma itemsBits_nil {X : Type*} (enc : X → List Bool) : itemsBits enc []=[] := rfl
lemma itemsBits_tail {X : Type*} (enc : X → List Bool) (xs : List X) :
    tail (itemsBits enc xs)=itemsBits enc xs.tail := by
  cases xs with
  | nil=>rfl
  | cons x xs=>exact tail_cons _ _
lemma itemsBits_tail_le {X : Type*} (enc : X → List Bool) (xs : List X) :
    (itemsBits enc xs.tail).length≤(itemsBits enc xs).length := by
  cases xs with
  | nil=>rfl
  | cons x xs=>simp only [List.tail_cons,itemsBits_cons,length_cons]; omega
lemma outBits_append {X : Type*} (enc : X → List Bool) (ps qs : List (List X × X × List X)) :
    outBits enc (ps++qs)=outBits enc ps++outBits enc qs := by simp only [outBits,List.map_append,encode_append]

lemma outBits_singleton {X : Type*} (enc : X → List Bool) (p : List X × X × List X) :
    outBits enc [p]=cons (cutBits enc p) [] := rfl

lemma step_pack {X : Type*} (enc : X → List Bool) (s : Acc X) (a : X) :
    step (pairBits ([],pairBits (enc a,accBits enc s)))=accBits enc (CanonicalSlices.step s a) := by
  simp only [step,front,rest,output,cut,sf,item,extractPrefix_pairBits,discardPrefix_pairBits,accBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,itemsBits_tail]
  simp only [CanonicalSlices.step,itemsBits_append,itemsBits_cons,itemsBits_nil,outBits_append,outBits_singleton,cutBits]

lemma Bounds.step {X : Type*} {enc : X → List Bool} {N n : ℕ} {s : Acc X} (hs : Bounds enc N n s)
    (a : X) (ha : (enc a).length≤N) : Bounds enc N (n+1) (CanonicalSlices.step s a) := by
  have ht:=(itemsBits_tail_le enc s.rest).trans hs.rest
  have hn : n*(2*N+2)≤(n+1)*(2*N+2) := Nat.mul_le_mul_right _ (Nat.le_succ n)
  refine ⟨?_,ht,?_,?_⟩
  · simp only [CanonicalSlices.step,itemsBits_append,itemsBits_cons,itemsBits_nil,List.length_append,length_cons,List.length_nil]
    have h:=hs.front
    simp only [Nat.add_mul,one_mul]
    omega
  · simp only [CanonicalSlices.step,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right hs.count 1
  · intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · exact (hs.each p hp).trans (by omega)
    · obtain rfl:=List.mem_singleton.mp hp
      simp only [cutBits,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
      have h:=hs.front
      omega
lemma Bounds.fold {X : Type*} {enc : X → List Bool} {N n : ℕ} {s : Acc X} (hs : Bounds enc N n s)
    (xs : List X) (hxs : ∀ x∈xs,(enc x).length≤N) :
    Bounds enc N (n+xs.length) (xs.foldl CanonicalSlices.step s) := by
  induction xs generalizing n s with
  | nil=>simpa only [List.foldl_nil,List.length_nil,Nat.add_zero] using hs
  | cons a xs ih=>
    simpa only [List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using
      ih (hs.step a (hxs a (List.mem_cons_self ..))) (fun x hx=>hxs x (List.mem_cons_of_mem _ hx))
lemma accBits_bound {X : Type*} {enc : X → List Bool} {N n : ℕ} {s : Acc X}
    (hs : Bounds enc N n s) (hn : n≤N) : (accBits enc s).length ≤ capacityPoly.eval N := by
  have hf := hs.front.trans (Nat.mul_le_mul_right _ hn)
  have ho := encode_le_bound (s.out.map (cutBits enc)) (2*(N*(2*N+2)+N+N)+6) (by
    intro w hw
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hw
    apply (hs.each p hp).trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) N) N)) 6)
  simp only [List.length_map] at ho
  have ho' : (outBits enc s.out).length≤N*(2*(2*(N*(2*N+2)+N+N)+6)+2) :=
    ho.trans (Nat.mul_le_mul_right _ (hs.count.trans hn))
  have hr:=hs.rest
  simp only [capacityPoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,accBits,
    length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega
lemma result_items {X : Type*} (enc : X → List Bool) (xs : List X) :
    result (itemsBits enc xs)=accBits enc ⟨xs,[],CanonicalMergeRefinement.cuts xs⟩ := by
  let N:=(itemsBits enc xs).length
  have hlen : xs.length≤N := by
    change xs.length≤(encode (xs.map enc)).length
    simpa only [List.length_map] using length_le_encode (xs.map enc)
  have hm : ∀ x∈xs,(enc x).length≤N := fun x hx=>member_length (List.mem_map.mpr ⟨x,hx,rfl⟩)
  have hs : Bounds enc N 0 (⟨[],xs,[]⟩:Acc X) :=
    ⟨by simp only [itemsBits_nil,List.length_nil,Nat.zero_mul,Nat.le_refl],le_rfl,le_rfl,by intro p hp; exact False.elim (List.not_mem_nil hp)⟩
  have ht:=CappedFold.run_typed (accBits enc) enc CanonicalSlices.step step [] (capacity.word (itemsBits enc xs))
    (step_pack enc) (⟨[],xs,[]⟩:Acc X) xs
  have heq:=ht (by
    intro n
    rw [capacity.word_length]
    apply accBits_bound
    · simpa only [Nat.zero_add] using hs.fold (xs.take n) (fun x hx=>hm x (List.mem_of_mem_take hx))
    · simp only [List.length_take]; exact (Nat.min_le_right n xs.length).trans hlen)
  change result (itemsBits enc xs)=_ at heq
  have ha : (addFront ([] : List X))=id := funext CanonicalSlices.addFront_nil
  simpa only [CanonicalSlices.fold_result,List.nil_append,ha,List.map_id] using heq
lemma run_items_s238_oai {X : Type*} (enc : X → List Bool) (xs : List X) :
    run (itemsBits enc xs)=outBits enc (CanonicalMergeRefinement.cuts xs) := by
  simp only [run,Function.comp_apply,result_items,accBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238_oai.{u_1}
