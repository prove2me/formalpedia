-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:17:16.218794+00:00
-- url     : https://prove2.me/submissions/06fba089-85d6-4971-a14f-b5802928e551

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L031
import Definitions.Def_Q238L049
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNodeScan_markers_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRegularChain_run_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryScan_nodes_pack_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

lemma base_F {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    field 2 (BinaryFiniteContext.pack distance loc F Q v z lam)=setBits F := by
  simp only [BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
variable {A B : Type*}

lemma walk_slots (step : A → A → Option B) (finish : A → B) (a : A) (T : List A) :
    walk step finish a T=(firstPresent (slots step a T)).getD (finish (finalNode a T)) := by
  induction T generalizing a with
  | nil=>rfl
  | cons b T ih=>
    simp only [walk,slots,finalNode]
    cases step a b <;> simp only [firstPresent,Option.getD_some,ih]

lemma firstPresent_append_none (L : List (Option B)) : firstPresent (L++[none])=firstPresent L := by
  induction L with
  | nil=>rfl
  | cons h L ih=>cases h <;> simp only [List.cons_append,firstPresent,ih]
lemma finalNode_reverse (a : A) (T : List A) : ((a::T).reverse.head?)=some (finalNode a T) := by
  induction T generalizing a with
  | nil=>rfl
  | cons b T ih=>
    rw [List.reverse_cons]
    change ((b::T).reverse++[a]).head?=some (finalNode b T)
    rw [List.head?_append]
    rw [ih]
    rfl

variable {X : Type*} [DecidableEq X]
lemma scan_walk (F Q : Finset X) (k : ℕ) (complete : Finset X → List (List X)) (U : List (List X))
    (H : List X) (T : List (List X)) (S : List (List X)) :
    scan F Q k complete U H T S=walk (transition F Q k) (fun p=>.common p.1 p.2 U)
      (H,T) (S.map (fun J=>(J,complete (Q∪J.toFinset)))) := by
  induction S generalizing H T with
  | nil=>rfl
  | cons J S ih=>
    simp only [scan,List.map_cons,walk,transition]
    split_ifs <;> simp only [ih]
end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.FirstPresent
open WordOperations
open CanonicalMergeCrossing
lemma find_markers {A : Type*} (enc : A → List Bool) (os : List (Option A)) :
    ((os.map (marker enc)).find? (fun b=>!decide (b=[])))=
      (firstPresent os).map (fun a=>true::enc a) := by
  induction os with
  | nil=>rfl
  | cons o os ih=>
    cases o <;> simp only [List.map_cons,marker,Option.map_none,Option.map_some,Find.optionEncode,
      List.find?_cons,List.cons_ne_nil,decide_false,decide_true,Bool.not_false,Bool.not_true,
      firstPresent,ih]
lemma run_pack {A : Type*} (enc : A → List Bool) (fallback : A) (os : List (Option A)) :
    run (pairBits (enc fallback,encode (os.map (marker enc))))=
      enc ((firstPresent os).getD fallback) := by
  have hf : found (pairBits (enc fallback,encode (os.map (marker enc))))=
      Find.optionEncode ((firstPresent os).map (fun a=>true::enc a)) := by
    simp only [found,discardPrefix_pairBits,Find.run_encode,present,find_markers]
  rw [run,hf,extractPrefix_pairBits]
  cases firstPresent os <;> rfl
end MetricKMedianRecovery.BitMachine.WordList.FirstPresent

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryCross.transition
lemma head_encode_of_head {A : Type*} (enc : A → List Bool) (xs : List A) (a : A) (h : xs.head?=some a) :
    head (encode (xs.map enc))=enc a := by
  cases xs with
  | nil=>simp only [List.head?_nil,reduceCtorEq] at h
  | cons b T=>
    simp only [List.head?_cons,Option.some.injEq] at h
    subst b
    exact head_cons _ _
lemma fallback_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (a : List (Label (Fin m)) × List (List (Label (Fin m))))
    (T : List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    fallback (pack F Q k U (a::T))=resultBits (.common (finalNode a T).1 (finalNode a T).2 U) := by
  simp only [fallback,lastNode,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,reverse_encode,←List.map_reverse]
  rw [head_encode_of_head nodeBits _ _ (finalNode_reverse a T)]
  rfl
lemma run_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (a : List (Label (Fin m)) × List (List (Label (Fin m))))
    (T : List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    run (pack F Q k U (a::T))=resultBits (walk (transition F Q k) (fun p=>.common p.1 p.2 U) a T) := by
  rw [run,fallback_pack,markers_pack_s238r,FirstPresent.run_pack,firstPresent_append_none,walk_slots]
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ScanMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryScan
open WordOperations WordList RationalLeaves CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation BinaryNodeScan.run
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (k n q : ℕ)
    (U : List (List (Label (Fin m)))) (H : List (Label (Fin m))) (T S : List (List (Label (Fin m)))) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) F Q k n q U H T S)=
      resultBits (scan F Q k (FiniteLabelContinuation.continuation loc (rows distance) F v lam q n) U H T S) := by
  simp only [run,Function.comp_apply,scanInput,nodes_pack_s238r]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [scan_walk]
  exact BinaryNodeScan.run_pack F Q k U (H,T) _
end MetricKMedianRecovery.BitMachine.BinaryScan

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegularChain.run BinaryScan.run
lemma chainInput_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key spare k n q : ℕ) (H G : List (Label (Fin m)))
    (T U : List (List (Label (Fin m)))) :
    chainInput (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare k n q H G T U)=
      BinaryRegularChain.pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare (BinaryLabel.orderedSort F) H G := by
  simp only [chainInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRegular.base_F,BinaryRegularChain.pack,setBits,BinaryLabel.orderedSort]
lemma crossCtx_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key spare k n q : ℕ) (H G : List (Label (Fin m)))
    (T U : List (List (Label (Fin m)))) :
    crossCtx (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare k n q H G T U)=BinaryCross.ctxBits F Q k := by
  simp only [crossCtx,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryFiniteContext.pack,BinaryCross.ctxBits]
lemma run_pack_s238r_oai {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v lam : ℚ) (eta : ℝ) (key spare k n q : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) ((1+v^2)^q:ℚ) lam
      (FiniteLabelContinuation.complete loc (rows distance) F v ((1+v^2)^q) lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H) (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v ((1+v^2)^q) lam) key spare k n q H G T U)=
      BinaryCross.resultBits (FiniteLabelCrossing.run loc (rows distance) F Q v lam q n k (copy key) (copy spare) H G T U) := by
  have hz : (((1+v^2)^q:ℚ):ℝ)=(1+(v:ℝ)^2)^q := by push_cast; rfl
  have hh:=BinaryRegularChain.run_pack_s238r distance loc F B Q v ((1+v^2)^q) lam eta key spare (BinaryLabel.orderedSort F) hc
    hv hvsmall (by rw [hz]; positivity) hlam heta hQ hdis (by simpa only [hz] using hrow) hfresh hco H G hHr hGr
    (by simpa only [hz] using hH) (by simpa only [hz] using hG)
  simp only [run,Function.comp_apply,scanInput,chainInput_pack,crossCtx_pack,hh]
  simp only [nextQ,firstNode,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  change BinaryScan.run (BinaryScan.pack (BinaryFiniteContext.pack distance loc F Q v ((1+v^2)^q) lam) F Q k n (q+1)
    U H T (CanonicalMergeRefinement.regularChain F (BinaryLabel.orderedSort F)
      (FiniteLabelContinuation.complete loc (rows distance) F v ((1+v^2)^q) lam) Q (copy key) (copy spare) H G))=_
  exact BinaryScan.run_pack distance loc F Q v ((1+v^2)^q) lam k n (q+1) U H T _
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238r_oai
