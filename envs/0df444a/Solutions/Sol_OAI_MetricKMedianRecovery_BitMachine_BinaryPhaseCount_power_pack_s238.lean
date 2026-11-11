-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:14:16.05517+00:00
-- url     : https://prove2.me/submissions/6ebbd67f-f044-4257-ad6f-a6c711dfee57

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningNearest_run_source_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFinish_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_run_length_bound_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

lemma rowEncode_eq {n : ℕ} (v : Fin n → ℚ) :
    rowEncode v=WordList.encode (List.ofFn (fun i=>BinaryRational.encode (v i))) := by
  simp only [rowEncode,RationalArray.encode,List.map_ofFn,Function.comp_def]

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_KindRows
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability

section
open RationalOpenability
variable {D W F : Type*}

lemma mem_subtypeList {m : ℕ} (F : Finset (Fin m)) (f : F) : f∈subtypeList F := by
  exact List.mem_ofFn.mpr ⟨(F.orderIsoOfFin rfl).symm f,by simp⟩

end

open RationalOpenability OpenabilityLinearization

end MetricKMedianRecovery.EffectiveOpenability

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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace MetricTable
open WordList

lemma get_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (f : Fin m) (j : Fin d) :
    get (pairBits (pairBits (Rectangular.encode distance,f.val.bits),j.val.bits))=
      BinaryRational.encode (distance f j) := by
  simp only [get,getRow,context,row,col,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,Rectangular.encode,lookup_ofFn,
    RationalMatrix.rowEncode_eq]
end MetricTable
namespace BinaryOpeningActivity
open WordList

lemma fails_context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (f : Fin m) :
    fails (pairBits (context distance v z j,f.val.bits))=decide ((1-3*v)*distance f j≤z) := by
  unfold fails distanceWord
  simp only [table,client,paramV,paramZ,context,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryRational.decode_encode]
  rw [MetricTable.get_pack,BinaryRational.decode_encode]
lemma optionEncode_nil_iff (o : Option (List Bool)) : Find.optionEncode o=[] ↔ o=none := by
  cases o <;> simp [Find.optionEncode]
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (fs : List (Fin m)) :
    run (pairBits (context distance v z j,indices fs))=
      [decide (∀ f∈fs,z<(1-3*v)*distance f j)] := by
  unfold run indices
  rw [Find.run_encode]
  congr 1
  apply decide_eq_decide.mpr
  rw [optionEncode_nil_iff,List.find?_eq_none]
  simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,fails_context,
    Bool.not_eq_true,decide_eq_false_iff_not,not_le]
lemma run_source {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (W : Finset (Fin m)) :
    run (pairBits (context distance v z j,
      indices ((EffectiveOpenability.subtypeList W).map Subtype.val)))=
      [decide (EffectiveOpenability.active distance v z W j)] := by
  rw [run_pack]
  congr 1
  apply decide_eq_decide.mpr
  simp only [EffectiveOpenability.active,List.mem_map,forall_exists_index,and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h f hf
    exact h ⟨f,hf⟩ (EffectiveOpenability.mem_subtypeList W ⟨f,hf⟩)
  · intro h f _
    exact h f.val f.property
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_Clipped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

lemma advance_get {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (j : Fin d) :
    (advance distance v s).budget[j] = if active distance v s.phase s.opened j then
      clipped distance v ((1+v^2)*s.phase) s.opened j else s.budget[j] := by
  simp only [advance,Fin.getElem_fin,Vector.getElem_ofFn]

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic WordList
namespace BinaryPhaseAdvance
open EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment

lemma parameters_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) :
    paramV (stateBits distance F v lam s)=v ∧ paramZ (stateBits distance F v lam s)=s.phase ∧
    phase (stateBits distance F v lam s)=(1+v^2)*s.phase := by
  simp only [paramV,paramZ,phase,sf,Function.comp_apply,stateBits,extractPrefix_pairBits,
    BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.decode_encode,pow_two,and_self]
lemma activityInput_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    BinaryOpeningPayment.activityInput (query (pairBits (stateBits distance F v lam s,j.val.bits)))=
      pairBits (BinaryOpeningActivity.context distance v s.phase j,
        BinaryOpeningActivity.indices ((subtypeList s.opened).map Subtype.val)) := by
  simp only [BinaryOpeningPayment.activityInput,query,itemField,Function.comp_apply,stateBits,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryPhaseFirst.context,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryOpeningActivity.context]
lemma isActive_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    isActive (pairBits (stateBits distance F v lam s,j.val.bits))=decide (EffectiveOpenability.active distance v s.phase s.opened j) := by
  simp only [isActive,BinaryOpeningPayment.active,activityInput_pack,BinaryOpeningActivity.run_source,
    List.head?_cons,Option.getD_some]
lemma nearest_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    nearest (pairBits (stateBits distance F v lam s,j.val.bits))=RationalOpenability.nearest distance s.opened j := by
  simp only [nearest,activityInput_pack,BinaryOpeningNearest.run_source_s238,BinaryRational.decode_encode]
lemma opened_nil {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : sf 1 (stateBits distance F v lam s)=[] ↔ ¬s.opened.Nonempty := by
  have hn (ws : List (List Bool)) : encode ws=[] ↔ ws=[] := by
    cases ws with
    | nil=>simp only [encode]
    | cons w ws=>simp only [encode,cons_ne_nil,List.cons_ne_nil]
  simp only [sf,Function.comp_apply,stateBits,extractPrefix_pairBits,BinaryPhaseFirst.context,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryOpeningActivity.indices,hn,
    ←List.length_eq_zero_iff,List.length_map,subtypeList,List.length_ofFn,
    Finset.not_nonempty_iff_eq_empty,Finset.card_eq_zero]
lemma clippedItem_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    clippedItem (pairBits (stateBits distance F v lam s,j.val.bits))=
      clipped distance v ((1+v^2)*s.phase) s.opened j := by
  simp only [clippedItem,extractPrefix_pairBits,opened_nil,parameters_pack,nearest_pack,clipped]
  split_ifs <;> simp_all
lemma budgetItem_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    budgetItem (pairBits (stateBits distance F v lam s,j.val.bits))=BinaryRational.encode (advance distance v s).budget[j] := by
  rw [budgetItem,isActive_pack,clippedItem_pack]
  simp only [stateBits,extractPrefix_pairBits,discardPrefix_pairBits,RationalMatrix.rowEncode_eq,lookup_ofFn,
    advance_get,decide_eq_true_eq,apply_ite]
  split_ifs <;> rfl
lemma budget_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : budget (stateBits distance F v lam s)=
      RationalMatrix.rowEncode (fun j=>(advance distance v s).budget[j]) := by
  have hc : BinaryOpeningEnumeration.clients (extractPrefix (stateBits distance F v lam s))=
      encode (List.ofFn (fun j : Fin d=>j.val.bits)) := by
    simp only [stateBits,extractPrefix_pairBits,BinaryOpeningEnumeration.clients,Function.comp_apply,
      BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      BinaryEllipsoidInitial.indices_replicate_s238]
  simp only [budget,hc,mapWith_ofFn,budgetItem_pack,RationalMatrix.rowEncode_eq]
lemma context_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : context (stateBits distance F v lam s)=
      BinaryPhaseFirst.context distance F s.opened v ((1+v^2)*s.phase) lam := by
  rw [context,(parameters_pack distance F v lam s).2.2]
  simp only [sf,Function.comp_apply,stateBits,extractPrefix_pairBits,BinaryPhaseFirst.context,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : run (stateBits distance F v lam s)=stateBits distance F v lam (advance distance v s) := by
  rw [run,context_pack,budget_pack]
  rfl
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Fuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
lemma fuel_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : fuel (stateBits distance F v lam s)=List.replicate F.card true := by
  simp only [fuel,BinaryPhaseAdvance.sf,Function.comp_apply,stateBits,extractPrefix_pairBits,
    BinaryPhaseFirst.context,BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryOpeningActivity.indices,Count.run_encode,List.length_map,subtypeList,List.length_ofFn]
lemma completed_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : completed (stateBits distance F v lam s)=
      stateBits distance F v lam (finish distance F v lam F.card s).1 := by
  rw [completed,fuel_pack,BinaryPhaseFinish.run_pack_s238]
lemma step_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : step (stateBits distance F v lam s)=
      stateBits distance F v lam (advance distance v (finish distance F v lam F.card s).1) := by
  rw [step,Function.comp_apply,completed_pack,BinaryPhaseAdvance.run_pack]
lemma iterate_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) :
    step^[q] (stateBits distance F v lam s)=stateBits distance F v lam (RationalPhase.run distance F v lam q s).1 := by
  induction q generalizing s with
  | zero=>rfl
  | succ q ih=>rw [Function.iterate_succ_apply,step_pack,ih]; rfl
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight
open BinaryPhaseFinish
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) :
    run (pairBits (List.replicate q true,stateBits distance F v lam s))=
      stateBits distance F v lam (RationalPhase.run distance F v lam q s).1 := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [BoundedIteration.run_eq]
  · simp only [List.length_replicate,iterate_pack]
  · intro j hj
    rw [iterate_pack,cap.word_length]
    apply run_length_bound_s238
    · simp only [pairBits_length,List.length_replicate]; omega
    · simp only [List.length_replicate] at hj
      simp only [pairBits_length,List.length_replicate]; omega
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability

lemma finish_phase {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) : (finish distance F v lam q s).1.phase=s.phase := by
  induction q generalizing s with
  | zero=>rfl
  | succ q ih=>
    cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simp only [finish,he]
    | some e=>simp only [finish,he,ih,update]
lemma run_phase {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) : (run distance F v lam q s).1.phase=(1+v^2)^q*s.phase := by
  induction q generalizing s with
  | zero=>simp only [run,pow_zero,one_mul]
  | succ q ih=>
    simp only [run,ih,advance,finish_phase,pow_succ]
    ring
end MetricKMedianRecovery.RationalPhase
namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.map WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run BinaryPhaseRun.run
lemma powerInput_pack (v : ℚ) : powerInput (BinaryRational.encode v)=
    stateBits (fun i : Fin 0=>i.elim0) ∅ v 0 (dummy v) := by
  simp only [powerInput,stateBits,dummy,BinaryPhaseFirst.context,Rectangular.encode,
    List.ofFn_zero,BinaryOpeningActivity.indices,subtypeList,Finset.card_empty,List.map_nil,
    encode,RationalMatrix.rowEncode_eq,List.replicate_zero]
lemma phase_field {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : BinaryPhaseAdvance.sf 3 (stateBits distance F v lam s)=BinaryRational.encode s.phase := by
  simp only [BinaryPhaseAdvance.sf,Function.comp_apply,stateBits,extractPrefix_pairBits,BinaryPhaseFirst.context,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma power_pack_s238_oai (v : ℚ) (q : ℕ) : power (pairBits (List.replicate q true,BinaryRational.encode v))=
    BinaryRational.encode ((1+v^2)^q) := by
  simp only [power,extractPrefix_pairBits,discardPrefix_pairBits,powerInput_pack,BinaryPhaseRun.run_pack,
    phase_field,run_phase,dummy,mul_one]
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238_oai
