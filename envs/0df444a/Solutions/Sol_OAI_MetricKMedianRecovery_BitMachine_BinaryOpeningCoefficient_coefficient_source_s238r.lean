-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:51:07.29168+00:00
-- url     : https://prove2.me/submissions/1b9363aa-11ba-4f28-aa4f-9c660fb07f70

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L030

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

lemma activityInput_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    activityInput (pairBits (pack distance F W v z lam eta i,j.val.bits))=
      pairBits (BinaryOpeningActivity.context distance v z j,
        BinaryOpeningActivity.indices ((EffectiveOpenability.subtypeList W).map Subtype.val)) := by
  simp only [activityInput,itemField,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryOpeningActivity.context]
lemma active_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    active (pairBits (pack distance F W v z lam eta i,j.val.bits))=
      decide (EffectiveOpenability.active distance v z W j) := by
  rw [active,activityInput_pack,BinaryOpeningActivity.run_source]
  rfl
lemma distance_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (j : Fin d) :
    distance (pairBits (pack distances F W v z lam eta i,j.val.bits))=distances i j := by
  unfold distance distanceWords
  simp only [itemField,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [MetricTable.get_pack,BinaryRational.decode_encode]

end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_IndexedPaymentCoeff
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability
lemma payment_coeff_bid {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (b : Fin d) :
    (payment distances F W v z i).coeff (.inl b)=
      if active distances v z W b then if distances i b≤v*z then 1 else 0 else 0 := by
  have he : (payment distances F W v z i).coeff (.inl b)=
      ∑ j, if active distances v z W j then
        if distances i j≤v*z then (if b=j then (1:ℚ) else 0) else 0 else 0 := by
    simp only [payment,Form.sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all [Form.sub,Form.const,bid,Form.coord]
  rw [he,Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp
lemma payment_coeff_slack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (f : F) (a b : Fin d) :
    (payment distances F W v z i).coeff (.inr (f,a,b))=0 := by
  simp only [payment,Form.sum]
  apply Finset.sum_eq_zero
  intro j _
  split_ifs <;> simp_all [Form.sub,Form.const,bid,Form.coord]
lemma dual_coeff_bid {m d : ℕ} (F : Finset (Fin m)) (f : F) (a b : Fin d) :
    (Form.sum (fun j : Fin d=>slack F f a j)).coeff (.inl b)=0 := by
  simp only [Form.sum,slack,Form.coord,Sum.inl_ne_inr,ite_false, if_false,Finset.sum_const_zero]
lemma dual_coeff_slack {m d : ℕ} (F : Finset (Fin m)) (f g : F) (a b u : Fin d) :
    (Form.sum (fun j : Fin d=>slack F f a j)).coeff (.inr (g,b,u))=
      if g=f ∧ b=a then 1 else 0 := by
  simp only [Form.sum,slack,Form.coord,Sum.inr.injEq,Prod.mk.injEq]
  by_cases hf : g=f <;> by_cases ha : b=a <;> simp [hf,ha]

lemma payment_coeff {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z : ℚ) (i : Fin m) (u : Variables (Fin d) F) :
    (payment distances F W v z i).coeff u=indexedPaymentCoeff distances F W v z i u := by
  cases u with
  | inl b=>exact payment_coeff_bid distances F W v z i b
  | inr p=>exact payment_coeff_slack distances F W v z i p.1 p.2.1 p.2.2
lemma dual_coeff {m d : ℕ} (F : Finset (Fin m)) (f : F) (a : Fin d) (u : Variables (Fin d) F) :
    (Form.sum (fun j : Fin d=>slack F f a j)).coeff u=indexedDualCoeff F f a u := by
  cases u with
  | inl b=>exact dual_coeff_bid F f a b
  | inr p=>exact dual_coeff_slack F f p.1 a p.2.1 p.2.2

lemma indexedCoeff_eq {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) :
    indexedCoeff distances F W v z i r u=(forms distances F W v z lam eta i r).coeff u := by
  cases r <;> simp only [indexedCoeff,forms]
  all_goals (try split_ifs)
  all_goals (try simp only [Form.sub,Form.const,payment_coeff,dual_coeff])
  all_goals simp_all [dual,bid,slack,Form.coord,Form.sub,Form.const]
  all_goals linarith

end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IfNat
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningCoefficient
open WordList RationalLinearFeasibility RationalOpenability

lemma coefficient_indexed {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) :
    coefficient (pairBits (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,
      BinaryOpeningConstant.kindWord r),variableWord u))=
      EffectiveOpenability.indexedCoeff distances F W v z i r u := by
  have hparam (j : List Bool) : BinaryOpeningPayment.paramV
      (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,j))=v ∧
      BinaryOpeningPayment.paramZ (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,j))=z := by
    simp only [BinaryOpeningPayment.paramV,BinaryOpeningPayment.paramZ,BinaryOpeningPayment.itemField,
      Function.comp_apply,extractPrefix_pairBits,BinaryOpeningPayment.pack,BinaryOpeningPayment.field_encode,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryRational.decode_encode,and_self]
  rcases u with b|⟨g,b,c⟩ <;> cases r <;>
    simp only [coefficient,extractPrefix_pairBits,BinaryOpeningConstant.tag,
      BinaryOpeningConstant.field,Function.comp_apply,discardPrefix_pairBits,BinaryOpeningConstant.kindWord,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,Option.getD_some,value_bits] <;> norm_num only
  all_goals (try simp only [ite_true, if_true,ite_false, if_false])
  all_goals (try simp only [BinaryOpeningConstant.near,BinaryOpeningConstant.active,BinaryOpeningConstant.query,
      BinaryOpeningConstant.field,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      BinaryOpeningPayment.active_pack,BinaryOpeningPayment.distance_pack,decide_eq_true_eq,(hparam _).1,(hparam _).2])
  all_goals (try simp only [bid,slack,dual,payment,paymentNear,paymentQuery,col,row,variableWord,
      BinaryOpeningConstant.field,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
      BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      value_bits,BinaryOpeningPayment.active_pack,BinaryOpeningPayment.distance_pack,decide_eq_true_eq,
      (hparam _).1,(hparam _).2])
  all_goals (try simp only [EffectiveOpenability.indexedCoeff,EffectiveOpenability.indexedPaymentCoeff,
      EffectiveOpenability.indexedDualCoeff])
  all_goals simp [Fin.val_inj,Prod.mk.injEq]
  all_goals (try split_ifs)
  all_goals simp_all

lemma coefficient_source_s238r_oai {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) (r : Kind (Fin d) W F) (u : Variables (Fin d) F) :
    coefficient (pairBits (pairBits (BinaryOpeningPayment.pack distances F W v z lam eta i,
      BinaryOpeningConstant.kindWord r),variableWord u))=
      (EffectiveOpenability.forms distances F W v z lam eta i r).coeff u := by
  rw [coefficient_indexed,EffectiveOpenability.indexedCoeff_eq]
end BinaryOpeningCoefficient
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningCoefficient.coefficient_source_s238r_oai
