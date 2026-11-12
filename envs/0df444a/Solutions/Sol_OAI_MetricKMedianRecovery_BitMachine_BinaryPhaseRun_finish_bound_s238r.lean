-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:15:05.3214+00:00
-- url     : https://prove2.me/submissions/9f8bdef7-3deb-4a80-b359-1dbd288cd4c9

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L051
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_bids_context_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_eligible_context_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
lemma encode_length (z : ℤ) : (encode z).length=z.natAbs.size+1 := by
  simp only [encode,List.length_cons,Nat.size_eq_bits_len]
end Signed
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
namespace BinaryRational
lemma encode_length (q : ℚ) : (encode q).length=2*(q.num.natAbs.size+1)+1+q.den.size := by
  simp only [encode,pairBits_length,Signed.encode_length,←Nat.size_eq_bits_len]
lemma encode_height {q : ℚ} {b : ℕ} (hq : RationalHeight.Height q b) :
    (encode q).length≤3*b+6 := by
  have hn := Nat.size_le_size hq.1
  have hd := Nat.size_le_size hq.2
  rw [Nat.size_pow] at hn hd
  rw [encode_length]
  omega
end BinaryRational
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer OpenabilityLinearization

lemma update_get {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (e : Event m d) (j : Fin d) :
    (update distance v s e).budget[j] =
      if active distance v s.phase s.opened j then e.bid[j] else s.budget[j] := by
  simp only [update,Fin.getElem_fin,Vector.getElem_ofFn]

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (todo : List (Fin m)) :
    run (pairBits (context distance F W v z lam,BinaryOpeningActivity.indices todo))=
      resultBits (RationalPhase.first distance F W v z lam todo) := by
  have chooseEq (todo : List (Fin m)) : chosen (pairBits (context distance F W v z lam,
      BinaryOpeningActivity.indices todo))=Find.optionEncode
        ((todo.find? (fun i=>decide (i∈F ∧ i∉W ∧ storedOpening distance F W v z lam 0 i≠none))).map (fun i=>i.val.bits)) := by
    simp only [chosen,BinaryOpeningActivity.indices,Find.run_encode,List.find?_map,Function.comp_def,eligible_context_s238r]
  induction todo with
  | nil=>simp [run,chooseEq,resultBits,RationalPhase.first,Find.optionEncode]
  | cons i todo ih=>
    by_cases hi : i∈F ∧ i∉W
    · cases ha : storedOpening distance F W v z lam 0 i with
      | none=>
        simp only [RationalPhase.first,ite_eq_left hi,ha] at ⊢
        rw [← ih]
        simp only [run,chosenQuery,chooseEq]
        simp only [List.find?_cons,ha,ne_eq,not_true_eq_false,and_false,decide_false]
        simp only [extractPrefix_pairBits]
      | some a=>
        have he : chosen (pairBits (context distance F W v z lam,BinaryOpeningActivity.indices (i::todo)))=true::i.val.bits := by
          rw [chooseEq]
          simp [hi.1,hi.2,ha,Find.optionEncode]
        simp only [run,he,List.cons_ne_nil,ite_false, if_false,List.tail_cons,chosenQuery,extractPrefix_pairBits,
          bids_context_s238r distance F W v z lam i a ha,RationalPhase.first,ite_eq_left hi,ha,resultBits,eventBits,
          Fin.getElem_fin,Vector.getElem_ofFn]
    · simp only [RationalPhase.first,ite_eq_right hi]
      rw [← ih]
      simp only [run,chosenQuery,chooseEq,extractPrefix_pairBits]
      have hf : ¬(i∈F ∧ i∉W ∧ storedOpening distance F W v z lam 0 i≠none) := fun h=>hi ⟨h.1,h.2.1⟩
      simp only [List.find?_cons,decide_eq_false hf]
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Answer
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate

lemma member_length_le (ws : List (List Bool)) {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>simp only [List.not_mem_nil] at hw
  | cons a ws ih=>
    simp only [encode,length_cons]
    rcases List.mem_cons.mp hw with h|h
    · subst w; omega
    · have hh:=ih h; omega
lemma indices_length {m : ℕ} (fs : List (Fin m)) (hl : fs.length ≤ m) :
    (BinaryOpeningActivity.indices fs).length ≤ m*(2*m+2) := by
  apply (encode_le_bound (fs.map (fun i=>i.val.bits)) m (by
    intro w hw
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hw
    exact (Indices.bits_length_le i.val).trans (Nat.le_of_lt i.isLt))).trans
  simpa only [List.length_map] using Nat.mul_le_mul_right (2*m+2) hl
lemma finset_indices_length {m : ℕ} (W : Finset (Fin m)) :
    (BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val)).length ≤ m*(2*m+2) := by
  apply indices_length
  simp only [List.length_map,subtypeList,List.length_ofFn]
  exact (Finset.card_le_univ W).trans_eq (Fintype.card_fin m)
lemma context_length_change {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W W' : Finset (Fin m))
    (v z lam : ℚ) :
    (BinaryPhaseFirst.context distance F W' v z lam).length≤
      (BinaryPhaseFirst.context distance F W v z lam).length+2*m*(2*m+2) := by
  have hh:=finset_indices_length W'
  simp only [BinaryPhaseFirst.context,length_encode,List.map_cons,List.sum_cons,List.length_cons,
    List.map_nil,List.sum_nil,List.length_nil]
  nlinarith
lemma dimensions {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : m≤(stateBits distance F v lam s).length ∧ d≤(stateBits distance F v lam s).length := by
  have hm := length_le_encode (List.ofFn (fun i : Fin m=>RationalMatrix.rowEncode (distance i)))
  have h0 := member_length_le [Rectangular.encode distance,
      BinaryOpeningActivity.indices ((subtypeList s.opened).map Subtype.val),BinaryRational.encode v,
      BinaryRational.encode s.phase,BinaryRational.encode lam,BinaryRational.encode 0,[],
      List.replicate d true,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)]
      (w:=Rectangular.encode distance) (by simp only [List.mem_cons, true_or])
  have hd := length_le_encode (List.ofFn (fun j : Fin d=>BinaryRational.encode s.budget[j]))
  simp only [List.length_ofFn] at hm hd
  change _≤(BinaryPhaseFirst.context distance F s.opened v s.phase lam).length at h0
  change m≤(Rectangular.encode distance).length at hm
  simp only [stateBits,pairBits_length,RationalMatrix.rowEncode_eq]
  constructor <;> omega
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
lemma ctx_bound {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v lam : ℚ) (s : State m d) :
    (BinaryPhaseFirst.context distance F W v s.phase lam).length ≤
      (stateBits distance F v lam s).length+2*(stateBits distance F v lam s).length*(2*(stateBits distance F v lam s).length+2) := by
  let L := (stateBits distance F v lam s).length
  have hm := (dimensions distance F v lam s).1
  have hc := context_length_change distance F s.opened W v s.phase lam
  have ho : (BinaryPhaseFirst.context distance F s.opened v s.phase lam).length ≤ L := by
    simp only [L,stateBits,pairBits_length]; omega
  have hmul := Nat.mul_le_mul hm (show 2*m+2 ≤ 2*L+2 by omega)
  change (BinaryPhaseFirst.context distance F W v s.phase lam).length ≤ L+2*L*(2*L+2)
  nlinarith
lemma first_bid_bound {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (e : Event m d)
    (he : first distance F W v s.phase lam (List.ofFn (fun i : Fin m=>i))=some e) (j : Fin d) :
    (BinaryRational.encode e.bid[j]).length ≤ bidPoly.eval (stateBits distance F v lam s).length := by
  let L := (stateBits distance F v lam s).length
  let q := pairBits (BinaryPhaseFirst.context distance F W v s.phase lam,
    BinaryOpeningActivity.indices (List.ofFn (fun i : Fin m=>i)))
  have hm := (dimensions distance F v lam s).1
  have hc := ctx_bound distance F W v lam s
  have hi := indices_length (List.ofFn (fun i : Fin m=>i)) (by simp only [List.length_ofFn,Nat.le_refl])
  have hmul := Nat.mul_le_mul hm (show 2*m+2 ≤ 2*L+2 by omega)
  have hq : q.length ≤ 20*(L+1)^2 := by
    simp only [q,pairBits_length]
    change (BinaryPhaseFirst.context distance F W v s.phase lam).length ≤ L+2*L*(2*L+2) at hc
    nlinarith
  have hout := BinaryPhaseFirst.run_computes.length_bound q
  have hp := polynomial_monotone BinaryPhaseFirst.run_computes.lengthPolynomial hq
  have heq : BinaryPhaseFirst.run q=true::BinaryPhaseFirst.eventBits e := by
    simp only [q,BinaryPhaseFirst.run_pack,he,BinaryPhaseFirst.resultBits]
  rw [heq] at hout
  have hj := member_length_le (List.ofFn (fun j : Fin d=>BinaryRational.encode e.bid[j]))
    (w:=BinaryRational.encode e.bid[j]) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  simp only [List.length_cons,BinaryPhaseFirst.eventBits,pairBits_length,RationalMatrix.rowEncode_eq] at hout
  simp only [bidPoly,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ BinaryPhaseFirst.run_computes.lengthPolynomial.eval (20*(L+1)^2)
  have hr : (encode (List.ofFn (fun j : Fin d=>BinaryRational.encode e.bid[j]))).length ≤ BinaryPhaseFirst.run_computes.lengthPolynomial.eval q.length := by omega
  exact hj.trans (hr.trans hp)
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

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
lemma change_phase_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (z : ℚ) :
    (stateBits distance F v lam {s with phase:=z}).length ≤
      (stateBits distance F v lam s).length+4*(BinaryRational.encode z).length := by
  simp only [stateBits,pairBits_length,BinaryPhaseFirst.context,length_encode,List.map_cons,List.sum_cons,
    List.length_cons,List.map_nil,List.sum_nil,List.length_nil]
  omega
lemma reference_length {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (z : ℚ) (hz : Height z (3*(N+1)^2)) :
    (stateBits distance F v lam {s with phase:=z}).length ≤ 100*(N+1)^2 := by
  have h := change_phase_length distance F v lam s z
  have hh := BinaryRational.encode_height hz
  nlinarith
lemma bid_bound {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (z : ℚ) (hz : Height z (3*(N+1)^2)) (e : Event m d)
    (he : first distance F W v z lam (List.ofFn (fun i : Fin m=>i))=some e) (j : Fin d) :
    (BinaryRational.encode e.bid[j]).length ≤ bidBound.eval N := by
  have hh := first_bid_bound distance F W v lam {s with phase:=z} e he j
  have hp := polynomial_monotone BinaryPhaseFinish.bidPoly (reference_length distance F v lam s hL z hz)
  exact (hh.trans hp).trans_eq (by simp only [bidBound,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one])
lemma finish_bound_s238r_oai {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (fuel : ℕ) (t : State m d) (hz : Height t.phase (3*(N+1)^2))
    (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤ budgetBound.eval N) :
    (finish distance F v lam fuel t).1.phase=t.phase ∧
    ∀ j : Fin d,(BinaryRational.encode (finish distance F v lam fuel t).1.budget[j]).length ≤ budgetBound.eval N := by
  induction fuel generalizing t with
  | zero=>exact ⟨rfl,hb⟩
  | succ fuel ih=>
    cases he : first distance F t.opened v t.phase lam (List.ofFn (fun i : Fin m=>i)) with
    | none=>simpa only [finish,he] using And.intro (rfl : t.phase=t.phase) hb
    | some e=>
      simp only [finish,he]
      apply ih (update distance v t e) hz
      intro j
      rw [update_get]
      split_ifs
      · have hh := bid_bound distance F t.opened v lam s hL t.phase hz e he j
        simp only [budgetBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
          Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_one]
        omega
      · exact hb j
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238r_oai
