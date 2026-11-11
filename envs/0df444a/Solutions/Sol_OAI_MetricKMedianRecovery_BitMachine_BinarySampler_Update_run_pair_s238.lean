-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:04:12.703732+00:00
-- url     : https://prove2.me/submissions/1b23a2a4-d723-4054-9f71-4e1930bb5dda

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K038
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFinSet_diff_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_ball_pair_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_radius_pair_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_remove_pair_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_reference_pair_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_total_pack_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma add_pair (s : RationalSampling.State n) (w : Fin n) (R : ℚ) :
    add (pairBits (encode s,BinarySamplingReference.leafBits w R))=encode (s.add w R) := by
  simp only [add,extractPrefix_pairBits,discardPrefix_pairBits,encode,RationalSampling.State.add,
    BinaryNearestLeaf.leavesBits,List.map_append,List.map_cons,List.map_nil,encode_append]
lemma retain_pair (m : ℕ) (s : RationalSampling.State n) : retain (pairBits (m.bits,encode s))=optionBits (RationalSampling.retain m s) := by
  have he : keep (pairBits (m.bits,encode s))=decide (s.leaves.length ≤ m ∧ s.deleted.card ≤ m) := by
    simp only [keep,encode,BinaryNearestLeaf.leavesBits,BinaryFinSet.encode_eq,extractPrefix_pairBits,discardPrefix_pairBits,
      Count.run_encode,List.length_map,UnaryResources.lengthBits_eq,List.length_replicate,value_bits,Finset.length_sort]
  rw [retain,he,discardPrefix_pairBits]
  simp only [RationalSampling.retain,optionBits,decide_eq_true_eq]
  split_ifs <;> rfl

end MetricKMedianRecovery.BitMachine.BinarySamplingState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma reference_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) :
    reference (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s))=BinarySamplingState.context Δ S s := by
  simp only [reference,c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    undeleted,deleted,BinarySamplingState.encode,discardPrefix_pairBits,BinaryFinSet.diff_pack_s238,leaves,BinarySamplingState.context]
lemma oracle_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) :
    oracle (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.encode s))=BinarySamplingOracle.pack δ D S Δ s := by
  rw [oracle,reference_pair]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinarySamplingOracle.pack]
end MetricKMedianRecovery.BitMachine.BinarySampler

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Weights
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma stateInput_some (cfg : List Bool) (s : RationalSampling.State n) :
    stateInput (pairBits (cfg,BinarySamplingState.optionBits (some s)))=pairBits (cfg,BinarySamplingState.encode s) := by
  simp only [stateInput,BinarySamplingState.optionBits,Option.toList_some,List.map_cons,List.map_nil,
    extractPrefix_pairBits,discardPrefix_pairBits,encode,head_cons]
lemma state_none : BinarySamplingState.optionBits (n:=n) none=[] := rfl
lemma state_some_ne (s : RationalSampling.State n) : BinarySamplingState.optionBits (some s)≠[] := by
  simp [BinarySamplingState.optionBits,encode,WordList.cons]
end MetricKMedianRecovery.BitMachine.BinarySampler.Weights

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdateParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField )
attribute [local irreducible] BinaryMenu.radius WordList.filterWith Client.row
variable {n : ℕ}
lemma chosen_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n)
    (w : D) (e : Option (Sampling.Entry M E J)) :
    chosen (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (e.elim (Sum.inr (Sum.inl w)) (fun e=>Sum.inr (Sum.inr (w,e))))))=
      (RationalSampling.chosenId δ S Δ s w).bits := by
  cases e <;> simp only [Option.elim,chosen,input,extractPrefix_pairBits,Weights.stateInput_some,oracle_pair,actionField,
    RationalSampling.actionCode,discardPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingOracle.reference_pair_s238]
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Weights (actionField )
attribute [local irreducible] radius
variable {n : ℕ}
lemma context_some (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) :
    Weights.context (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)))=
      encode [BinarySamplingOracle.pack δ D S Δ s,BinaryRational.encode (RationalSampling.totalWeight δ D S Δ s),BinaryMenu.weights M E J,
        BinarySamplingState.optionBits (some s)] := by
  rw [Weights.context,Weights.stateInput_some,oracle_pair,BinarySamplingOracle.total_pack_s238]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,discardPrefix_pairBits]
lemma active_none (cfg ac : List Bool) : active (pairBits (pairBits (cfg,BinarySamplingState.optionBits (n:=n) none),ac))=false := by
  simp only [active,Weights.active,Weights.context,extractPrefix_pairBits,discardPrefix_pairBits,c,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Weights.state_none,decide_true,Bool.not_true,Bool.false_and]
lemma active_some (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (ac : List Bool) :
    active (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),ac))=
      decide (0<RationalSampling.totalWeight δ D S Δ s) := by
  simp only [active,extractPrefix_pairBits,context_some,Weights.active,c,extractPrefix_pairBits,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Weights.state_some_ne,decide_false,Bool.not_false,
    Bool.true_and,BinaryRational.decode_encode]
lemma old_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : D) :
    old (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=decide (RationalSampling.chosenId δ S Δ s w<n) := by
  rw [old,show RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))=RationalSampling.actionCode D M E J
    ((none : Option (Sampling.Entry M E J)).elim (Sum.inr (Sum.inl w)) (fun e=>Sum.inr (Sum.inr (w,e)))) from rfl,chosen_pair]
  simp only [input,extractPrefix_pairBits,Weights.stateInput_some,c,config,field_encode,List.getElem?_cons_zero,Option.getD_some,value_bits]
lemma add_pair (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) (s : RationalSampling.State n) (w : D)
    (e : Sampling.Entry M E J) (R : ℚ) (hr : RationalSampling.menuRadius δ D P κ m M E J s w e=some R) :
    add (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
      RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=BinarySamplingState.optionBits (RationalSampling.retain m (s.add w R)) := by
  rw [add,radius_pair_s238,hr]
  simp only [input,extractPrefix_pairBits,Weights.stateInput_some,discardPrefix_pairBits,actionField,RationalSampling.actionCode,
    field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryMenu.optBits,
    Option.toList_some,List.map_cons,List.map_nil]
  simp only [c,config,extractPrefix_pairBits,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  simp only [WordList.encode,WordList.head_cons]
  rw [show pairBits (w.val.val.bits,BinaryRational.encode R)=BinarySamplingReference.leafBits w.val R from rfl,
    BinarySamplingState.add_pair,BinarySamplingState.retain_pair]

end MetricKMedianRecovery.BitMachine.BinarySampler.Update

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Update
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma optionRadius_eq_nil (R : Option ℚ) : BinaryMenu.optBits R=[] ↔ R=none := by
  cases R with
  | none=>simp [BinaryMenu.optBits,encode]
  | some q=>simp [BinaryMenu.optBits,encode,WordList.cons]
lemma finset_eq_nil (F : Finset (Fin n)) : BinaryFinSet.encode F=[] ↔ ¬F.Nonempty := by
  have hh (xs : List (List Bool)) : encode xs=[] ↔ xs=[] := ⟨fun h=>encode_injective (show encode xs=encode [] from h),fun h=>by subst xs;rfl⟩
  rw [BinaryFinSet.encode_eq,hh]
  rw [List.map_eq_nil_iff,←List.length_eq_zero_iff,Finset.length_sort,Finset.card_eq_zero,Finset.not_nonempty_iff_eq_empty]
lemma run_pair_s238_oai (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (RationalSampling.State n)) (a : Sampling.Action D M E J) :
    run (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits s),RationalSampling.actionCode D M E J a))=
      BinarySamplingState.optionBits (RationalSampling.update δ D F S Δ P κ m M E J s a) := by
  cases s with
  | none=>rw [run,active_none];rfl
  | some s=>
    rw [run,active_some]
    simp only [decide_eq_true_eq,RationalSampling.update]
    by_cases htot : 0<RationalSampling.totalWeight δ D S Δ s
    · rw [ite_eq_left htot,ite_eq_left htot]
      rcases a with u | (w | ⟨w,e⟩)
      · cases u
        simp only [Weights.kind,Weights.actionField,discardPrefix_pairBits,RationalSampling.actionCode,field_encode,
          List.getElem?_cons_zero,Option.getD_some,value_bits,decide_true,ite_true, if_true,Weights.state_none]
      · have hk0 : Weights.kind 0 (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
            RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=false := by
          norm_num [Weights.kind,Weights.actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,value_bits,value]
        have hk1 : Weights.kind 1 (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
            RationalSampling.actionCode D M E J (Sum.inr (Sum.inl w))))=true := by
          norm_num [Weights.kind,Weights.actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,value_bits,value]
        rw [hk0,hk1]
        simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,old_pair,decide_eq_true_eq]
        by_cases h : RationalSampling.chosenId δ S Δ s w<n
        · rw [ite_eq_left h,dite_eq_left h,remove_pair_s238 δ D F S Δ P κ m M E J s w h]
        · rw [ite_eq_right h,dite_eq_right h];rfl
      · have hk0 : Weights.kind 0 (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
            RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=false := by
          norm_num [Weights.kind,Weights.actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,value_bits,value]
        have hk1 : Weights.kind 1 (pairBits (pairBits (config δ D F S Δ P κ m M E J,BinarySamplingState.optionBits (some s)),
            RationalSampling.actionCode D M E J (Sum.inr (Sum.inr (w,e)))))=false := by
          norm_num [Weights.kind,Weights.actionField,RationalSampling.actionCode,discardPrefix_pairBits,field_encode,value_bits,value]
        rw [hk0,hk1]
        simp only [Bool.false_eq_true,ite_false, if_false,radius_pair_s238,optionRadius_eq_nil]
        cases hr : RationalSampling.menuRadius δ D P κ m M E J s w e with
        | none=>simp only [ite_true, if_true,Weights.state_none]
        | some R=>
          simp only [reduceCtorEq,ite_false, if_false,ball_pair_s238 δ D F S Δ P κ m M E J s w e R hr,finset_eq_nil]
          by_cases hb : (F.filter (fun v=>δ w.val v≤R)).Nonempty
          · rw [ite_eq_right (not_not.mpr hb),ite_eq_left hb,add_pair δ D F S Δ P κ m M E J s w e R hr]
          · simp only [hb,not_false_eq_true,ite_true, if_true,ite_false, if_false,Weights.state_none]
    · rw [ite_eq_right htot,ite_eq_right htot];rfl
end MetricKMedianRecovery.BitMachine.BinarySampler.Update

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238_oai
