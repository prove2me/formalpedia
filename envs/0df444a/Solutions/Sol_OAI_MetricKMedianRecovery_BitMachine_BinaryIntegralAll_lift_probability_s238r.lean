-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:21:12.957908+00:00
-- url     : https://prove2.me/submissions/1284b35d-d429-47f1-af12-ae0a34e18f9c

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L012
import Definitions.Def_Q238L054
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralDispatch_run_output_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryOpeningActivity
open WordList

lemma optionEncode_nil_iff (o : Option (List Bool)) : Find.optionEncode o=[] ↔ o=none := by
  cases o <;> simp [Find.optionEncode]
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
namespace RationalMin
open WordList

lemma fold_lower (qs : List ℚ) (a u : ℚ) (ha : u≤a) (hq : ∀ q∈qs,u≤q) : u≤qs.foldl min a := by
  induction qs generalizing a with
  | nil=>exact ha
  | cons q qs ih=>
    rw [List.foldl_cons]
    exact ih (min a q) (le_min ha (hq q (by simp))) (by intro r hr; exact hq r (by simp [hr]))
lemma fold_le_init (qs : List ℚ) (a : ℚ) : qs.foldl min a≤a := by
  induction qs generalizing a with
  | nil=>exact le_rfl
  | cons q qs ih=>exact (ih (min a q)).trans (min_le_left a q)
lemma fold_le_mem (qs : List ℚ) (a q : ℚ) (hq : q∈qs) : qs.foldl min a≤q := by
  induction qs generalizing a with
  | nil=>simp only [List.not_mem_nil] at hq
  | cons r rs ih=>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hq with rfl|hq
    · exact (fold_le_init rs (min a q)).trans (min_le_right a q)
    · exact ih (min a r) hq
lemma minimum_lower (qs : List ℚ) (u : ℚ) (hne : qs≠[]) (hu : ∀q∈qs,u≤q) : u ≤ minimum qs := by
  cases qs with
  | nil=>exact (hne rfl).elim
  | cons q qs=>
    apply fold_lower
    · exact hu q (by simp)
    · exact hu
lemma minimum_le_mem (qs : List ℚ) (q : ℚ) (hq : q∈qs) : minimum qs≤q := fold_le_mem qs _ q hq
end RationalMin
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
lemma contains_pack (a : ℕ) (xs : List ℕ) : contains (pairBits (a.bits,pack xs))=decide (a∈xs) := by
  simp only [contains,BinaryPhaseFirst.contains,Find.run_encode]
  apply decide_eq_decide.mpr
  simp only [ne_eq,BinaryOpeningActivity.optionEncode_nil_iff,List.find?_eq_none,List.mem_map,
    forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,BinaryPhaseFirst.natEq,
    extractPrefix_pairBits,discardPrefix_pairBits,value_bits,decide_eq_true_eq,not_forall,exists_prop,not_not]
  exact ⟨fun ⟨b,hb,he⟩=>he ▸ hb,fun ha=>⟨a,ha,rfl⟩⟩
end MetricKMedianRecovery.BitMachine.BinaryNatSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : average X ≤ average Y :=
  Finset.expect_le_expect (fun ω _ => h ω)

end Average

section Probability
variable {Ω : Type*} [Fintype Ω]

lemma probability_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    probability P ≤ probability Q := by
  classical
  apply average_mono
  intro ω
  split_ifs with hp hq hq <;> try norm_num
  exact absurd (h ω hp) hq

end Probability

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Virtual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [DecidableEq V] in
lemma distanceTo_le {S : Finset V} (hS : S.Nonempty) (x : V) {s : V} (hs : s ∈ S) :
    distanceTo S hS x ≤ dist x s := Finset.inf'_le _ hs

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSetDecode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma decode_encode (S : Finset (Fin n)) : decode n (encode S)=S := by
  classical
  ext i
  simp only [decode,encode,BinaryNatSet.encode,BinaryNatSet.contains_pack,Finset.mem_filter,
    Finset.mem_univ,true_and,decide_eq_true_eq,Finset.mem_sort,values,Finset.mem_image]
  exact ⟨fun ⟨j,hj,he⟩=>Fin.val_injective he ▸ hj,fun hi=>⟨i,hi,rfl⟩⟩
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
lemma map_enum {β : Type*} (S : Finset α) (f : α→β) :
    (S.sort (·≤·)).map f=List.ofFn (fun i=>f (enum S i)) := by rw [←enum_list,List.map_ofFn]; rfl
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFairCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α β : Type*} [LinearOrder α] [AddCommMonoid β]
lemma sum_enum (S : Finset α) (f : α→β) : (∑ i:Fin S.card,f (enum S i))=∑ x∈S,f x := by
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ enum S)).sum = _
  rw [←List.map_ofFn,enum_list,←List.sum_toFinset f (S.sort_nodup (·≤·)),Finset.sort_toFinset]
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricCost
open WordOperations WordList
variable {n : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma connection_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (S : Finset (Fin n)) (hS : S.Nonempty) (x : Fin n) :
    (connection δ S x:ℝ)=Completion.distanceTo S hS x := by
  have he : List.ofFn (fun j:Fin S.card=>δ x (SortedIndex.enum S j))=(S.sort (·≤·)).map (δ x) :=
    (SortedIndex.map_enum S (δ x)).symm
  have hne : (S.sort (·≤·)).map (δ x)≠[] := by
    intro hem
    have hl:=congrArg List.length hem
    simp only [List.length_map,Finset.length_sort,List.length_nil] at hl
    exact hS.card_pos.ne' hl
  rw [connection,he]
  apply le_antisymm
  · apply Finset.le_inf'
    intro y hy
    rw [←hδ x y]
    exact_mod_cast RationalMin.minimum_le_mem ((S.sort (·≤·)).map (δ x)) (δ x y)
      (List.mem_map.mpr ⟨y,(Finset.mem_sort (·≤·)).mpr hy,rfl⟩)
  · obtain ⟨y,hy,hmin⟩:=Finset.exists_min_image S (δ x) hS
    have hh : δ x y≤RationalMin.minimum ((S.sort (·≤·)).map (δ x)) := by
      apply RationalMin.minimum_lower _ _ hne
      intro q hq
      obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hq
      exact hmin z ((Finset.mem_sort (·≤·)).mp hz)
    exact (Completion.distanceTo_le hS x hy).trans (hδ x y ▸ Rat.cast_le.mpr hh)
lemma cost_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) :
    (cost δ D S:ℝ)=Completion.realCost D S := by
  simp only [cost,Rat.cast_sum,connection_cast δ hδ S hS,Completion.realCost,dite_eq_left hS]
  exact SortedIndex.sum_enum D (Completion.distanceTo S hS)
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma best_mem (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    best δ D S xs=S ∨ best δ D S xs∈xs := OrderedMaximum.mem _ _ _
lemma cost_le_mem (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (U : Finset (Fin n)) (hU : U∈xs) :
    BinaryMetricCost.cost δ D (best δ D S xs)≤BinaryMetricCost.cost δ D U := by
  exact neg_le_neg_iff.mp (OrderedMaximum.score_le (fun U=> -BinaryMetricCost.cost δ D U) S xs U hU)
lemma best_property (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (P : Finset (Fin n)→Prop) (hS : P S) (hxs : ∀ U∈xs,P U) : P (best δ D S xs) := by
  rcases best_mem δ D S xs with h|h
  · rwa [h]
  · exact hxs _ h
variable [PseudoMetricSpace (Fin n)]
lemma realCost_le_mem (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (xs : List (Finset (Fin n)))
    (hxs : ∀ U∈xs,U.Nonempty) (U : Finset (Fin n)) (hU : U∈xs) :
    Completion.realCost D (best δ D S xs)≤Completion.realCost D U := by
  rw [←BinaryMetricCost.cost_cast δ hδ D U (hxs U hU),
    ←BinaryMetricCost.cost_cast δ hδ D (best δ D S xs) (best_property δ D S xs Finset.Nonempty hS hxs)]
  exact_mod_cast cost_le_mem δ D S xs U hU
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma output_feasible (F S : Finset (Fin n)) (k : ℕ) (raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    output F S k raw⊆F ∧ (output F S k raw).Nonempty ∧ (output F S k raw).card≤k := by
  unfold output
  split_ifs with h
  · exact ⟨Finset.filter_subset _ _,h⟩
  · exact ⟨hSF,hS,hSk⟩
lemma clipped_encode (F U : Finset (Fin n)) :
    clipped F (BinaryFinSet.encode U)=F∩U := by
  classical
  have hh:=BinaryFinSet.decode_encode U
  ext i
  have hi:=Finset.ext_iff.mp hh i
  simp only [BinaryFinSet.decode,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  simp only [clipped,Finset.mem_filter,Finset.mem_inter,hi]
lemma output_encode (F S U : Finset (Fin n)) (k : ℕ) (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤k) :
    output F S k (BinaryFinSet.encode U)=U := by
  rw [output,clipped_encode,Finset.inter_eq_right.mpr hUF,ite_eq_left ⟨hU,hUk⟩]
end MetricKMedianRecovery.BitMachine.BinaryCandidateSanitize

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma output_feasible (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool))
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    output δ D F S k xs⊆F ∧ (output δ D F S k xs).Nonempty ∧ (output δ D F S k xs).card≤k := by
  apply BinaryMetricBest.best_property δ D S _ (fun U=>U⊆F ∧ U.Nonempty ∧ U.card≤k) ⟨hSF,hS,hSk⟩
  intro U hU
  obtain ⟨raw,_,rfl⟩:=List.mem_map.mp hU
  exact BinaryCandidateSanitize.output_feasible F S k raw hSF hS hSk
variable [PseudoMetricSpace (Fin n)]
lemma realCost_le_good (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool))
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) (U : Finset (Fin n))
    (hUF : U⊆F) (hU : U.Nonempty) (hUk : U.card≤k) (hmem : BinaryFinSet.encode U∈xs) :
    Completion.realCost D (output δ D F S k xs)≤Completion.realCost D U := by
  apply BinaryMetricBest.realCost_le_mem δ hδ D S hS _ _ U
  · exact List.mem_map.mpr ⟨BinaryFinSet.encode U,hmem,BinaryCandidateSanitize.output_encode F S U k hUF hU hUk⟩
  · intro V hV
    obtain ⟨raw,_,rfl⟩:=List.mem_map.mp hV
    exact (BinaryCandidateSanitize.output_feasible F S k raw hSF hS hSk).2.1
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralDispatchLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList Completion Sampling.Comparison FiniteSampling
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] anchor BinaryMetricAnchor.run BinaryIntegralRecovery.Guesses.run recoveryParams demand budget
variable {n : ℕ}
lemma output_feasible (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    output Q d δ D F S Δ k g raw⊆F ∧ (output Q d δ D F S Δ k g raw).Nonempty ∧
      (output Q d δ D F S Δ k g raw).card≤k :=
  BinarySanitizedBest.output_feasible δ D F S k _ hSF hS hSk
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open Completion Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
attribute [local irreducible] output words surplus BinaryIntegralDispatch.output BinaryIntegralDispatch.run
lemma cost_le_dispatch (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S) :
    realCost D (output v C Q d δ D F S Δ k g raw)≤
      realCost D (BinaryIntegralDispatch.output Q d δ D F S Δ k g raw) := by
  rw [output]
  have hh:=BinaryIntegralDispatch.output_feasible Q d δ D F S Δ k g raw hSF hS hSk
  apply BinarySanitizedBest.realCost_le_good δ hδ D F S k _ hSF hS hSk _ hh.1 hh.2.1 hh.2.2
  rw [←BinaryIntegralDispatch.run_output_s238r Q d δ D F S Δ k g raw hs,words]
  exact List.mem_cons_self
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralDispatchGuarantee
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma lift_probability_s238r_oai (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F k)=BinaryFinSet.encode S)
    (B p : ℝ) (hp : p≤ probability (fun seed:Fin ((Dsp.budget Q).eval (Dsp.pack δ D F Δ k g []).length)→ Bool=>
      realCost D (BinaryIntegralDispatch.output Q d δ D F S Δ k g (List.ofFn seed))≤ B)) :
    p≤ probability (fun seed:Fin ((Dsp.budget Q).eval (Dsp.pack δ D F Δ k g []).length)→ Bool=>
      realCost D (output v C Q d δ D F S Δ k g (List.ofFn seed))≤ B) :=
  hp.trans (probability_mono (fun seed hh=>(cost_le_dispatch v C Q d δ hδ D F S Δ k g (List.ofFn seed) hSF hS hSk hs).trans hh))
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.lift_probability_s238r_oai
