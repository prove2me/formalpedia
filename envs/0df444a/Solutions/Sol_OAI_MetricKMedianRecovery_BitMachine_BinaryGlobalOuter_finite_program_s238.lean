-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:20:24.321856+00:00
-- url     : https://prove2.me/submissions/ebf532f5-f98d-489f-bbc9-008db0b79672

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K053
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalCall_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_demand_bound_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_zero_bits_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalRounding_rounded_program_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_FiniteSampling_probability_prefix_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_optimum_attained_s238

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
lemma bottomSet_card (U : Finset α) (k : ℕ) : (bottomSet U k).card=min k U.card := by
  rw [bottomSet,List.toFinset_card_of_nodup ((U.sort_nodup (·≤·)).sublist (List.take_sublist _ _)),List.length_take,Finset.length_sort]
end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFillMath
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.Canonical
variable {V : Type*} [LinearOrder V]
lemma pad_subset (F U : Finset V) (n : ℕ) (hUF : U⊆F) : pad F U n⊆F :=
  Finset.union_subset hUF ((bottomSet_subset _ _).trans Finset.sdiff_subset)
lemma pad_card (F U : Finset V) (n : ℕ) (hUF : U⊆F) (hUn : U.card≤n) (hnF : n≤F.card) :
    (pad F U n).card=n := by
  have hd : Disjoint U (bottomSet (F\U) (n-U.card)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    exact (Finset.mem_sdiff.mp (bottomSet_subset _ _ hb)).2 hx
  rw [pad,Finset.card_union_of_disjoint hd,bottomSet_card,Finset.card_sdiff_of_subset hUF,
    min_eq_left (Nat.sub_le_sub_right hnF _)]
  omega
end MetricKMedianRecovery.Completion.Canonical

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_FairPrefix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
lemma take_ofFn_cast {n N : ℕ} (h : n≤N) (seed : Fin N→Bool) :
    (List.ofFn seed).take n=List.ofFn (fun i:Fin n=>seed (Fin.castLE h i)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,min_eq_left h]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl
end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Produce
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma mem_feasibleSets (F S : Finset V) (r : ℕ) :
    S ∈ feasibleSets F r ↔ S ⊆ F ∧ S.Nonempty ∧ S.card ≤ r := by
  simp only [feasibleSets,Finset.mem_filter,Finset.mem_powerset]
omit [PseudoMetricSpace V] in
lemma feasibleSets_nonempty (F : Finset V) (hF : F.Nonempty) (r : ℕ) (hr : 0 < r) :
    (feasibleSets F r).Nonempty := by
  obtain ⟨i,hi⟩ := hF
  exact ⟨{i},(mem_feasibleSets F {i} r).mpr
    ⟨Finset.singleton_subset_iff.mpr hi,Finset.singleton_nonempty i,by simp only [Finset.card_singleton]; omega⟩⟩
lemma optimum_nonneg (F D : Finset V) (r : ℕ) : 0 ≤ optimum F D r := by
  unfold optimum
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => cost_nonneg _ _)
  · rfl

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LowCandidate
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling Surplus FiniteSampling IntegralCandidates

lemma gamma_le_coarse : gamma ≤ 3/100 := min_le_left _ _
lemma gamma_lt_one : gamma < 1 := lt_of_le_of_lt gamma_le_coarse (by norm_num)

end MetricKMedianRecovery.IntegralAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Rounding
open LocalSearch
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [DecidableEq V] in

lemma largest_guess (D O F : Finset V) (hD : D.Nonempty) (hO : O.Nonempty)
    (hOF : O ⊆ F) (hP : 0 < LocalSearch.cost D O) :
    ∃ p ∈ D, ∃ f ∈ F, 0 < dist p f ∧ dist p f ≤ LocalSearch.cost D O ∧
      LocalSearch.cost D O ≤ D.card*dist p f := by
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image D (LocalSearch.connection O) hD
  let f := LocalSearch.nearest O hO p
  have hdf : dist p f = LocalSearch.connection O p := LocalSearch.nearest_distance O hO p
  have hupper : LocalSearch.cost D O ≤ D.card*dist p f := by
    calc
      _ ≤ ∑ _q ∈ D, LocalSearch.connection O p :=
        Finset.sum_le_sum (fun q hq => hmax q hq)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,hdf]
  have hpos : 0 < dist p f := by
    by_contra hn
    have hh : D.card*dist p f ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_gt hn)
    linarith
  refine ⟨p,hp,f,hOF (LocalSearch.nearest_mem O hO p),hpos,?_,hupper⟩
  rw [hdf]
  exact Finset.single_le_sum (fun q _ => LocalSearch.connection_nonneg O q) hp

end MetricKMedianRecovery.Rounding

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ZeroClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

lemma zero_cost_connection (D S : Finset V) (hc : cost D S = 0) :
    ∀ p ∈ D, connection S p = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => connection_nonneg S p)).mp hc

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_Metric
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

lemma cast_inf' {V : Type*} (S : Finset V) (hS : S.Nonempty) (f : V → ℚ) :
    ((S.inf' hS f:ℚ):ℝ) = S.inf' hS (fun x => (f x:ℝ)) := by
  apply le_antisymm
  · exact Finset.le_inf' hS _ (fun i hi => by exact_mod_cast Finset.inf'_le f hi)
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hS f
    rw [he]
    exact Finset.inf'_le _ hi

lemma metric_cost (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) :
    @LocalSearch.cost _ I.metric I.clients S = (I.cost S:ℝ) := by
  by_cases hS : S.Nonempty
  · simp only [cost,LocalSearch.cost,LocalSearch.connection,dite_eq_left hS,Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    exact (cast_inf' S hS (I.distance p)).symm
  · simp only [cost,LocalSearch.cost,LocalSearch.connection,dite_eq_right hS,
      Finset.sum_const_zero,Rat.cast_zero]

lemma metric_optimum (I : RationalMetricInput) :
    @LocalSearch.optimum _ I.metric I.facilities I.clients I.budget = (I.optimum:ℝ) := by
  let := I.metric
  have h : (LocalSearch.feasibleSets I.facilities I.budget).Nonempty :=
    LocalSearch.feasibleSets_nonempty _ I.facilities_nonempty _ I.budget_pos
  have hf : LocalSearch.cost I.clients = fun S => (I.cost S:ℝ) := funext (metric_cost I)
  rw [LocalSearch.optimum,dite_eq_left h,hf,optimum,cast_inf']
  rfl

lemma optimum_nonneg (I : RationalMetricInput) : 0 ≤ I.optimum := by
  have h := @LocalSearch.optimum_nonneg _ I.metric I.facilities I.clients I.budget
  rw [metric_optimum] at h
  exact_mod_cast h

end MetricKMedianRecovery.RationalMetricInput

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Failure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FailureBudget

lemma failure_pos {g : ℝ} (hg : 0 < g) (e N : ℕ) : 0 < failure g e N := by
  unfold failure
  positivity

end MetricKMedianRecovery.FailureBudget

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList
open BinaryRationalSort (entryBits)
variable {n : ℕ}
lemma pick_mem (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) : pick F hF row∈F := by
  obtain ⟨f,hf,he⟩:=key_mem F hF row
  have hp : pick F hF row=f := by apply Fin.ext;exact (congrArg (fun z:ℚ ×ₗ ℕ=>(ofLex z).2) he).symm
  exact hp.symm ▸ hf
lemma pick_key (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) :
    toLex (row (pick F hF row),(pick F hF row).val)=key F hF row := by
  obtain ⟨f,hf,he⟩:=key_mem F hF row
  have hp : pick F hF row=f := by apply Fin.ext;exact (congrArg (fun z:ℚ ×ₗ ℕ=>(ofLex z).2) he).symm
  rw [hp];exact he
lemma pick_min (F : Finset (Fin n)) (hF : F.Nonempty) (row : Fin n→ℚ) (f : Fin n) (hf : f∈F) :
    row (pick F hF row) ≤ row f := by
  have hh:=Finset.min'_le (keys F row) (toLex (row f,f.val)) (Finset.mem_image.mpr ⟨f,hf,rfl⟩)
  change key F hF row≤toLex (row f,f.val) at hh
  rw [←pick_key F hF row] at hh
  exact Prod.Lex.monotone_fst _ _ hh
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList LocalSearch
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma output_subset (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) :
    output δ D F hF⊆F := by
  intro f hf
  obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp hf
  exact pick_mem F hF (δ p)
lemma output_nonempty (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) (hD : D.Nonempty) :
    (output δ D F hF).Nonempty := hD.image _
variable [PseudoMetricSpace (Fin n)]
lemma rows_eq (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (p q : Fin n) (h : dist p q=0) : δ p=δ q := by
  funext f
  apply Rat.cast_injective (α:=ℝ)
  rw [hδ,hδ,dist_comm p f,dist_comm q f]
  exact PseudoMetricSpace.dist_eq_of_dist_zero f h

lemma zero_cost_spec (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F O : Finset (Fin n)) (hF : F.Nonempty) (hO : O.Nonempty) (hOF : O⊆F)
    (hzero : cost D O=0) :
    (output δ D F hF).card≤O.card ∧ cost D (output δ D F hF)=0 := by
  have hz (p:Fin n) (hp:p∈D) : dist p (nearest O hO p)=0 := by
    rw [nearest_distance]
    exact zero_cost_connection D O hzero p hp
  have hrows (p:Fin n) (hp:p∈D) : δ p=δ (nearest O hO p) := rows_eq δ hδ p _ (hz p hp)
  constructor
  · have hh : output δ D F hF⊆O.image (fun p=>pick F hF (δ p)) := by
      intro f hf
      obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hf
      exact Finset.mem_image.mpr ⟨nearest O hO p,nearest_mem O hO p,by rw [←hrows p hp]⟩
    exact (Finset.card_le_card hh).trans Finset.card_image_le
  · apply le_antisymm _ (cost_nonneg _ _)
    apply Finset.sum_nonpos
    intro p hp
    have hm:=pick_min F hF (δ p) (nearest O hO p) (hOF (nearest_mem O hO p))
    have hmR : dist p (pick F hF (δ p))≤0 := by
      have hh : (δ p (pick F hF (δ p)):ℝ)≤(δ p (nearest O hO p):ℝ) := by exact_mod_cast hm
      simpa only [hδ,hz p hp] using hh
    exact (connection_le (Finset.mem_image.mpr ⟨p,hp,rfl⟩)).trans hmR
lemma optimum_zero_spec (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F : Finset (Fin n)) (hF : F.Nonempty) (k : ℕ) (hk : 0<k) (hz : optimum F D k=0) :
    (output δ D F hF).card≤k ∧ cost D (output δ D F hF)=0 := by
  obtain ⟨O,hOF,hO,hOk,hOcost⟩:=optimum_attained_s238 F D hF k hk
  have hh:=zero_cost_spec δ hδ D F O hF hO hOF (hOcost.trans hz)
  exact ⟨hh.1.trans hOk,hh.2⟩
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open WordOperations WordList LocalSearch Completion
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryGlobalCall.run BinaryGlobalCall.demand budget select BinarySanitizedBest.output
lemma start_subset (I : RationalMetricInput) : start I⊆I.facilities := Canonical.pad_subset _ _ _ (Finset.empty_subset _)
lemma start_card (I : RationalMetricInput) : (start I).card=1 :=
  Canonical.pad_card _ _ _ (Finset.empty_subset _) (by simp) I.facilities_nonempty.card_pos
lemma start_nonempty (I : RationalMetricInput) : (start I).Nonempty := Finset.card_pos.mp (by rw [start_card];norm_num)
lemma start_budget (I : RationalMetricInput) : (start I).card≤I.budget := by rw [start_card];exact I.budget_pos
lemma flat_mem (I : RationalMetricInput) (i j : Fin I.pointCount) : I.distance i j∈BinaryInputParser.Metric.flat I :=
  List.mem_flatten.mpr ⟨List.ofFn (I.distance i),List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩
lemma realCost_eq (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) :
    @Completion.realCost _ I.metric I.clients S=(I.cost S:ℝ) := by
  have hh : @Completion.realCost _ I.metric I.clients S=@cost _ I.metric I.clients S := by
    by_cases hS:S.Nonempty
    · simp only [Completion.realCost,cost,connection,dite_eq_left hS,Completion.distanceTo]
    · simp only [Completion.realCost,cost,connection,dite_eq_right hS,Finset.sum_const_zero]
  exact hh.trans (I.metric_cost S)
lemma cost_le_word (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool)
    (U : Finset (Fin I.pointCount)) (hUF : U⊆I.facilities) (hU : U.Nonempty) (hUk : U.card≤I.budget)
    (hmem : BinaryFinSet.encode U∈words v C Q d I raw) :
    (I.cost (output v C Q d I raw):ℝ)≤(I.cost U:ℝ) := by
  have hh:=@BinarySanitizedBest.realCost_le_good _ I.metric I.distance (fun _ _=>rfl) I.clients I.facilities
    (start I) I.budget (words v C Q d I raw) (start_subset I) (start_nonempty I) (start_budget I) U hUF hU hUk hmem
  simpa only [realCost_eq,output] using hh
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalOuterProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalOuter
open LocalSearch Completion IntegralAssembly FiniteSampling Sampling.Comparison
attribute [local irreducible] BinaryGlobalCall.run BinaryIntegralAll.run BinaryIntegralDispatch.budget output words budget
lemma run_take (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M raw)=BinaryGlobalCall.run v C Q d
      (BinaryGlobalCall.pack I M (raw.take ((BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length))) := by
  rw [BinaryGlobalCall.run_pack_s238,BinaryGlobalCall.run_pack_s238,List.take_take,min_self]
lemma probability_all {m : ℕ} (E : (Fin m→Bool)→Prop) (h : ∀ seed,E seed) : probability E=1 := by
  unfold probability
  simp only [ite_eq_left (h _),average_const]

theorem finite_program_s238_oai (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ I : RationalMetricInput,
      let K := (budget Q).eval I.bits.length
      (∀ seed:Fin K→Bool,(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤6*(I.optimum:ℝ)) ∧
      1-FailureBudget.failure gamma e I.size≤probability
        (fun seed:Fin K→Bool=>(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤(2-gamma/2)*(I.optimum:ℝ)) := by
  obtain ⟨v,C,Q,d,hR⟩:=BinaryGlobalRounding.rounded_program_s238 e
  refine ⟨v,C,Q,d,?_⟩
  intro I
  dsimp only
  let := I.metric
  let K := (budget Q).eval I.bits.length
  have hp0 : 0≤(I.optimum:ℝ) := by exact_mod_cast I.optimum_nonneg
  have hf0 : 0≤FailureBudget.failure gamma e I.size := (FailureBudget.failure_pos gamma_pos_s238 _ _).le
  have hfactor : 0≤2-gamma/2 := by linarith [gamma_lt_one]
  by_cases hD : I.clients.Nonempty
  · obtain ⟨O,hOF,hO,hOk,hOC⟩:=optimum_attained_s238 I.facilities I.clients I.facilities_nonempty I.budget I.budget_pos
    rw [I.metric_cost,I.metric_optimum] at hOC
    by_cases hz : (I.optimum:ℝ)=0
    · let Z:=BinaryGlobalZero.output I.distance I.clients I.facilities I.facilities_nonempty
      have hZ:=@BinaryGlobalZero.optimum_zero_spec _ I.metric I.distance (fun _ _=>rfl) I.clients I.facilities
        I.facilities_nonempty I.budget I.budget_pos (by rw [I.metric_optimum,hz])
      have hZF : Z⊆I.facilities := BinaryGlobalZero.output_subset _ _ _ _
      have hZN : Z.Nonempty := BinaryGlobalZero.output_nonempty _ _ _ _ hD
      have hZcost : (I.cost Z:ℝ)=0 := by rw [I.metric_cost] at hZ;exact hZ.2
      have hall (seed:Fin K→Bool) : (I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤0 := by
        apply (cost_le_word v C Q d I (List.ofFn seed) Z hZF hZN hZ.1 ?_).trans_eq hZcost
        rw [words,zero_bits_s238];exact List.mem_cons_self
      constructor
      · intro seed;rw [hz,mul_zero];exact hall seed
      · have he : probability (fun seed:Fin K→Bool=>(I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤(2-gamma/2)*(I.optimum:ℝ))=1 :=
          probability_all _ (fun seed=>by rw [hz,mul_zero];exact hall seed)
        rw [he];linarith
    · have hp : 0<(I.optimum:ℝ) := lt_of_le_of_ne hp0 (Ne.symm hz)
      have hcp : 0 < cost I.clients O := by rw [I.metric_cost,hOC];exact hp
      obtain ⟨p,_,f,_,hm,hmP,hPm⟩:=Rounding.largest_guess I.clients O I.facilities hD hO hOF hcp
      let M:=I.distance p f
      have hM : 0<M := by
        have hm' : (0:ℝ)<(M:ℝ) := hm
        exact_mod_cast hm'
      obtain ⟨U,hRun,hFeas,hBounds⟩:=hR I hD M hM
      have hMP : (M:ℝ)≤(I.cost O:ℝ) := by
        rw [I.metric_cost] at hmP
        exact hmP
      have hPM : (I.cost O:ℝ)≤I.clients.card*(M:ℝ) := by
        rw [I.metric_cost] at hPm
        exact hPm
      obtain ⟨hAll,hProb⟩:=hBounds O hOF hO hOk hMP hPM
      let k:=(BinaryGlobalCall.A.budget Q).eval (BinaryGlobalCall.integralPack I M []).length
      have hk : k≤K := demand_bound_s238 Q I M (flat_mem I p f)
      let sub (seed:Fin K→Bool) : Fin k→Bool := fun i=>seed (Fin.castLE hk i)
      have hCall (seed:Fin K→Bool) : BinaryGlobalCall.run v C Q d (BinaryGlobalCall.pack I M (List.ofFn seed))=BinaryFinSet.encode (U (sub seed)) := by
        have hh:=run_take v C Q d I M (List.ofFn seed)
        rw [take_ofFn_cast hk] at hh
        exact hh.trans (hRun (sub seed))
      have hle (seed:Fin K→Bool) : (I.cost (output v C Q d I (List.ofFn seed)):ℝ)≤(I.cost (U (sub seed)):ℝ) := by
        have h:=hFeas (sub seed)
        apply cost_le_word v C Q d I (List.ofFn seed) (U (sub seed)) h.1 h.2.1 h.2.2
        rw [words]
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨M,flat_mem I p f,hCall seed⟩
      constructor
      · intro seed;exact (hle seed).trans (by rw [←hOC];exact hAll (sub seed))
      · rw [hOC] at hProb
        apply hProb.trans
        rw [←probability_prefix_s238 hk (fun seed:Fin k→Bool=>(I.cost (U seed):ℝ)≤(2-gamma/2)*(I.optimum:ℝ))]
        exact probability_mono (fun seed hs=>(hle seed).trans hs)
  · have hd : I.clients=∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    have hc (S : Finset (Fin I.pointCount)) : (I.cost S:ℝ)=0 := by
      simp only [RationalMetricInput.cost,hd,Finset.sum_empty,dite_eq_ite,ite_self,Rat.cast_zero]
    constructor
    · intro seed;rw [hc];positivity
    · rw [probability_all _ (fun seed=>by rw [hc];exact mul_nonneg hfactor hp0)]
      linarith
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238_oai
