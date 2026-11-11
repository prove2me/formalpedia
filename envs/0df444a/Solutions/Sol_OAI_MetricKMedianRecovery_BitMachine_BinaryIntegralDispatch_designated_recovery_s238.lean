-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:17:52.80451+00:00
-- url     : https://prove2.me/submissions/992951d3-0b19-4be8-b140-ec8429db4138

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K051
import Definitions.Def_Q238K052
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralDispatch_cost_le_call_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralDispatch_demand_bound_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralDispatch_run_output_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_integral_recovery_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_FiniteSampling_average_le_threshold_add_failure_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_FiniteSampling_probability_prefix_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawDrop
open WordOperations BinaryArithmetic

lemma step_zero (ws : List Bool) : step (pairBits (Nat.bits 0,ws))=pairBits (Nat.bits 0,ws) := by
  simp only [step,extractPrefix_pairBits,value_bits,ite_true, if_true]
lemma step_succ (i : ℕ) (ws : List Bool) :
    step (pairBits ((i+1).bits,ws))=pairBits (i.bits,ws.tail) := by
  simp only [step,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,Nat.add_sub_cancel,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false, if_false]
lemma drop_iterate (n i : ℕ) (ws : List Bool) (hn : ws.length≤n) :
    discardPrefix (step^[n] (pairBits (i.bits,ws)))=ws.drop i := by
  induction n generalizing i ws with
  | zero=>
    have hw : ws=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ws
    simp only [Function.iterate_zero_apply,discardPrefix_pairBits,List.drop_nil]
  | succ n ih=>
    cases i with
    | zero=>rw [Function.iterate_fixed (step_zero ws),discardPrefix_pairBits,List.drop_zero]
    | succ i=>
      rw [Function.iterate_succ_apply,step_succ]
      have hl : ws.tail.length≤n := by simp only [List.length_tail]; omega
      rw [ih i ws.tail hl]
      cases ws with
      | nil=>simp only [List.tail_nil,List.drop_nil]
      | cons w ws=>rfl
lemma run_encode (i : ℕ) (ws : List Bool) :
    run (pairBits (i.bits,ws))=ws.drop i := by
  apply drop_iterate
  rw [pairBits_length]
  dsimp only
  omega
end MetricKMedianRecovery.BitMachine.RawDrop
namespace MetricKMedianRecovery.BitMachine.RawTake
open WordOperations BinaryArithmetic
attribute [local irreducible] number RawDrop.run
lemma run_pack (n : ℕ) (ws : List Bool) : run (pairBits (n.bits,ws))=ws.take n := by
  simp only [run,number,extractPrefix_pairBits,discardPrefix_pairBits,UnaryResources.lengthBits_eq,value_bits,
    RawDrop.run_encode,List.reverse_drop,List.reverse_reverse,List.length_reverse]
  rw [show ws.length-(ws.length-n)=min n ws.length by omega]
  exact List.take_eq_take_min.symm
end MetricKMedianRecovery.BitMachine.RawTake

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

lemma average_sub (X Y : Ω → ℝ) :
    average (fun ω => X ω - Y ω) = average X - average Y :=
  Finset.expect_sub_distrib _ _ _

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

lemma probability_compl [Nonempty Ω] (P : Ω → Prop) :
    probability (fun ω => ¬P ω) = 1 - probability P := by
  classical
  unfold probability
  rw [average_congr (Y := fun ω => 1 - if P ω then 1 else 0) (by
    intro ω
    by_cases hp : P ω <;> simp [hp]), average_sub, average_const]

lemma probability_congr {P Q : Ω → Prop} (h : ∀ ω, P ω ↔ Q ω) :
    probability P = probability Q := by
  classical
  apply average_congr
  intro ω
  simp only [h ω]

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
lemma distanceTo_nonneg (S : Finset V) (hS : S.Nonempty) (x : V) :
    0 ≤ distanceTo S hS x := Finset.le_inf' hS _ (fun _ _ => dist_nonneg)

omit [DecidableEq V] in
lemma distanceTo_le {S : Finset V} (hS : S.Nonempty) (x : V) {s : V} (hs : s ∈ S) :
    distanceTo S hS x ≤ dist x s := Finset.inf'_le _ hs

end MetricKMedianRecovery.Completion

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
lemma cost_le_self (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    BinaryMetricCost.cost δ D (best δ D S xs)≤BinaryMetricCost.cost δ D S := by
  exact neg_le_neg_iff.mp (OrderedMaximum.own_le (fun U=> -BinaryMetricCost.cost δ D U) S xs)
lemma best_property (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (P : Finset (Fin n)→Prop) (hS : P S) (hxs : ∀ U∈xs,P U) : P (best δ D S xs) := by
  rcases best_mem δ D S xs with h|h
  · rwa [h]
  · exact hxs _ h
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_MetricBestProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open Completion FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma realCost_le_self (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (xs : List (Finset (Fin n)))
    (hxs : ∀ U∈xs,U.Nonempty) : realCost D (best δ D S xs) ≤ realCost D S := by
  rw [←BinaryMetricCost.cost_cast δ hδ D S hS,
    ←BinaryMetricCost.cost_cast δ hδ D (best δ D S xs) (best_property δ D S xs Finset.Nonempty hS hxs)]
  exact_mod_cast cost_le_self δ D S xs
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
lemma realCost_le_self (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool))
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    Completion.realCost D (output δ D F S k xs)≤Completion.realCost D S := by
  apply BinaryMetricBest.realCost_le_self δ hδ D S hS
  intro U hU
  obtain ⟨raw,_,rfl⟩:=List.mem_map.mp hU
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryGuesses
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Guided Comparison
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}

omit [Fintype V] in
lemma comparison_cost_positive (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F)
    (hsep : ∀ p ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist p f) : 0 < comparisonCost D C.assign := by
  unfold comparisonCost
  exact Finset.sum_pos (fun p hp => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (hsep p hp _ (hOF (C.assigned p hp)))) hD

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
attribute [local irreducible] counter demand bare RawTake.run UnaryResources.lengthBits BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.run
attribute [local irreducible] mapWith
attribute [local irreducible] start calls
lemma anchorInput_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (r : ℕ) :
    anchorInput (pairBits (pack δ D F Δ k g raw,r.bits))=BinaryMetricAnchor.pack δ D F r := by
  simp only [anchorInput,pack,src,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryMetricAnchor.pack]
lemma anchor_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (r : ℕ) :
    anchor (pairBits (pack δ D F Δ k g raw,r.bits))=BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r) := by
  rw [anchor,Function.comp_apply,anchorInput_pack]
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

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
lemma params_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    recoveryParams (pairBits (pack δ D F Δ k g raw,r.bits))=BinarySampler.Parameters.pack δ D F S Δ 0 0 := by
  rw [recoveryParams,anchor_pack,hs]
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinarySampler.Parameters.pack]
lemma bare_pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    bare (pairBits (pack δ D F Δ k g raw,r.bits))=R.pack δ D F S Δ g [] := by
  rw [bare,params_pack δ D F S Δ k g raw r hs]
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,R.pack,BinaryIntegralRecovery.Fair.pack]
lemma demand_length (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
    (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    (demand Q (pairBits (pack δ D F Δ k g raw,r.bits))).length=(R.budget Q).eval (R.pack δ D F S Δ g []).length := by
  rw [demand,Function.comp_apply,bare_pack δ D F S Δ k g raw r hs,(counter Q).word_length]
lemma callInput_pack (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
    (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    callInput Q (pairBits (pack δ D F Δ k g raw,r.bits))=R.pack δ D F S Δ g
      (raw.take ((R.budget Q).eval (R.pack δ D F S Δ g []).length)) := by
  rw [callInput,params_pack δ D F S Δ k g raw r hs,cutRaw,UnaryResources.lengthBits_eq,
    demand_length Q δ D F S Δ k g raw r hs]
  simp only [src,pack,Function.comp_apply,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,RawTake.run_pack,R.pack,BinaryIntegralRecovery.Fair.pack]
lemma call_pack (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ k : ℕ)
    (g raw : List Bool) (r : ℕ)
    (hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack δ D F r)=BinaryFinSet.encode S) :
    call Q d (pairBits (pack δ D F Δ k g raw,r.bits))=R.run Q d (R.pack δ D F S Δ g
      (raw.take ((R.budget Q).eval (R.pack δ D F S Δ g []).length))) := by
  rw [call,Function.comp_apply,callInput_pack Q δ D F S Δ k g raw r hs]
lemma output_feasible (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    output Q d δ D F S Δ k g raw⊆F ∧ (output Q d δ D F S Δ k g raw).Nonempty ∧
      (output Q d δ D F S Δ k g raw).card≤k :=
  BinarySanitizedBest.output_feasible δ D F S k _ hSF hS hSk
variable [PseudoMetricSpace (Fin n)]
lemma cost_le_start (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤k) :
    realCost D (output Q d δ D F S Δ k g raw) ≤ realCost D S :=
  BinarySanitizedBest.realCost_le_self δ hδ D F S k _ hSF hS hSk
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralDispatchGuarantee
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output BinaryIntegralRecovery.Guesses.output
  BinaryIntegralRecovery.Repeat.output budget BinaryIntegralRecovery.Guesses.budget
  BinaryIntegralRecovery.Fair.pack BinaryMetricAnchor.run

lemma designated_recovery_s238_oai (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→ Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S T O : Finset (Fin n)) (C : Comparison D T O) (_hD : D.Nonempty)
    (k r : ℕ) (_hr : r≤ F.card) (_hSF : S⊆F) (_hS : S.Nonempty) (_hSk : S.card≤ k)
    (_hTF : T⊆F) (_hT : T.Nonempty) (_hTk : T.card≤ k) (_hOF : O⊆F)
    (_hs : BinaryMetricAnchor.run (BinaryMetricAnchor.pack (fun i j=>(δ i j:ℚ)) D F k)=BinaryFinSet.encode S)
    (_ht : BinaryMetricAnchor.run (BinaryMetricAnchor.pack (fun i j=>(δ i j:ℚ)) D F r)=BinaryFinSet.encode T)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤ Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ) (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤ dist w f)
    (N : ℕ) (g : List Bool) (_hN : N≤ g.length) (_hlog : (C.bad.card:ℝ)≤ A*Real.log ((N:ℝ)+2)),
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (budget Q).eval (pack δQ D F Δ k g []).length
    (∀ seed:Fin K→ Bool,run Q d (pack δQ D F Δ k g (List.ofFn seed))=
      BinaryFinSet.encode (output Q d δQ D F S Δ k g (List.ofFn seed))) ∧
    (∀ seed:Fin K→ Bool,output Q d δQ D F S Δ k g (List.ofFn seed)⊆F ∧
      (output Q d δQ D F S Δ k g (List.ofFn seed)).Nonempty ∧
      (output Q d δQ D F S Δ k g (List.ofFn seed)).card≤ k ∧
      realCost D (output Q d δQ D F S Δ k g (List.ofFn seed))≤ realCost D S) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤ probability
      (fun seed:Fin K→ Bool=>realCost D (output Q d δQ D F S Δ k g (List.ofFn seed))≤
        (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin K→ Bool=>realCost D (output Q d δQ D F S Δ k g (List.ofFn seed)))≤
      (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  obtain ⟨Q,d,hd⟩:=BinaryIntegralRecovery.Guesses.integral_recovery_s238 A e
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F S T O C hD k r hr hSF hS hSk hTF hT hTk hOF hs ht Δ hΔ hcap hbound hsep N g hN hlog
  dsimp only
  let δQ := fun i j=>(δ i j:ℚ)
  let KT := (R.budget Q).eval (R.pack δQ D F T Δ g []).length
  let K := (budget Q).eval (pack δQ D F Δ k g []).length
  have hKT : KT≤ K := demand_bound_s238 Q δQ D F T Δ k g r hr ht
  have hδQ : ∀ i j,(δQ i j:ℝ)=dist i j := by intro i j; simpa only [δQ,Rat.cast_natCast] using hδ i j
  obtain ⟨htrace,hgood,hprob,_⟩:=hd δ hδ D F T O C hD hTF hOF hT Δ hΔ hcap hbound hsep N g hN hlog
  let sub (seed:Fin K→ Bool) : Fin KT→ Bool := fun i=>seed (Fin.castLE hKT i)
  let U (seed:Fin KT→ Bool) := BinaryIntegralRecovery.Guesses.output Q d δQ D F T Δ g (List.ofFn seed)
  let V (seed:Fin K→ Bool) := output Q d δQ D F S Δ k g (List.ofFn seed)
  have hcall (seed:Fin K→ Bool) : call Q d (pairBits (pack δQ D F Δ k g (List.ofFn seed),r.bits))=
      BinaryFinSet.encode (U (sub seed)) := by
    rw [call_pack Q d δQ D F T Δ k g (List.ofFn seed) r ht,take_ofFn_cast hKT]
    exact htrace (sub seed)
  have hle (seed:Fin K→ Bool) : realCost D (V seed)≤ realCost D (U (sub seed)) := by
    have hh:=hgood (sub seed)
    exact cost_le_call_s238 Q d δQ hδQ D F S Δ k g (List.ofFn seed) hSF hS hSk r hr
      (U (sub seed)) hh.1 hh.2.1 (hh.2.2.1.trans hTk) (hcall seed)
  have hpoint (seed:Fin K→ Bool) : realCost D (V seed)≤ realCost D S :=
    cost_le_start Q d δQ hδQ D F S Δ k g (List.ofFn seed) hSF hS hSk
  have hp : 1-FailureBudget.failure IntegralAssembly.gamma e N≤ probability
      (fun seed:Fin K→ Bool=>realCost D (V seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
    apply le_trans hprob
    rw [←probability_prefix_s238 hKT (fun seed:Fin KT→ Bool=>realCost D (U seed)≤(197/100:ℝ)*comparisonCost D C.assign)]
    exact probability_mono (fun seed hh=>(hle seed).trans hh)
  refine ⟨fun seed=>run_output_s238 Q d δQ D F S Δ k g (List.ofFn seed) hs,?_,hp,?_⟩
  · intro seed
    have hh:=output_feasible Q d δQ D F S Δ k g (List.ofFn seed) hSF hS hSk
    exact ⟨hh.1,hh.2.1,hh.2.2,hpoint seed⟩
  · have hP := C.comparison_cost_positive hD F hOF hsep
    have hbase : (0:ℝ)≤ realCost D S := by
      rw [realCost,dite_eq_left hS]
      exact Finset.sum_nonneg (fun _ _=>distanceTo_nonneg _ _ _)
    have hf : probability (fun seed:Fin K→ Bool=>(197/100:ℝ)*comparisonCost D C.assign < realCost D (V seed))≤
        FailureBudget.failure IntegralAssembly.gamma e N := by
      have he : probability (fun seed:Fin K→ Bool=>(197/100:ℝ)*comparisonCost D C.assign < realCost D (V seed))=
          1-probability (fun seed:Fin K→ Bool=>realCost D (V seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
        rw [←probability_compl]
        exact probability_congr (fun _=>not_le.symm)
      rw [he]; linarith
    exact (average_le_threshold_add_failure_s238 (B := (197/100:ℝ)*comparisonCost D C.assign) (fun seed:Fin K→ Bool=>realCost D (V seed)) (by positivity) hpoint).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hf hbase])
end MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.designated_recovery_s238_oai
