-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_start_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:20:05.866937+00:00
-- url     : https://prove2.me/submissions/e8ec6e48-1887-4ab5-bb44-bfeb1b582f8b

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L012
import Definitions.Def_Q238L054

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
lemma cost_le_start_s238r_oai (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→ Fin n→ℚ)
    (hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F S : Finset (Fin n)) (Δ k : ℕ) (g raw : List Bool)
    (hSF : S⊆F) (hS : S.Nonempty) (hSk : S.card≤ k) :
    realCost D (output v C Q d δ D F S Δ k g raw)≤ realCost D S := by
  rw [output]
  exact BinarySanitizedBest.realCost_le_self δ hδ D F S k _ hSF hS hSk
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_start_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.cost_le_start_s238r_oai
