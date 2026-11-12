-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:12.21336+00:00
-- url     : https://prove2.me/submissions/1de18e8e-4463-45fc-b221-b77f6dc34611

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L012
import Definitions.Def_Q238L040
import Definitions.Def_Q238L045
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_polynomial_recovery_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_run_output_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma cluster_mem (D : Finset V) (c : V → V) (p o : V) :
    p ∈ cluster D c o ↔ p ∈ D ∧ c p = o := Finset.mem_filter

omit [PseudoMetricSpace V] in
lemma cluster_partition (D O : Finset V) (c : V → V)
    (hc : ∀ p ∈ D, c p ∈ O) (f : V → ℝ) :
    (∑ o ∈ O, ∑ p ∈ cluster D c o, f p) = ∑ p ∈ D, f p := by
  classical
  simp only [cluster, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp [hc p hp]

lemma comparisonCost_eq (D O : Finset V) (c : V → V) (hc : ∀ p ∈ D, c p ∈ O) :
    (∑ o ∈ O, clusterCost D c o) = comparisonCost D c := by
  have hh := cluster_partition D O c hc (fun p => dist p (c p))
  refine Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro p hp
  rw [(cluster_mem D c p o).mp hp |>.2]

end MetricKMedianRecovery.Sampling

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
lemma no_bad_proxy_cost (C : Comparison D S O) (hS : S.Nonempty) (hm : C.bad.card = 0) :
    realCost D S ≤ (101/100:ℝ)*comparisonCost D C.assign := by
  have hOS : O ⊆ C.good := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hm)
  have he : C.good = O := Finset.Subset.antisymm C.good_subset hOS
  have hpart := cluster_partition D C.good C.assign (fun p hp => hOS (C.assigned p hp))
    (distanceTo S hS)
  have hc : realCost D S ≤ ∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, dist p (C.proxy o) := by
    simp only [realCost,dite_eq_left hS]
    rw [← hpart]
    apply Finset.sum_le_sum
    intro o ho
    exact Finset.sum_le_sum (fun p _ => distanceTo_le hS p (C.proxy_mem o ho))
  have hcO := comparisonCost_eq D O C.assign C.assigned
  have hcost := C.proxy_cost
  rw [he,hcO] at hcost
  rw [he] at hc
  linarith

omit [Fintype V] in
lemma integer_comparison_cost (C : Comparison D S O) (F : Finset V) (hOF : O ⊆ F)
    (δ : V → V → ℕ) (M : ℕ)
    (hδ : ∀ p ∈ D, ∀ f ∈ F, (δ p f:ℝ) = dist p f)
    (hM : ∀ p ∈ D, ∀ f ∈ F, δ p f ≤ M) :
    ∃ P : ℕ, P ≤ D.card*M ∧ comparisonCost D C.assign = (P:ℝ) := by
  refine ⟨∑ p ∈ D, δ p (C.assign p),?_,?_⟩
  · calc
      _ ≤ ∑ _p ∈ D, M := Finset.sum_le_sum (fun p hp => hM p hp _ (hOF (C.assigned p hp)))
      _ = _ := by simp
  · simp only [comparisonCost,Nat.cast_sum]
    exact Finset.sum_congr rfl (fun p hp => (hδ p hp _ (hOF (C.assigned p hp))).symm)

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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
lemma output_feasible (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (g raw : List Bool) :
    output Q d δ D F S Δ g raw⊆F ∧ (output Q d δ D F S Δ g raw).Nonempty ∧
      (output Q d δ D F S Δ g raw).card≤S.card :=
  BinarySanitizedBest.output_feasible δ D F S S.card _ hSF hS le_rfl
variable [PseudoMetricSpace (Fin n)]
lemma cost_le_start (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (g raw : List Bool) :
    realCost D (output Q d δ D F S Δ g raw) ≤ realCost D S :=
  BinarySanitizedBest.realCost_le_self δ hδ D F S S.card _ hSF hS le_rfl
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output Repeat.output budget Fair.pack

lemma integral_recovery_s238r_oai (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℕ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (N : ℕ) (g : List Bool) (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (budget Q).eval (pack δQ D F S Δ g []).length
    (∀ seed:Fin K→Bool,run Q d (pack δQ D F S Δ g (List.ofFn seed))=
      BinaryFinSet.encode (output Q d δQ D F S Δ g (List.ofFn seed))) ∧
    (∀ seed:Fin K→Bool,output Q d δQ D F S Δ g (List.ofFn seed)⊆F ∧
      (output Q d δQ D F S Δ g (List.ofFn seed)).Nonempty ∧
      (output Q d δQ D F S Δ g (List.ofFn seed)).card≤S.card ∧
      realCost D (output Q d δQ D F S Δ g (List.ofFn seed)) ≤ realCost D S) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
      (fun seed:Fin K→Bool=>realCost D (output Q d δQ D F S Δ g (List.ofFn seed))≤
        (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin K→Bool=>realCost D (output Q d δQ D F S Δ g (List.ofFn seed)))≤
      (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  obtain ⟨Q,d,hd⟩:=polynomial_recovery_s238r A e
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F S O C hD hSF hOF hS Δ hΔ hcap hbound hsep N g hN hlog
  dsimp only
  have hδQ : ∀ i j,((δ i j:ℚ):ℝ)=dist i j := by simpa only [Rat.cast_natCast] using hδ
  have hboundQ : ∀ x,∀ f∈F,(δ x f:ℚ)≤Δ := by intro x f hf; exact_mod_cast hbound x f hf
  have hP := C.comparison_cost_positive hD F hOF hsep
  by_cases hz : C.bad.card=0
  · have hfall := C.no_bad_proxy_cost hS hz
    have hs (raw : List Bool) : realCost D (output Q d (fun i j=>(δ i j:ℚ)) D F S Δ g raw)≤
        (197/100:ℝ)*comparisonCost D C.assign := by
      have hh:=cost_le_start Q d (fun i j=>(δ i j:ℚ)) hδQ D F S hSF hS Δ g raw
      linarith
    refine ⟨fun _=>run_output_s238r Q d _ D F S Δ g _ hcap,?_,?_,?_⟩
    · intro seed
      have hf:=output_feasible Q d (fun i j=>(δ i j:ℚ)) D F S hSF hS Δ g (List.ofFn seed)
      exact ⟨hf.1,hf.2.1,hf.2.2,cost_le_start Q d _ hδQ D F S hSF hS Δ g _⟩
    · have he : probability (fun seed:Fin ((budget Q).eval (pack (fun i j=>(δ i j:ℚ)) D F S Δ g []).length)→Bool=>
          realCost D (output Q d (fun i j=>(δ i j:ℚ)) D F S Δ g (List.ofFn seed))≤
            (197/100:ℝ)*comparisonCost D C.assign)=1 := by
        have hh : (fun seed:Fin ((budget Q).eval (pack (fun i j=>(δ i j:ℚ)) D F S Δ g []).length)→Bool=>
          realCost D (output Q d (fun i j=>(δ i j:ℚ)) D F S Δ g (List.ofFn seed))≤
            (197/100:ℝ)*comparisonCost D C.assign)=(fun _=>True) := by
          funext seed; exact propext ⟨fun _=>trivial,fun _=>hs _⟩
        rw [hh]; simp [probability]
      rw [he]
      have hh:=FailureBudget.failure_pos IntegralAssembly.gamma_pos_s238r e N
      linarith
    · have hbase : (0:ℝ) ≤ realCost D S := by
        rw [realCost,dite_eq_left hS]
        exact Finset.sum_nonneg (fun _ _=>distanceTo_nonneg _ _ _)
      have hmean:=average_mono (fun seed:Fin ((budget Q).eval (pack (fun i j=>(δ i j:ℚ)) D F S Δ g []).length)→Bool=>hs (List.ofFn seed))
      rw [average_const] at hmean
      exact hmean.trans (le_add_of_nonneg_right (mul_nonneg hbase (FailureBudget.failure_pos IntegralAssembly.gamma_pos_s238r e N).le))
  · obtain ⟨p,hp,heq⟩:=C.integer_comparison_cost F hOF δ Δ (fun w _ f _=>hδ w f) (fun w _ f hf=>hbound w f hf)
    obtain ⟨r0,hr0⟩:=hS
    exact hd (fun i j=>(δ i j:ℚ)) hδQ D F S O C hD hSF hOF ⟨r0,hr0⟩ Δ hΔ hcap hboundQ p hp heq.symm
      hsep hP (Nat.pos_of_ne_zero hz) (by simpa only [Fintype.card_fin] using C.bad.card_le_univ) r0 r0 N g hN hlog
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.integral_recovery_s238r_oai
