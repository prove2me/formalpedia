-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:15:26.895718+00:00
-- url     : https://prove2.me/submissions/d43d78f9-215d-4cf2-b028-b16383abb563

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K049
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_all_counts_budget_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_cost_le_designated_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Guesses_run_output_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Repeat_FiniteTape_demandWord_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryIntegralRecovery_Repeat_polynomial_program_s238
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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
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

lemma average_prod (X : Ω × Ξ → ℝ) :
    average X = average (fun ω => average (fun ξ => X (ω,ξ))) := by
  simpa only [average, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ) X

lemma average_equiv (e : Ω ≃ Ξ) (X : Ω → ℝ) (Y : Ξ → ℝ)
    (h : ∀ ω, X ω = Y (e ω)) : average X = average Y :=
  Fintype.expect_equiv e X Y h

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ProbabilityProd
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I Ω Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ]

lemma average_pi_restrict [DecidableEq I] [Nonempty Ω] (Q : Finset I)
    (X : (↥Q → Ω) → ℝ) :
    average (fun seed : I → Ω => X (fun i => seed i)) = average X := by
  classical
  rw [average_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Q) (fun _ => Ω))
    (fun seed : I → Ω => X (fun i => seed i)) (fun p => X p.1) (fun _ => rfl),average_prod]
  simp

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_AveragePrecomposeEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I J Ω : Type*} [Fintype I] [Fintype J] [Fintype Ω] [Nonempty Ω]
  [DecidableEq I] [DecidableEq J]

lemma average_precompose_embedding (e : I ↪ J) (X : (I → Ω) → ℝ) :
    average (fun seed : J → Ω => X (fun i => seed (e i))) = average X := by
  classical
  let Q : Finset J := Finset.univ.image e
  let eqv : I ≃ ↥Q :=
    { toFun := fun i => ⟨e i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
      invFun := fun j => Classical.choose (Finset.mem_image.mp j.property)
      left_inv := by
        intro i
        apply e.injective
        exact (Classical.choose_spec (Finset.mem_image.mp
          (show e i ∈ Q from Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).2
      right_inv := by
        intro j
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp j.property)).2 }
  let ee : (↥Q → Ω) ≃ (I → Ω) :=
    { toFun := fun seed i => seed (eqv i)
      invFun := fun seed j => seed (eqv.symm j)
      left_inv := by intro s; funext j; simp
      right_inv := by intro s; funext i; simp }
  calc
    _ = average (fun seed : ↥Q → Ω => X (ee seed)) :=
      average_pi_restrict Q (fun seed => X (ee seed))
    _ = average X := average_equiv ee _ X (fun _ => rfl)

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ProbabilityCompEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
lemma probability_comp_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (E : Ξ → Prop) : probability (fun x => E (e x)) = probability E := by
  classical
  exact average_equiv e _ _ (fun _ => rfl)

end MetricKMedianRecovery.FiniteSampling

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_TensorEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
lemma raw_tensorEquiv (ds : List ℕ) (b : ℕ) (s : Fin (count ds b)→Bool) :
    raw (tensorEquiv ds b s)=List.ofFn s := by
  induction ds with
  | nil=>rfl
  | cons n ns ih=>
    change Fin (n*count ns b)→Bool at s
    change (List.ofFn (fun i:Fin n=>raw (tensorEquiv ns b (fun j=>s (finProdFinEquiv (i,j)))))).flatten =
      List.ofFn (s:Fin (n*count ns b)→Bool)
    simp only [ih]
    conv_rhs => rw [List.ofFn_mul]
    congr 2
    funext i
    congr 1
    funext j
    congr 1
    apply Fin.ext
    change j.val+count ns b*i.val=i.val*count ns b+j.val
    ring
end MetricKMedianRecovery.BitMachine.BinarySeed

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
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAmplified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
open WordOperations WordList Sampling.Comparison FiniteSampling
attribute [local irreducible] Repeat.run Fair.pack Fair.raw Repeat.rword Repeat.bword RawTake.run extra
attribute [local irreducible] demandBits
variable {n : ℕ}
lemma cut_pack (Q : Polynomial ℕ) (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n))
    (Δ : ℕ) (P : ℚ) (m : ℕ) (g raw : List Bool) (hm : m≤n)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    cut Q (Fair.pack δ D F S Δ P m g raw)=Fair.pack δ D F S Δ P m g
      (raw.take (Q.eval g.length*Fair.count D Δ m)) := by
  have hh : demandBits Q (Fair.pack δ D F S Δ P m g raw)=(Q.eval g.length*Fair.count D Δ m).bits := by
    rw [demandBits,Function.comp_apply,UnaryResources.lengthBits_eq,demandWord_pack_s238 Q δ D F S Δ P m g raw hm hΔ]
  rw [cut,hh]
  simp only [extra,Fair.raw,Fair.pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,RawTake.run_pack]
lemma probability_layout {t b K : ℕ} (hK : t*b≤K) (E : (Fin t→Fin b→Bool)→Prop) :
    probability (fun seed:Fin K→Bool=>E (layout t b (fun i=>seed (Fin.castLE hK i))))=probability E :=
  (probability_prefix_s238 hK (fun z=>E (layout t b z))).trans (probability_comp_equiv (layout t b) E)
lemma average_layout {t b K : ℕ} (hK : t*b≤K) (X : (Fin t→Fin b→Bool)→ℝ) :
    average (fun seed:Fin K→Bool=>X (layout t b (fun i=>seed (Fin.castLE hK i))))=average X := by
  exact (average_precompose_embedding ⟨Fin.castLE hK,Fin.castLE_injective hK⟩ (fun z=>X (layout t b z))).trans
    (average_equiv (layout t b) _ _ (fun _=>rfl))
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
open WordOperations WordList Sampling.Comparison FiniteSampling
lemma run_of_repeat {n K : ℕ} (Q : Polynomial ℕ) (d : ℕ) (δ : Fin n→Fin n→ℚ)
    (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ) (hm : m≤n)
    (hΔ : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16)) (g : List Bool)
    (r0 y0 : Fin n) (hK : Q.eval g.length*Fair.count D Δ m≤K)
    (hrun : ∀ seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ m)→Bool,
      Repeat.run Q d (Fair.pack δ D F S Δ P m g (BinarySeed.raw (ds:=[Q.eval g.length]) seed))=
        BinaryFinSet.encode (Repeat.output δ D F S Δ P m hm r0 y0 (Q.eval g.length) seed))
    (seed : Fin K→Bool) :
    run Q d (Fair.pack δ D F S Δ P m g (List.ofFn seed))=
      BinaryFinSet.encode (Repeat.output δ D F S Δ P m hm r0 y0 (Q.eval g.length)
        (layout (Q.eval g.length) (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i)))) := by
  rw [run,Function.comp_apply,cut_pack Q δ D F S Δ P m g _ hm hΔ,take_ofFn_cast hK]
  have hr:=BinarySeed.raw_tensorEquiv [Q.eval g.length] (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i))
  change BinarySeed.raw (ds:=[Q.eval g.length]) (layout (Q.eval g.length) (Fair.count D Δ m) (fun i=>seed (Fin.castLE hK i)))=_ at hr
  exact (congrArg (fun raw=>Repeat.run Q d (Fair.pack δ D F S Δ P m g raw)) hr).symm.trans (hrun _)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.FiniteTape
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

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses
open Completion Sampling Sampling.Comparison FiniteSampling
attribute [local irreducible] output Repeat.output budget Fair.pack Repeat.FiniteTape.layout

lemma polynomial_recovery_s238_oai (A : ℝ) (e : ℕ) : ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [PseudoMetricSpace (Fin n)]
    (δ : Fin n→Fin n→ℚ) (_hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (_hD : D.Nonempty)
    (_hSF : S⊆F) (_hOF : O⊆F) (_hS : S.Nonempty)
    (Δ : ℕ) (_hΔ : 1≤Δ) (_hcap : Δ≤Rounding.cap D.card (IntegralAssembly.gamma/16))
    (_hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (p : ℕ) (_hp : p≤D.card*Δ) (_hPeq : (p:ℝ)=comparisonCost D C.assign)
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (_hP : 0 < comparisonCost D C.assign) (_hm0 : 0<C.bad.card)
    (_hm : C.bad.card≤n) (_r0 _y0 : Fin n) (N : ℕ) (g : List Bool)
    (_hN : N≤g.length) (_hlog : (C.bad.card:ℝ)≤A*Real.log ((N:ℝ)+2)),
    let K := (budget Q).eval (pack δ D F S Δ g []).length
    (∀ seed:Fin K→Bool,run Q d (pack δ D F S Δ g (List.ofFn seed))=
      BinaryFinSet.encode (output Q d δ D F S Δ g (List.ofFn seed))) ∧
    (∀ seed:Fin K→Bool,output Q d δ D F S Δ g (List.ofFn seed)⊆F ∧
      (output Q d δ D F S Δ g (List.ofFn seed)).Nonempty ∧
      (output Q d δ D F S Δ g (List.ofFn seed)).card≤S.card ∧
      realCost D (output Q d δ D F S Δ g (List.ofFn seed)) ≤ realCost D S) ∧
    (1-FailureBudget.failure IntegralAssembly.gamma e N≤probability
      (fun seed:Fin K→Bool=>realCost D (output Q d δ D F S Δ g (List.ofFn seed))≤
        (197/100:ℝ)*comparisonCost D C.assign)) ∧
    average (fun seed:Fin K→Bool=>realCost D (output Q d δ D F S Δ g (List.ofFn seed)))≤
      (197/100:ℝ)*comparisonCost D C.assign+realCost D S*FailureBudget.failure IntegralAssembly.gamma e N := by
  obtain ⟨Q,d,hd⟩:=Repeat.polynomial_program_s238 A e
  refine ⟨Q,d,?_⟩
  intro n _ δ hδ D F S O C hD hSF hOF hS Δ hΔ hcap hbound p hp hPeq hsep hP hm0 hm r0 y0 N g hN hlog
  dsimp only
  have hPeq' : ((p:ℚ):ℝ)=comparisonCost D C.assign := by simpa only [Rat.cast_natCast] using hPeq
  obtain ⟨hrun,hfeas,hprob,havg⟩:=hd δ hδ D F S O C hD hSF hOF hS Δ hΔ hcap hbound p hPeq'
    hsep hP hm0 hm r0 y0 N g hN hlog
  have hK:=all_counts_budget_s238 Q δ D F S Δ g hcap C.bad.card hm
  let Θ := (budget Q).eval (pack δ D F S Δ g []).length
  let trial (seed : Fin Θ→Bool) : Finset (Fin n) := Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length)
    (Repeat.FiniteTape.layout (Q.eval g.length) (Fair.count D Δ C.bad.card) (fun i=>seed (Fin.castLE hK i)))
  have hdom (seed : Fin Θ→Bool) : realCost D (output Q d δ D F S Δ g (List.ofFn seed)) ≤ realCost D (trial seed) := by
    have hf:=hfeas (Repeat.FiniteTape.layout (Q.eval g.length) (Fair.count D Δ C.bad.card) (fun i=>seed (Fin.castLE hK i)))
    apply cost_le_designated_s238 Q d δ hδ D F S hSF hS Δ g (List.ofFn seed) p C.bad.card hp hm (trial seed)
      hf.1 hf.2.2 hf.2.1.le
    exact Repeat.FiniteTape.run_of_repeat Q d δ D F S Δ p C.bad.card hm hcap g r0 y0 hK hrun seed
  refine ⟨fun _=>run_output_s238 Q d δ D F S Δ g _ hcap,?_,?_,?_⟩
  · intro seed
    have hf:=output_feasible Q d δ D F S hSF hS Δ g (List.ofFn seed)
    exact ⟨hf.1,hf.2.1,hf.2.2,cost_le_start Q d δ hδ D F S hSF hS Δ g _⟩
  · have hh : probability (fun seed:Fin Θ→Bool=>realCost D (trial seed)≤(197/100:ℝ)*comparisonCost D C.assign)=
        probability (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
          realCost D (Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length) seed)≤
            (197/100:ℝ)*comparisonCost D C.assign) := Repeat.FiniteTape.probability_layout hK (fun seed=>
          realCost D (Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length) seed)≤
            (197/100:ℝ)*comparisonCost D C.assign)
    exact (hprob.trans_eq hh.symm).trans (probability_mono (fun seed hs=>(hdom seed).trans hs))
  · have hh : average (fun seed:Fin Θ→Bool=>realCost D (trial seed))=
        average (fun seed:Fin (Q.eval g.length)→Fin (Fair.count D Δ C.bad.card)→Bool=>
          realCost D (Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length) seed)) :=
      Repeat.FiniteTape.average_layout hK (fun seed=>
          realCost D (Repeat.output δ D F S Δ p C.bad.card hm r0 y0 (Q.eval g.length) seed))
    exact (average_mono hdom).trans (hh.le.trans havg)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.polynomial_recovery_s238_oai
