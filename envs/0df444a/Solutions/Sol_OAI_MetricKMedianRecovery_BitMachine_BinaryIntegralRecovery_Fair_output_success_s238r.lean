-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:52:52.153581+00:00
-- url     : https://prove2.me/submissions/aaa70a95-85dc-415c-96dc-8b1a68e014b9

import Mathlib
import Definitions.Def_Q238L021
import Definitions.Def_Q238L030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_result_guarantee_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_result_success_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_RationalSampling_trace_probability_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_integral_records_success_s238r

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

lemma average_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ average X :=
  Finset.expect_nonneg (fun ω _ => h ω)

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

lemma probability_nonneg (P : Ω → Prop) : 0 ≤ probability P := by
  classical
  apply average_nonneg
  intro ω
  split_ifs <;> norm_num

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ProbabilityProd
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I Ω Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ]

lemma probability_prod (E : Ω → Ξ → Prop) :
    probability (fun p : Ω × Ξ => E p.1 p.2) =
      average (fun x => probability (E x)) := by
  classical
  exact average_prod _

lemma probability_prod_lower (P : Ω → Prop) (E : Ω → Ξ → Prop) {p : ℝ}
    (h : ∀ x, P x → p ≤ probability (E x)) :
    probability P * p ≤ probability (fun xy : Ω × Ξ => E xy.1 xy.2) := by
  classical
  rw [probability_prod,probability,← average_mul_const]
  apply average_mono
  intro x
  split_ifs with hx
  · simpa only [one_mul] using h x hx
  · simpa only [zero_mul] using probability_nonneg (E x)

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n) (bits) :
    output δ D F S Δ s colors label q c r0 y0 bits⊆F ∧
      (output δ D F S Δ s colors label q c r0 y0 bits).card=S.card ∧
      (output δ D F S Δ s colors label q c r0 y0 bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · split
    · exact ⟨hSF,rfl,hS⟩
    · rename_i v xs hb
      let P:=BlueDP.makePlan _ _ _ _ _ r0 y0 v xs hb
      have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
        change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
        exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
      exact (result_guarantee_s238r δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius P.sel P.dst c q
        P.selected_injective (fun j=>(P.selection j).1) (fun j=>(P.selection j).2.2) P.destination_count hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

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
open BinaryOpeningPayment (field field_encode)
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_HitsState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided
variable {S A : Type*}
lemma hits_iff_exists_state (f : S → A → S) (stop : S → Prop)
    (n : ℕ) (s : S) (seed : Fin n → A) :
    Hits f stop n s seed ↔ ∃ i : Fin (n+1), stop (states f n s seed i) := by
  induction n generalizing s with
  | zero =>
    change stop s ↔ ∃ _ : Fin 1, stop s
    exact ⟨fun h => ⟨0,h⟩,fun ⟨_,h⟩ => h⟩
  | succ n ih =>
    rw [Hits,ih]
    constructor
    · rintro (h | ⟨i,hi⟩)
      · exact ⟨0,by simpa only [states,Fin.cases_zero] using h⟩
      · exact ⟨i.succ,by simpa only [states,Fin.cases_succ] using hi⟩
    · rintro ⟨i,hi⟩
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        exact Or.inl (by simpa only [states,Fin.cases_zero] using hi)
      · intro hi
        exact Or.inr ⟨j,by simpa only [states,Fin.cases_succ] using hi⟩
end MetricKMedianRecovery.Guided

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
lemma retain_bounded (m : ℕ) (s t : State n) (ht : retain m s=some t) : t.Bounded m := by
  unfold retain at ht
  split_ifs at ht with h
  cases Option.some.inj ht
  exact h
lemma update_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) (t : State n)
    (ht : update δ D F S Δ P κ m M E J s a=some t) : t.Bounded m := by
  cases s with
  | none=>simp only [update] at ht;contradiction
  | some s=>
    simp only [update] at ht
    split_ifs at ht
    rcases a with u | (w | ⟨w,e⟩)
    · contradiction
    · dsimp only at ht
      split_ifs at ht
      exact retain_bounded m _ t ht
    · dsimp only at ht
      cases he : menuRadius δ D P κ m M E J s w e with
      | none=>simp only [he] at ht;contradiction
      | some R=>
        simp only [he] at ht
        split_ifs at ht
        exact retain_bounded m _ t ht
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
lemma fold_next_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (seeds : List (Fin b→Bool)) (s : Option (State n)) (hs : ∀ z,s=some z→z.Bounded m) (t : State n)
    (ht : seeds.foldl (next δ D F S Δ P κ m M E J b) s=some t) : t.Bounded m := by
  induction seeds generalizing s with
  | nil=>exact hs t ht
  | cons seed seeds ih=>exact ih _ (fun z hz=>update_bounded δ D F S Δ P κ m M E J s _ z hz) ht
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape Completion FiniteSampling
variable {n m H : ℕ}
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (hn : n≤H) (hm : m≤H) (hH : 1≤H)
  (hp : s.leaves.length≤H) (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
lemma candidates_property (P : Finset (Fin n)→Prop)
    (hz : ∀ q,P (zero δ D F S Δ s hn hH hp seed q))
    (hb : ∀ q c b,P (positive δ D F S Δ s hn hm hp r0 y0 seed q c b)) :
    ∀ U∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed,P U := by
  intro U hU
  rcases List.mem_append.mp hU with hz'|hb'
  · obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz'
    exact hz q
  · obtain ⟨q,_,hq⟩:=List.mem_flatMap.mp hb'
    obtain ⟨c,_,hc⟩:=List.mem_flatMap.mp hq
    obtain ⟨b,rfl⟩:=List.mem_ofFn.mp hc
    exact hb q c b
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
variable {n : ℕ}
lemma stateAt_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool) (i : Fin (2*m+1))
    (s : RationalSampling.State n) (hs : stateAt δ D F S Δ P m seed i=some s) : s.Bounded m := by
  apply RationalSampling.fold_next_bounded δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M BinarySampler.Parameters.E
    (RadiusMenus.thirdSize mainKappa m) (integralPrecision D (Δ:ℝ) m) _ _ _ s hs
  intro z hz
  cases Option.some.inj hz
  simp [RationalSampling.State.Bounded,RationalSampling.State.initial]
lemma optionOutput_some (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (m : ℕ) (hm : m≤n)
    (r0 y0 : Fin n) (seed : Fin (BinaryRecovery.tapeSize (n+1))→Bool) (s : RationalSampling.State n)
    (hp : s.leaves.length≤n+1) : optionOutput δ D F S Δ m hm r0 y0 seed (some s)=
      BinaryRecovery.result δ D F S Δ s (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp r0 y0 seed := by
  simp only [optionOutput,Option.elim_some,dite_eq_left hp]
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_DesignatedBranchSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (q : ℕ) (bits) :
    output δ D F S Δ s colors q bits⊆F ∧
      (output δ D F S Δ s colors q bits).card=S.card ∧
      (output δ D F S Δ s colors q bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
      change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
      exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
    exact (result_guarantee_s238r δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius
      (Fin.elim0 : Fin 0→Fin n) Fin.elim0 0 q (fun i=>Fin.elim0 i) (fun i=>Fin.elim0 i)
      (fun i=>Fin.elim0 i) (by simp) hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryFeasible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open Completion FiniteSampling
variable {n m H : ℕ} [PseudoMetricSpace (Fin n)]
variable (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
  (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
  (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n)
  (hn : n≤H) (hm : m≤H) (hH : 1≤H) (hp : s.leaves.length≤H)
  (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
include hδ hSF hS hΔ hbound
lemma candidates_feasible : ∀ U∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed,
    U⊆F ∧ U.card=S.card ∧ U.Nonempty := by
  apply candidates_property
  · intro q
    exact BinaryZeroBranch.output_feasible δ hδ D F S hSF hS Δ hΔ hbound s _ q.val _
  · intro q c b
    exact BinaryObservableBranch.output_feasible δ hδ D F S hSF hS Δ hΔ hbound s _ _ q.val c.val r0 y0 _
lemma result_feasible : result δ D F S Δ s hn hm hH hp r0 y0 seed⊆F ∧
    (result δ D F S Δ s hn hm hH hp r0 y0 seed).card=S.card ∧
    (result δ D F S Δ s hn hm hH hp r0 y0 seed).Nonempty := by
  exact BinaryMetricBest.best_property δ D S _ _ ⟨hSF,rfl,hS⟩
    (candidates_feasible δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryFeasible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open Completion Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
variable (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
  (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ)
  (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n)
  (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
  (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool)
include hδ hSF hS hbound
lemma optionOutput_feasible (w : Option (RationalSampling.State n)) :
    optionOutput δ D F S Δ m hm r0 y0 complete w⊆F ∧
    (optionOutput δ D F S Δ m hm r0 y0 complete w).card=S.card ∧
    (optionOutput δ D F S Δ m hm r0 y0 complete w).Nonempty := by
  cases w with
  | none=>exact ⟨hSF,rfl,hS⟩
  | some s=>
    unfold optionOutput
    simp only [Option.elim_some]
    split_ifs with hp
    · exact BinaryRecovery.result_feasible δ hδ D F S hSF hS Δ (by positivity) hbound s _ _ _ hp r0 y0 complete
    · exact ⟨hSF,rfl,hS⟩
lemma candidates_feasible : ∀ U∈candidates δ D F S Δ P m hm r0 y0 sample complete,
    U⊆F ∧ U.card=S.card ∧ U.Nonempty := by
  intro U hU
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hU
  exact optionOutput_feasible δ hδ D F S hSF hS Δ hbound m hm r0 y0 complete _
lemma result_cost_le_prefix (i : Fin (2*m+1)) :
    realCost D (result δ D F S Δ P m hm r0 y0 sample complete)≤
      realCost D (optionOutput δ D F S Δ m hm r0 y0 complete (stateAt δ D F S Δ P m sample i)) :=
  BinaryMetricBest.realCost_le_mem δ hδ D S hS _
    (fun U hU=>(candidates_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 sample complete U hU).2.2)
    _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerPrefixSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling Sampling.Comparison Guided FiniteSampling RadiusMenus
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma prefix_success (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset (Fin n)) (hOF : O⊆F) (hSF : S⊆F)
    (Δ P : ℚ) (hΔ : (1:ℚ)≤Δ) (hPeq : (P:ℝ)=comparisonCost D C.assign)
    (hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card) :
    (1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card ≤
      probability (fun bits : Fin (2*C.bad.card)→Fin (integralPrecision D (Δ:ℝ) C.bad.card)→Bool =>
        ∃ i : Fin (2*C.bad.card+1), C.stop hD (Δ:ℝ)
          ((((List.ofFn bits).take i.val).foldl
            (next δ D F S Δ P (1/1000000) C.bad.card (firstSize mainKappa)
              (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
              (integralPrecision D (Δ:ℝ) C.bad.card)) (some State.initial)).map State.real)) := by
  rw [trace_probability_s238r δ hδ D F S hD Δ P (1/1000000) C.bad.card (firstSize mainKappa)
    (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card)
    (integralPrecision D (Δ:ℝ) C.bad.card) (2*C.bad.card)
    (by unfold firstSize;omega) (by unfold thirdSize;omega) (some State.initial)
    (fun xs=>∃ i,C.stop hD (Δ:ℝ) (xs i))]
  have hκ : ((1/1000000:ℚ):ℝ)=mainKappa := by norm_num [mainKappa]
  simp only [hκ,hPeq]
  have hΔ' : (1:ℝ)≤(Δ:ℝ) := by exact_mod_cast hΔ
  have hh:=C.integral_records_success_s238r hD F hOF hSF (Δ:ℝ) hΔ' hsep hP hm
  simp only [Guided.hits_iff_exists_state] at hh
  simp only [blindUpdate,integralActions,mainActual,Option.map_some,State.real,State.initial,
    Sampling.State.initial,List.map_nil] at hh ⊢
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext seed
  congr 1
  funext i
  congr 3
  apply Subsingleton.elim
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open Completion FiniteSampling Sampling Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma result_success
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℕ) (hΔ : 1≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (hPeq : (P:ℝ)=comparisonCost D C.assign)
    (hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (hP : 0 < comparisonCost D C.assign) (hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n) :
    ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card)*
      ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))≤
      probability (fun seed:(Fin (2*C.bad.card)→Fin (integralPrecision D (Δ:ℝ) C.bad.card)→Bool)×
          (Fin (BinaryRecovery.tapeSize (n+1))→Bool)=>realCost D
        (result δ D F S Δ P C.bad.card hm r0 y0 seed.1 seed.2)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  let E:=fun sample:Fin (2*C.bad.card)→Fin (integralPrecision D (Δ:ℝ) C.bad.card)→Bool=>
    ∃ i:Fin (2*C.bad.card+1),C.stop hD (Δ:ℝ) ((stateAt δ D F S Δ P C.bad.card sample i).map RationalSampling.State.real)
  have hsample : (1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card≤probability E := by
    have hh := RationalSampling.prefix_success δ hδ D S O C hD F hOF hSF (Δ:ℚ) P
      (by exact_mod_cast hΔ) hPeq hsep hP hm0
    have hcast : ((Δ:ℚ):ℝ)=(Δ:ℝ) := by simp only [Rat.cast_natCast]
    generalize he : ((Δ:ℚ):ℝ)=dr at hh
    rw [show dr=(Δ:ℝ) from he.symm.trans hcast] at hh
    simpa only [E,stateAt,BinarySampler.Parameters.M,BinarySampler.Parameters.E] using hh
  apply (mul_le_mul_of_nonneg_right hsample (by positivity : 0≤(1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))).trans
  refine probability_prod_lower E (fun sample complete=>realCost D
    (result δ D F S Δ P C.bad.card hm r0 y0 sample complete)≤(197/100:ℝ)*comparisonCost D C.assign) ?_
  intro sample hsamp
  obtain ⟨i,hi⟩:=hsamp
  cases hst : stateAt δ D F S Δ P C.bad.card sample i with
  | none=>simp only [hst,Option.map_none,stop] at hi
  | some s=>
    rw [hst,Option.map_some] at hi
    change C.Correct hD (1/1000000) s.real ∧
      C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign ∧
      C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign at hi
    have hp : s.leaves.length≤n+1 := ((stateAt_bounded δ D F S Δ P C.bad.card sample i s hst).1.trans hm).trans (Nat.le_succ n)
    have hgood := BinaryRecovery.result_success_s238r δ hδ D F S O C hD hSF hOF hS (Δ:ℚ)
      (by positivity) hbound s hi.1 hP hm0 (by simpa only [Rat.cast_natCast] using hi.2.2)
      (by simpa only [Rat.cast_natCast] using hi.2.1) (Nat.le_succ n) (hm.trans (Nat.le_succ n)) (by omega) hp r0 y0
    apply hgood.trans
    apply probability_mono
    intro complete hc
    have hl:=result_cost_le_prefix δ hδ D F S hSF hS Δ hbound P C.bad.card hm r0 y0 sample complete i
    rw [hst,optionOutput_some δ D F S Δ C.bad.card hm r0 y0 complete s hp] at hl
    exact hl.trans hc
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma output_success_s238r_oai (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℕ) (hΔ : 1≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (hPeq : (P:ℝ)=comparisonCost D C.assign)
    (hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (hP : 0 < comparisonCost D C.assign) (hm0 : 0<C.bad.card)
    (hm : C.bad.card≤n) (r0 y0 : Fin n) :
    ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card)*
      ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ))≤
      probability (fun seed:Fin (count D Δ C.bad.card)→Bool=>realCost D
        (output δ D F S Δ P C.bad.card hm r0 y0 seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  have hh:=BinaryIntegralRecovery.result_success δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound P hPeq hsep hP hm0 hm r0 y0
  have he:=probability_comp_equiv (layout D Δ C.bad.card)
    (fun z=>realCost D (BinaryIntegralRecovery.result δ D F S Δ P C.bad.card hm r0 y0 z.1 z.2)≤
      (197/100:ℝ)*comparisonCost D C.assign)
  exact hh.trans_eq he.symm
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.output_success_s238r_oai
