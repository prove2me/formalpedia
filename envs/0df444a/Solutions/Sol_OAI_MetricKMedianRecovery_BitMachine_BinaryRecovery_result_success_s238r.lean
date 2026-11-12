-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:53:00.159259+00:00
-- url     : https://prove2.me/submissions/faebf7a8-bfca-4eff-b2d1-ec664423d748

import Mathlib
import Definitions.Def_Q238L012
import Definitions.Def_Q238L030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_result_guarantee_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryObservableBranch_fair_color_label_completion_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryZeroBranch_fair_zero_completion_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_FiniteSampling_probability_prefix_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}

lemma nonproxy_card (C : Comparison D S O) : C.nonproxy.card = C.bad.card := by
  have hsub : C.good.image C.proxy ⊆ S := Finset.image_subset_iff.mpr C.proxy_mem
  rw [nonproxy, Finset.card_sdiff_of_subset hsub, bad,
    Finset.card_sdiff_of_subset C.good_subset, C.same_card,
    Finset.card_image_of_injOn C.proxy_inj]

end Comparison
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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchSeedLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
open BinarySeed BinaryObservableBranch
lemma probability_layout (n b p : ℕ) (P : Seed n b p→Prop) :
    FiniteSampling.probability (fun s=>P (layout n b p s))=FiniteSampling.probability P :=
  FiniteSampling.probability_comp_equiv (layout n b p) P
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
open WordOperations BinaryBranchContext
lemma probability_layout {n b p K : ℕ} (hK : BinaryBranchTape.count n b p≤K)
    (E : BinaryBranchTape.Seed n b p→Prop) :
    FiniteSampling.probability (fun seed:Fin K→Bool=>E (BinaryBranchTape.layout n b p
      (fun i=>seed (Fin.castLE hK i))))=FiniteSampling.probability E := by
  exact (FiniteSampling.probability_prefix_s238r hK (fun z=>E (BinaryBranchTape.layout n b p z))).trans
    (BinaryBranchTape.probability_layout n b p E)
end MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.Prefix
namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix
open WordOperations
lemma probability_layout {n p K : ℕ} (hK : BinaryRandomizedZeroBranch.count n p≤K)
    (E : BinaryRandomizedZeroBranch.Seed n p→Prop) :
    FiniteSampling.probability (fun seed:Fin K→Bool=>E (BinaryRandomizedZeroBranch.layout n p
      (fun i=>seed (Fin.castLE hK i))))=FiniteSampling.probability E := by
  exact (FiniteSampling.probability_prefix_s238r hK (fun z=>E (BinaryRandomizedZeroBranch.layout n p z))).trans
    (FiniteSampling.probability_comp_equiv (BinaryRandomizedZeroBranch.layout n p) E)
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Prefix

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RecoveryTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] zeroContext
  BinaryObservableBranch.output BinaryZeroBranch.output ColorLabel.label ColorLabel.color
  BinaryBranchTape.layout BinaryRandomizedZeroBranch.layout
lemma positiveSeed_probability {n m p H : ℕ} (hn : n≤H) (hm : m≤H) (hp : p≤H) (b : Fin m)
    (E : BinaryBranchTape.Seed n (b.val+1) p→Prop) :
    FiniteSampling.probability (fun seed:Fin (tapeSize H)→Bool=>E (positiveSeed hn hm hp b seed))=FiniteSampling.probability E :=
  BinaryRandomizedBranch.Prefix.probability_layout (BinaryBranchTape.count_bound hn ((Nat.succ_le_of_lt b.isLt).trans hm) hp) E
lemma zeroSeed_probability {n p H : ℕ} (hn : n≤H) (hH : 1≤H) (hp : p≤H)
    (E : BinaryRandomizedZeroBranch.Seed n p→Prop) :
    FiniteSampling.probability (fun seed:Fin (tapeSize H)→Bool=>E (zeroSeed hn hH hp seed))=FiniteSampling.probability E :=
  BinaryRandomizedZeroBranch.Prefix.probability_layout (zeroCount_bound hn hH hp) E
end MetricKMedianRecovery.BitMachine.BinaryRecovery

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
lemma zero_mem (q : Fin (n+1)) : zero δ D F S Δ s hn hH hp seed q∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed := by
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨q,rfl⟩)
lemma positive_mem (q c : Fin (n+1)) (b : Fin m) : positive δ D F S Δ s hn hm hp r0 y0 seed q c b∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨q,List.mem_ofFn.mpr ⟨q,rfl⟩,
    List.mem_flatMap.mpr ⟨c,List.mem_ofFn.mpr ⟨c,rfl⟩,List.mem_ofFn.mpr ⟨b,rfl⟩⟩⟩
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
lemma result_cost_le_zero (q : Fin (n+1)) :
    realCost D (result δ D F S Δ s hn hm hH hp r0 y0 seed)≤
      realCost D (zero δ D F S Δ s hn hH hp seed q) :=
  BinaryMetricBest.realCost_le_mem δ hδ D S hS _
    (fun U hU=>(candidates_feasible δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed U hU).2.2)
    _ (zero_mem δ D F S Δ s hn hm hH hp r0 y0 seed q)
lemma result_cost_le_positive (q c : Fin (n+1)) (b : Fin m) :
    realCost D (result δ D F S Δ s hn hm hH hp r0 y0 seed)≤
      realCost D (positive δ D F S Δ s hn hm hp r0 y0 seed q c b) :=
  BinaryMetricBest.realCost_le_mem δ hδ D S hS _
    (fun U hU=>(candidates_feasible δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed U hU).2.2)
    _ (positive_mem δ D F S Δ s hn hm hH hp r0 y0 seed q c b)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoverySuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open Completion FiniteSampling Sampling
attribute [local irreducible] BinaryZeroBranch.output BinaryObservableBranch.output
variable {n H : ℕ} [PseudoMetricSpace (Fin n)]
lemma result_success_s238r_oai
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0 < comparisonCost D C.assign) (hm0 : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hn : n≤H) (hm : C.bad.card≤H) (hH : 1≤H) (hp : s.leaves.length≤H) (r0 y0 : Fin n) :
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
      probability (fun seed:Fin (tapeSize H)→Bool=>realCost D
        (result δ D F S Δ s hn hm hH hp r0 y0 seed)≤(197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  let R:=C.nonproxy\s.real.deleted
  let dest:=C.designatedDestination hD s.real (19/50)
  let B:=designatedBlue R dest
  let Q:=designatedRed R dest
  let Z:=B.image (C.blueDestination hD s.real (19/50))
  have hqn : Q.card≤n := (Finset.card_le_univ Q).trans_eq (Fintype.card_fin n)
  have hcn : Z.card≤n := (Finset.card_le_univ Z).trans_eq (Fintype.card_fin n)
  let q : Fin (n+1):=⟨Q.card,Nat.lt_succ_of_le hqn⟩
  let c : Fin (n+1):=⟨Z.card,Nat.lt_succ_of_le hcn⟩
  have hB : B.card≤C.bad.card := by
    apply (Finset.card_filter_le _ _).trans
    rw [←C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  rcases hb : B.card with _|b
  · have hgood := BinaryZeroBranch.fair_zero_completion_s238r δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm0 hI hN hb
    have hevent : (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
        probability (fun seed:Fin (tapeSize H)→Bool=>realCost D (zero δ D F S Δ s hn hH hp seed q)≤
          (197/100:ℝ)*comparisonCost D C.assign) := by
      exact hgood.trans_eq (zeroSeed_probability hn hH hp
        (fun z:BinaryRandomizedZeroBranch.Seed n s.leaves.length=>realCost D
          (BinaryZeroBranch.output δ D F S Δ s (fun i=>ColorLabel.color (z.1 i)) q.val z.2)≤
            (197/100:ℝ)*comparisonCost D C.assign)).symm
    apply hevent.trans
    exact probability_mono (fun seed h=>(result_cost_le_zero δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed q).trans h)
  · have hbm : b<C.bad.card := by omega
    let bi : Fin C.bad.card:=⟨b,hbm⟩
    have hgood := BinaryObservableBranch.fair_color_label_completion_s238r δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm0 hI hN
      (b+1) (by omega) hb r0 y0
    have hevent : (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
        probability (fun seed:Fin (tapeSize H)→Bool=>realCost D (positive δ D F S Δ s hn hm hp r0 y0 seed q c bi)≤
          (197/100:ℝ)*comparisonCost D C.assign) := by
      exact hgood.trans_eq (positiveSeed_probability hn hm hp bi
        (fun z:BinaryBranchTape.Seed n (b+1) s.leaves.length=>realCost D
          (BinaryObservableBranch.output δ D F S Δ s (fun i=>ColorLabel.color (z.1.1 i))
            (fun i=>ColorLabel.label (b+1) (by omega) (z.1.2 i)) q.val c.val r0 y0 z.2)≤
              (197/100:ℝ)*comparisonCost D C.assign)).symm
    apply hevent.trans
    exact probability_mono (fun seed h=>(result_cost_le_positive δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed q c bi).trans h)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238r_oai
