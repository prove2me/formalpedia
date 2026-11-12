-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.global_application
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:20:40.710517+00:00
-- url     : https://prove2.me/submissions/a4c7d7e4-e100-41b6-bbb1-640728c1ecb3

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L054
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_algorithm_output_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalOuter_finite_program_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_FiniteSampling_average_le_threshold_add_failure_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma best_mem (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    best δ D S xs=S ∨ best δ D S xs∈xs := OrderedMaximum.mem _ _ _
lemma best_property (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (P : Finset (Fin n)→Prop) (hS : P S) (hxs : ∀ U∈xs,P U) : P (best δ D S xs) := by
  rcases best_mem δ D S xs with h|h
  · rwa [h]
  · exact hxs _ h
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
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

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
open LocalSearch Anchoring Completion Sampling FiniteSampling IntegralCandidates

lemma gamma_le_coarse : gamma ≤ 3/100 := min_le_left _ _
lemma gamma_lt_one : gamma < 1 := lt_of_le_of_lt gamma_le_coarse (by norm_num)

end MetricKMedianRecovery.IntegralAssembly

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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FailureBudget

lemma failure_le_margin {g : ℝ} (hg : 0 ≤ g) (e N : ℕ) : failure g e N ≤ g/24 := by
  have hp : (1:ℝ) ≤ ((N:ℝ)+2)^e := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
  unfold failure
  apply div_le_div_of_nonneg_left hg (by norm_num)
  nlinarith

lemma failure_le_power {g a : ℝ} (hg1 : g ≤ 1) (N : ℕ) :
    failure g ⌈a⌉₊ N ≤ Real.rpow ((N:ℝ)+2) (-a) := by
  have hb : (0:ℝ) < (N:ℝ)+2 := by positivity
  have hb1 : (1:ℝ) ≤ (N:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have he : Real.rpow ((N:ℝ)+2) a ≤ ((N:ℝ)+2)^⌈a⌉₊ := by
    simpa only [Real.rpow_eq_pow,Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hb1 (Nat.le_ceil a)
  have hp : (0:ℝ) < ((N:ℝ)+2)^⌈a⌉₊ := pow_pos hb _
  calc
    failure g ⌈a⌉₊ N ≤ 1 / (((N:ℝ)+2)^⌈a⌉₊) := by
      unfold failure
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hp) hp).mpr
      nlinarith
    _ ≤ 1 / Real.rpow ((N:ℝ)+2) a :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hb _) he
    _ = _ := by simpa only [Real.rpow_eq_pow,one_div] using (Real.rpow_neg hb.le a).symm

lemma expectation_margin {g P ζ : ℝ} (hP : 0 ≤ P) (hζ : ζ ≤ g/24) :
    (2-g/2+6*ζ)*P ≤ (2-g/4)*P := by
  apply mul_le_mul_of_nonneg_right _ hP
  linarith

end MetricKMedianRecovery.FailureBudget

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
lemma output_feasible (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (raw : List Bool) :
    output v C Q d I raw⊆I.facilities ∧ (output v C Q d I raw).Nonempty ∧ (output v C Q d I raw).card≤I.budget :=
  BinarySanitizedBest.output_feasible _ _ _ _ _ _ (start_subset I) (start_nonempty I) (start_budget I)
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
open IntegralAssembly FiniteSampling Sampling.Comparison
attribute [local irreducible] output run budget
lemma probability_eq (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput) (B : ℝ) :
    A.successProbability I B=probability (fun seed:A.Seed I=>(I.cost (A.output I seed):ℝ)≤B) := by
  classical
  rw [BinaryRandomizedAlgorithm.successProbability,probability,average,Fintype.expect_eq_sum_div_card]
  simp only [BinaryRandomizedAlgorithm.Seed,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
lemma expected_eq (A : BinaryRandomizedAlgorithm) (I : RationalMetricInput) :
    A.expectedCost I=average (fun seed:A.Seed I=>(I.cost (A.output I seed):ℝ)) := by
  rw [BinaryRandomizedAlgorithm.expectedCost,average,Fintype.expect_eq_sum_div_card]
  simp only [BinaryRandomizedAlgorithm.Seed,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
theorem algorithm_guarantee : globalApplicationClaim := by
  refine ⟨gamma/4,div_pos gamma_pos_s238r (by norm_num),?_⟩
  intro a _ha
  obtain ⟨v,C,Q,d,h⟩:=finite_program_s238r ⌈a⌉₊
  refine ⟨algorithm v C Q d,?_,?_,?_⟩
  · intro I seed
    rw [algorithm_output_s238r]
    have hh:=output_feasible v C Q d I (List.ofFn seed)
    exact ⟨hh.1,hh.2.2,fun _=>hh.2.1⟩
  · intro I
    rw [probability_eq]
    simp only [algorithm_output_s238r]
    have hp0 : 0≤(I.optimum:ℝ) := by exact_mod_cast I.optimum_nonneg
    have hf:=FailureBudget.failure_le_power (g:=gamma) (a:=a) gamma_lt_one.le I.size
    apply (sub_le_sub_left hf 1).trans
    apply (h I).2.trans
    exact probability_mono (fun seed hs=>hs.trans (mul_le_mul_of_nonneg_right (by linarith [gamma_pos_s238r]) hp0))
  · intro I
    rw [expected_eq]
    simp only [algorithm_output_s238r]
    have hp0 : 0≤(I.optimum:ℝ) := by exact_mod_cast I.optimum_nonneg
    have hb0 : 0≤(2-gamma/2)*(I.optimum:ℝ) := mul_nonneg (by linarith [gamma_lt_one]) hp0
    let K := (budget Q).eval I.bits.length
    let X (seed:Fin K→Bool) : ℝ := (I.cost (output v C Q d I (List.ofFn seed)):ℝ)
    have hFail : probability (fun seed:Fin K→Bool=>(2-gamma/2)*(I.optimum:ℝ)<X seed)≤FailureBudget.failure gamma ⌈a⌉₊ I.size := by
      have he : probability (fun seed:Fin K→Bool=>(2-gamma/2)*(I.optimum:ℝ)<X seed)=
          1-probability (fun seed:Fin K→Bool=>X seed≤(2-gamma/2)*(I.optimum:ℝ)) := by
        rw [←probability_compl];exact probability_congr (fun _=>not_le.symm)
      rw [he];have hh:=(h I).2;linarith
    have hAve:=average_le_threshold_add_failure_s238r X hb0 (h I).1
    have hζ:=FailureBudget.failure_le_margin gamma_pos_s238r.le ⌈a⌉₊ I.size
    have hmargin:=FailureBudget.expectation_margin hp0 hζ
    change average X≤_
    exact hAve.trans (le_trans (by nlinarith [mul_le_mul_of_nonneg_right hFail (mul_nonneg (by norm_num : (0:ℝ)≤6) hp0)]) hmargin)
end MetricKMedianRecovery.BitMachine.BinaryGlobalOuter

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
theorem global_application_oai : globalApplicationClaim := BitMachine.BinaryGlobalOuter.algorithm_guarantee
end MetricKMedianRecovery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.global_application_oai := @OAI.MetricKMedianRecovery.global_application_oai
