-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:56.911568+00:00
-- url     : https://prove2.me/submissions/4d921410-13db-43e1-ad03-d94875d5c8d3

import Mathlib
import Definitions.Def_Q238K022

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Score
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {E R : Type*} [Fintype R]

lemma le_topSum {q : ℕ} (v : R → ℝ) {S : Finset R}
    (hS : S.card = min q (Fintype.card R)) : (∑ s ∈ S, v s) ≤ topSum q v := by
  apply Finset.le_sup' (f := fun S => ∑ s ∈ S, v s)
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  exact hS

lemma topSum_le {q : ℕ} {v : R → ℝ} {a : ℝ}
    (h : ∀ S : Finset R, S.card = min q (Fintype.card R) → (∑ s ∈ S, v s) ≤ a) :
    topSum q v ≤ a := by
  apply Finset.sup'_le
  intro S hS
  exact h S (Finset.mem_powersetCard.mp hS).2

lemma topSum_attained (q : ℕ) (v : R → ℝ) :
    ∃ S : Finset R, S.card = min q (Fintype.card R) ∧ (∑ s ∈ S, v s) = topSum q v := by
  classical
  obtain ⟨S,hS,hm⟩ := Finset.exists_max_image
    (Finset.univ.powersetCard (min q (Fintype.card R)))
    (fun S => ∑ s ∈ S, v s) (Finset.powersetCard_nonempty.mpr (by simp))
  have hc := (Finset.mem_powersetCard.mp hS).2
  refine ⟨S,hc,le_antisymm (le_topSum v hc) ?_⟩
  exact topSum_le (fun T hT => hm T (by simp [Finset.mem_powersetCard, hT]))

lemma bottomSum_attained (q : ℕ) (v : R → ℝ) :
    ∃ S : Finset R, S.card = min q (Fintype.card R) ∧ (∑ s ∈ S, v s) = bottomSum q v := by
  obtain ⟨S,hS,hm⟩ := topSum_attained q (fun r => -v r)
  refine ⟨S,hS,?_⟩
  unfold bottomSum
  rw [← hm,Finset.sum_neg_distrib,neg_neg]

lemma bottomSum_le {q : ℕ} (v : R → ℝ) {S : Finset R}
    (hS : S.card = min q (Fintype.card R)) : bottomSum q v ≤ ∑ s ∈ S, v s := by
  have hh := le_topSum (fun r => -v r) hS
  simp only [Finset.sum_neg_distrib] at hh
  exact neg_le.mp (by simpa only [bottomSum] using hh)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [PseudoMetricSpace V] in
lemma real_mem_tags (S : Finset V) (s : State V) (v : V) :
    realTag v ∈ tags S s ↔ v ∈ S \ s.deleted := by
  simp [tags, realTag, leafTag]

omit [PseudoMetricSpace V] in
lemma leaf_mem_tags (S : Finset V) (s : State V) (j : ℕ) :
    leafTag j ∈ tags S s ↔ j ≤ s.leaves.length := by
  simp [tags, realTag, leafTag]

lemma chosen_mem (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    chosen S Δ s x ∈ tags S s :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).1

lemma chosen_key_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) :
    toLex (tagDistance Δ s x (chosen S Δ s x),chosen S Δ s x) ≤
      toLex (tagDistance Δ s x t,t) :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).2 t ht

lemma reference_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) : reference S Δ s x ≤ tagDistance Δ s x t :=
  Prod.Lex.monotone_fst _ _ (chosen_key_le S Δ s x ht)

lemma reference_le_real (S : Finset V) (Δ : ℝ) (s : State V) (x v : V)
    (hv : v ∈ S \ s.deleted) : reference S Δ s x ≤ dist x v :=
  reference_le S Δ s x ((real_mem_tags S s v).mpr hv)

lemma reference_le_diameter (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    reference S Δ s x ≤ Δ :=
  reference_le S Δ s x ((leaf_mem_tags S s 0).mpr (Nat.zero_le _))

lemma reference_le_leaf (S : Finset V) (Δ : ℝ) (s : State V) (x : V)
    (j : ℕ) (z : V × ℝ) (hz : s.leaves[j]? = some z) :
    reference S Δ s x ≤ dist x z.1 + z.2 := by
  have hj : j < s.leaves.length := List.getElem?_eq_some_iff.mp hz |>.1
  have hh := reference_le S Δ s x ((leaf_mem_tags S s (j+1)).mpr (by omega))
  simpa only [tagDistance, leafTag, ofLex_toLex, hz] using hh

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoveredCenter
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_ball _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_permanent _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real_iff _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma toVirtual_real_iff (s : State V) (t : Tag V) (v : V) :
    toVirtual s t = .real v ↔ t = realTag v := by
  cases ht : ofLex t with
  | inl u =>
    have he : t = realTag u := congrArg toLex ht
    subst t
    simp [toVirtual,realTag]
  | inr j =>
    have he : t = leafTag j := congrArg toLex ht
    subst t
    cases j with
    | zero => simp [toVirtual,leafTag,realTag]
    | succ j => simp [toVirtual,leafTag,realTag]; split <;> simp_all

omit [PseudoMetricSpace V] in
lemma toVirtual_mem (S : Finset V) (s : State V) (t : Tag V)
    (ht : t ∈ tags S s) : toVirtual s t ∈ withGhosts (S \ s.deleted) := by
  cases he : ofLex t with
  | inl v =>
    have hh : t = realTag v := congrArg toLex he
    have hv := (real_mem_tags S s v).mp (hh ▸ ht)
    simp [toVirtual,he,hv]
  | inr j =>
    cases j with
    | zero => simp [toVirtual,he]
    | succ j => simp only [toVirtual,he]; split <;> simp

lemma toVirtual_distance (S : Finset V) (Δ : ℝ) (s : State V) (x : V) (t : Tag V)
    (ht : t ∈ tags S s) :
    virtualDistance (leafCenter s) (leafRadius s) Δ x (toVirtual s t) = tagDistance Δ s x t := by
  cases he : ofLex t with
  | inl v => simp [toVirtual,tagDistance,he,virtualDistance]
  | inr j =>
    have htag : t = leafTag j := congrArg toLex he
    have hj := (leaf_mem_tags S s j).mp (htag ▸ ht)
    cases j with
    | zero => simp [toVirtual,tagDistance,he,virtualDistance]
    | succ j =>
      have hj' : j < s.leaves.length := by omega
      simp [toVirtual,tagDistance,he,hj',virtualDistance,leafCenter,leafRadius]

lemma reference_eq_virtualNearest (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    reference S Δ s x = virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ x := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro t ht
    cases t with
    | real v =>
      exact reference_le_real S Δ s x v (real_mem_withGhosts.mp ht)
    | ball i =>
      exact reference_le_leaf S Δ s x i.val s.leaves[i.val]
        (List.getElem?_eq_getElem i.isLt)
    | permanent => exact reference_le_diameter S Δ s x
  · have hh := Finset.inf'_le (virtualDistance (leafCenter s) (leafRadius s) Δ x)
      (toVirtual_mem S s (chosen S Δ s x) (chosen_mem S Δ s x))
    simpa only [toVirtual_distance S Δ s x _ (chosen_mem S Δ s x), virtualNearest, reference] using hh

lemma completionAssignment_real_iff (S : Finset V) (Δ : ℝ) (s : State V) (x v : V) :
    completionAssignment S Δ s x = .real v ↔ chosen S Δ s x = realTag v :=
  toVirtual_real_iff s (chosen S Δ s x) v

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RationalSampling
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling
variable {n : ℕ}
lemma tagId_le_iff (t u : Tag (Fin n)) : tagId t≤tagId u ↔ t≤u := by
  cases t using Sum.rec with
  | inl a =>
    cases u using Sum.rec with
    | inl b =>
      change a.val≤b.val ↔ toLex (Sum.inl a:Fin n⊕ℕ)≤toLex (Sum.inl b)
      exact (@Sum.Lex.inl_le_inl_iff (Fin n) ℕ _ _ a b).symm
    | inr b =>
      change a.val≤n+b ↔ toLex (Sum.inl a:Fin n⊕ℕ)≤toLex (Sum.inr b)
      exact iff_of_true (by omega) (Sum.Lex.inl_le_inr a b)
  | inr a =>
    cases u using Sum.rec with
    | inl b =>
      change n+a≤b.val ↔ toLex (Sum.inr a:Fin n⊕ℕ)≤toLex (Sum.inl b)
      exact iff_of_false (by omega) Sum.Lex.not_inr_le_inl
    | inr b =>
      change n+a≤n+b ↔ toLex (Sum.inr a:Fin n⊕ℕ)≤toLex (Sum.inr b)
      rw [Sum.Lex.inr_le_inr_iff]
      omega
lemma tagId_injective : Function.Injective (tagId (n:=n)) := by
  intro t u h
  exact le_antisymm ((tagId_le_iff t u).mp h.le) ((tagId_le_iff u t).mp h.ge)
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ in
lemma tagDistance_cast (Δ : ℚ) (s : State n) (w : Fin n) (t : Tag (Fin n)) :
    (tagDistance δ Δ s w t:ℝ)=Sampling.tagDistance (Δ:ℝ) s.real w t := by
  cases ht : ofLex t with
  | inl v=>simp only [tagDistance,Sampling.tagDistance,ht,hδ]
  | inr j=>
    cases j with
    | zero=>simp only [tagDistance,Sampling.tagDistance,ht]
    | succ j=>
      simp only [tagDistance,Sampling.tagDistance,ht,State.real,List.getElem?_map]
      cases hz : s.leaves[j]? <;> simp only [Option.map_none,Option.map_some,Rat.cast_add,hδ]
include hδ in
lemma key_le_iff (Δ : ℚ) (s : State n) (w : Fin n) (t u : Tag (Fin n)) :
    key δ Δ s w t≤ key δ Δ s w u ↔
      toLex (Sampling.tagDistance (Δ:ℝ) s.real w t,t)≤toLex (Sampling.tagDistance (Δ:ℝ) s.real w u,u) := by
  rw [←tagDistance_cast δ hδ Δ s w t,←tagDistance_cast δ hδ Δ s w u]
  simp only [key,Prod.Lex.le_iff,ofLex_toLex,Rat.cast_lt,Rat.cast_inj,tagId_le_iff]
include hδ in
lemma minimum_key (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (keys δ S Δ s w).min' (keys_nonempty δ S Δ s w)=key δ Δ s w (Sampling.chosen S (Δ:ℝ) s.real w) := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_,Sampling.chosen_mem S (Δ:ℝ) s.real w,rfl⟩)
  · apply Finset.le_min'
    intro x hx
    obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp hx
    exact (key_le_iff δ hδ Δ s w _ t).mpr (Sampling.chosen_key_le S (Δ:ℝ) s.real w ht)
include hδ in
lemma minimum_reference (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    ((ofLex ((keys δ S Δ s w).min' (keys_nonempty δ S Δ s w))).1:ℝ)=Sampling.reference S (Δ:ℝ) s.real w := by
  rw [minimum_key δ hδ]
  exact tagDistance_cast δ hδ Δ s w _
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalMenus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma reference_cast (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (reference δ S Δ s w:ℝ)=Sampling.reference S (Δ:ℝ) s.real w := minimum_reference δ hδ S Δ s w
lemma chosenId_eq (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    chosenId δ S Δ s w=tagId (Sampling.chosen S (Δ:ℝ) s.real w) := by
  simp only [chosenId,chosenKey,minimum_key δ hδ,key,ofLex_toLex]
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
variable {n : ℕ}
lemma assignmentWeight_cast [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) (u : Fin n) :
    (assignmentWeight δ D S Δ s u:ℝ)=Completion.assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) u := by
  have he (p : Fin n) : chosenId δ S Δ s p=u.val ↔ Sampling.completionAssignment S (Δ:ℝ) s.real p=Completion.Virtual.real u := by
    rw [Sampling.completionAssignment_real_iff,chosenId_eq δ hδ]
    change tagId (Sampling.chosen S (Δ:ℝ) s.real p)=tagId (Sampling.realTag u) ↔ _
    exact tagId_injective.eq_iff
  simp only [assignmentWeight,Completion.assignmentWeight,he,Rat.cast_natCast]
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RationalBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {P P' R R' E : Type*} [Fintype P] [Fintype P'] [Fintype R] [Fintype R']

lemma bottomSum_equiv (e : R≃R') (k : ℕ) (v : R'→ℝ) : bottomSum k (v ∘ e)=bottomSum k v := by
  classical
  apply le_antisymm
  · obtain ⟨S,hS,hv⟩:=bottomSum_attained k v
    have hc : (S.map e.symm.toEmbedding).card=min k (Fintype.card R) := by
      simpa only [Finset.card_map,Fintype.card_congr e] using hS
    have hh:=bottomSum_le (v ∘ e) hc
    simpa only [Finset.sum_map,Equiv.toEmbedding_apply,Function.comp_apply,Equiv.apply_symm_apply,hv] using hh
  · obtain ⟨S,hS,hv⟩:=bottomSum_attained k (v ∘ e)
    have hc : (S.map e.toEmbedding).card=min k (Fintype.card R') := by
      simpa only [Finset.card_map,←Fintype.card_congr e] using hS
    have hh:=bottomSum_le v hc
    simp only [Finset.sum_map,Equiv.toEmbedding_apply] at hh
    simpa only [Function.comp_def] using hh.trans_eq hv
lemma surrogate_reindex (ep : P≃P') (er : R≃R') (K : ℝ) (k : ℕ) (base : P'→ℝ)
    (distance : P'→E→ℝ) (weight redBase : R'→ℝ) (redDistance : R'→E→ℝ) (X : Finset E) :
    surrogate K k (base ∘ ep) (distance ∘ ep) (weight ∘ er) (redBase ∘ er) (redDistance ∘ er) X=
      surrogate K k base distance weight redBase redDistance X := by
  unfold surrogate
  have hp:=Equiv.sum_comp ep (fun p=>cappedCost (base p) (distance p) X)
  have hr:=bottomSum_equiv er k (fun r=>weight r*cappedCost (redBase r) (redDistance r) X)
  simp only [Function.comp_def] at hp hr ⊢
  rw [hp,hr]
end MetricKMedianRecovery.Completion
namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
lemma equiv_val (S : Finset α) (i : Fin S.card) : (equiv S i).val=enum S i := rfl
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

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma objective_eq_source_s238_oai (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (sel dest : Fin m→Fin n) (k : ℕ)
    (X : Finset (Fin (s.leaves.length*n))) :
    objective δ D F S Δ s colors hH sel dest k X=
    surrogate (∑ j,Sampling.branchScore D S (Δ:ℝ) s.real (sel j) (dest j)) k
      (fun p : D=>virtualNearest (S\s.deleted) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) p)
      (fun p e=>dist (p:Fin n) (CopyGround.location (balls δ F s) hH e))
      (fun i : Fin ((S\s.deleted).filter (fun i=>colors i=1)).card=>assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) (SortedIndex.enum _ i))
      (fun i=>virtualNearest ((S\s.deleted).filter (fun i=>colors i=0)) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) (SortedIndex.enum _ i))
      (fun i e=>dist (SortedIndex.enum _ i) (CopyGround.location (balls δ F s) hH e)) X := by
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  have hw : Sampling.leafCenter (RationalSampling.State.real (⟨∅,s.leaves⟩ : RationalSampling.State n))=Sampling.leafCenter s.real := rfl
  have hr : Sampling.leafRadius (RationalSampling.State.real (⟨∅,s.leaves⟩ : RationalSampling.State n))=Sampling.leafRadius s.real := rfl
  simp only [RationalSampling.State.real] at hw hr
  unfold objective
  simp only [Rat.cast_mul,hδ,RationalSampling.assignmentWeight_cast δ hδ,
    RationalSampling.reference_cast δ hδ,Sampling.reference_eq_virtualNearest,
    RationalSampling.State.real,Finset.sdiff_empty,Sampling.branchScore]
  rw [hw,hr]
  have hh:=surrogate_reindex (SortedIndex.equiv D) (Equiv.refl (Fin red.card))
    (∑ j,Sampling.branchScore D S (Δ:ℝ) s.real (sel j) (dest j)) k
    (fun p : D=>virtualNearest (S\s.deleted) (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) p)
    (fun p e=>dist (p:Fin n) (CopyGround.location (balls δ F s) hH e))
    (fun i : Fin red.card=>assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) (SortedIndex.enum red i))
    (fun i=>virtualNearest green (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) (Δ:ℝ) (SortedIndex.enum red i))
    (fun i e=>dist (SortedIndex.enum red i) (CopyGround.location (balls δ F s) hH e)) X
  simpa only [Function.comp_def,Equiv.refl_apply,SortedIndex.equiv_val,Sampling.branchScore,
    RationalSampling.State.real,red,green] using hh
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238_oai
