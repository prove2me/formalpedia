-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:17:49.592662+00:00
-- url     : https://prove2.me/submissions/5d2154b1-76d6-4756-b782-ff8b13d8af2d

import Mathlib
import Definitions.Def_Q238K022
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionFair_result_guarantee_s238

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

lemma completionAssignment_mem (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    completionAssignment S Δ s x ∈ withGhosts (S \ s.deleted) :=
  toVirtual_mem S s (chosen S Δ s x) (chosen_mem S Δ s x)

lemma completionAssignment_distance (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    virtualDistance (leafCenter s) (leafRadius s) Δ x (completionAssignment S Δ s x) =
      virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ x := by
  exact (toVirtual_distance S Δ s x _ (chosen_mem S Δ s x)).trans
    (reference_eq_virtualNearest S Δ s x)

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyGround
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.CopyGround
variable {n a : ℕ}
lemma location_mem (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (e : Fin (a*n)) :
    location H hH e ∈ H (part e) := by
  unfold location part
  split_ifs with h
  · exact h
  · exact Finset.min'_mem _ _
end MetricKMedianRecovery.Completion.CopyGround

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_VirtualCast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} {a b : ℕ}
variable [DecidableEq V]
lemma virtual_cast_mem (h : a=b) (S : Finset V) (t : Virtual V a) : Virtual.cast h t∈withGhosts S ↔ t∈withGhosts S := by subst b;rfl
variable [PseudoMetricSpace V]
omit [DecidableEq V] in
lemma virtualDistance_cast (h : a=b) (w : Fin a→V) (r : Fin a→ℝ) (w' : Fin b→V) (r' : Fin b→ℝ)
    (hw : ∀ i,w' (Fin.cast h i)=w i) (hr : ∀ i,r' (Fin.cast h i)=r i) (M : ℝ) (p : V) (t : Virtual V a) :
    virtualDistance w' r' M p (Virtual.cast h t)=virtualDistance w r M p t := by
  subst b
  have hw' : w'=w := funext hw
  have hr' : r'=r := funext hr
  subst w';subst r';rfl
lemma virtualNearest_cast (h : a=b) (w : Fin a→V) (r : Fin a→ℝ) (w' : Fin b→V) (r' : Fin b→ℝ)
    (hw : ∀ i,w' (Fin.cast h i)=w i) (hr : ∀ i,r' (Fin.cast h i)=r i) (S : Finset V) (M : ℝ) (p : V) :
    virtualNearest S w' r' M p=virtualNearest S w r M p := by
  subst b
  have hw' : w'=w := funext hw
  have hr' : r'=r := funext hr
  subst w';subst r';rfl
omit [PseudoMetricSpace V] in
lemma assignmentWeight_cast (h : a=b) (D : Finset V) (ass : V→Virtual V a) (v : V) :
    assignmentWeight D (Virtual.cast h ∘ ass) v=assignmentWeight D ass v := by subst b;rfl
end MetricKMedianRecovery.Completion
namespace MetricKMedianRecovery.RationalSampling
open Completion
variable {n : ℕ}
lemma State.center_cast (s : State n) (i : Fin s.real.leaves.length) :
    s.center (Fin.cast s.real_length i)=Sampling.leafCenter s.real i := by
  simp only [State.center,Sampling.leafCenter,State.real,List.getElem_map]
  rfl
lemma State.radius_cast (s : State n) (i : Fin s.real.leaves.length) :
    s.radius (Fin.cast s.real_length i)=Sampling.leafRadius s.real i := by
  simp only [State.radius,Sampling.leafRadius,State.real,List.getElem_map]
  rfl
variable [PseudoMetricSpace (Fin n)]
lemma State.assignment_mem (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (p : Fin n) :
    s.assignment S Δ p ∈ withGhosts (S\s.deleted) := by
  rw [State.assignment,Function.comp_apply,virtual_cast_mem]
  exact Sampling.completionAssignment_mem S (Δ:ℝ) s.real p
lemma State.assignment_distance (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (p : Fin n) :
    virtualDistance s.center s.radius (Δ:ℝ) p (s.assignment S Δ p)=virtualNearest (S\s.deleted) s.center s.radius (Δ:ℝ) p := by
  rw [State.assignment,Function.comp_apply,virtualDistance_cast s.real_length _ _ _ _ s.center_cast s.radius_cast,
    virtualNearest_cast s.real_length _ _ _ _ s.center_cast s.radius_cast]
  exact Sampling.completionAssignment_distance S (Δ:ℝ) s.real p
lemma reference_array_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (p : Fin n) :
    (reference δ S Δ s p:ℝ)=virtualNearest (S\s.deleted) s.center s.radius (Δ:ℝ) p := by
  rw [reference_cast δ hδ,Sampling.reference_eq_virtualNearest,
    virtualNearest_cast s.real_length _ _ _ _ s.center_cast s.radius_cast]
  rfl
lemma assignment_array_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) (p : Fin n) :
    (assignmentWeight δ D S Δ s p:ℝ)=Completion.assignmentWeight D (s.assignment S Δ) p := by
  rw [State.assignment,Completion.assignmentWeight_cast,assignmentWeight_cast δ hδ]
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

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext
variable {n m : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma result_guarantee_s238_oai (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (hdel : s.deleted⊆S)
    (colors : Fin n→Fin 3) (hH : ∀ i,(balls δ F s i).Nonempty) (hr : ∀ i,0≤ s.radius i)
    (sel dest : Fin m→Fin n) (c k : ℕ)
    (hinj : Function.Injective sel) (hsel : ∀ j,sel j∈(S\s.deleted).filter (fun i=>colors i=2))
    (hdest : ∀ j,dest j∈F) (hcountDest : (Finset.univ.image dest).card ≤ c)
    (hcount : s.leaves.length+c≤ s.deleted.card+k+m)
    (hk : k≤((S\s.deleted).filter (fun i=>colors i=1)).card) :
    (∀ bits,result δ D F S Δ s colors hH sel dest k bits⊆F ∧
      (result δ D F S Δ s colors hH sel dest k bits).card=S.card ∧
      (result δ D F S Δ s colors hH sel dest k bits).Nonempty) ∧
    ∀ X,PartitionFeasible CopyGround.part X →
      average (fun bits=>realCost D (result δ D F S Δ s colors hH sel dest k bits))≤
        (38/100:ℝ)*objective δ D F S Δ s colors hH sel dest k ∅+
        (62/100:ℝ)*objective δ D F S Δ s colors hH sel dest k X := by
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let loc:=CopyGround.location (balls δ F s) hH
  have hloc (e : Fin (s.leaves.length*n)) : loc e∈F :=
    (Finset.mem_filter.mp (CopyGround.location_mem (balls δ F s) hH e)).1
  have hball (e : Fin (s.leaves.length*n)) : dist (s.center (CopyGround.part e)) (loc e)≤ s.radius (CopyGround.part e) := by
    have hh:=(Finset.mem_filter.mp (CopyGround.location_mem (balls δ F s) hH e)).2
    change δ (s.center (CopyGround.part e)) (loc e)≤ s.leaves[(CopyGround.part e).val].2 at hh
    exact (hδ _ _ ▸ Rat.cast_le.mpr hh)
  have hredMem (i : Fin red.card) : SortedIndex.enum red i∈S\s.deleted :=
    (Finset.mem_filter.mp (SortedIndex.enum_mem red i)).1
  have hredColor (i : Fin red.card) : colors (SortedIndex.enum red i)=1 :=
    (Finset.mem_filter.mp (SortedIndex.enum_mem red i)).2
  have hblueColor (j : Fin m) : colors (sel j)=2 := (Finset.mem_filter.mp (hsel j)).2
  have hRB (i : Fin red.card) (j : Fin m) : SortedIndex.enum red i≠sel j := by
    intro he
    have hh:=hredColor i
    rw [he,hblueColor] at hh
    exact (by decide : (2:Fin 3)≠1) hh
  have hGR (i : Fin red.card) : SortedIndex.enum red i∉green := by
    intro hh
    have hz:=(Finset.mem_filter.mp hh).2
    rw [hredColor] at hz
    exact (by decide : (1:Fin 3)≠0) hz
  have hGB (j : Fin m) : sel j∉green := by
    intro hh
    have hz:=(Finset.mem_filter.mp hh).2
    rw [hblueColor] at hz
    exact (by decide : (2:Fin 3)≠0) hz
  have hK : (∑ j,assignmentWeight D (s.assignment S Δ) (sel j)*dist (sel j) (dest j))≤
      (∑ j,(RationalSampling.assignmentWeight δ D S Δ s (sel j)*δ (sel j) (dest j):ℚ):ℚ) := by
    simp only [Rat.cast_sum,Rat.cast_mul,hδ,RationalSampling.assignment_array_cast δ hδ]
    exact le_rfl
  have hbase (i : Fin D.card) := RationalSampling.reference_array_cast δ hδ S Δ s (SortedIndex.enum D i)
  have hweight (i : Fin red.card) := RationalSampling.assignment_array_cast δ hδ D S Δ s (SortedIndex.enum red i)
  have hredBase (i : Fin red.card) :
      (RationalSampling.reference δ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i):ℝ)=
      virtualNearest green s.center s.radius (Δ:ℝ) (SortedIndex.enum red i) := by
    have hew : (⟨∅,s.leaves⟩ : RationalSampling.State n).center=s.center := rfl
    have her : (⟨∅,s.leaves⟩ : RationalSampling.State n).radius=s.radius := rfl
    simpa only [Finset.sdiff_empty,hew,her] using RationalSampling.reference_array_cast δ hδ green Δ ⟨∅,s.leaves⟩ (SortedIndex.enum red i)
  have hw (i : Fin red.card) : 0≤RationalSampling.assignmentWeight δ D S Δ s (SortedIndex.enum red i) := by
    unfold RationalSampling.assignmentWeight
    positivity
  simpa only [result,objective,Rat.cast_sum] using BinaryCompletionFair.result_guarantee_s238 D F S s.deleted green hSF hS hdel CopyGround.part
    (CopyGround.origin (balls δ F s) hH) (CopyGround.part_origin (balls δ F s) hH) loc s.center s.radius (Δ:ℝ)
    (s.assignment S Δ) (s.assignment_mem S Δ) (s.assignment_distance S Δ) hr (Rat.cast_nonneg.mpr hΔ)
    hloc hball (fun x f hf=>hδ x f ▸ Rat.cast_le.mpr (hbound x f hf))
    (SortedIndex.enum red) sel dest (SortedIndex.enum_injective red) hinj hredMem
    (fun j=>(Finset.mem_filter.mp (hsel j)).1) hRB (Finset.filter_subset _ _) hGR hGB hdest c k hcountDest hcount hk
    _ hK _ _ _ _ _ hbase (fun i e=>hδ _ _) hweight hredBase (fun i e=>hδ _ _)
    (CopyGround.part_surjective (balls δ F s) hH) hw
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238_oai
