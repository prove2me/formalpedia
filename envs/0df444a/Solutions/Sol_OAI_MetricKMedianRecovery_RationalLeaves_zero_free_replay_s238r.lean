-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:36:21.587406+00:00
-- url     : https://prove2.me/submissions/53b73d53-213d-4cbb-a4fa-79671192a85b

import Mathlib
import Definitions.Def_Q238L019
import Definitions.Def_Q238L020

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LeafTransfer
variable {A X : Type*} [PseudoMetricSpace X] [DecidableEq X]

lemma nearest_images (W : Finset A) (hW : W.Nonempty) (r s : A → X) (p : X)
    (eps : ℝ) (hshrink : ∀ a ∈ W, dist p (s a) ≤ dist p (r a))
    (hloss : ∀ a ∈ W, dist p (r a) ≤ dist p (s a)+eps) :
    nearestDistance p (W.image s) ≤ nearestDistance p (W.image r) ∧
    nearestDistance p (W.image r) ≤ nearestDistance p (W.image s)+eps := by
  have hr : (W.image r).Nonempty := hW.image r
  have hs : (W.image s).Nonempty := hW.image s
  constructor
  · obtain ⟨x,hx,he⟩ := nearestDistance_attained p (W.image r) hr
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [he]
    exact (nearestDistance_le_mem p (W.image s) (s a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)).trans
      (hshrink a ha)
  · obtain ⟨x,hx,he⟩ := nearestDistance_attained p (W.image s) hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    rw [he]
    exact (nearestDistance_le_mem p (W.image r) (r a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)).trans
      (hloss a ha)

end MetricKMedianRecovery.LeafTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
namespace Entry
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {i : X}
lemma mem (h : Entry loc F B Q v z lam eta i) : i ∈ F ∪ B := by
  rcases h.2 with h|h
  · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ h.1
end Entry

namespace Prefix
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {H G : List X}

lemma opened_subset (h : Prefix loc F B v z lam eta Q H) : H.toFinset ⊆ F ∪ B := by
  intro i hi
  induction h with
  | nil => simp at hi
  | cons ha ht ih =>
    simp only [List.toFinset_cons,Finset.mem_insert] at hi
    rcases hi with rfl|hi
    · exact ha.mem
    · exact ih hi

lemma disjoint (h : Prefix loc F B v z lam eta Q H) : Disjoint Q H.toFinset := by
  induction h with
  | nil => simp
  | @cons Q i H hi ht ih =>
    rw [List.toFinset_cons,Finset.disjoint_insert_right]
    exact ⟨hi.1,Finset.disjoint_of_subset_left (Finset.subset_insert _ _) ih⟩

lemma nodup (h : Prefix loc F B v z lam eta Q H) : H.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons Q i H hi ht ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hm
    exact Finset.disjoint_left.mp ht.disjoint (Finset.mem_insert_self _ _)
      (List.mem_toFinset.mpr hm)
end Prefix

end PhaseSequence
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ImagePhaseUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_phase_union (Q : Finset X) (H : List X) (r : X → X) :
    Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
  ext x
  simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
  aesop

end MetricKMedianRecovery.PhaseHistoryTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PhasesBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LeafMetric
variable {V C : Type*} [PseudoMetricSpace V]

lemma original_distance (root : C → V) (u : C → ℝ) (x y : V) :
    leafDist root u (.inl x) (.inl y) = dist x y := by
  by_cases h : x = y
  · subst y; simp [leafDist_self]
  · simp [leafDist,h,height,parent]
lemma copy_distance (root : C → V) (u : C → ℝ) (x : V) (c : C) :
    leafDist root u (.inl x) (.inr c) = dist x (root c)+u c := by
  simp [leafDist,height,parent]

end MetricKMedianRecovery.LeafMetric

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestInsertEqual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CoincidentCopy
variable {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]

variable [Fintype D]

omit [DecidableEq X] in

lemma payment_zero (loc : D → X) (t K v z : ℝ) (Q : Finset X) (i f : X)
    (hf : f ∈ Q) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ t) (tau : D → ℝ) (hb : admissibleBids loc t K v z Q i tau) :
    openingPayment loc t z Q i tau = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  change max ((if activeAt loc t z Q j then tau j else t*nearestDistance (loc j) Q)
    -t*dist i (loc j)) 0 = 0
  apply max_eq_right
  by_cases hj : activeAt loc t z Q j
  · rw [ite_eq_left hj]
    have hh := (hb j hj).2.2.1 f hf
    rw [← h j,dist_comm (loc j) i] at hh
    linarith only [hh]
  · rw [ite_eq_right hj]
    have hh := mul_le_mul_of_nonneg_left (nearestDistance_le_mem (loc j) Q f hf) ht
    rw [← h j,dist_comm (loc j) i] at hh
    linarith only [hh]

omit [DecidableEq X] in
lemma not_openable (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ)
    (i f : X) (hf : f ∈ Q) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ t) (hlam : 0 < lam-(Fintype.card D:ℝ)*eta) :
    ¬etaOpenable loc F Q t K v z lam eta i := by
  rintro ⟨tau,hb,hpay,_⟩
  rw [payment_zero loc t K v z Q i f hf h ht tau hb] at hpay
  exact (not_lt_of_ge hpay) hlam

end MetricKMedianRecovery.CoincidentCopy

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

lemma original_dist (i j : V) :
    dist (original i) (original j)=dist i j := LeafMetric.original_distance root height i j

lemma leaf_dist (i j : V) (key : ℕ) (s : ℚ) :
    dist (original i) (leaf key j s)=dist i j+(max s 0:ℚ) :=
  LeafMetric.copy_distance root height i (key,j,s)

variable [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma fresh (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B)
    (i : V) (s : ℚ) : leaf key i s ∉ F.image original ∪ B := by
  intro h
  rcases Finset.mem_union.mp h with h|h
  · obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    cases hx
  · exact (lt_irrefl key) (hB (key,i,s) h)

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CoincidentHistory
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] in
lemma nearest_image (loc : D → X) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (j : D) :
    nearestDistance (loc j) (Q.image r) = nearestDistance (loc j) Q := by
  by_cases hQ : Q.Nonempty
  · have hh := LeafTransfer.nearest_images Q hQ id r (loc j) 0
      (fun x _ => (hd j x).le) (fun x _ => by simp only [id_eq,hd,add_zero,le_refl])
    have hr := hh.2
    rw [add_zero] at hr
    simpa using le_antisymm hh.1 hr
  · simp [Finset.not_nonempty_iff_eq_empty.mp hQ,nearestDistance]

omit [Fintype D] in
lemma active_image (loc : D → X) (t z : ℝ) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (j : D) :
    activeAt loc t z (Q.image r) j ↔ activeAt loc t z Q j := by
  simp only [activeAt,Finset.forall_mem_image,hd]

omit [Fintype D] in
lemma admissible_image (loc : D → X) (t K v z : ℝ) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (i : X) (tau : D → ℝ) :
    admissibleBids loc t K v z (Q.image r) i tau ↔ admissibleBids loc t K v z Q i tau := by
  simp only [admissibleBids,active_image loc t z Q r hd,Finset.forall_mem_image,hd]

lemma payment_image (loc : D → X) (t z : ℝ) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (i : X) (tau : D → ℝ) :
    openingPayment loc t z (Q.image r) i tau = openingPayment loc t z Q i tau := by
  unfold openingPayment
  apply Finset.sum_congr rfl
  intro j _
  rw [active_image loc t z Q r hd j,nearest_image loc Q r hd j]

lemma dual_image (loc : D → X) (t z : ℝ) (Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (i : X) (tau : D → ℝ) (a : D) :
    openingDual loc t z (Q.image r) i tau a = openingDual loc t z Q i tau a := by
  unfold openingDual
  apply Finset.sum_congr rfl
  intro j _
  rw [active_image loc t z Q r hd j]

lemma openable_image (loc : D → X) (F Q : Finset X) (r : X → X)
    (hd : ∀ j x, dist (loc j) (r x) = dist (loc j) x) (t K v z lam eta : ℝ) (i : X) :
    etaOpenable loc F (Q.image r) t K v z lam eta i ↔ etaOpenable loc F Q t K v z lam eta i := by
  simp only [etaOpenable,admissible_image loc t K v z Q r hd,
    payment_image loc t z Q r hd,dual_image loc t z Q r hd,active_image loc t z Q r hd]

omit [Fintype D] in
lemma swap_distances (loc : D → X) (i f : X) (hd : ∀ j, dist (loc j) i = dist (loc j) f) :
    ∀ j x, dist (loc j) (Equiv.swap i f x) = dist (loc j) x := by
  intro j x
  by_cases hxi : x = i
  · subst x; simpa using (hd j).symm
  by_cases hxf : x = f
  · subst x; simpa using hd j
  · rw [Equiv.swap_apply_of_ne_of_ne hxi hxf]

omit [PseudoMetricSpace X] in
lemma swap_alphabet (F B : Finset X) (i f : X) (hf : f ∉ F ∪ B) (x : X) (hx : x ∈ F ∪ B) :
    Equiv.swap i f x ∈ F ∪ insert f B := by
  by_cases hxi : x = i
  · subst x; simp
  · have hxf : x ≠ f := fun h => hf (h ▸ hx)
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxf]
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)

theorem entry_swap (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (i f x : X) (hf : f ∉ F ∪ B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (h : PhaseSequence.Entry loc F B Q v z lam eta x) :
    PhaseSequence.Entry loc F (insert f B) (Q.image (Equiv.swap i f)) v z lam eta (Equiv.swap i f x) := by
  have hnot : Equiv.swap i f x ∉ Q.image (Equiv.swap i f) := by
    intro hh
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hh
    exact h.1 ((Equiv.swap i f).injective he ▸ hy)
  refine ⟨hnot,?_⟩
  by_cases hxi : x = i
  · subst x
    left
    simp
  have hxf : x ≠ f := fun he => hf (he ▸ h.mem)
  rw [Equiv.swap_apply_of_ne_of_ne hxi hxf]
  rcases h.2 with hx | ⟨hx,W,hQ,hW,hop⟩
  · exact Or.inl (Finset.mem_insert_of_mem hx)
  · right
    refine ⟨hx,W.image (Equiv.swap i f),Finset.image_subset_image hQ,?_,?_⟩
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact swap_alphabet F B i f hf x (hW hx)
    · exact (openable_image loc F W (Equiv.swap i f) (swap_distances loc i f hd)
        (1-3*v) (1+v^2) v z lam eta x).mpr hop

theorem prefix_swap (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (i f : X) (hf : f ∉ F ∪ B) (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (H : List X) (h : PhaseSequence.Prefix loc F B v z lam eta Q H) :
    PhaseSequence.Prefix loc F (insert f B) v z lam eta (Q.image (Equiv.swap i f))
      (H.map (Equiv.swap i f)) := by
  induction h with
  | nil => exact PhaseSequence.Prefix.nil _
  | cons he ht ih =>
    apply PhaseSequence.Prefix.cons (entry_swap loc F B _ v z lam eta i f _ hf hd he)
    simpa only [Finset.image_insert] using ih

theorem maximal_swap (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (i f : X) (hf : f ∉ F) (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (h : PhaseSequence.Maximal loc F Q v z lam) :
    PhaseSequence.Maximal loc F (Q.image (Equiv.swap i f)) v z lam := by
  intro x hx hnot hop
  by_cases hxi : x = i
  · subst x
    by_cases hiQ : i ∈ Q
    · have hfQ : f ∈ Q.image (Equiv.swap i f) := by
        exact Finset.mem_image.mpr ⟨i,hiQ,Equiv.swap_apply_left i f⟩
      exact CoincidentCopy.not_openable loc F (Q.image (Equiv.swap i f)) (1-3*v) (1+v^2)
        v z lam 0 i f hfQ hd ht (by simpa only [mul_zero,sub_zero] using hlam) hop
    · exact h i hx hiQ ((openable_image loc F Q (Equiv.swap i f) (swap_distances loc i f hd)
        (1-3*v) (1+v^2) v z lam 0 i).mp hop)
  · have hxf : x ≠ f := fun he => hf (he ▸ hx)
    have hxQ : x ∉ Q := by
      intro hh
      apply hnot
      exact Finset.mem_image.mpr ⟨x,hh,Equiv.swap_apply_of_ne_of_ne hxi hxf⟩
    exact h x hx hxQ ((openable_image loc F Q (Equiv.swap i f) (swap_distances loc i f hd)
      (1-3*v) (1+v^2) v z lam 0 x).mp hop)

theorem valid_swap (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ)
    (i f : X) (hf : f ∉ F ∪ B) (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (H : List X)
    (h : PhaseSequence.Valid loc F B Q v z lam eta H) :
    PhaseSequence.Valid loc F (insert f B) (Q.image (Equiv.swap i f)) v z lam eta (H.map (Equiv.swap i f)) := by
  refine ⟨prefix_swap loc F B Q v z lam eta i f hf hd H h.1,?_⟩
  rw [image_phase_union]
  exact maximal_swap loc F (Q ∪ H.toFinset) v z lam i f (fun he => hf (Finset.mem_union_left _ he)) hd ht hlam h.2

theorem history_swap (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (i f : X) (hf : f ∉ F ∪ B) (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam) (q : ℕ) (T : List (List X))
    (h : History loc F B v lam eta q Q T) :
    History loc F (insert f B) v lam eta q (Q.image (Equiv.swap i f))
      (T.map (List.map (Equiv.swap i f))) := by
  induction h with
  | nil => exact History.nil _ _
  | cons hhead htail ih =>
    apply History.cons (valid_swap loc F B _ v _ lam eta i f hf hd ht hlam _ hhead)
    simpa only [image_phase_union] using ih

end MetricKMedianRecovery.CoincidentHistory

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.HistoryIsometry
open PhaseHistoryTransfer
variable {D X Y : Type*} [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [DecidableEq X] [DecidableEq Y]

omit [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y] in
lemma image_union (r : X → Y) (Q : Finset X) (H : List X) :
    Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
  ext x
  simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
  aesop

omit [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y] in
lemma after_map (r : X → Y) (Q : Finset X) (T : List (List X)) :
    after (Q.image r) (T.map (List.map r)) = (after Q T).image r := by
  induction T generalizing Q with
  | nil => rfl
  | cons H T ih =>
    simp only [List.map_cons,after,image_union]
    exact ih _

end MetricKMedianRecovery.HistoryIsometry

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeRefinement

section
open PhaseSequence PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma entry_fresh {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {C T : List X} {i : X} (h : Prefix loc F B v z lam eta Q (C++i::T)) :
    i ∉ Q ∪ (C++T).toFinset := by
  have hiL : i ∈ C++i::T := List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
  have hiQ : i ∉ Q := fun hi => Finset.disjoint_left.mp h.disjoint hi (List.mem_toFinset.mpr hiL)
  have hd := List.nodup_append.mp h.nodup
  have hiC : i ∉ C := fun hi => hd.2.2 i hi i (List.mem_cons_self ..) rfl
  have hiT := (List.nodup_cons.mp hd.2.1).1
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_append,not_or]
  exact ⟨hiQ,hiC,hiT⟩

end

open PhaseSequence PhaseMergePath

end MetricKMedianRecovery.PhaseMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafReplay
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLeafReplay
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Runs.swap_free {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (h : Runs loc F B Q v lam q n T) (i f : X)
    (hi : i∉F) (hf : f∉F∪B) (hd : ∀ j,dist (loc j) i=dist (loc j) f)
    (ht : 0≤1-3*v) (hlam : 0<lam) :
    Runs loc F (insert f B) (Q.image (Equiv.swap i f)) v lam q n T ∧
      ((after Q T)∩F).card=((after (Q.image (Equiv.swap i f)) T)∩F).card := by
  have hfix : ∀ x∈F,Equiv.swap i f x=x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (fun he=>hi (he ▸ hx))
      (fun he=>hf (Finset.mem_union_left _ (he ▸ hx)))
  have hT : T.map (List.map (Equiv.swap i f))=T := by
    have hmap : ∀ H∈T,H.map (Equiv.swap i f)=H := by
      intro H hH
      calc
        _=H.map id := List.map_congr_left (fun x hx=>hfix x (h.2.2 H hH x hx))
        _=H := List.map_id H
    calc
      _=T.map id := List.map_congr_left hmap
      _=T := List.map_id T
  have hF : F.image (Equiv.swap i f)=F := by
    calc
      _=F.image id := Finset.image_congr hfix
      _=F := Finset.image_id
  refine ⟨⟨h.1,?_,h.2.2⟩,?_⟩
  · simpa only [hT] using CoincidentHistory.history_swap loc F B Q v lam 0 i f hf hd ht hlam q T h.2.1
  · conv_rhs => rw [←hT,HistoryIsometry.after_map,←hF,
      ←Finset.image_inter _ _ (Equiv.swap i f).injective,
      Finset.card_image_of_injective _ (Equiv.swap i f).injective]

end MetricKMedianRecovery.CanonicalLeafReplay

namespace MetricKMedianRecovery.RationalLeaves

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing CanonicalLeafReplay
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] metric

lemma zero_free_replay_s238r_oai (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (f : Label V) (H : List (Label V)) (T : List (List (Label V)))
    (v lam eta : ℝ) (q n : ℕ) (hB : Before key B) (hdis : Disjoint (F.image original) B)
    (hQ : Q⊆F.image original ∪ B) (hf : f∈B) (hd : ∀ j,dist (original (loc j)) (original i)=dist (original (loc j)) f)
    (ht : 0≤1-3*v) (hlam : 0<lam)
    (hphase : Valid (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta (H++[f]))
    (h : Runs (fun j=>original (loc j)) (F.image original) B (Q∪(H++[f]).toFinset) v lam (q+1) n T) :
    Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
      (insert (leaf key i 0) (Q∪H.toFinset)) v lam (q+1) n T ∧
      finalCount (F.image original) Q (H++[f]) T =
        ((after (insert (leaf key i 0) (Q∪H.toFinset)) T)∩F.image original).card := by
  have hfF : f∉F.image original := fun he=>Finset.disjoint_left.mp hdis he hf
  have hfQ : f∉Q∪H.toFinset := by
    have he := PhaseMergeRefinement.entry_fresh (C:=H) (T:=[]) hphase.1
    simpa only [List.append_nil] using he
  have hfresh := fresh F B key hB i 0
  have hco : ∀ j,dist (original (loc j)) f=dist (original (loc j)) (leaf key i 0) := by
    intro j
    rw [←hd j,leaf_dist,original_dist]
    simp
  obtain ⟨hh,hcount⟩ := Runs.swap_free h f (leaf key i 0) hfF hfresh hco ht hlam
  have hsub : Q∪H.toFinset⊆F.image original ∪ B := by
    apply Finset.union_subset hQ
    intro x hx
    apply hphase.1.opened_subset
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hx))
  have hfix : ∀ x∈Q∪H.toFinset,Equiv.swap f (leaf key i 0) x=x := by
    intro x hx
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; exact hfQ (he ▸ hx)
    · intro he; exact hfresh (hsub (he ▸ hx))
  have him : (Q∪H.toFinset).image (Equiv.swap f (leaf key i 0))=Q∪H.toFinset := by
    calc
      _=(Q∪H.toFinset).image id := Finset.image_congr hfix
      _=_ := Finset.image_id
  have hb : Q∪(H++[f]).toFinset=insert f (Q∪H.toFinset) := by
    simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
  simpa only [finalCount,hb,Finset.image_insert,Equiv.swap_apply_left,him] using And.intro hh hcount

end MetricKMedianRecovery.RationalLeaves

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r_oai.{u_1}
