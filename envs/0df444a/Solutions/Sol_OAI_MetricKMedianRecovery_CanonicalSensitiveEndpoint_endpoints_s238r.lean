-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:41:41.039697+00:00
-- url     : https://prove2.me/submissions/27dc6f77-2a50-4a6f-ae2d-3eb91cf8bb7a

import Mathlib
import Definitions.Def_Q238L026
import Theorems.Thm_OAI_MetricKMedianRecovery_RationalLeaves_zero_free_replay_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ActiveInsert
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.DisablingCopy
variable {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]

variable [Fintype D]

lemma numerical_bound (v M : ℝ) (N : ℕ) (hv : 0 < v) (hv' : v < 1/6)
    (hM : 0 < M) (hN : 3 ≤ N) :
    (1+v^2)*(M+8*N*M) < 10*N*M ∧ 10*N*M < (1-3*v)*(20*N*M) := by
  have hv2 : v^2 < 1/36 := by nlinarith
  have hn : (3:ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · have hz : 0 < M+8*N*M := by positivity
    have hh := mul_lt_mul_of_pos_right hv2 hz
    have hnm : 3*M ≤ N*M := mul_le_mul_of_nonneg_right hn hM.le
    nlinarith
  · have hnm : 0 < (N:ℝ)*M := mul_pos (by linarith) hM
    nlinarith

end MetricKMedianRecovery.DisablingCopy

namespace MetricKMedianRecovery.DisablingHistory
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [PseudoMetricSpace X] in
lemma member_ne (F B : Finset X) (f i : X) (hf : f ∉ F ∪ B) (hi : i ∈ F ∪ B) : i ≠ f := by
  rintro rfl
  exact hf hi

omit [PseudoMetricSpace X] in
lemma after_insert (Q : Finset X) (T : List (List X)) (f : X) :
    PhaseHistoryTransfer.after (insert f Q) T = insert f (PhaseHistoryTransfer.after Q T) := by
  induction T generalizing Q with
  | nil => rfl
  | cons H T ih =>
    simp only [PhaseHistoryTransfer.after,Finset.insert_union]
    exact ih _

end MetricKMedianRecovery.DisablingHistory

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

lemma advance_rows (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ)
    (H : List X) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hhead : PhaseSequence.Valid loc F B Q v ((1+v^2)^q) lam eta H) :
    ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^(q+1)) (Q ∪ H.toFinset) i ≤ lam := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hrow' : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (Q ∪ H.toFinset) i ≤ lam := by
    intro i hi
    exact (bidRow_antitone_open loc (1-3*v) ((1+v^2)^q) Q (Q ∪ H.toFinset) i ht
      Finset.subset_union_left).trans (hrow i hi)
  have hz : 0 < (1+v^2)^q := by positivity
  simpa only [pow_succ,mul_comm] using
    phase_update_no_overbid loc F (Q ∪ H.toFinset) v ((1+v^2)^q) lam
      hv hvsmall hz hlam hrow' hhead.2

end MetricKMedianRecovery.PhaseHistoryTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_BudgetBound
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.UniformRowDisabling
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [DecidableEq X] in

lemma budget_bound (loc : D → X) (F Q : Finset X) (hF : F.Nonempty)
    (t z lam M : ℝ) (hrow : ∀ i ∈ F, bidRow loc t z Q i ≤ lam)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (j : D) :
    clippedAt loc t z Q j ≤ M+lam := by
  obtain ⟨i,hi⟩ := hF
  have hsum : max (clippedAt loc t z Q j-dist i (loc j)) 0 ≤ bidRow loc t z Q i :=
    Finset.single_le_sum (fun a _ => le_max_right (clippedAt loc t z Q a-dist i (loc a)) 0)
      (Finset.mem_univ j)
  have hh := (le_max_left (clippedAt loc t z Q j-dist i (loc j)) 0).trans (hsum.trans (hrow i hi))
  linarith only [hh,hM i hi j]

omit [Fintype D] in
lemma active_insert (loc : D → X) (Q : Finset X) (t z K W : ℝ) (f : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (j : D) :
    activeAt loc t z (insert f Q) j ↔ activeAt loc t z Q j := by
  constructor
  · intro h i hi
    exact h i (Finset.mem_insert_of_mem hi)
  · intro h i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hz : z ≤ W := by simpa only [clippedAt_of_active loc t z Q j ht h] using hbound j
      exact (hz.trans (by nlinarith only [hK,hW] : W ≤ K*W)).trans_lt (hfar j)
    · exact h i hi

omit [Fintype D] in
lemma inactive_distance (loc : D → X) (Q : Finset X) (t z K W : ℝ) (f : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (j : D) (hj : ¬activeAt loc t z Q j) :
    t*nearestDistance (loc j) (insert f Q) = t*nearestDistance (loc j) Q := by
  have hQ := inactive_nonempty loc t z Q j hj
  have hb : t*nearestDistance (loc j) Q ≤ W := by
    simpa only [clippedAt_of_inactive loc t z Q j ht hj] using hbound j
  apply le_antisymm
  · exact mul_le_mul_of_nonneg_left
      (nearestDistance_antitone _ _ _ hQ (Finset.subset_insert _ _)) ht
  · obtain ⟨g,hg,he⟩ := nearestDistance_attained (loc j) (insert f Q) (Finset.insert_nonempty _ _)
    rw [he]
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact (hb.trans (by nlinarith only [hK,hW] : W ≤ K*W)).trans (hfar j).le
    · exact mul_le_mul_of_nonneg_left (nearestDistance_le_mem _ _ _ hg) ht

omit [Fintype D] in
lemma admissible_insert (loc : D → X) (Q : Finset X) (t z K W v : ℝ) (f i : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (tau : D → ℝ) :
    admissibleBids loc t K v z (insert f Q) i tau ↔ admissibleBids loc t K v z Q i tau := by
  constructor
  · intro h j hj
    have hh := h j ((active_insert loc Q t z K W f ht hK hW hbound hfar j).mpr hj)
    exact ⟨hh.1,hh.2.1,(fun g hg => hh.2.2.1 g (Finset.mem_insert_of_mem hg)),hh.2.2.2⟩
  · intro h j hj
    have hj' := (active_insert loc Q t z K W f ht hK hW hbound hfar j).mp hj
    have hh := h j hj'
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.2⟩
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · have hz : z ≤ W := by simpa only [clippedAt_of_active loc t z Q j ht hj'] using hbound j
      exact hh.2.1.trans ((mul_le_mul_of_nonneg_left hz (by linarith only [hK])).trans (hfar j).le)
    · exact hh.2.2.1 g hg

lemma payment_insert (loc : D → X) (Q : Finset X) (t z K W : ℝ) (f i : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (tau : D → ℝ) :
    openingPayment loc t z (insert f Q) i tau = openingPayment loc t z Q i tau := by
  classical
  unfold openingPayment
  apply Finset.sum_congr rfl
  intro j _
  rw [active_insert loc Q t z K W f ht hK hW hbound hfar j]
  by_cases hj : activeAt loc t z Q j
  · simp only [ite_eq_left hj]
  · simp only [ite_eq_right hj,inactive_distance loc Q t z K W f ht hK hW hbound hfar j hj]

lemma dual_insert (loc : D → X) (Q : Finset X) (t z K W : ℝ) (f i : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (tau : D → ℝ) (a : D) :
    openingDual loc t z (insert f Q) i tau a = openingDual loc t z Q i tau a := by
  classical
  simp only [openingDual,active_insert loc Q t z K W f ht hK hW hbound hfar]

theorem openable_insert (loc : D → X) (F Q : Finset X) (t z K W v lam eta : ℝ) (f i : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) :
    etaOpenable loc F (insert f Q) t K v z lam eta i ↔ etaOpenable loc F Q t K v z lam eta i := by
  simp only [etaOpenable,admissible_insert loc Q t z K W v f i ht hK hW hbound hfar,
    payment_insert loc Q t z K W f i ht hK hW hbound hfar,
    dual_insert loc Q t z K W f _ ht hK hW hbound hfar,
    active_insert loc Q t z K W f ht hK hW hbound hfar]

lemma entry_insert (loc : D → X) (F B Q : Finset X) (v z lam eta W : ℝ) (f i : X)
    (hv : v < 1/6) (hW : 0 ≤ W) (hf : f ∉ F ∪ B)
    (hbound : ∀ j, clippedAt loc (1-3*v) z Q j ≤ W)
    (hfar : ∀ j, (1+v^2)*W < (1-3*v)*dist (loc j) f)
    (h : Entry loc F B Q v z lam eta i) :
    Entry loc F (insert f B) (insert f Q) v z lam eta i := by
  have ht : 0 ≤ 1-3*v := by linarith only [hv]
  have hif := DisablingHistory.member_ne F B f i hf h.mem
  refine ⟨by simpa only [Finset.mem_insert,not_or] using And.intro hif h.1,?_⟩
  rcases h.2 with hi | ⟨hi,S,hQ,hS,hop⟩
  · exact Or.inl (Finset.mem_insert_of_mem hi)
  · right
    refine ⟨hi,insert f S,Finset.insert_subset_insert f hQ,?_,?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · exact (Finset.union_subset_union_right (Finset.subset_insert _ _)) (hS hx)
    · exact (openable_insert loc F S (1-3*v) z (1+v^2) W v lam eta f i ht
        (by nlinarith only [sq_nonneg v]) hW
        (fun j => (clippedAt_antitone_open loc (1-3*v) z Q S j ht hQ).trans (hbound j)) hfar).mpr hop

lemma prefix_insert (loc : D → X) (F B Q : Finset X) (v z lam eta W : ℝ) (f : X)
    (H : List X) (hv : v < 1/6) (hW : 0 ≤ W) (hf : f ∉ F ∪ B)
    (hbound : ∀ j, clippedAt loc (1-3*v) z Q j ≤ W)
    (hfar : ∀ j, (1+v^2)*W < (1-3*v)*dist (loc j) f)
    (h : Prefix loc F B v z lam eta Q H) :
    Prefix loc F (insert f B) v z lam eta (insert f Q) H := by
  induction h with
  | nil Q => exact Prefix.nil _
  | @cons Q i H hi htail ih =>
    apply Prefix.cons (entry_insert loc F B Q v z lam eta W f i hv hW hf hbound hfar hi)
    rw [Finset.insert_comm]
    apply ih
    intro j
    exact (clippedAt_antitone_open loc (1-3*v) z Q (insert i Q) j
      (by linarith only [hv]) (Finset.subset_insert _ _)).trans (hbound j)

lemma valid_insert (loc : D → X) (F B Q : Finset X) (v z lam eta W : ℝ) (f : X)
    (H : List X) (hv : v < 1/6) (hW : 0 ≤ W) (hf : f ∉ F ∪ B)
    (hbound : ∀ j, clippedAt loc (1-3*v) z Q j ≤ W)
    (hfar : ∀ j, (1+v^2)*W < (1-3*v)*dist (loc j) f)
    (h : Valid loc F B Q v z lam eta H) :
    Valid loc F (insert f B) (insert f Q) v z lam eta H := by
  refine ⟨prefix_insert loc F B Q v z lam eta W f H hv hW hf hbound hfar h.1,?_⟩
  intro i hi hnot hop
  have hiQ : i ∉ Q ∪ H.toFinset := by
    intro hh
    apply hnot
    simpa only [Finset.insert_union] using Finset.mem_insert_of_mem hh
  apply h.2 i hi hiQ
  apply (openable_insert loc F (Q ∪ H.toFinset) (1-3*v) z (1+v^2) W v lam 0 f i
    (by linarith only [hv]) (by nlinarith only [sq_nonneg v]) hW
    (fun j => (clippedAt_antitone_open loc (1-3*v) z Q (Q ∪ H.toFinset) j
      (by linarith only [hv]) Finset.subset_union_left).trans (hbound j)) hfar).mp
  simpa only [Finset.insert_union] using hop

theorem history_insert (loc : D → X) (F B Q : Finset X) (hF : F.Nonempty)
    (v lam eta M : ℝ) (f : X) (q : ℕ) (T : List (List X))
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hf : f ∉ F ∪ B) (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hfar : ∀ j, (1+v^2)*(M+lam) < (1-3*v)*dist (loc j) f)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (h : History loc F B v lam eta q Q T) :
    History loc F (insert f B) v lam eta q (insert f Q) T := by
  induction h with
  | nil q Q => exact History.nil _ _
  | @cons q Q H T hhead htail ih =>
    apply History.cons (valid_insert loc F B Q v ((1+v^2)^q) lam eta (M+lam) f H
      hvsmall (add_nonneg hM hlam.le) hf (budget_bound loc F Q hF (1-3*v)
        ((1+v^2)^q) lam M hrow hdiam) hfar hhead)
    rw [Finset.insert_union]
    exact ih (advance_rows loc F B Q v lam eta q H hv hvsmall hlam hrow hhead)

end MetricKMedianRecovery.UniformRowDisabling

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

lemma nearest_insert_equal (x : X) (Q : Finset X) (i f : X)
    (h : dist x i = dist x f) :
    nearestDistance x (insert i Q) = nearestDistance x (insert f Q) := by
  have hh (i f : X) (h : dist x i = dist x f) :
      nearestDistance x (insert i Q) ≤ nearestDistance x (insert f Q) := by
    obtain ⟨g,hg,he⟩ := nearestDistance_attained x (insert f Q) (Finset.insert_nonempty _ _)
    rw [he]
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact (nearestDistance_le_mem x (insert i Q) i (Finset.mem_insert_self _ _)).trans h.le
    · exact nearestDistance_le_mem x (insert i Q) g (Finset.mem_insert_of_mem hg)
  exact le_antisymm (hh i f h) (hh f i h.symm)

lemma active_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (j : D) :
    activeAt loc t z (insert i Q) j ↔ activeAt loc t z (insert f Q) j := by
  simp only [activeAt,Finset.forall_mem_insert,h j]

lemma admissible_insert_equal (loc : D → X) (t K v z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) :
    admissibleBids loc t K v z (insert i Q) k tau ↔
      admissibleBids loc t K v z (insert f Q) k tau := by
  simp only [admissibleBids,active_insert_equal loc t z Q i f h,
    Finset.forall_mem_insert,h]

variable [Fintype D]

lemma payment_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) :
    openingPayment loc t z (insert i Q) k tau = openingPayment loc t z (insert f Q) k tau := by
  classical
  simp only [openingPayment,active_insert_equal loc t z Q i f h,
    nearest_insert_equal _ _ _ _ (h _)]

lemma dual_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) (a : D) :
    openingDual loc t z (insert i Q) k tau a = openingDual loc t z (insert f Q) k tau a := by
  classical
  simp only [openingDual,active_insert_equal loc t z Q i f h]

theorem openable_insert_equal (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ)
    (i f k : X) (h : ∀ j, dist (loc j) i = dist (loc j) f) :
    etaOpenable loc F (insert i Q) t K v z lam eta k ↔
      etaOpenable loc F (insert f Q) t K v z lam eta k := by
  simp only [etaOpenable,admissible_insert_equal loc t K v z Q i f _ h,
    payment_insert_equal loc t z Q i f _ h,dual_insert_equal loc t z Q i f _ h,
    active_insert_equal loc t z Q i f h]

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

theorem maximal_replace (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (i f : X) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hmax : ∀ k ∈ F, k ∉ insert i Q →
      ¬etaOpenable loc F (insert i Q) (1-3*v) (1+v^2) v z lam 0 k) :
    ∀ k ∈ F, k ∉ insert f Q →
      ¬etaOpenable loc F (insert f Q) (1-3*v) (1+v^2) v z lam 0 k := by
  intro k hk hkn
  by_cases hki : k = i
  · subst k
    exact not_openable loc F (insert f Q) (1-3*v) (1+v^2) v z lam 0 i f
      (Finset.mem_insert_self _ _) h ht (by simpa only [mul_zero,sub_zero] using hlam)
  · intro hop
    have hn : k ∉ insert i Q := by
      simpa only [Finset.mem_insert,not_or] using ⟨hki,fun hkQ => hkn (Finset.mem_insert_of_mem hkQ)⟩
    exact hmax k hk hn ((openable_insert_equal loc F Q (1-3*v) (1+v^2) v z lam 0 i f k h).mpr hop)

omit [Fintype D] [PseudoMetricSpace X] in

lemma paid_count (F Q : Finset X) (i f : X) (hi : i ∈ F) (hin : i ∉ Q) (hf : f ∉ F) :
    (F ∩ insert i Q).card = (F ∩ insert f Q).card+1 := by
  have he : F ∩ insert i Q = insert i (F ∩ Q) := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨hF,hx | hQ⟩
      · exact Or.inl hx
      · exact Or.inr ⟨hF,hQ⟩
    · rintro (rfl | ⟨hF,hQ⟩)
      · exact ⟨hi,Or.inl rfl⟩
      · exact ⟨hF,Or.inr hQ⟩
  have hf' : F ∩ insert f Q = F ∩ Q := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨hF,rfl | hQ⟩
      · exact (hf hF).elim
      · exact ⟨hF,hQ⟩
    · intro hx
      exact ⟨hx.1,Or.inr hx.2⟩
  rw [he,hf',Finset.card_insert_of_notMem (fun h => hin (Finset.mem_inter.mp h).2)]

end MetricKMedianRecovery.CoincidentCopy

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EntryFreeMono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeSurgery
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma entry_free_mono {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ} {i : X}
    (h : Entry loc F B Q v z lam eta i) (hB : B ⊆ B') :
    Entry loc F B' Q v z lam eta i := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with hi | ⟨hi,W,hW,hWF,hop⟩
  · exact Or.inl (hB hi)
  · exact Or.inr ⟨hi,W,hW,hWF.trans (Finset.union_subset_union_right hB),hop⟩

lemma prefix_free_mono {loc : D → X} {F B B' Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Prefix loc F B v z lam eta Q H) (hB : B ⊆ B') :
    Prefix loc F B' v z lam eta Q H := by
  induction h with
  | nil Q => exact Prefix.nil Q
  | cons hi ht ih => exact Prefix.cons (entry_free_mono hi hB) ih

end MetricKMedianRecovery.PhaseMergeSurgery

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

lemma rows_spec {d : ℕ} (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hd : ∀ i j,(distance i j:ℝ)=dist i (loc j)) :
    ∀ x j,(rows distance x j:ℝ)=dist x (original (loc j)) := by
  intro x j
  cases x with
  | inl x =>
    change (distance x j:ℝ)=dist (original x) (original (loc j))
    rw [original_dist,hd]
  | inr c =>
    rw [dist_comm]
    change ((distance (root c) j+max c.2.2 0:ℚ):ℝ)=dist (original (loc j)) (leaf c.1 c.2.1 c.2.2)
    rw [Rat.cast_add,leaf_dist,hd,dist_comm]
    rfl

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeRefinement

section
open PhaseSequence PhaseMergeSurgery PhaseMergePath
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

open PhaseSequence PhaseMergeSurgery PhaseMergePath

end MetricKMedianRecovery.PhaseMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseSequence PhaseMergeSurgery PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem prefix_twin (loc : D → X) (F B : Finset X) (v z lam eta : ℝ)
    (i f : X) (_hi : i ∈ F) (hf : f ∈ B) (hdis : Disjoint F B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f)
    (H : List X) (R : Finset X) (hiR : i ∉ R) (hfR : f ∉ R)
    (hreg : ∀ k ∈ H, k ∈ F) (h : Prefix loc F B v z lam eta (insert i R) H) :
    Prefix loc F B v z lam eta (insert f R) H := by
  have hfF : f ∉ F := fun h => Finset.disjoint_left.mp hdis h hf
  induction H generalizing R with
  | nil => exact Prefix.nil _
  | cons k H ih =>
    cases h with
    | cons hk ht =>
      have hkF : k ∈ F := hreg k (List.mem_cons_self ..)
      have hki : k ≠ i := fun e => hk.1 (e ▸ Finset.mem_insert_self _ _)
      have hkf : k ≠ f := fun e => hfF (e ▸ hkF)
      have hkR : k ∉ R := fun h => hk.1 (Finset.mem_insert_of_mem h)
      have hentry : Entry loc F B (insert f R) v z lam eta k := by
        refine ⟨by simpa only [Finset.mem_insert,not_or] using And.intro hkf hkR,?_⟩
        rcases hk.2 with hkB | ⟨hkF',W,hW,hWF,hop⟩
        · exact (Finset.disjoint_left.mp hdis hkF hkB).elim
        · have hiW : i ∈ W := hW (Finset.mem_insert_self _ _)
          refine Or.inr ⟨hkF',insert f (W.erase i),?_,?_,?_⟩
          · apply Finset.insert_subset_insert
            intro x hx
            exact Finset.mem_erase.mpr ⟨fun e => hiR (e ▸ hx),hW (Finset.mem_insert_of_mem hx)⟩
          · exact Finset.insert_subset (Finset.mem_union_right _ hf) ((Finset.erase_subset _ _).trans hWF)
          · have heq : insert i (W.erase i) = W := Finset.insert_erase hiW
            rw [← heq] at hop
            exact (CoincidentCopy.openable_insert_equal loc F (W.erase i) (1-3*v)
              (1+v^2) v z lam eta i f k hd).mp hop
      have hiR' : i ∉ insert k R := by simpa only [Finset.mem_insert,not_or] using And.intro (Ne.symm hki) hiR
      have hfR' : f ∉ insert k R := by simpa only [Finset.mem_insert,not_or] using And.intro (Ne.symm hkf) hfR
      have htail : Prefix loc F B v z lam eta (insert i (insert k R)) H := by
        simpa only [Finset.insert_comm] using ht
      have hp := ih (insert k R) hiR' hfR' (fun j hj => hreg j (List.mem_cons_of_mem _ hj)) htail
      exact Prefix.cons hentry (by simpa only [Finset.insert_comm] using hp)

lemma absent_after_prefix {loc : D → X} {F B R : Finset X} {v z lam eta : ℝ}
    {i : X} {H : List X} (hiR : i ∉ R)
    (h : Prefix loc F B v z lam eta (insert i R) H) : i ∉ R ∪ H.toFinset := by
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hiR hm
  · exact Finset.disjoint_left.mp h.disjoint (Finset.mem_insert_self _ _) hm

omit [PseudoMetricSpace X] in
lemma free_absent_after {F B R : Finset X} {f : X} {H : List X}
    (hf : f ∈ B) (hdis : Disjoint F B) (hfR : f ∉ R) (hreg : ∀ k ∈ H, k ∈ F) :
    f ∉ R ∪ H.toFinset := by
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hfR hm
  · exact Finset.disjoint_left.mp hdis (hreg f (List.mem_toFinset.mp hm)) hf

theorem history_twin (loc : D → X) (F B : Finset X) (v lam : ℝ)
    (i f : X) (hi : i ∈ F) (hf : f ∈ B) (hdis : Disjoint F B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (T : List (List X)) (q : ℕ) (R : Finset X) (hiR : i ∉ R) (hfR : f ∉ R)
    (hreg : Regular F T) (h : History loc F B v lam 0 q (insert i R) T) :
    History loc F B v lam 0 q (insert f R) T ∧
      ∃ U : Finset X, i ∉ U ∧ f ∉ U ∧
        after (insert i R) T = insert i U ∧ after (insert f R) T = insert f U := by
  induction T generalizing q R with
  | nil => exact ⟨History.nil _ _,R,hiR,hfR,rfl,rfl⟩
  | cons H T ih =>
    cases h with
    | cons hH hT =>
      have hHr : ∀ k ∈ H, k ∈ F := hreg H (List.mem_cons_self ..)
      have hp := prefix_twin loc F B v ((1+v^2)^q) lam 0 i f hi hf hdis hd H R hiR hfR hHr hH.1
      have hmax : Maximal loc F (insert i (R ∪ H.toFinset)) v ((1+v^2)^q) lam := by
        simpa only [Finset.insert_union] using hH.2
      have hm := CoincidentCopy.maximal_replace loc F (R ∪ H.toFinset) v ((1+v^2)^q) lam i f hd ht hlam hmax
      have hH' : Valid loc F B (insert f R) v ((1+v^2)^q) lam 0 H :=
        ⟨hp,by simpa only [PhaseSequence.Maximal,Finset.insert_union] using hm⟩
      have hiU := absent_after_prefix hiR hH.1
      have hfU := free_absent_after hf hdis hfR hHr
      have hrT : Regular F T := fun G hG => hreg G (List.mem_cons_of_mem _ hG)
      have hhT : History loc F B v lam 0 (q+1) (insert i (R ∪ H.toFinset)) T := by
        simpa only [Finset.insert_union] using hT
      obtain ⟨hT',U,hiU',hfU',ha,hb⟩ := ih (q+1) (R ∪ H.toFinset) hiU hfU hrT hhT
      refine ⟨History.cons hH' (by simpa only [Finset.insert_union] using hT'),U,hiU',hfU',?_,?_⟩
      · simpa only [after,Finset.insert_union] using ha
      · simpa only [after,Finset.insert_union] using hb

end MetricKMedianRecovery.PhaseMergeCompletion
namespace MetricKMedianRecovery.PhaseCountCrossing
open PhaseSequence PhaseMergeRefinement PhaseMergeCompletion PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Sandwich.symm {k a b : ℕ} (h : Sandwich k a b) : Sandwich k b a := Or.symm h

end MetricKMedianRecovery.PhaseCountCrossing

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Runs.mono_free {loc : D → X} {F B B' Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (h : Runs loc F B Q v lam q n T) (hB : B⊆B') :
    Runs loc F B' Q v lam q n T := by
  refine ⟨h.1,?_,h.2.2⟩
  have hh := h.2.1
  clear h
  induction hh with
  | nil => exact .nil _ _
  | cons hhead htail ih =>
    exact .cons ⟨PhaseMergeSurgery.prefix_free_mono hhead.1 hB,hhead.2⟩ ih

end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafReplay
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.levelWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.parentWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLeafReplay
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Runs.insert_far {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (h : Runs loc F B Q v lam q n T) (M : ℝ) (f : X)
    (hF : F.Nonempty) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam) (hM : 0≤M)
    (hf : f∉F∪B) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M)
    (hfar : ∀ j,(1+v^2)*(M+lam)<(1-3*v)*dist (loc j) f)
    (hrow : ∀ i∈F,bidRow loc (1-3*v) ((1+v^2)^q) Q i≤lam) :
    Runs loc F (insert f B) (insert f Q) v lam q n T ∧
      ((after Q T)∩F).card=((after (insert f Q) T)∩F).card := by
  refine ⟨⟨h.1,UniformRowDisabling.history_insert loc F B Q hF v lam 0 M f q T
    hv hv1 hlam hM hf hdiam hfar hrow h.2.1,h.2.2⟩,?_⟩
  rw [DisablingHistory.after_insert,Finset.insert_inter_of_notMem
    (fun he=>hf (Finset.mem_union_left _ he))]

lemma Runs.replace_paid {loc : D → X} {F B R : Finset X} {v lam : ℝ} {q n : ℕ}
    {T : List (List X)} (i f : X) (hi : i∈F) (hf : f∈B) (hdis : Disjoint F B)
    (hiR : i∉R) (hfR : f∉R) (hd : ∀ j,dist (loc j) i=dist (loc j) f)
    (ht : 0≤1-3*v) (hlam : 0<lam) (h : Runs loc F B (insert i R) v lam q n T) :
    Runs loc F B (insert f R) v lam q n T ∧
      ((after (insert i R) T)∩F).card=((after (insert f R) T)∩F).card+1 := by
  obtain ⟨hh,U,hiU,_,ha,hb⟩ := history_twin loc F B v lam i f hi hf hdis hd ht hlam
    T q R hiR hfR h.2.2 h.2.1
  refine ⟨⟨h.1,hh,h.2.2⟩,?_⟩
  rw [ha,hb,Finset.inter_comm (insert i U),Finset.inter_comm (insert f U)]
  exact CoincidentCopy.paid_count F U i f hi hiU (fun he=>Finset.disjoint_left.mp hdis he hf)

end MetricKMedianRecovery.CanonicalLeafReplay

namespace MetricKMedianRecovery.RationalLeaves

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing CanonicalLeafReplay
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] metric

lemma far_replay (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (v lam M : ℝ) (q n N : ℕ) (s : ℚ) (T : List (List (Label V)))
    (hF : F.Nonempty) (hB : Before key B) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (hM : 0<M) (hN : 3≤N) (hlamUpper : lam≤8*N*M) (hs : 20*N*M≤(s:ℝ))
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M)
    (hrow : ∀ x∈F.image original,bidRow (fun j=>original (loc j)) (1-3*v) ((1+v^2)^q) Q x≤lam)
    (h : Runs (fun j=>original (loc j)) (F.image original) B Q v lam q n T) :
    Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i s) B)
      (insert (leaf key i s) Q) v lam q n T ∧
      ((after Q T)∩F.image original).card=((after (insert (leaf key i s) Q) T)∩F.image original).card := by
  apply Runs.insert_far h M (leaf key i s) (hF.image original) hv hv1 hlam hM.le (fresh F B key hB i s)
  · rintro x hx j
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    simpa only [original_dist] using hdiam a ha j
  · intro j
    obtain ⟨h₁,h₂⟩ := DisablingCopy.numerical_bound v M N hv hv1 hM hN
    have h₀ : (1+v^2)*(M+lam)≤(1+v^2)*(M+8*N*M) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlamUpper]) (by positivity)
    have ht : 0≤1-3*v := by linarith only [hv1]
    have hs' : 20*N*M≤dist (original (loc j)) (leaf key i s) := by
      rw [leaf_dist]
      have hm : (s:ℝ)≤(max s 0:ℚ) := by exact_mod_cast le_max_left s 0
      exact hs.trans (hm.trans (le_add_of_nonneg_left dist_nonneg))
    exact (h₀.trans_lt (h₁.trans h₂)).trans_le (mul_le_mul_of_nonneg_left hs' ht)
  · exact hrow

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing CanonicalLeafReplay
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] metric

lemma zero_paid_replay (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (C H : List (Label V)) (T : List (List (Label V)))
    (v lam eta : ℝ) (q n : ℕ) (hi : i∈F) (hB : Before key B)
    (hdis : Disjoint (F.image original) B) (hQ : Q⊆F.image original ∪ B)
    (ht : 0≤1-3*v) (hlam : 0<lam)
    (hphase : Valid (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta (C++original i::H))
    (h : Runs (fun j=>original (loc j)) (F.image original) B (Q∪(C++original i::H).toFinset) v lam (q+1) n T) :
    Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
      (insert (leaf key i 0) (Q∪(C++H).toFinset)) v lam (q+1) n T ∧
      finalCount (F.image original) Q (C++original i::H) T =
        ((after (insert (leaf key i 0) (Q∪(C++H).toFinset)) T)∩F.image original).card+1 := by
  have hfresh := fresh F B key hB i 0
  have hiQ := PhaseMergeRefinement.entry_fresh hphase.1
  have hco : ∀ j,dist (original (loc j)) (original i)=dist (original (loc j)) (leaf key i 0) := by
    intro j; rw [leaf_dist,original_dist]; simp
  have hd' : Disjoint (F.image original) (insert (leaf key i 0) B) := by
    rw [Finset.disjoint_insert_right]
    exact ⟨fun he=>hfresh (Finset.mem_union_left _ he),hdis⟩
  have hb : Q∪(C++original i::H).toFinset=insert (original i) (Q∪(C++H).toFinset) := by
    simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
  have hfR : leaf key i 0∉Q∪(C++H).toFinset := by
    intro he
    apply hfresh
    rcases Finset.mem_union.mp he with he|he
    · exact hQ he
    · apply hphase.1.opened_subset
      apply List.mem_toFinset.mpr
      rcases List.mem_append.mp (List.mem_toFinset.mp he) with he|he
      · exact List.mem_append_left _ he
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ he)
  have hm := h.mono_free (Finset.subset_insert (leaf key i 0) B)
  rw [hb] at hm
  obtain ⟨hh,hcount⟩ := Runs.replace_paid (original i) (leaf key i 0)
    (Finset.mem_image.mpr ⟨i,hi,rfl⟩) (Finset.mem_insert_self _ _) hd' hiQ hfR hco ht hlam hm
  exact ⟨hh,by simpa only [finalCount,hb] using hcount⟩

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthSearch
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma endpoints_s238r_oai (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (B Q : Finset (Label V)) (v lam eta M : ℝ)
    (q n k key N : ℕ) (b : ℚ) (H G : List (Label V))
    (T U : List (List (Label V))) (J : Plan (Label V))
    (hF : F.Nonempty) (hB : Before key B) (hQ : Q⊆F.image original∪B)
    (hdis : Disjoint (F.image original) B) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (hM : 0<M) (hN : 3≤N) (hlamUpper : lam≤8*N*M) (hb : 20*N*M≤(b:ℝ))
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M)
    (hrow : ∀ x∈F.image original,bidRow (fun j=>original (loc j)) (1-3*v) ((1+v^2)^q) Q x≤lam)
    (hH : Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta H)
    (hG : Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta G)
    (hT : Runs (fun j=>original (loc j)) (F.image original) B (Q∪H.toFinset) v lam (q+1) n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) B (Q∪G.toFinset) v lam (q+1) n U)
    (hacc : accepts (rows distance) (F.image original) H G J)
    (hs : Sandwich k (finalCount (F.image original) Q H T) (finalCount (F.image original) Q G U)) :
    EndpointSpec loc F B Q v lam eta q n k key b H T U J := by
  have hfar : ∀ (i : V) (C : List (Label V)) (W : List (List (Label V))),
      Valid (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta C →
      Runs (fun j=>original (loc j)) (F.image original) B (Q∪C.toFinset) v lam (q+1) n W →
      Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i b) B)
        (insert (leaf key i b) (Q∪C.toFinset)) v lam (q+1) n W ∧
      finalCount (F.image original) Q C W=
        ((after (insert (leaf key i b) (Q∪C.toFinset)) W)∩F.image original).card := by
    intro i C W hC hW
    exact far_replay loc F B (Q∪C.toFinset) key i v lam M (q+1) n N b W
      hF hB hv hv1 hlam hM hN hlamUpper hb hdiam
      (PhaseHistoryTransfer.advance_rows _ _ _ _ _ _ _ _ C hv hv1 hlam hrow hC) hW
  cases J with
  | free i f =>
    obtain ⟨hi,hf,rfl,hco⟩ := hacc
    obtain ⟨i,hiV,rfl⟩ := Finset.mem_image.mp hi
    have hfB : f∈B := by
      have hh := hG.1.1.opened_subset (List.mem_toFinset.mpr (List.mem_append_right H (List.mem_cons_self ..)))
      exact (Finset.mem_union.mp hh).resolve_left hf
    have hdist : ∀ j,dist (original (loc j)) (original i)=dist (original (loc j)) f := by
      intro j
      rw [dist_comm (original (loc j)) (original i),dist_comm (original (loc j)) f]
      rw [← rows_spec loc distance hmetric,← rows_spec loc distance hmetric,hco j]
    obtain ⟨hz,hzcount⟩ := zero_free_replay_s238r loc F B Q key i f H U v lam eta q n hB hdis hQ hfB
      hdist (by linarith) hlam hG.1 hU
    obtain ⟨hb',hbcount⟩ := hfar i H T hH.1 hT
    refine ⟨hH,hz,hb',Or.inr ?_⟩
    simp only [Plan.root,Plan.common,Plan.small,Plan.large,parent,original,Function.Embedding.coeFn_mk,Sum.elim_inl,id_eq] at hzcount hbcount hs ⊢
    rw [←hzcount,←hbcount]
    exact hs.symm
  | paid C L i =>
    obtain ⟨hi,rfl,rfl⟩ := hacc
    obtain ⟨i,hiV,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hz,hzcount⟩ := zero_paid_replay loc F B Q key i C L T v lam eta q n hiV hB hdis hQ
      (by linarith) hlam hH.1 hT
    obtain ⟨hb',hbcount⟩ := hfar i (C++L) U hG.1 hU
    refine ⟨hG,hz,hb',?_⟩
    simp only [Plan.root,Plan.common,Plan.small,Plan.large,parent,original,Function.Embedding.coeFn_mk,Sum.elim_inl,id_eq] at hzcount hbcount hs ⊢
    rw [←hbcount]
    unfold Sandwich at hs ⊢
    omega

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238r_oai.{u_1}
