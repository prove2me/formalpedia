-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:36:17.182772+00:00
-- url     : https://prove2.me/submissions/d07c8e9b-6dcb-45e8-be32-988a55c8cbe1

import Mathlib
import Definitions.Def_Q238L020
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergeCrossing_continuation_spec_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergeRefinement_regularChain_spec_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_RationalPhase_completion_spec_s238r

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

omit [Fintype D] [DecidableEq X] in
lemma nearest_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (p : X) (Q : Finset X) : nearestDistance (r p) (Q.image r) = nearestDistance p Q := by
  by_cases hQ : Q.Nonempty
  · apply le_antisymm
    · obtain ⟨x,hx,he⟩ := nearestDistance_attained p Q hQ
      rw [he,← hr p x]
      exact nearestDistance_le_mem _ _ _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    · obtain ⟨y,hy,he⟩ := nearestDistance_attained (r p) (Q.image r) (hQ.image r)
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      rw [he,hr]
      exact nearestDistance_le_mem _ _ _ hx
  · simp [Finset.not_nonempty_iff_eq_empty.mp hQ,nearestDistance]

omit [Fintype D] [DecidableEq X] in
lemma active_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D) :
    activeAt (fun a => r (loc a)) t z (Q.image r) j ↔ activeAt loc t z Q j := by
  simp only [activeAt,Finset.forall_mem_image,hr]

omit [Fintype D] [DecidableEq X] in
lemma admissible_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t K v z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) :
    admissibleBids (fun a => r (loc a)) t K v z (Q.image r) (r i) tau ↔
      admissibleBids loc t K v z Q i tau := by
  simp only [admissibleBids,active_map r hr loc t z Q,Finset.forall_mem_image,hr]

omit [DecidableEq X] in
lemma payment_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) :
    openingPayment (fun a => r (loc a)) t z (Q.image r) (r i) tau =
      openingPayment loc t z Q i tau := by
  unfold openingPayment
  apply Finset.sum_congr rfl
  intro j _
  rw [active_map r hr loc t z Q j,nearest_map r hr,hr]

omit [DecidableEq X] in
lemma dual_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (t z : ℝ) (Q : Finset X) (i : X) (tau : D → ℝ) (a : D) :
    openingDual (fun j => r (loc j)) t z (Q.image r) (r i) tau a =
      openingDual loc t z Q i tau a := by
  unfold openingDual
  apply Finset.sum_congr rfl
  intro j _
  rw [active_map r hr loc t z Q j,hr,hr]

omit [DecidableEq X] in
lemma openable_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ) (i : X) :
    etaOpenable (fun j => r (loc j)) (F.image r) (Q.image r) t K v z lam eta (r i) ↔
      etaOpenable loc F Q t K v z lam eta i := by
  constructor
  · rintro ⟨tau,ha,hp,hd⟩
    refine ⟨tau,(admissible_map r hr loc t K v z Q i tau).mp ha,?_,?_⟩
    · simpa only [payment_map r hr loc t z Q i tau] using hp
    · intro i₀ hi₀ a hact
      have hh := hd (r i₀) (Finset.mem_image.mpr ⟨i₀,hi₀,rfl⟩) a
        ((active_map r hr loc t z Q a).mpr hact)
      simpa only [dual_map r hr loc t z Q i₀ tau a] using hh
  · rintro ⟨tau,ha,hp,hd⟩
    refine ⟨tau,(admissible_map r hr loc t K v z Q i tau).mpr ha,?_,?_⟩
    · simpa only [payment_map r hr loc t z Q i tau] using hp
    · intro i₀ hi₀ a hact
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hi₀
      simpa only [dual_map r hr loc t z Q i tau a] using hd i hi a
        ((active_map r hr loc t z Q a).mp hact)

lemma entry_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (i : X)
    (h : PhaseSequence.Entry loc F B Q v z lam eta i) :
    PhaseSequence.Entry (fun j => r (loc j)) (F.image r) (B.image r) (Q.image r)
      v z lam eta (r i) := by
  refine ⟨?_,?_⟩
  · simpa only [r.injective.mem_finset_image] using h.1
  · rcases h.2 with hi | ⟨hi,W,hQ,hW,hop⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · right
      refine ⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,W.image r,Finset.image_subset_image hQ,?_,?_⟩
      · intro x hx
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
        rcases Finset.mem_union.mp (hW hy) with hyF | hyB
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y,hyF,rfl⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hyB,rfl⟩)
      · exact (openable_map r hr loc F W (1-3*v) (1+v^2) v z lam eta i).mpr hop

lemma prefix_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X)
    (h : PhaseSequence.Prefix loc F B v z lam eta Q H) :
    PhaseSequence.Prefix (fun j => r (loc j)) (F.image r) (B.image r) v z lam eta
      (Q.image r) (H.map r) := by
  induction h with
  | nil => exact PhaseSequence.Prefix.nil _
  | cons he ht ih =>
    apply PhaseSequence.Prefix.cons (entry_map r hr loc F B _ v z lam eta _ he)
    simpa only [Finset.image_insert] using ih

omit [Fintype D] [PseudoMetricSpace X] [PseudoMetricSpace Y] in
lemma image_union (r : X → Y) (Q : Finset X) (H : List X) :
    Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
  ext x
  simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
  aesop

omit [DecidableEq X] in
lemma maximal_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (h : PhaseSequence.Maximal loc F Q v z lam) :
    PhaseSequence.Maximal (fun j => r (loc j)) (F.image r) (Q.image r) v z lam := by
  intro x hx hnot hop
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  exact h i hi (fun hiQ => hnot (Finset.mem_image.mpr ⟨i,hiQ,rfl⟩))
    ((openable_map r hr loc F Q (1-3*v) (1+v^2) v z lam 0 i).mp hop)

lemma valid_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X)
    (h : PhaseSequence.Valid loc F B Q v z lam eta H) :
    PhaseSequence.Valid (fun j => r (loc j)) (F.image r) (B.image r) (Q.image r)
      v z lam eta (H.map r) := by
  refine ⟨prefix_map r hr loc F B Q v z lam eta H h.1,?_⟩
  rw [image_union]
  exact maximal_map r hr loc F (Q ∪ H.toFinset) v z lam h.2

theorem history_map (r : X ↪ Y) (hr : ∀ x y, dist (r x) (r y) = dist x y)
    (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ) (T : List (List X))
    (h : History loc F B v lam eta q Q T) :
    History (fun j => r (loc j)) (F.image r) (B.image r) v lam eta q (Q.image r)
      (T.map (List.map r)) := by
  induction h with
  | nil => exact History.nil _ _
  | cons hhead htail ih =>
    apply History.cons (valid_map r hr loc F B _ v _ lam eta _ hhead)
    simpa only [image_union] using ih

end MetricKMedianRecovery.HistoryIsometry

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence PhaseMergeSurgery
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [PseudoMetricSpace X] in
lemma subset_pool (F B : Finset X) (copy : X → X) : B ⊆ pool F B copy :=
  Finset.subset_union_left

end MetricKMedianRecovery.PhaseMergePath

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

lemma Chain.first_good {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {n : ℕ} {H G : List X} (h : Chain loc F B Q v z lam eta n H G) :
    Good loc F B Q v z lam eta H := by
  cases h with
  | nil h => exact h
  | cons h _ _ => exact h

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

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergeSurgery PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma EPath.toChain {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H J : List X} {T : List (List X)} (h : EPath loc F B Q v z lam eta H T J) :
    Chain loc F B Q v z lam eta T.length H J := by
  induction h with
  | nil h => exact .nil h
  | cons h e t ih => exact .cons h e ih

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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

lemma twin_replay (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n : ℕ) (H G : List X) (T : List (List X))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hG : Good loc F B Q v ((1+v^2)^q) lam eta G)
    (hco : Coincident loc F Q H G)
    (hT : Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T) :
    Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n T ∧
      finalCount F Q H T = finalCount F Q G T + 1 := by
  obtain ⟨i,f,R,hi,hfF,hiR,hfR,hHq,hGq,hd⟩ := hco
  have hfQ : f ∈ Q ∪ G.toFinset := hGq ▸ Finset.mem_insert_self f R
  have hf : f ∈ B := (Finset.mem_union.mp
    ((Finset.union_subset hQ hG.1.1.opened_subset) hfQ)).resolve_left hfF
  have hh : History loc F B v lam 0 (q+1) (insert i R) T := hHq ▸ hT.2.1
  obtain ⟨hh',U,hiU,_,ha,hb⟩ := history_twin loc F B v lam i f hi hf hdis hd ht hlam
    T (q+1) R hiR hfR hT.2.2 hh
  refine ⟨⟨hT.1,hGq.symm ▸ hh',hT.2.2⟩,?_⟩
  simp only [finalCount,hHq,hGq,ha,hb,Finset.inter_comm (insert i U),Finset.inter_comm (insert f U)]
  exact CoincidentCopy.paid_count F U i f hi hiU hfF

omit [Fintype D] in
lemma coincident_paid {loc : D → X} {F Q : Finset X} {H G : List X}
    (hco : Coincident loc F Q H G) : paid F Q H = paid F Q G + 1 := by
  obtain ⟨i,f,R,hi,hfF,hiR,_,hHq,hGq,_⟩ := hco
  simp only [paid,hHq,hGq,Finset.inter_comm (insert i R),Finset.inter_comm (insert f R)]
  exact CoincidentCopy.paid_count F R i f hi hiR hfF

lemma coincident_length {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ} {H G : List X}
    (hH : Valid loc F B Q v z lam eta H) (hG : Valid loc F B Q v z lam eta G)
    (hco : Coincident loc F Q H G) : H.length=G.length := by
  obtain ⟨i,f,R,_,_,hiR,hfR,hHq,hGq,_⟩ := hco
  have hh := congrArg Finset.card hHq
  have hg := congrArg Finset.card hGq
  rw [Finset.card_union_of_disjoint hH.1.disjoint,List.toFinset_card_of_nodup hH.1.nodup,
    Finset.card_insert_of_notMem hiR] at hh
  rw [Finset.card_union_of_disjoint hG.1.disjoint,List.toFinset_card_of_nodup hG.1.nodup,
    Finset.card_insert_of_notMem hfR] at hg
  omega

omit [PseudoMetricSpace X] in
lemma forward_reverse {F Q : Finset X} {H G : List X}
    (h : forward F Q H G = true) : forward F Q G H = false := by
  unfold forward at *
  split at h
  · rename_i he
    rw [ite_eq_left he.symm]
    simp only [decide_eq_true_eq] at h
    exact decide_eq_false (by omega)
  · rename_i he
    rw [ite_eq_right (Ne.symm he)]
    simp only [decide_eq_true_eq] at h
    exact decide_eq_false (by omega)

omit [PseudoMetricSpace X] in
lemma freeAppend_paid (F Q : Finset X) (H : List X) (f : X) (hf : f ∉ F) :
    paid F Q (H++[f]) = paid F Q H := by
  unfold paid
  congr 1
  ext x
  simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,Finset.notMem_empty,or_false,
    Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨h,hx⟩
    rcases h with h|h|rfl
    · exact ⟨Or.inl h,hx⟩
    · exact ⟨Or.inr h,hx⟩
    · exact (hf hx).elim
  · rintro ⟨h,hx⟩
    exact ⟨h.imp_right Or.inl,hx⟩

lemma paidDelete_paid {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    (C T : List X) (i : X) (hi : i ∈ F)
    (hH : Valid loc F B Q v z lam eta (C++i::T)) :
    paid F Q (C++i::T) = paid F Q (C++T) + 1 := by
  have hnot := entry_fresh hH.1
  have hset : Q ∪ (C++i::T).toFinset = insert i (Q ∪ (C++T).toFinset) := by
    simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert]
  unfold paid
  rw [hset,Finset.insert_inter_of_mem hi,Finset.card_insert_of_notMem]
  exact fun hh => hnot (Finset.mem_of_mem_inter_left hh)

lemma edit_forward {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H G : List X} (hdis : Disjoint F B)
    (hH : Valid loc F B Q v z lam eta H) (he : Edit loc F B Q H G) :
    forward F Q H G = true := by
  cases he with
  | freeAppend H i f hi hf hd =>
    have hfF : f∉F := fun hh => Finset.disjoint_left.mp hdis hh hf
    rw [forward,freeAppend_paid F Q H f hfF,ite_eq_left rfl]
    simp only [List.length_append,List.length_singleton,decide_eq_true_eq]
    omega
  | paidDelete C T i hi =>
    have hh := paidDelete_paid C T i hi hH
    rw [forward,ite_eq_right (by omega)]
    exact decide_eq_true (by omega)
  | coincident hc =>
    have hh := coincident_paid hc
    rw [forward,ite_eq_right (by omega)]
    exact decide_eq_true (by omega)

lemma directed_spec (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k : ℕ) (H G : List X) (T U : List (List X))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hH : Good loc F B Q v ((1+v^2)^q) lam eta H)
    (hG : Good loc F B Q v ((1+v^2)^q) lam eta G)
    (he : Edit loc F B Q H G)
    (hs : Sandwich k (finalCount F Q H T) (finalCount F Q G U))
    (hT : Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n U) :
    (directed F Q k H G T U).Correct loc F B Q v lam eta q n k := by
  cases he with
  | freeAppend H i f hi hf hd =>
    have hne : H.length≠(H++[f]).length := by simp only [List.length_append,List.length_singleton]; omega
    rw [directed,ite_eq_right hne]
    exact ⟨hH,hG,.freeAppend H i f hi hf hd,hT,hU,hs⟩
  | paidDelete C T' i hi =>
    have hne : (C++i::T').length≠(C++T').length := by
      simp only [List.length_append,List.length_cons]; omega
    rw [directed,ite_eq_right hne]
    exact ⟨hH,hG,.paidDelete C T' i hi,hT,hU,hs⟩
  | coincident hc =>
    have hlen := coincident_length hH.1 hG.1 hc
    have hh := twin_replay loc F B Q v lam eta q n H G T hQ hdis ht hlam hG hc hT
    rw [directed,ite_eq_left hlen]
    split
    · rename_i hk
      exact ⟨hG,hh.1,hk⟩
    · rename_i hk
      refine ⟨hG,hh.1,hU,?_⟩
      obtain heq := hh.2
      rcases hs with hs|hs <;> unfold Sandwich <;> omega

lemma edge_spec (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k : ℕ) (H G : List X) (T U : List (List X))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hH : Good loc F B Q v ((1+v^2)^q) lam eta H)
    (hG : Good loc F B Q v ((1+v^2)^q) lam eta G)
    (he : Adjacent loc F B Q H G)
    (hs : Sandwich k (finalCount F Q H T) (finalCount F Q G U))
    (hT : Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n U) :
    (edge F Q k H G T U).Correct loc F B Q v lam eta q n k := by
  rcases he with he|he
  · have hh := edit_forward hdis hH.1 he
    rw [edge,hh]
    exact directed_spec loc F B Q v lam eta q n k H G T U hQ hdis ht hlam hH hG he hs hT hU
  · have hh := forward_reverse (edit_forward hdis hG.1 he)
    rw [edge,hh]
    exact directed_spec loc F B Q v lam eta q n k G H U T hQ hdis ht hlam hG hH he hs.symm hU hT

lemma scan_spec (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k : ℕ) (complete : Finset X → List (List X))
    (hcomplete : ∀ R, R⊆F∪B → Runs loc F B R v lam (q+1) n (complete R))
    (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    {H G : List X} {S : List (List X)}
    (hp : CanonicalMergeRefinement.EPath loc F B Q v ((1+v^2)^q) lam eta H S G)
    (T U : List (List X))
    (hs : Sandwich k (finalCount F Q H T) (finalCount F Q G U))
    (hT : Runs loc F B (Q ∪ H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q ∪ G.toFinset) v lam (q+1) n U) :
    (scan F Q k complete U H T S).Correct loc F B Q v lam eta q n k := by
  induction hp generalizing T with
  | nil hH => exact ⟨hH,hT,hU,hs⟩
  | @cons H J S G hH he htail ih =>
    have hJ := htail.toChain.first_good
    have hV := hcomplete (Q ∪ J.toFinset) (Finset.union_subset hQ hJ.1.1.opened_subset)
    dsimp only [scan]
    split
    · rename_i hk
      exact ⟨hJ,hV,hk⟩
    · rename_i hk
      split
      · rename_i hs'
        exact edge_spec loc F B Q v lam eta q n k H J T _ hQ hdis ht hlam hH hJ he hs' hT hV
      · rename_i hs'
        have hs'' : Sandwich k (finalCount F Q J (complete (Q ∪ J.toFinset))) (finalCount F Q G U) := by
          unfold Sandwich at *
          omega
        exact ih _ hs'' hV hU

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

omit [Fintype D] [PseudoMetricSpace X] in
lemma disjoint_pool (F B : Finset X) (copy : X → X) (hdis : Disjoint F B)
    (hc : ∀ i∈F,copy i∉F∪B) : Disjoint F (PhaseMergePath.pool F B copy) := by
  rw [Finset.disjoint_left]
  intro x hx hxpool
  rcases Finset.mem_union.mp hxpool with hxB|hxc
  · exact Finset.disjoint_left.mp hdis hx hxB
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hxc
    exact hc i hi (Finset.mem_union_left _ hx)

end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContinuation
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelContinuation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

lemma image_select (loc : Fin d → X) (F Q S : Finset X)
    (hS : ∀ x∈S,x∈alphabet loc F Q) : (select loc F Q S).image (embed loc F Q)=S := by
  ext x
  simp only [Finset.mem_image,mem_select]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact hi
  · intro hx
    refine ⟨index loc F Q x (hS x hx),?_,embed_index ..⟩
    simpa only [embed_index] using hx

lemma select_cover (loc : Fin d → X) (F Q : Finset X) :
    select loc F Q Q ⊆ select loc F Q F ∪ select loc F Q (Q\F) := by
  intro i hi
  simp only [mem_select,Finset.mem_union,Finset.mem_sdiff] at *
  tauto

variable [PseudoMetricSpace X]

lemma complete_spec (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset X) (v z lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) (hQ : Q⊆F∪B) :
    Valid loc F B Q v z lam 0 (complete loc distance F v z lam Q) ∧
      (∀ i∈complete loc distance F v z lam Q,i∈F) ∧
      (complete loc distance F v z lam Q).length ≤ F.card := by
  let := metric loc F Q
  have he : ∀ a b,dist (embed loc F Q a) (embed loc F Q b)=dist a b := fun _ _=>rfl
  have hrows : ∀ f j,((rows loc F Q distance) f j:ℝ)=dist f (located loc F Q j) := by
    intro f j
    change (distance (embed loc F Q f) j:ℝ)=dist (embed loc F Q f) (embed loc F Q (located loc F Q j))
    rw [embed_located,hd]
  have hF : (select loc F Q F).image (embed loc F Q)=F :=
    image_select loc F Q F (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inl hx))
  have hQQ : (select loc F Q Q).image (embed loc F Q)=Q :=
    image_select loc F Q Q (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inr (Or.inl hx)))
  have hB : (select loc F Q (Q\F)).image (embed loc F Q)=Q\F :=
    image_select loc F Q (Q\F) (fun x hx=>(mem_alphabet loc F Q x).mpr
      (Or.inr (Or.inl (Finset.mem_sdiff.mp hx).1)))
  obtain ⟨hh,hr,hl⟩ := RationalPhase.completion_spec_s238r (located loc F Q) (rows loc F Q distance)
    hrows (select loc F Q F) (select loc F Q (Q\F)) (select loc F Q Q) v z lam hv hv1 hz
    (select_cover loc F Q)
  have hm := HistoryIsometry.valid_map (embed loc F Q) he _ _ _ _ _ _ _ _ _ hh
  simp only [embed_located,hF,hQQ,hB] at hm
  have hsub : Q\F⊆B := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx,hn⟩
    exact (Finset.mem_union.mp (hQ hx)).resolve_left hn
  refine ⟨⟨PhaseMergeSurgery.prefix_free_mono hm.1 hsub,hm.2⟩,?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact (mem_select ..).mp (hr j hj)
  · unfold complete
    rw [List.length_map]
    have hc : (select loc F Q F).card=F.card :=
      (Finset.card_image_of_injective (select loc F Q F) (embed loc F Q).injective).symm.trans (congrArg Finset.card hF)
    exact hl.trans_eq hc

lemma continuation_spec (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset X) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (q n : ℕ) (hQ : Q⊆F∪B) :
    Runs loc F B Q v lam q n (continuation loc distance F v lam q n Q) := by
  let := metric loc F Q
  have he : ∀ a b,dist (embed loc F Q a) (embed loc F Q b)=dist a b := fun _ _=>rfl
  have hrows : ∀ f j,((rows loc F Q distance) f j:ℝ)=dist f (located loc F Q j) := by
    intro f j
    change (distance (embed loc F Q f) j:ℝ)=dist (embed loc F Q f) (embed loc F Q (located loc F Q j))
    rw [embed_located,hd]
  have hF : (select loc F Q F).image (embed loc F Q)=F :=
    image_select loc F Q F (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inl hx))
  have hQQ : (select loc F Q Q).image (embed loc F Q)=Q :=
    image_select loc F Q Q (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inr (Or.inl hx)))
  have hB : (select loc F Q (Q\F)).image (embed loc F Q)=Q\F :=
    image_select loc F Q (Q\F) (fun x hx=>(mem_alphabet loc F Q x).mpr
      (Or.inr (Or.inl (Finset.mem_sdiff.mp hx).1)))
  obtain ⟨hl,hh,hr⟩ := CanonicalMergeCrossing.continuation_spec_s238r (located loc F Q)
    (rows loc F Q distance) hrows (select loc F Q F) (select loc F Q (Q\F))
    (select loc F Q Q) v lam hv hv1 q n (select_cover loc F Q)
  have hm := HistoryIsometry.history_map (embed loc F Q) he _ _ _ _ _ _ _ _ _ hh
  simp only [embed_located,hF,hQQ,hB] at hm
  have hsub : Q\F⊆B := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx,hn⟩
    exact (Finset.mem_union.mp (hQ hx)).resolve_left hn
  apply Runs.mono_free (B:=Q\F) _ hsub
  refine ⟨?_,hm,?_⟩
  · simpa only [continuation,List.length_map] using hl
  · intro H hH i hi
    obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hH
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact (mem_select ..).mp (hr G hG j hj)

 theorem correct_completion (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F : Finset X) (v z lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    CanonicalMergePath.CorrectCompletion loc F v z lam (complete loc distance F v z lam) := by
  intro B Q hQ
  have hh := complete_spec loc distance hd F B Q v z lam hv hv1 hz hQ
  exact ⟨hh.1,hh.2.1⟩

end MetricKMedianRecovery.FiniteLabelContinuation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing PhaseCountCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

variable [PseudoMetricSpace X]
 theorem run_spec_s238r_oai (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hmetric : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset X)
    (v lam : ℚ) (eta : ℝ) (q n k : ℕ) (copy spare : X → X)
    (hv : (0:ℝ)<(v:ℝ)) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i ≤ (lam:ℝ))
    (hc : ∀ i∈F,copy i∉F∪B) (hd : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy i))
    (hs : ∀ i∈F,spare i∉F∪PhaseMergePath.pool F B copy)
    (he : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (spare i))
    (H G : List X) (T U : List (List X))
    (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H)
    (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G)
    (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hT : Runs loc F B (Q∪H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q∪G.toFinset) v lam (q+1) n U)
    (hbr : Sandwich k (finalCount F Q H T) (finalCount F Q G U)) :
    (run loc distance F Q v lam q n k copy spare H G T U).Correct loc F
      (PhaseMergePath.pool F (PhaseMergePath.pool F B copy) spare) Q v lam eta q n k := by
  let B' := PhaseMergePath.pool F (PhaseMergePath.pool F B copy) spare
  have hB : B⊆B' := (PhaseMergePath.subset_pool F B copy).trans (PhaseMergePath.subset_pool ..)
  let complete := FiniteLabelContinuation.complete loc distance F v ((1+v^2)^q) lam
  have hz : (((1+v^2)^q:ℚ):ℝ)=(1+(v:ℝ)^2)^q := by push_cast; rfl
  have hcomp : CanonicalMergePath.CorrectCompletion loc F v ((1+(v:ℝ)^2)^q) lam complete := by
    have hh := FiniteLabelContinuation.correct_completion loc distance hmetric F v ((1+v^2)^q) lam
      hv hvsmall (by rw [hz]; positivity)
    simpa only [hz] using hh
  obtain ⟨_,hp⟩ := CanonicalMergeRefinement.regularChain_spec_s238r loc F B Q (F.sort (·≤·)) copy spare
    v ((1+(v:ℝ)^2)^q) lam eta complete hcomp hv hvsmall (by positivity) hlam heta
    (fun i hi=>by simpa only [Finset.mem_sort] using hi) hQ hdis hrow hc hd hs he H G hH hG hHr hGr
  apply scan_spec loc F B' Q v lam eta q n k _ _
    (hQ.trans (Finset.union_subset_union_right hB))
    (CanonicalMergeCrossing.disjoint_pool F _ spare (CanonicalMergeCrossing.disjoint_pool F B copy hdis hc) hs)
    (by linarith) hlam hp T U hbr (hT.mono_free hB) (hU.mono_free hB)
  intro R hR
  exact FiniteLabelContinuation.continuation_spec loc distance hmetric F B' R v lam hv hvsmall (q+1) n hR

end MetricKMedianRecovery.FiniteLabelCrossing

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238r_oai.{u_1}
