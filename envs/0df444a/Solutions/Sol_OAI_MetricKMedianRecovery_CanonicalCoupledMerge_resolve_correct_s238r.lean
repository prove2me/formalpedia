-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:41:40.103257+00:00
-- url     : https://prove2.me/submissions/149f469a-0198-4792-9910-d9ee801870f6

import Mathlib
import Definitions.Def_Q238L026
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_leaf_certified_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergeCrossing_continuation_spec_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalSensitiveEndpoint_endpoints_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_RationalLeaves_prefix_leaf_s238r

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

end Prefix

omit [DecidableEq X] in
lemma exact_opening_eta {loc : D → X} {F W : Finset X} {v z lam eta : ℝ} {i : X}
    (h : etaOpenable loc F W (1-3*v) (1+v^2) v z lam 0 i) (heta : 0 ≤ eta) :
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i := by
  obtain ⟨tau,hb,hp,hd⟩ := h
  refine ⟨tau,hb,?_,hd⟩
  have hn : 0 ≤ (Fintype.card D:ℝ)*eta := mul_nonneg (Nat.cast_nonneg _) heta
  simp only [mul_zero,sub_zero] at hp
  exact (sub_le_self lam hn).trans hp

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

lemma History.after_subset {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {T : List (List X)} (h : History loc F B v lam eta q Q T)
    (hQ : Q ⊆ F ∪ B) : after Q T ⊆ F ∪ B := by
  induction h with
  | nil => exact hQ
  | cons hhead htail ih =>
    exact ih (Finset.union_subset hQ hhead.1.opened_subset)

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

lemma prefix_exact_eta {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Prefix loc F B v z lam 0 Q H) (heta : 0 ≤ eta) :
    Prefix loc F B v z lam eta Q H := by
  induction h with
  | nil Q => exact Prefix.nil Q
  | cons hi ht ih =>
    refine Prefix.cons ⟨hi.1,?_⟩ ih
    rcases hi.2 with hi | ⟨hi,W,hW,hWF,hop⟩
    · exact Or.inl hi
    · exact Or.inr ⟨hi,W,hW,hWF,exact_opening_eta hop heta⟩

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

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma Before.mono {B : Finset (Label V)} {a b : ℕ} (h : Before a B) (hab : a≤b) : Before b B :=
  fun c hc=>(h c hc).trans_le hab

end MetricKMedianRecovery.RationalLeaves

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergeSurgery PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [PseudoMetricSpace X] [DecidableEq X] in
lemma mem_cuts {H C T : List X} {i : X} : (C,i,T)∈cuts H ↔ H=C++i::T := by
  constructor
  · intro h
    induction H generalizing C T i with
    | nil => simp only [cuts,List.not_mem_nil] at h
    | cons x H ih =>
      rcases List.mem_cons.mp h with h | h
      · cases h
        rfl
      · obtain ⟨⟨C',i',T'⟩,hp,he⟩ := List.mem_map.mp h
        cases he
        exact congrArg (List.cons x) (ih hp)
  · intro h
    subst H
    induction C with
    | nil => exact List.mem_cons_self ..
    | cons c C ih =>
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(C,i,T),ih,rfl⟩)

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_PrefixFreeMono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CommonPrefixTransfer
open PhaseHistoryTransfer FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma history_rows (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q : ℕ) (T : List (List X)) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hh : History loc F B v lam eta q Q T) :
    ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^(q+T.length)) (after Q T) i ≤ lam := by
  induction hh with
  | nil q Q => simpa only [List.length_nil,Nat.add_zero,after] using hrow
  | @cons q Q H T hhead htail ih =>
    have hr := ih (advance_rows loc F B Q v lam eta q H hv hvsmall hlam hrow hhead)
    simpa only [after,List.length_cons,Nat.add_right_comm,Nat.add_assoc] using hr

lemma history_append (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q : ℕ) (P T : List (List X)) (hp : History loc F B v lam eta q Q P)
    (ht : History loc F B v lam eta (q+P.length) (after Q P) T) :
    History loc F B v lam eta q Q (P++T) := by
  induction hp with
  | nil q Q => simpa only [List.nil_append,List.length_nil,Nat.add_zero,after] using ht
  | @cons q Q H P hhead htail ih =>
    apply History.cons hhead
    apply ih
    simpa only [after,List.length_cons,Nat.add_right_comm,Nat.add_assoc] using ht

end MetricKMedianRecovery.CommonPrefixTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_PrefixData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeInvariant
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
universe uD uX uY
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma after_append (Q : Finset X) (P T : List (List X)) :
    after Q (P++T) = after (after Q P) T := by
  induction P generalizing Q with
  | nil => rfl
  | cons H P ih => exact ih _

lemma history_exact_eta {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : History loc F B v lam 0 q Q P) (heta : 0 ≤ eta) :
    History loc F B v lam eta q Q P := by
  induction h with
  | nil => exact History.nil _ _
  | cons hhead htail ih =>
    exact History.cons ⟨PhaseMergeSurgery.prefix_exact_eta hhead.1 heta,hhead.2⟩ ih

lemma PrefixData.after_subset {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) :
    after ∅ P ⊆ F ∪ B := h.history.after_subset (Finset.empty_subset _)

lemma PrefixData.append_phase {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (H : List X) (hh : Valid loc F B (after ∅ P) v ((1+v^2)^q) lam eta H)
    (hfree : (H.toFinset \ F).card ≤ 3) :
    PrefixData loc F B v lam eta (q+1) (P++[H]) := by
  refine ⟨by simp only [List.length_append,List.length_singleton,h.length_eq],?_,?_,?_⟩
  · apply CommonPrefixTransfer.history_append loc F B ∅ v lam eta 0 P [H] h.history
    simpa only [Nat.zero_add,h.length_eq] using History.cons hh (History.nil _ _)
  · intro G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact h.free_bound G hG
    · simpa only [List.mem_singleton.mp hG] using hfree
  · simpa only [after_append,after] using
      advance_rows loc F B (after ∅ P) v lam eta q H hv hvsmall hlam h.row hh

lemma PrefixData.append_exact {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (T : List (List X)) (hh : History loc F B v lam 0 q (after ∅ P) T)
    (hreg : Regular F T) : PrefixData loc F B v lam eta (q+T.length) (P++T) := by
  refine ⟨by simp only [List.length_append,h.length_eq],?_,?_,?_⟩
  · apply CommonPrefixTransfer.history_append loc F B ∅ v lam eta 0 P T h.history
    simpa only [Nat.zero_add,h.length_eq] using history_exact_eta hh heta
  · intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · exact h.free_bound H hH
    · have hs : H.toFinset ⊆ F := fun i hi => hreg H hH i (List.mem_toFinset.mp hi)
      simp only [Finset.sdiff_eq_empty_iff_subset.mpr hs,Finset.card_empty,Nat.zero_le]
  · rw [after_append]
    exact CommonPrefixTransfer.history_rows loc F B (after ∅ P) v lam 0 q T
      hv hvsmall hlam h.row hh

end MetricKMedianRecovery.PhaseMergeInvariant

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DisjointPool
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PriceBisection

lemma refine_bounds (count : ℚ → ℕ) (h : ℕ) (a b : ℚ) (hab : a ≤ b) :
    a ≤ (refine count h (a,b)).1 ∧
    (refine count h (a,b)).1 ≤ (refine count h (a,b)).2 ∧
    (refine count h (a,b)).2 ≤ b := by
  dsimp only [refine]
  split_ifs <;> dsimp
  · exact ⟨by linarith, by linarith, le_rfl⟩
  · exact ⟨le_rfl, by linarith, by linarith⟩

lemma refine_width (count : ℚ → ℕ) (h : ℕ) (a b : ℚ) :
    (refine count h (a,b)).2-(refine count h (a,b)).1 = (b-a)/2 := by
  dsimp only [refine]
  split_ifs <;> dsimp <;> ring

lemma refine_bracket (count : ℚ → ℕ) (h : ℕ) (a b : ℚ)
    (ha : h ≤ count a) (hb : count b ≤ h) :
    h ≤ count (refine count h (a,b)).1 ∧ count (refine count h (a,b)).2 ≤ h := by
  dsimp only [refine]
  split_ifs with hm
  · exact ⟨hm,hb⟩
  · exact ⟨ha,(Nat.lt_of_not_ge hm).le⟩

lemma search_spec (count : ℚ → ℕ) (h n : ℕ) (a b : ℚ) (hab : a ≤ b)
    (ha : h ≤ count a) (hb : count b ≤ h) :
    let I := search count h n (a,b)
    a ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ b ∧
      h ≤ count I.1 ∧ count I.2 ≤ h ∧ I.2-I.1 = (b-a)/2^n := by
  induction n generalizing a b with
  | zero =>
    simp only [search,pow_zero,div_one]
    exact ⟨le_rfl,hab,le_rfl,ha,hb,True.intro⟩
  | succ n ih =>
    obtain ⟨hlo,hm,hhi⟩ := refine_bounds count h a b hab
    obtain ⟨hcl,hch⟩ := refine_bracket count h a b ha hb
    obtain ⟨hl',he',hh',hcl',hch',hw'⟩ := ih _ _ hm hcl hch
    refine ⟨hlo.trans hl',he',hh'.trans hhi,hcl',hch',?_⟩
    change (search count h n (refine count h (a,b))).2 -
      (search count h n (refine count h (a,b))).1 = _
    rw [hw',refine_width,pow_succ]
    ring

lemma iterations_precision (a b : ℚ) (N : ℕ) :
    (b-a) / (2:ℚ) ^ iterations a b N ≤ 1 / (2:ℚ)^N := by
  have hwidth : b-a ≤ (2:ℚ)^(Nat.clog 2 (Nat.ceil (b-a))) := by
    exact (Nat.le_ceil (b-a)).trans (by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (Nat.ceil (b-a)))
  unfold iterations
  rw [pow_add]
  apply (div_le_iff₀ (by positivity : (0:ℚ) < 2^N*2^(Nat.clog 2 (Nat.ceil (b-a))))).mpr
  simpa using hwidth

end MetricKMedianRecovery.PriceBisection

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

end MetricKMedianRecovery.FiniteLabelContinuation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

lemma view_sound (distance : X → Fin d → ℚ) (F : Finset X) (R H G : List X) (J : Plan X)
    (h : view distance F R H G=some J) : accepts distance F H G J :=
  of_decide_eq_true (List.find?_some (p := fun J=>decide (accepts distance F H G J)) h)

variable [PseudoMetricSpace X]
lemma view_exists (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hd : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F B : Finset X) (R H G : List X)
    (hR : ∀ i∈F,i∈R) (hdis : Disjoint F B) (h : LengthEdit loc F B H G) :
    ∃ J,view distance F R H G=some J := by
  have hex : ∃ J∈candidates R H G,accepts distance F H G J := by
    cases h with
    | freeAppend H i f hi hf hco =>
      refine ⟨.free i f,?_,hi,fun he=>Finset.disjoint_left.mp hdis he hf,rfl,?_⟩
      · apply List.mem_append_left
        apply List.mem_flatMap.mpr
        refine ⟨i,hR i hi,List.mem_map.mpr ⟨f,?_,rfl⟩⟩
        exact List.mem_append_right _ (List.mem_cons_self ..)
      · intro j
        apply Rat.cast_injective (α:=ℝ)
        rw [hd,hd,dist_comm i,dist_comm f]
        exact hco j
    | paidDelete C T i hi =>
      refine ⟨.paid C T i,?_,hi,rfl,rfl⟩
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨(C,i,T),mem_cuts.mpr rfl,rfl⟩
  have hn : view distance F R H G≠none := by
    intro hn
    obtain ⟨J,hJ,hacc⟩ := hex
    exact List.find?_eq_none.mp hn J hJ (decide_eq_true hacc)
  exact Option.ne_none_iff_exists'.mp hn

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthSearch
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthSearch
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing CanonicalMergeCrossing
variable {X : Type*} [DecidableEq X]

lemma range_spec (f : ℚ  →  ℕ) (k N : ℕ) (b : ℚ) (hb : 0 ≤ b)
    (hs : Sandwich k (f 0) (f b)) :
    let J := range f k N b
    0 ≤ J.1  ∧  J.1 ≤ J.2  ∧  J.2 ≤ b  ∧  J.2-J.1 ≤ 1/(2:ℚ)^N  ∧
      (f J.1=k ∨ f J.2=k ∨ Sandwich k (f J.1) (f J.2)) := by
  dsimp only [range]
  split
  · rename_i hf
    have ha : k ≤ f b := by unfold Sandwich at hs; omega
    have hb' : f 0 ≤ k := hf.le
    obtain ⟨hl,hle,hu,hcl,hcu,hw⟩ := PriceBisection.search_spec (fun s=>f (b-s)) k
      (PriceBisection.iterations 0 b N) 0 b hb (by simpa using ha) (by simpa using hb')
    have hp := PriceBisection.iterations_precision 0 b N
    simp only [sub_zero] at hw hp
    refine ⟨by linarith,by linarith,by linarith,by linarith,?_⟩
    unfold Sandwich
    dsimp only
    omega
  · rename_i hf
    have ha : k ≤ f 0 := by omega
    have hb' : f b ≤ k := by unfold Sandwich at hs; omega
    obtain ⟨hl,hle,hu,hcl,hcu,hw⟩ := PriceBisection.search_spec f k
      (PriceBisection.iterations 0 b N) 0 b hb ha hb'
    have hp := PriceBisection.iterations_precision 0 b N
    refine ⟨hl,hle,hu,hw ▸ hp,?_⟩
    unfold Sandwich
    omega

lemma run_spec (F Q : Finset X) (leaf : ℚ  →  X) (complete : ℚ  →  List (List X))
    (T U : List (List X)) (b : ℚ) (k N : ℕ) (R : ℚ  →  List (List X)  →  Prop)
    (hb : 0<b) (hT : R 0 T) (hU : R b U) (hc : ∀ s,0 ≤ s → s ≤ b → R s (complete s))
    (hs : Sandwich k ((after (insert (leaf 0) Q) T) ∩ F).card ((after (insert (leaf b) Q) U) ∩ F).card) :
    (run F Q leaf complete T U b k N).Spec F Q leaf R b k N := by
  have hchoose : ∀ s,0 ≤ s → s ≤ b → R s (chosen complete T U b s) := by
    intro s hs0 hsb
    unfold chosen
    split_ifs with hz hu
    · subst s; exact hT
    · subst s; exact hU
    · exact hc s hs0 hsb
  have hs' : Sandwich k (count F Q leaf complete T U b 0) (count F Q leaf complete T U b b) := by
    simpa only [count,chosen,ite_true, if_true,ite_eq_right (ne_of_gt hb)] using hs
  obtain ⟨hl,hle,hu,hw,hcs⟩ := range_spec (count F Q leaf complete T U b) k N b hb.le hs'
  dsimp only [run]
  split
  · rename_i hk
    exact ⟨hl,hle.trans hu,hchoose _ hl (hle.trans hu),hk⟩
  · rename_i hk
    split
    · rename_i hk'
      exact ⟨hl.trans hle,hu,hchoose _ (hl.trans hle) hu,hk'⟩
    · rename_i hk'
      exact ⟨hl,hle,hu,hw,hchoose _ hl (hle.trans hu),hchoose _ (hl.trans hle) hu,
        (hcs.resolve_left hk).resolve_left hk'⟩

end MetricKMedianRecovery.CanonicalLengthSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma run_spec (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (B Q : Finset (Label V)) (v lam b : ℚ) (eta : ℝ)
    (q n k key precision : ℕ) (H : List (Label V)) (T U : List (List (Label V))) (J : Plan (Label V))
    (hQ : Q⊆F.image original∪B) (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hb : 0<b)
    (h : EndpointSpec loc F B Q v lam eta q n k key b H T U J) :
    (run loc distance F Q v lam b q n k key precision H T U J).Spec
      (F.image original) (Q∪(J.common H).toFinset) (leaf key (parent J.root))
      (fun s W=>Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key (parent J.root) s) B)
        (insert (leaf key (parent J.root) s) (Q∪(J.common H).toFinset)) v lam (q+1) n W)
      b k precision := by
  obtain ⟨hC,hA,hZ,hs⟩ := h
  dsimp only [run]
  split
  · rename_i hk
    exact ⟨le_rfl,hb.le,hA,hk⟩
  · rename_i hk
    apply CanonicalLengthSearch.run_spec _ _ _ _ _ _ _ _ _ _ hb hA hZ _ (hs.resolve_left hk)
    intro s _ _
    apply FiniteLabelContinuation.continuation_spec _ _ (rows_spec loc distance hmetric) _ _ _
      v lam hv hv1 (q+1) n
    exact Finset.insert_subset (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
      ((Finset.union_subset hQ hC.1.1.opened_subset).trans
        (Finset.union_subset_union_right (Finset.subset_insert _ _)))

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledFinish
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.levelWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.parentWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma finish_correct {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P T : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (hv : 0<v) (hv1 : v<1/6) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hd : Disjoint (F.image original) B) (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hT : Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam q n T)
    (hc : ((after (after ∅ P) T)∩F.image original).card=k) :
    (finish B lam P T).Correct loc F v eta lo hi (q+n) k := by
  refine ⟨hd,hl,hu,?_,?_⟩
  · simpa only [hT.1,finish] using hp.append_exact hv hv1 hlam heta T hT.2.1 hT.2.2
  · simpa only [finish,after_append] using hc

lemma same_certified {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P T U : List (List (Label V))}
    (hB : Before (3*q) B) (heta : 0≤eta) (hd : Disjoint (F.image original) B)
    (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (hT : Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam q n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam q n U)
    (hs : Sandwich k ((after (after ∅ P) T)∩F.image original).card
      ((after (after ∅ P) U)∩F.image original).card) :
    Certified loc F v eta lo hi q n k (sameState B lam P T U) := by
  refine {
    before := hB
    before_map := ?_
    disjoint := hd
    low := hl
    high := hu
    price := le_rfl
    eps_nonneg := by norm_num [sameState,Correction.error]
    error := ?_
    inj := Function.injective_id
    fixed := fun _ _=>rfl
    shrink := fun _ _ _=>le_rfl
    loss := ?_
    old_prefix := hp
    new_prefix := ?_
    sandwich := ?_
    new_tail := ?_
    old_tail := hU }
  · simpa only [sameState,State.mapFree,Correction.apply,Finset.image_id] using hB
  · change (lam:ℝ)-lam+(d:ℝ)*((1-3*v)*(0:ℚ))≤(d:ℝ)*eta
    simpa only [Rat.cast_zero,sub_self,mul_zero,add_zero] using mul_nonneg (Nat.cast_nonneg d) heta
  · intro j x _
    change dist _ x≤dist _ x+(0:ℚ)
    simp
  · simpa only [sameState,State.mapPrefix,State.mapFree,Correction.apply,Finset.image_id,List.map_id_fun,List.map_id] using hp
  · simpa only [sameState,State.a,State.b,State.mapPrefix,Correction.apply,List.map_id_fun,List.map_id] using hs
  · simpa only [sameState,State.mapPrefix,State.mapFree,Correction.apply,Finset.image_id,List.map_id_fun,List.map_id] using hT

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledResolve
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma resolve_correct_s238r_oai (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision q n k key : ℕ)
    (B : Finset (Label V)) (lam : ℚ) (P : List (List (Label V)))
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N) (hB : Before key B) (hkey : key<3*(q+1))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
    (hdis : Disjoint (F.image original) B) (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hlamUpper : (lam:ℝ)≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ))
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (R : CanonicalMergeCrossing.Result (Label V))
    (hR : R.Correct (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam eta q n k) :
    (resolve loc distance F v M N precision q n k key B lam P R).Correct loc F v eta lo hi q n k := by
  have hfinish : ∀ (H : List (Label V)) (T : List (List (Label V))),
      Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+(v:ℝ)^2)^q) lam eta H →
      Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P∪H.toFinset) v lam (q+1) n T →
      finalCount (F.image original) (after ∅ P) H T=k →
      (finish B lam (P++[H]) T).Correct loc F v eta lo hi (q+(n+1)) k := by
    intro H T hH hT hc
    have hpn := hp.append_phase hv hv1 hlam H hH.1 (hH.2.trans (by omega))
    have hh := finish_correct hpn hv hv1 hlam heta hdis hl hu
      (T:=T) (n:=n) (by simpa only [after_append,after] using hT)
      (by simpa only [after_append,after,finalCount] using hc)
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hh
  cases R with
  | success H T =>
    exact hfinish H T hR.1 hR.2.1 hR.2.2
  | common H T U =>
    obtain ⟨hH,hT,hU,hs⟩ := hR
    apply same_certified (hB.mono (by omega)) heta hdis hl hu
      (hp.append_phase hv hv1 hlam H hH.1 (hH.2.trans (by omega)))
    · simpa only [after_append,after] using hT
    · simpa only [after_append,after] using hU
    · simpa only [after_append,after,finalCount] using hs
  | sensitive H G T U =>
    obtain ⟨hH,hG,he,hT,hU,hs⟩ := hR
    obtain ⟨J,hJ⟩ := view_exists (fun j=>original (loc j)) (rows distance) (rows_spec loc distance hmetric)
      (F.image original) B ((F.sort (·≤·)).map original) H G
      (fun i hi=>by
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
        exact List.mem_map.mpr ⟨j,by simpa only [Finset.mem_sort] using hj,rfl⟩) hdis he
    have ha := view_sound (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G J hJ
    have hNr : (0:ℚ)<N := by exact_mod_cast (show 0<N by omega)
    have hb : (0:ℚ)<20*N*M := by positivity
    have hE := CanonicalSensitiveEndpoint.endpoints_s238r loc distance hmetric F B (after ∅ P)
      v lam eta M q n k key N (20*N*M) H G T U J hF hB hp.after_subset hdis hv hv1 hlam
      (by exact_mod_cast hM) hN hlamUpper (by push_cast; rfl) hdiam hp.row hH hG hT hU ha hs
    have hc := CanonicalSensitiveEndpoint.run_spec loc distance hmetric F B (after ∅ P) v lam (20*N*M) eta
      q n k key precision H T U J hp.after_subset hv hv1 hb hE
    have hC := hE.1
    dsimp only [resolve]
    rw [hJ]
    dsimp only
    cases hr : CanonicalSensitiveEndpoint.run loc distance F (after ∅ P) v lam (20*N*M) q n k key precision H T U J with
    | success x W =>
      rw [hr] at hc
      obtain ⟨_,_,hW,hcount⟩ := hc
      have hpn := prefix_leaf_s238r hp key hB (parent J.root) x hv hv1 hlam (J.common H) hC
      have hd' : Disjoint (F.image original) (insert (leaf key (parent J.root) x) B) := by
        rw [Finset.disjoint_insert_right]
        exact ⟨fun he=>fresh F B key hB (parent J.root) x (Finset.mem_union_left _ he),hdis⟩
      have hbdy : after ∅ (P++[J.common H++[leaf key (parent J.root) x]])=
          insert (leaf key (parent J.root) x) (after ∅ P∪(J.common H).toFinset) := by
        simp only [after_append,after,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
      have hh := finish_correct hpn hv hv1 hlam heta hd' hl hu (T:=W) (n:=n) (k:=k)
        (by simpa only [hbdy] using hW) (by simpa only [hbdy] using hcount)
      simpa only [Outcome.Correct,Nat.add_assoc,Nat.add_comm 1 n] using hh
    | bracket l u A Z =>
      rw [hr] at hc
      obtain ⟨hl0,hlu,_,hw,hA,hZ,hAZ⟩ := hc
      apply leaf_certified_s238r hp key hB hkey (parent J.root) (J.common H) l u A Z hv hv1 hlam hdis hl hu hC hl0 hlu _ hA hZ hAZ
      have hh : ((u-l:ℚ):ℝ)≤((1/(2:ℚ)^precision:ℚ):ℝ) := by exact_mod_cast hw
      simpa only [Rat.cast_sub] using hh.trans hprecision

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238r_oai.{u_1}
