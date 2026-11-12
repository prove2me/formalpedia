-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:39:33.64702+00:00
-- url     : https://prove2.me/submissions/ec7e0d38-6e8f-4afa-9e5e-31e1cd74e32b

import Mathlib
import Definitions.Def_Q238L026
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergeCrossing_continuation_spec_s238r

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

end MetricKMedianRecovery.PhaseMergeSurgery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledInitial
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma initialHistory_spec_s238r_oai (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lam : ℚ) (total : ℕ) (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) :
    Runs (fun j=>original (loc j)) (F.image original) ∅ ∅ v lam 0 total
      (initialHistory loc distance F v lam total) :=
  FiniteLabelContinuation.continuation_spec _ _ (rows_spec loc distance hmetric) _ _ _ _ _ hv hv1 _ _
    (Finset.empty_subset _)

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238r_oai.{u_1}
