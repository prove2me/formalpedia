-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:31.331514+00:00
-- url     : https://prove2.me/submissions/0be8aeed-0c30-466b-8540-048c7d874f77

import Mathlib
import Definitions.Def_Q238K031
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_resolve_correct_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergeCrossing_continuation_spec_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_FiniteLabelCrossing_run_spec_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_PhaseParameterAlignment_align_s238

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

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_phase_union (Q : Finset X) (H : List X) (r : X → X) :
    Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
  ext x
  simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
  aesop

omit [Fintype D] [PseudoMetricSpace X] in
lemma after_map (Q : Finset X) (T : List (List X)) (r : X → X) :
    after (Q.image r) (T.map (List.map r)) = (after Q T).image r := by
  induction T generalizing Q with
  | nil => rfl
  | cons H T ih =>
    simp only [List.map_cons,after,image_phase_union]
    exact ih _

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.levelWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.parentWords_encode
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

omit [DecidableEq V] in
lemma copy_dist (key : ℕ) (i j : V) :
    dist (original i) (copy key (original j))=dist i j := by
  rw [show copy key (original j)=leaf key j 0 from rfl,leaf_dist]
  simp

omit [PseudoMetricSpace V] in
lemma pool_before (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B) :
    Before (key+1) (PhaseMergePath.pool (F.image original) B (copy key)) := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc|hc
  · exact (hB c hc).trans (by omega)
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    have hh : c=(key,j,0) := by simpa only [copy,original,leaf,Function.Embedding.coeFn_mk,Sum.elim_inl,Sum.inr.injEq] using he.symm
    subst c
    omega

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseParameterAlignment
open PhaseSequence PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] [DecidableEq X] in
lemma regular_map_eq (F : Finset X) (G : List X) (r : X → X)
    (hfix : ∀ i ∈ F, r i = i) (hG : ∀ i ∈ G, i ∈ F) : G.map r = G := by
  have he : G.map r = G.map id := List.map_congr_left (fun i hi => hfix i (hG i hi))
  simpa only [List.map_id] using he

end MetricKMedianRecovery.PhaseParameterAlignment

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

lemma prefix_free_mono (loc : D → X) (F B B' Q : Finset X)
    (v z lam eta : ℝ) (H : List X) (hBB : B ⊆ B')
    (hh : PhaseSequence.Prefix loc F B v z lam eta Q H) :
    PhaseSequence.Prefix loc F B' v z lam eta Q H := by
  induction hh with
  | nil Q => exact PhaseSequence.Prefix.nil Q
  | @cons Q i H hi htail ih =>
    apply PhaseSequence.Prefix.cons _ ih
    refine ⟨hi.1,?_⟩
    rcases hi.2 with hb|⟨hF,W,hQ,hW,hop⟩
    · exact Or.inl (hBB hb)
    · exact Or.inr ⟨hF,W,hQ,hW.trans (Finset.union_subset_union_right hBB),hop⟩

lemma history_free_mono (loc : D → X) (F B B' Q : Finset X)
    (v lam eta : ℝ) (q : ℕ) (T : List (List X)) (hBB : B ⊆ B')
    (hh : History loc F B v lam eta q Q T) : History loc F B' v lam eta q Q T := by
  induction hh with
  | nil q Q => exact History.nil q Q
  | @cons q Q H T hhead htail ih =>
    exact History.cons ⟨prefix_free_mono loc F B B' Q v _ lam eta H hBB hhead.1,hhead.2⟩ ih

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

lemma PrefixData.mono_free {loc : D → X} {F B B' : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) (hB : B ⊆ B') :
    PrefixData loc F B' v lam eta q P :=
  ⟨h.length_eq,CommonPrefixTransfer.history_free_mono loc F B B' ∅ v lam eta 0 P hB h.history,
    h.free_bound,h.row⟩

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Coupled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma disjoint_map {F B : Finset X} {r : X → X} (hd : Disjoint F B)
    (hi : Function.Injective r) (hf : ∀ i ∈ F, r i = i) : Disjoint F (B.image r) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hy
  have hyx : y = x := hi (he.trans (hf x hx).symm)
  exact Finset.disjoint_left.mp hd hx (hyx ▸ hy)

end MetricKMedianRecovery.PhaseCoupledMerge

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
  obtain ⟨hl,hh,hr⟩ := CanonicalMergeCrossing.continuation_spec_s238 (located loc F Q)
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledFinish
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
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

end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
lemma Runs.cons_iff {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n : ℕ}
    {H : List X} {T : List (List X)} :
    Runs loc F B Q v lam q (n+1) (H::T) ↔
      Valid loc F B Q v ((1+v^2)^q) lam 0 H ∧ (∀ i∈H,i∈F) ∧
      Runs loc F B (Q∪H.toFinset) v lam (q+1) n T := by
  constructor
  · rintro ⟨hlen,hh,hr⟩
    cases hh with
    | cons hH hT =>
      exact ⟨hH,fun i hi=>hr H (List.mem_cons_self ..) i hi,
        by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen,
        hT,fun G hG=>hr G (List.mem_cons_of_mem _ hG)⟩
  · rintro ⟨hH,hHr,hT⟩
    refine ⟨by simp only [List.length_cons,hT.1],History.cons hH hT.2.1,?_⟩
    intro G hG
    rcases List.mem_cons.mp hG with rfl|hG
    · exact hHr
    · exact hT.2.2 G hG
end MetricKMedianRecovery.CanonicalMergeCrossing

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma aligned_phase {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q n k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q (n+1) k s)
    (hv : 0<v) (hv1 : v<1/6) (hlo : 0<lo) (G : List (Label V)) (U : List (List (Label V)))
    (hU : s.U=G::U) :
    Valid (fun j=>original (loc j)) (F.image original) s.mapFree (after ∅ s.mapPrefix)
      v ((1+v^2)^q) s.lam' eta G := by
  have hh := h.old_tail
  rw [hU] at hh
  obtain ⟨hG,hGr,_⟩ := Runs.cons_iff.mp hh
  have halign := PhaseParameterAlignment.align_s238 (fun j=>original (loc j)) (F.image original)
    s.B (after ∅ s.P) G s.correction.apply v s.lam s.lam' eta s.correction.error q n k (s.a F) (s.b F)
    hv hv1 (hlo.trans_le h.low) h.eps_nonneg h.price (by simpa only [Fintype.card_fin] using h.error)
    h.inj h.fixed h.old_prefix.after_subset h.shrink h.loss h.old_prefix.row hG hGr h.sandwich
  have hafter : (after ∅ s.P).image s.correction.apply=after ∅ s.mapPrefix := by
    simpa only [Finset.image_empty,State.mapPrefix] using (PhaseHistoryTransfer.after_map ∅ s.P s.correction.apply).symm
  simpa only [State.mapFree,hafter] using halign.1

lemma advance_certified {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q n k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q (n+1) k s)
    (hv : 0<v) (hv1 : v<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (G : List (Label V)) (T U : List (List (Label V))) (hU : s.U=G::U)
    (hT : Runs (fun j=>original (loc j)) (F.image original) s.mapFree
      (after ∅ s.mapPrefix∪G.toFinset) v s.lam' (q+1) n T)
    (hs : Sandwich k (finalCount (F.image original) (after ∅ s.mapPrefix) G T) (s.b F)) :
    Certified loc F v eta lo hi (q+1) n k (advanceState s G T U) := by
  have hh := h.old_tail
  rw [hU] at hh
  obtain ⟨hG,hGr,hUr⟩ := Runs.cons_iff.mp hh
  have hG' := aligned_phase h hv hv1 hlo G U hU
  have hfree : (G.toFinset \ F.image original).card≤3 := by
    have hh : G.toFinset⊆F.image original := fun i hi=>hGr i (List.mem_toFinset.mp hi)
    simp only [Finset.sdiff_eq_empty_iff_subset.mpr hh,Finset.card_empty,Nat.zero_le]
  have he : (s.P++[G]).map (List.map s.correction.apply)=s.mapPrefix++[G] := by
    simp only [List.map_append,List.map_cons,List.map_nil,
      PhaseParameterAlignment.regular_map_eq (F.image original) G s.correction.apply h.fixed hGr,State.mapPrefix]
  refine {
    before := h.before.mono (by omega)
    before_map := h.before_map.mono (by omega)
    disjoint := h.disjoint
    low := h.low
    high := h.high
    price := h.price
    eps_nonneg := h.eps_nonneg
    error := h.error
    inj := h.inj
    fixed := h.fixed
    shrink := h.shrink
    loss := h.loss
    old_prefix := h.old_prefix.append_phase hv hv1 (hlo.trans_le h.low) G
      ⟨PhaseMergeSurgery.prefix_exact_eta hG.1 heta,hG.2⟩ hfree
    new_prefix := ?_
    sandwich := ?_
    new_tail := ?_
    old_tail := ?_ }
  · change PrefixData _ _ s.mapFree _ _ _ _ ((s.P++[G]).map (List.map s.correction.apply))
    rw [he]
    exact h.new_prefix.append_phase hv hv1 ((hlo.trans_le h.low).trans_le h.price) G hG' hfree
  · change Sandwich k ((after (after ∅ ((s.P++[G]).map (List.map s.correction.apply))) T)∩F.image original).card
      ((after (after ∅ (s.P++[G])) U)∩F.image original).card
    simpa only [finalCount,List.toFinset_nil,Finset.union_empty,he,after_append,after,State.b,hU] using hs
  · change Runs _ _ s.mapFree (after ∅ ((s.P++[G]).map (List.map s.correction.apply))) _ _ _ _ T
    simpa only [he,after_append,after,advanceState] using hT
  · change Runs _ _ s.B (after ∅ (s.P++[G])) _ _ _ _ U
    simpa only [after_append,after,advanceState] using hUr

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

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma step_correct_s238_oai (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision q n k : ℕ) (s : State V)
    (h : Certified loc F v eta lo hi q (n+1) k s)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    (step loc distance F v M N precision q n k s).Correct loc F v eta lo hi q n k := by
  obtain ⟨H,T,hT⟩ : ∃ H T,s.T=H::T := by
    cases ht : s.T with
    | nil => have hh:=h.new_tail.1; rw [ht] at hh; simp only [List.length_nil] at hh; omega
    | cons H T => exact ⟨H,T,rfl⟩
  obtain ⟨G,U,hU⟩ : ∃ G U,s.U=G::U := by
    cases ht : s.U with
    | nil => have hh:=h.old_tail.1; rw [ht] at hh; simp only [List.length_nil] at hh; omega
    | cons G U => exact ⟨G,U,rfl⟩
  have hTr := h.new_tail
  rw [hT] at hTr
  obtain ⟨hH,hHr,hTr⟩ := Runs.cons_iff.mp hTr
  have hUr := h.old_tail
  rw [hU] at hUr
  obtain ⟨_,hGr,_⟩ := Runs.cons_iff.mp hUr
  have hG := aligned_phase h hv hv1 hlo G U hU
  have hdis := disjoint_map h.disjoint h.inj h.fixed
  have hp := h.new_prefix
  let W := FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
    (F.image original) v s.lam' (q+1) n (after ∅ s.mapPrefix∪G.toFinset)
  have hW : Runs (fun j=>original (loc j)) (F.image original) s.mapFree
      (after ∅ s.mapPrefix∪G.toFinset) v s.lam' (q+1) n W :=
    FiniteLabelContinuation.continuation_spec _ _ (rows_spec loc distance hmetric) _ _ _ _ _ hv hv1 _ _
      (Finset.union_subset hp.after_subset hG.1.opened_subset)
  let c := finalCount (F.image original) (after ∅ s.mapPrefix) G W
  have hfree : (G.toFinset \ F.image original).card≤3 := by
    have hh : G.toFinset⊆F.image original := fun i hi=>hGr i (List.mem_toFinset.mp hi)
    simp only [Finset.sdiff_eq_empty_iff_subset.mpr hh,Finset.card_empty,Nat.zero_le]
  dsimp only [step]
  rw [hT,hU]
  change Outcome.Correct loc F v eta lo hi q n k (if c=k then _ else if Sandwich k (s.a F) c then _ else _)
  split
  next hc =>
    have hh := finish_correct (hp.append_phase hv hv1 ((hlo.trans_le h.low).trans_le h.price) G hG hfree)
      hv hv1 ((hlo.trans_le h.low).trans_le h.price) heta hdis (h.low.trans h.price) h.high
      (T:=W) (n:=n) (by simpa only [after_append,after] using hW)
      (by simpa only [c,finalCount,after_append,after] using hc)
    simpa only [Outcome.Correct,Nat.add_assoc,Nat.add_comm 1 n] using hh
  next hc =>
    split
    next hac =>
      have hcopy : ∀ i∈F.image original,copy (3*q) i∉F.image original∪s.mapFree := by
        intro x hx
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact fresh F s.mapFree (3*q) h.before_map i 0
      have hspare : ∀ i∈F.image original,copy (3*q+1) i∉F.image original∪PhaseMergePath.pool (F.image original) s.mapFree (copy (3*q)) := by
        intro x hx
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        exact fresh F _ (3*q+1) (pool_before F s.mapFree (3*q) h.before_map) i 0
      have hdist : ∀ key,∀ i∈F.image original,∀ j,dist (original (loc j)) i=dist (original (loc j)) (copy key i) := by
        intro key x hx j
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
        rw [original_dist,copy_dist]
      have hcross := FiniteLabelCrossing.run_spec_s238 (fun j=>original (loc j)) (rows distance)
        (rows_spec loc distance hmetric) (F.image original) s.mapFree (after ∅ s.mapPrefix) v s.lam' eta
        q n k (copy (3*q)) (copy (3*q+1)) hv hv1 ((hlo.trans_le h.low).trans_le h.price) heta
        hp.after_subset hdis hp.row hcopy (hdist _) hspare (hdist _) H G T W
        ⟨PhaseMergeSurgery.prefix_exact_eta hH.1 heta,hH.2⟩ hG hHr hGr hTr hW
        (by simpa only [State.a,hT,c,finalCount,after] using hac)
      have hB : Before (3*q+2) (banks F s.mapFree q) := by
        exact pool_before F _ (3*q+1) (pool_before F s.mapFree (3*q) h.before_map)
      have hbdis : Disjoint (F.image original) (banks F s.mapFree q) :=
        CanonicalMergeCrossing.disjoint_pool _ _ _ (CanonicalMergeCrossing.disjoint_pool _ _ _ hdis hcopy) hspare
      exact resolve_correct_s238 loc distance hmetric F v M eta lo hi N precision q n k (3*q+2)
        (banks F s.mapFree q) s.lam' s.mapPrefix hF hM hN hB (by omega) hv hv1
        ((hlo.trans_le h.low).trans_le h.price) heta hbdis (h.low.trans h.price) h.high
        (h.high.trans hhi) hprecision hdiam
        (hp.mono_free ((PhaseMergePath.subset_pool ..).trans (PhaseMergePath.subset_pool ..))) _ hcross
    next hac =>
      apply advance_certified h hv hv1 hlo heta G W U hU hW
      have hh:=h.sandwich
      unfold Sandwich at hh hac ⊢
      omega

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238_oai.{u_1}
