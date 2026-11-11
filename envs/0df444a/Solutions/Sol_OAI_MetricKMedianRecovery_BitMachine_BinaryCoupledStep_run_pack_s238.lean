-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:14:03.602457+00:00
-- url     : https://prove2.me/submissions/d82f175d-953c-47a7-924d-0a5aece2e745

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_Q_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_a_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_advanceInput_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_banks_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_c_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_crossInput_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_finishInput_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_mapped_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_power_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteCross_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryResolve_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_PhaseParameterAlignment_align_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_RationalPhase_completion_spec_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

namespace WordList

lemma cons_ne_nil (w ws : List Bool) : cons w ws≠[] := List.cons_ne_nil _ _

end WordList
end MetricKMedianRecovery.BitMachine

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

end MetricKMedianRecovery.PhaseHistoryTransfer

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

end MetricKMedianRecovery.HistoryIsometry

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

lemma PrefixData.after_subset {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) :
    after ∅ P ⊆ F ∪ B := h.history.after_subset (Finset.empty_subset _)

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
  obtain ⟨hh,hr,hl⟩ := RationalPhase.completion_spec_s238 (located loc F Q) (rows loc F Q distance)
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

omit [DecidableEq V] in
lemma copy_dist (key : ℕ) (i j : V) :
    dist (original i) (copy key (original j))=dist i j := by
  rw [show copy key (original j)=leaf key j 0 from rfl,leaf_dist]
  simp

end MetricKMedianRecovery.RationalLeaves

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

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CoupledEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
attribute [local irreducible] BinaryCorrection.mapHistory
lemma historyBits_append {m : ℕ} (P T : List (List (Label (Fin m)))) : historyBits (P++T)=historyBits P++historyBits T := by
  simp only [historyBits,List.map_append,encode_append]
lemma historyBits_cons {m : ℕ} (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    historyBits (H::T)=cons (labels H) (historyBits T) := rfl
lemma finish_pack {m : ℕ} (B : Finset (Label (Fin m))) (lam : ℚ) (P T : List (List (Label (Fin m)))) :
    finish (encode [setBits B,BinaryRational.encode lam,historyBits P,historyBits T])=
      outputBits (CanonicalCoupledMerge.finish B lam P T) := by
  simp only [finish,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    outputBits,CanonicalCoupledMerge.finish,historyBits_append]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
lemma advance_pack {m : ℕ} (s : State (Fin m)) (G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    advance (encode [stateBits s,labels G,historyBits T,historyBits U])=stateBits (advanceState s G T U) := by
  simp only [advance,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    stateBits,advanceState,historyBits_append,historyBits_cons]
  rfl

end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StepPack
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
attribute [local irreducible] BinaryFiniteMachine.continuation BinaryFiniteCross.run
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
  (Q₀ : Finset (Label (Fin m))) (v z b : ℚ) (n q precision k : ℕ) (s : State (Fin m))
local notation "xx" => pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q b precision k s
lemma bf_pack (i : ℕ) : bf i xx=field i (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) := by
  simp only [bf,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,Option.getD_some]
lemma sf_pack (i : ℕ) : sf i xx=field i (stateBits s) := by
  simp only [sf,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma base_pack : base xx=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original)
    (after ∅ s.mapPrefix) v ((1+v^2)^q) s.lam' := by
  simp only [base,bf_pack,sf_pack,Q_pack_s238,power_pack_s238]
  simp only [BinaryFiniteContext.pack,stateBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma keys_pack : key xx=(3*q).bits ∧ spare xx=(3*q+1).bits ∧ leafKey xx=(3*q+2).bits := by
  simp only [key,spare,leafKey,qbits,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,List.length_replicate,
    value_bits,and_self]
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open PhaseSequence PhaseMergeCompletion PhaseMergeInvariant PhaseCoupledMerge PhaseMergeRefinement CanonicalMergeCrossing
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma cross_pack (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (Q₀ : Finset (Label (Fin m))) (v z b : ℚ) (n q precision k : ℕ) (s : State (Fin m))
    (eta lo hi : ℝ) (h : Certified loc F v eta lo hi q (n+1) k s)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m)))) (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) :
    BinaryFiniteCross.run (crossInput (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q b precision k s))=
      BinaryCross.resultBits (FiniteLabelCrossing.run (fun j=>original (loc j)) (rows distance) (F.image original)
        (after ∅ s.mapPrefix) v s.lam' q n k (copy (3*q)) (copy (3*q+1)) H₀ G₀ T₀
        (FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance) (F.image original)
          v s.lam' (q+1) n (after ∅ s.mapPrefix∪G₀.toFinset))) := by
  rw [crossInput_pack_s238 distance loc F Q₀ v z b n q precision k s H₀ G₀ T₀ U₀ hT hU]
  have hTr:=h.new_tail
  rw [hT] at hTr
  obtain ⟨hH,hHr,_⟩:=Runs.cons_iff.mp hTr
  have hUr:=h.old_tail
  rw [hU] at hUr
  obtain ⟨_,hGr,_⟩:=Runs.cons_iff.mp hUr
  have hG:=aligned_phase h hv hv1 hlo G₀ U₀ hU
  have hdis:=disjoint_map h.disjoint h.inj h.fixed
  have hp:=h.new_prefix
  have hcopy : ∀ i∈F.image original,copy (3*q) i∉F.image original∪s.mapFree := by
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    exact fresh F s.mapFree (3*q) h.before_map i 0
  have hdist : ∀ i∈F.image original,∀ j,dist (original (loc j)) i=dist (original (loc j)) (copy (3*q) i) := by
    intro x hx j
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist,copy_dist]
  have hz : (((1+v^2)^q:ℚ):ℝ)=(1+(v:ℝ)^2)^q := by push_cast; rfl
  have hc:=FiniteLabelContinuation.correct_completion (fun j=>original (loc j)) (rows distance)
    (rows_spec loc distance hmetric) (F.image original) v ((1+v^2)^q) s.lam' hv hv1 (by rw [hz]; positivity)
  exact BinaryFiniteCross.run_pack_s238 distance (fun j=>original (loc j)) (F.image original) s.mapFree
    (after ∅ s.mapPrefix) v s.lam' eta (3*q) (3*q+1) k n q hc hv hv1
    ((hlo.trans_le h.low).trans_le h.price) heta hp.after_subset hdis hp.row hcopy hdist H₀ G₀ T₀ _ hHr hGr
    ⟨PhaseMergeSurgery.prefix_exact_eta hH.1 heta,hH.2⟩ hG
lemma run_pack_s238_oai (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (Q₀ : Finset (Label (Fin m))) (v z M : ℚ) (N n q precision k : ℕ) (s : State (Fin m))
    (eta lo hi : ℝ) (h : Certified loc F v eta lo hi q (n+1) k s)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q (20*N*M) precision k s)=
      outcomeBits (CanonicalCoupledMerge.step loc distance F v M N precision q n k s) := by
  obtain ⟨H₀,T₀,hT⟩ : ∃ H T,s.T=H::T := by
    cases ht : s.T with
    | nil=>have hh:=h.new_tail.1; rw [ht] at hh; simp only [List.length_nil] at hh; omega
    | cons H T=>exact ⟨H,T,rfl⟩
  obtain ⟨G₀,U₀,hU⟩ : ∃ G U,s.U=G::U := by
    cases ht : s.U with
    | nil=>have hh:=h.old_tail.1; rw [ht] at hh; simp only [List.length_nil] at hh; omega
    | cons G U=>exact ⟨G,U,rfl⟩
  let x:=pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q (20*N*M) precision k s
  have hne : nonempty x=true := by
    simp only [nonempty,x,sf_pack,stateBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      hT,hU,BinaryCoupled.historyBits_cons,cons_ne_nil,decide_false,Bool.not_false,Bool.true_and]
  have hc:=c_pack_s238 distance loc F Q₀ v z (20*N*M) n q precision k s H₀ G₀ T₀ U₀ hT hU
  have ha:=a_pack_s238 distance loc F Q₀ v z (20*N*M) n q precision k s
  have hkey : field 5 x=k.bits := by simp only [x,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hs : sandwiched x=decide (PhaseCountCrossing.Sandwich k (s.a F)
      (CanonicalMergeCrossing.finalCount (F.image original) (after ∅ s.mapPrefix) G₀
        (FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance) (F.image original)
          v s.lam' (q+1) n (after ∅ s.mapPrefix∪G₀.toFinset)))) := by
    apply Bool.eq_iff_iff.mpr
    simp only [sandwiched,show a x=_ from ha,show c x=_ from hc,hkey,value_bits,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    rfl
  have hcross:=cross_pack distance loc hmetric F Q₀ v z (20*N*M) n q precision k s eta lo hi h hv hv1 hlo heta H₀ G₀ T₀ U₀ hT hU
  have hr : resolveInput x=BinaryResolve.pack
      (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (after ∅ s.mapPrefix) v ((1+v^2)^q) s.lam')
      n q (3*q+2) (20*N*M) k precision (CanonicalCoupledMerge.banks F s.mapFree q) s.mapPrefix
      (FiniteLabelCrossing.run (fun j=>original (loc j)) (rows distance) (F.image original)
        (after ∅ s.mapPrefix) v s.lam' q n k (copy (3*q)) (copy (3*q+1)) H₀ G₀ T₀
        (FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance) (F.image original)
          v s.lam' (q+1) n (after ∅ s.mapPrefix∪G₀.toFinset))) := by
    simp only [resolveInput,Function.comp_apply,x]
    simp only [base_pack,(keys_pack distance loc F Q₀ v z (20*N*M) n q precision k s).2.2,
      banks_pack_s238,(mapped_pack_s238 distance loc F Q₀ v z (20*N*M) n q precision k s).2,hcross,
      ]
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryResolve.pack]
  change run x=_
  simp only [run,hne,ite_true, if_true,active]
  rw [show c x=_ from hc,hkey,hs,hr]
  simp only [value_bits,decide_eq_true_eq]
  rw [BinaryResolve.run_pack_s238]
  simp only [CanonicalCoupledMerge.step,hT,hU]
  split_ifs
  · rw [show finishInput x=_ from finishInput_pack_s238 distance loc F Q₀ v z (20*N*M) n q precision k s H₀ G₀ T₀ U₀ hT hU,BinaryCoupled.finish_pack]
    rfl
  · rfl
  · rw [show advanceInput x=_ from advanceInput_pack_s238 distance loc F Q₀ v z (20*N*M) n q precision k s H₀ G₀ T₀ U₀ hT hU,BinaryCoupled.advance_pack]
    rfl
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238_oai
