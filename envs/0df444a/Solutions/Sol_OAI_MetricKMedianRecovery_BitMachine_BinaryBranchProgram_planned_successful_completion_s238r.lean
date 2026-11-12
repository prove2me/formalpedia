-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:34:39.430454+00:00
-- url     : https://prove2.me/submissions/e930939d-69d5-44db-a9c6-13f1fe2b11bb

import Mathlib
import Definitions.Def_Q238L018
import Definitions.Def_Q238L021
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_objective_eq_source_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_result_guarantee_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Sampling_Comparison_surrogate_success_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_Blue
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [DecidableEq V] {a : ℕ}

lemma designated_partition (R : Finset V) (dest : V → Destination V a) :
    Disjoint (designatedRed R dest) (designatedBlue R dest) ∧
      designatedRed R dest ∪ designatedBlue R dest = R := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro s hs ht
    have h₁ := (Finset.mem_filter.mp hs).2
    have h₂ := (Finset.mem_filter.mp ht).2
    simp only [h₁] at h₂
    contradiction
  · ext s
    simp only [designatedBlue,designatedRed,Finset.mem_union,Finset.mem_filter]
    cases (dest s).isBlue <;> simp

lemma designated_count (R : Finset V) (dest : V → Destination V a) :
    (designatedRed R dest).card+(designatedBlue R dest).card = R.card := by
  rw [← Finset.card_union_of_disjoint (designated_partition R dest).1,
    (designated_partition R dest).2]

lemma designatedProxies_mem (R : Finset V) (dest : V → Destination V a) (v : V) :
    v ∈ designatedProxies R dest ↔ ∃ s ∈ R, dest s = .proxy v := by
  simp only [designatedProxies,Finset.mem_biUnion]
  constructor
  · rintro ⟨s,hs,hv⟩
    refine ⟨s,hs,?_⟩
    cases he : dest s with
    | proxy w =>
      simp only [he,Finset.mem_singleton] at hv
      subst w
      rfl
    | covered i => simp only [he,Finset.notMem_empty] at hv
    | uncovered o => simp only [he,Finset.notMem_empty] at hv
  · rintro ⟨s,hs,he⟩
    exact ⟨s,hs,by simp only [he,Finset.mem_singleton]⟩

lemma favorable_color_consequences (R : Finset V) (dest : V → Destination V a)
    (hdisj : Disjoint R (designatedProxies R dest)) (colors : V → Fin 3)
    (hcolors : ∀ s ∈ R ∪ designatedProxies R dest, colors s = requiredColors R dest s) :
    (∀ s ∈ designatedRed R dest, colors s = 1) ∧
    (∀ s ∈ designatedBlue R dest, colors s = 2) ∧
    (∀ s ∈ designatedProxies R dest, colors s = 0) := by
  refine ⟨?_,?_,?_⟩
  · intro s hs
    obtain ⟨hsR,hsd⟩ := Finset.mem_filter.mp hs
    simpa only [requiredColors,hsR,↓reduceIte,hsd,Bool.false_eq_true] using
      hcolors s (Finset.mem_union_left _ hsR)
  · intro s hs
    obtain ⟨hsR,hsd⟩ := Finset.mem_filter.mp hs
    simpa only [requiredColors,hsR,↓reduceIte,hsd] using
      hcolors s (Finset.mem_union_left _ hsR)
  · intro s hs
    have hn : s ∉ R := fun hr => Finset.disjoint_left.mp hdisj hr hs
    simpa only [requiredColors,hn,↓reduceIte] using
      hcolors s (Finset.mem_union_right _ hs)

lemma proxy_requirements_consistent (R Proxies : Finset V)
    (dest : V → Destination V a) (hRP : Disjoint R Proxies)
    (hdest : ∀ s ∈ R, ∀ v, dest s = .proxy v → v ∈ Proxies) :
    Disjoint R (designatedProxies R dest) := by
  refine hRP.mono_right ?_
  intro v hv
  obtain ⟨s,hs,he⟩ := (designatedProxies_mem R dest v).mp hv
  exact hdest s hs v he

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}

lemma nonproxy_card (C : Comparison D S O) : C.nonproxy.card = C.bad.card := by
  have hsub : C.good.image C.proxy ⊆ S := Finset.image_subset_iff.mpr C.proxy_mem
  rw [nonproxy, Finset.card_sdiff_of_subset hsub, bad,
    Finset.card_sdiff_of_subset C.good_subset, C.same_card,
    Finset.card_image_of_injOn C.proxy_inj]

lemma proxy_survives (C : Comparison D S O) (s : State V) (hq : s.deleted ⊆ C.nonproxy)
    (o : V) (ho : o ∈ C.good) : C.proxy o ∈ S \ s.deleted := by
  refine Finset.mem_sdiff.mpr ⟨C.proxy_mem o ho, ?_⟩
  intro hh
  have hn := (Finset.mem_sdiff.mp (hq hh)).2
  exact hn (Finset.mem_image.mpr ⟨o,ho,rfl⟩)

lemma correct_covered_subset (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : C.covered s ⊆ C.bad := by
  intro o ho
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  exact (hs.2.2 z hz).2.1

lemma correct_lengths (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) :
    s.leaves.length ≤ C.bad.card ∧ s.deleted.card ≤ C.bad.card := by
  have hc : (C.covered s).card = s.leaves.length := by
    rw [covered, List.toFinset_card_of_nodup hs.2.1, List.length_map]
  refine ⟨?_, ?_⟩
  · rw [← hc]
    exact Finset.card_le_card (C.correct_covered_subset hD kappa s hs)
  · rw [← C.nonproxy_card]
    exact Finset.card_le_card hs.1

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoveredCenter
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}
lemma coveredCenter_mem (C : Comparison D S O) (s : State V) (i : Fin s.leaves.length) :
    C.coveredCenter s i ∈ C.covered s := by
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨s.leaves[i.val],List.getElem_mem i.isLt,rfl⟩
lemma covered_card_eq_length (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) :
    (C.covered s).card = s.leaves.length := by
  rw [covered,List.toFinset_card_of_nodup hs.2.1,List.length_map]
lemma coveredCenter_ball (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) (i : Fin s.leaves.length) :
    dist s.leaves[i.val].1 (C.coveredCenter s i) ≤ s.leaves[i.val].2 :=
  (hs.2.2 _ (List.getElem_mem i.isLt)).2.2.2.2.1
lemma coveredCenter_facility (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (F : Finset V) (hOF : O ⊆ F) (i : Fin s.leaves.length) : C.coveredCenter s i ∈ F := by
  have hh := C.correct_covered_subset hD kappa s hs (C.coveredCenter_mem s i)
  exact hOF (Finset.mem_sdiff.mp hh).1

lemma exact_completion_counts (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) :
    s.leaves.length + (C.bad \ C.covered s).card = C.bad.card ∧
    s.deleted.card + (C.nonproxy \ s.deleted).card = C.bad.card := by
  have hcov := C.correct_covered_subset hD kappa s hs
  rw [Finset.card_sdiff_of_subset hcov,Finset.card_sdiff_of_subset hs.1,
    C.covered_card_eq_length hD kappa s hs,C.nonproxy_card]
  have hc := C.correct_lengths hD kappa s hs
  omega

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PartitionPullback
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
open Categorical
variable {E B I : Type*} [DecidableEq B] [DecidableEq I]
lemma filter_image_part (partE : E→I) (partB : B→I) (f : E→B)
    (hf : ∀ e,partB (f e)=partE e) (X : Finset E) (i : I) :
    (X.image f).filter (fun e=>partB e=i)=(X.filter (fun e=>partE e=i)).image f := by
  ext b
  simp only [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨e,he,rfl⟩,hi⟩
    exact ⟨e,⟨he,(hf e) ▸ hi⟩,rfl⟩
  · rintro ⟨e,⟨he,hi⟩,rfl⟩
    exact ⟨⟨e,he,rfl⟩,by rw [hf];exact hi⟩
lemma partition_image {a : ℕ} (partE : E→Fin a) (partB : B→Fin a) (f : E→B)
    (hf : ∀ e,partB (f e)=partE e) (X : Finset E) (hX : PartitionFeasible partE X) :
    PartitionFeasible partB (X.image f) := by
  intro i
  rw [filter_image_part partE partB f hf]
  exact Finset.card_image_le.trans (hX i)
end MetricKMedianRecovery.Completion

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
lemma mod_embed (H : Fin a→Finset (Fin n)) (e : (i : Fin a)×(H i)) : (embed H e).modNat=e.2.val := by
  exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (e.1,e.2.val))
lemma location_embed (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (e : (i : Fin a)×(H i)) :
    location H hH (embed H e)=e.2.val := by
  simp only [location,mod_embed,show (embed H e).divNat=e.1 from part_embed H e,ite_eq_left e.2.property]
end MetricKMedianRecovery.Completion.CopyGround

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ClientCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [DecidableEq V] in
lemma selectedDestination_mem {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) :
    selectedDestination theta center w radius Ω hΩ s ∈ Ω :=
  (Classical.choose_spec (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)).1

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DestinationFacility
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [DecidableEq V] {a : ℕ}

omit [DecidableEq V] in
lemma blue_destination_eq (d : Destination V a) (h : d.isBlue = true) (center : Fin a → V) :
    d = .uncovered (destinationFacility center d) := by
  cases d <;> simp_all [Destination.isBlue,destinationFacility]

end MetricKMedianRecovery.Completion

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma designatedDestination_mem (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (v : V) :
    C.designatedDestination hD s theta v ∈ C.destinations s :=
  selectedDestination_mem theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
    (C.destinations s) (C.destinations_nonempty hD s) v

lemma designation_disjoint (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) :
    Disjoint (C.nonproxy \ s.deleted)
      (designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) := by
  apply proxy_requirements_consistent (C.nonproxy \ s.deleted) (C.good.image C.proxy)
  · apply Finset.disjoint_left.mpr
    intro v hv hp
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
  · intro u _ v he
    have hh := C.designatedDestination_mem hD s theta u
    rw [he] at hh
    exact (C.destinations_proxy s v).mp hh

lemma favorable_destination_green (C : Comparison D S O) (hD : D.Nonempty)
    (kappa theta : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u)
    (u : V) (hu : u ∈ C.nonproxy \ s.deleted) (v : V)
    (hdest : C.designatedDestination hD s theta u = .proxy v) :
    v ∈ colorClass (S \ s.deleted) colors 0 := by
  have hh := favorable_color_consequences (C.nonproxy \ s.deleted)
    (C.designatedDestination hD s theta) (C.designation_disjoint hD s theta) colors hcolors
  have hgreen := hh.2.2 v ((designatedProxies_mem _ _ v).mpr ⟨u,hu,hdest⟩)
  have hv := C.designatedDestination_mem hD s theta u
  rw [hdest] at hv
  obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp ((C.destinations_proxy s v).mp hv)
  exact Finset.mem_filter.mpr ⟨C.proxy_survives s hs.1 o ho,hgreen⟩

lemma favorable_red_rule (C : Comparison D S O) (hD : D.Nonempty)
    (kappa theta : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u)
    (u : V) (hu : u ∈ designatedRed (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    match C.designatedDestination hD s theta u with
    | .proxy v => v ∈ colorClass (S \ s.deleted) colors 0
    | .covered _ => True
    | .uncovered _ => False := by
  have huR := (Finset.mem_filter.mp hu).1
  have hblue := (Finset.mem_filter.mp hu).2
  cases he : C.designatedDestination hD s theta u with
  | proxy v => exact C.favorable_destination_green hD kappa theta s hs colors hcolors u huR v he
  | covered i => trivial
  | uncovered v => simp only [he,Destination.isBlue,Bool.true_eq_false] at hblue

lemma blueDestination_uncovered (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V)
    (hu : u ∈ designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    C.designatedDestination hD s theta u = .uncovered (C.blueDestination hD s theta u) :=
  blue_destination_eq _ (Finset.mem_filter.mp hu).2 _

lemma blueDestination_mem (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V)
    (hu : u ∈ designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    C.blueDestination hD s theta u ∈ C.bad \ C.covered s := by
  have hh := C.designatedDestination_mem hD s theta u
  rw [C.blueDestination_uncovered hD s theta u hu] at hh
  exact (C.destinations_uncovered s _).mp hh

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SubsetSubtypeRepresentative
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma nonproxy_remaining_in (C : Comparison D S O) (s : State V) :
    C.nonproxy \ s.deleted ⊆ S \ s.deleted := by
  intro u hu
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu).1).1,
    (Finset.mem_sdiff.mp hu).2⟩

lemma favorable_color_subsets (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u) :
    designatedRed (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) ⊆
        colorClass (S \ s.deleted) colors 1 ∧
    designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) ⊆
        colorClass (S \ s.deleted) colors 2 := by
  have hh := favorable_color_consequences (C.nonproxy \ s.deleted)
    (C.designatedDestination hD s theta) (C.designation_disjoint hD s theta) colors hcolors
  exact ⟨fun u hu => Finset.mem_filter.mpr
    ⟨C.nonproxy_remaining_in s (Finset.mem_filter.mp hu).1,hh.1 u hu⟩,
    fun u hu => Finset.mem_filter.mpr
    ⟨C.nonproxy_remaining_in s (Finset.mem_filter.mp hu).1,hh.2.1 u hu⟩⟩

lemma affordable_blue_destinations (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) :
    let B := designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)
    (B.image (C.blueDestination hD s theta)).card ≤ (C.bad \ C.covered s).card ∧
    (B.image (C.blueDestination hD s theta)).card ≤ B.card := by
  classical
  dsimp only
  refine ⟨Finset.card_le_card ?_,Finset.card_image_le⟩
  intro v hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  exact C.blueDestination_mem hD s theta u hu

lemma favorable_counter_bound (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (hs : C.Correct hD (1/1000000) s) (theta : ℝ) :
    let dest := C.designatedDestination hD s theta
    let B := designatedBlue (C.nonproxy \ s.deleted) dest
    let R := designatedRed (C.nonproxy \ s.deleted) dest
    s.leaves.length + (B.image (C.blueDestination hD s theta)).card ≤
      s.deleted.card + R.card + B.card := by
  dsimp only
  have hh := C.exact_completion_counts hD (1/1000000) s hs
  have hc := designated_count (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)
  have hb := C.affordable_blue_destinations hD s theta
  dsimp only at hb
  omega

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_VirtualCast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_SortedRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {V : Type*} [LinearOrder V]
lemma representative_image (S T : Finset V) (h : T⊆S) :
    (representative S T).image (enum S)=T := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hi).2
  · intro hx
    let i:=(equiv S).symm ⟨x,h hx⟩
    have hi : enum S i=x := by
      exact congrArg Subtype.val ((equiv S).apply_symm_apply ⟨x,h hx⟩)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi ▸ hx⟩,hi⟩
lemma representative_card (S T : Finset V) (h : T⊆S) :
    (representative S T).card=T.card := by
  calc (representative S T).card = ((representative S T).image (enum S)).card :=
        (Finset.card_image_of_injective _ (enum_injective S)).symm
       _ = T.card := congrArg Finset.card (representative_image S T h)
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion.CopyGround
variable {n a : ℕ}
lemma transversal_feasible (H : Fin a→Finset (Fin n)) (v : Fin a→Fin n) (hv : ∀ i,v i∈H i) :
    Categorical.PartitionFeasible part (transversal H v hv) := by
  apply partition_image id part (fun i=>embed H ⟨i,⟨v i,hv i⟩⟩) (fun i=>part_embed H _) Finset.univ
  intro i
  simp only [id_eq,Finset.filter_eq',Finset.mem_univ,ite_true, if_true,Finset.card_singleton,le_refl]
lemma transversal_center (H : Fin a→Finset (Fin n)) (v : Fin a→Fin n) (hv : ∀ i,v i∈H i)
    (hH : ∀ i,(H i).Nonempty) (i : Fin a) : ∃ e∈transversal H v hv,location H hH e=v i :=
  ⟨embed H ⟨i,⟨v i,hv i⟩⟩,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,location_embed H hH _⟩
end MetricKMedianRecovery.Completion.CopyGround
namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open Completion
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma balls_eq_source (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (F : Finset (Fin n)) (s : RationalSampling.State n) (i : Fin s.real.leaves.length) :
    balls δ F s (Fin.cast s.real_length i)=ballSet F (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) i := by
  have hil : i.val < s.leaves.length := by simpa only [s.real_length] using i.isLt
  ext f
  simp only [balls,ballSet,Finset.mem_filter]
  apply and_congr_right
  intro _
  have hw:=s.center_cast i
  have hr:=s.radius_cast i
  change s.leaves[i.val].1=Sampling.leafCenter s.real i at hw
  change (s.leaves[i.val].2:ℝ)=Sampling.leafRadius s.real i at hr
  rw [←hw,←hr,←hδ,Rat.cast_le]
  rfl
lemma padded_comparison (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (F : Finset (Fin n)) (s : RationalSampling.State n) (center : Fin s.real.leaves.length→Fin n)
    (hF : ∀ i,center i∈F) (hball : ∀ i,dist (Sampling.leafCenter s.real i) (center i)≤Sampling.leafRadius s.real i) :
    ∃ hH : ∀ i,(balls δ F s i).Nonempty, ∃ X : Finset (Fin (s.leaves.length*n)),
      Categorical.PartitionFeasible CopyGround.part X ∧
      ∀ i,∃ e∈X,CopyGround.location (balls δ F s) hH e=center i := by
  let v : Fin s.leaves.length→Fin n := fun i=>center (Fin.cast s.real_length.symm i)
  have hv (i : Fin s.leaves.length) : v i∈balls δ F s i := by
    have he : i=Fin.cast s.real_length (Fin.cast s.real_length.symm i) := by ext;rfl
    rw [he,balls_eq_source δ hδ]
    exact Finset.mem_filter.mpr ⟨hF _,hball _⟩
  have hH (i : Fin s.leaves.length) : (balls δ F s i).Nonempty := ⟨v i,hv i⟩
  refine ⟨hH,CopyGround.transversal (balls δ F s) v hv,CopyGround.transversal_feasible _ _ _,?_⟩
  intro i
  have he : Fin.cast s.real_length.symm (Fin.cast s.real_length i)=i := by ext;rfl
  simpa only [v,he] using CopyGround.transversal_center (balls δ F s) v hv hH (Fin.cast s.real_length i)
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext Sampling
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma planned_successful_completion_s238r_oai
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (colors : Fin n→Fin 3)
    (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)) u)
    (label : Fin n→Fin m)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (P : BlueSubsetDP.Plan ((S\s.deleted).filter (fun i=>colors i=2)) F label
      (fun u v=>(rationalScore δ D S Δ s u v:ℝ))
      (((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
        (C.blueDestination hD s.real (19/50))).card))
    (hvalue : (∑ l,branchScore D S (Δ:ℝ) s.real (P.sel l) (P.dst l))≤
      ∑ u∈designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)),
        assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
          minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
            (C.destinations s.real) (C.destinations_nonempty hD s.real) u) :
    ∃ hH : ∀ i,(balls δ F s i).Nonempty,
      (∀ bits,result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits⊆F ∧
        (result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).card=S.card ∧
        (result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).Nonempty) ∧
      average (fun bits=>realCost D (result δ D F S Δ s colors hH P.sel P.dst
        (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits))≤
          (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  let dest:=C.designatedDestination hD s.real (19/50)
  let Rstar:=C.nonproxy\s.real.deleted
  let rd:=designatedRed Rstar dest
  let bd:=designatedBlue Rstar dest
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let Y:=bd.image (C.blueDestination hD s.real (19/50))
  have hc:=C.favorable_color_subsets hD s.real (19/50) colors hcolors
  have hrd : rd⊆red := hc.1
  let T:=SortedIndex.representative red rd
  have hTim : T.image (SortedIndex.enum red)=rd := SortedIndex.representative_image red rd hrd
  have hT : T.card=rd.card := SortedIndex.representative_card red rd hrd
  have hq : rd.card ≤ red.card := Finset.card_le_card hrd
  have hcount : s.leaves.length+Y.card≤ s.deleted.card+rd.card+m := by
    have hh:=C.favorable_counter_bound hD s.real hs (19/50)
    dsimp only at hh
    change s.real.leaves.length+Y.card≤ s.deleted.card+rd.card+bd.card at hh
    rw [s.real_length,show bd.card=m from hcard] at hh
    exact hh
  have hdel : s.deleted⊆S := by
    intro u hu
    exact (Finset.mem_sdiff.mp (hs.1 hu)).1
  have hr : ∀ i,0≤ s.radius i := by
    intro i
    let j:=Fin.cast s.real_length.symm i
    have hj : Fin.cast s.real_length j=i := by ext;rfl
    rw [←hj,s.radius_cast]
    exact (hs.2.2 _ (List.getElem_mem j.isLt)).2.2.2.1.le
  obtain ⟨hH,X,hX,hcenter⟩:=padded_comparison δ hδ F s (C.coveredCenter s.real)
    (C.coveredCenter_facility hD (1/1000000) s.real hs F hOF)
    (C.coveredCenter_ball hD (1/1000000) s.real hs)
  have hh:=result_guarantee_s238r δ hδ D F S hSF hS Δ hΔ hbound s hdel colors hH hr P.sel P.dst Y.card rd.card
    P.selected_injective (fun j=>(P.selection j).1) (fun j=>(P.selection j).2.2) P.destination_count hcount hq
  refine ⟨hH,hh.1,(hh.2 X hX).trans ?_⟩
  rw [objective_eq_source_s238r δ hδ,objective_eq_source_s238r δ hδ]
  have hdisj : Disjoint (T.image (SortedIndex.enum red)) bd := by
    rw [hTim];exact (designated_partition Rstar dest).1
  have hcover : T.image (SortedIndex.enum red)∪bd=C.nonproxy\s.real.deleted := by
    rw [hTim];exact (designated_partition Rstar dest).2
  have hredDest : ∀ r∈T,
      match selectedDestination (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
          (C.destinations s.real) (C.destinations_nonempty hD s.real) (SortedIndex.enum red r) with
      | .proxy φ=>φ∈green | .covered _=>True | .uncovered _=>False := by
    intro r hrT
    have hrD : SortedIndex.enum red r∈rd := by
      rw [←hTim];exact Finset.mem_image.mpr ⟨r,hrT,rfl⟩
    have hh:=C.favorable_red_rule hD (1/1000000) (19/50) s.real hs colors hcolors _ hrD
    simp only [Comparison.designatedDestination] at hh
    cases hd : selectedDestination (19/50) (C.coveredCenter s.real) (leafCenter s.real)
        (leafRadius s.real) (C.destinations s.real) (C.destinations_nonempty hD s.real) (SortedIndex.enum red r) with
    | proxy v=>
      simp only [hd] at hh
      simpa only [Comparison.colorClass,green,RationalSampling.State.real] using hh
    | covered i=>trivial
    | uncovered v=>simp only [hd] at hh
  have hss:=C.surrogate_success_s238r hD (Δ:ℝ) s.real hs (Rat.cast_nonneg.mpr hΔ) hP hm hI hN
    (CopyGround.location (balls δ F s) hH) X hcenter green bd (SortedIndex.enum red) (SortedIndex.enum_injective red)
    rd.card T hT hdisj hcover (fun r hrT=>by
      have hh:=hredDest r hrT
      cases hd : selectedDestination (19/50) (C.coveredCenter s.real) (leafCenter s.real)
          (leafRadius s.real) (C.destinations s.real) (C.destinations_nonempty hD s.real) (SortedIndex.enum red r) with
      | proxy v=>simpa only [hd] using hh
      | covered i=>trivial
      | uncovered v=>simp only [hd] at hh) _ hvalue
  norm_num at hss ⊢
  exact hss
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.planned_successful_completion_s238r_oai
