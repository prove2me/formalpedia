-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_global_height_with_local_singular_limits
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:47.722428+00:00
-- url     : https://prove2.me/submissions/4d1708a4-742f-435a-b71e-71611f6a4306

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Definitions.Def_OAIQ231Rr001

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology

variable {ι : Type*} [Fintype ι]

theorem dyadicBoxPartition_isPartition (I : Box ι) (k : ℕ) :
    (dyadicBoxPartition I k).IsPartition := by
  induction k with
  | zero => exact Prepartition.isPartitionTop I
  | succ k ih =>
    exact ih.biUnion (fun J _ => Prepartition.isPartition_splitCenter J)

theorem dyadicBoxPartition_width (I : Box ι) (k : ℕ) (J : Box ι)
    (hJ : J ∈ dyadicBoxPartition I k) (i : ι) :
    J.upper i - J.lower i = (I.upper i - I.lower i) * (1 / 2 : ℝ) ^ k := by
  induction k generalizing J with
  | zero =>
    have h : J = I := Prepartition.mem_top.mp hJ
    subst J
    simp
  | succ k ih =>
    obtain ⟨P, hP, hJP⟩ := (dyadicBoxPartition I k).mem_biUnion.mp hJ
    rw [Prepartition.upper_sub_lower_of_mem_splitCenter hJP, ih P hP, pow_succ]
    ring

theorem dyadicBoxPartition_volume (I : Box ι) (k : ℕ) (J : Box ι)
    (hJ : J ∈ dyadicBoxPartition I k) :
    (volume : Measure (ι → ℝ)).real J =
      (volume : Measure (ι → ℝ)).real I * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι := by
  simp only [Measure.real, Box.volume_apply']
  simp_rw [dyadicBoxPartition_width I k J hJ]
  rw [Finset.prod_mul_distrib]
  simp

theorem box_volume_real_pos (I : Box ι) :
    0 < (volume : Measure (ι → ℝ)).real I := by
  rw [Measure.real, Box.volume_apply']
  exact Finset.prod_pos (fun i _ => sub_pos.mpr (I.lower_lt_upper i))

theorem boxWidthBound_nonneg (I : Box ι) : 0 ≤ boxWidthBound I :=
  Finset.sum_nonneg (fun i _ => (sub_pos.mpr (I.lower_lt_upper i)).le)

theorem box_width_le_bound (I : Box ι) (i : ι) :
    I.upper i - I.lower i ≤ boxWidthBound I := by
  classical
  exact Finset.single_le_sum (fun j _ => (sub_pos.mpr (I.lower_lt_upper j)).le)
    (Finset.mem_univ i)

theorem dyadicBoxPartition_dist_upper_le (I : Box ι) (k : ℕ) (J : Box ι)
    (hJ : J ∈ dyadicBoxPartition I k) (x : ι → ℝ) (hx : x ∈ J) :
    dist x J.upper ≤ boxWidthBound I * (1 / 2 : ℝ) ^ k := by
  have hp : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  apply (dist_pi_le_iff (mul_nonneg (boxWidthBound_nonneg I) hp)).mpr
  intro i
  have hi := hx i
  calc
    dist (x i) (J.upper i) = J.upper i - x i := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hi.2)]
      ring
    _ ≤ J.upper i - J.lower i := by linarith [hi.1]
    _ = (I.upper i - I.lower i) * (1 / 2 : ℝ) ^ k :=
      dyadicBoxPartition_width I k J hJ i
    _ ≤ boxWidthBound I * (1 / 2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (box_width_le_bound I i) hp

theorem box_frontier_volume_zero (I : Box ι) :
    (volume : Measure (ι → ℝ)) (frontier (I : Set (ι → ℝ))) = 0 := by
  have hopen : IsOpen (Box.Ioo I) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : frontier (I : Set (ι → ℝ)) ⊆ Box.Icc I \ Box.Ioo I := by
    intro x hx
    exact ⟨closure_minimal Box.coe_subset_Icc I.isCompact_Icc.isClosed hx.1,
      fun hi => hx.2 (hopen.subset_interior_iff.mpr I.Ioo_subset_coe hi)⟩
  have heq : (Box.Icc I \ Box.Ioo I) =ᵐ[volume] (∅ : Set (ι → ℝ)) := by
    filter_upwards [I.Ioo_ae_eq_Icc] with x hx
    apply propext
    change (x ∈ Box.Icc I ∧ x ∉ Box.Ioo I) ↔ False
    have hx' : x ∈ Box.Ioo I ↔ x ∈ Box.Icc I := iff_of_eq hx
    tauto
  exact measure_mono_null hsub ((measure_congr heq).trans measure_empty)

theorem dyadic_box_scale_tendsto_zero :
    Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem dyadicBoxCell_measurable (I : Box ι) (k : ℕ) (J : DyadicBoxIndex I k) :
    MeasurableSet (dyadicBoxCell I k J) := J.val.measurableSet_coe

theorem dyadicBoxCell_disjoint (I : Box ι) (k : ℕ) :
    Pairwise (Disjoint on dyadicBoxCell I k) := by
  intro J P hne
  exact (dyadicBoxPartition I k).pairwiseDisjoint J.property P.property
    (fun h => hne (Subtype.ext h))

theorem dyadicBoxCell_cover (I : Box ι) (k : ℕ) :
    (⋃ J : DyadicBoxIndex I k, dyadicBoxCell I k J) = (I : Set (ι → ℝ)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨J, hx⟩ := mem_iUnion.mp hx
    exact (dyadicBoxPartition I k).le_of_mem J.property hx
  · intro hx
    obtain ⟨J, hJ, hxJ⟩ := dyadicBoxPartition_isPartition I k x hx
    exact mem_iUnion.mpr ⟨⟨J, hJ⟩, hxJ⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]
  [OpensMeasurableSpace X] [Nonempty X]

theorem finiteMeasure_cell_mass_tendsto (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (s : Set X) (hboundary : (ν : Measure X) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure X).real s) atTop (𝓝 ((ν : Measure X).real s)) := by
  have hn : Tendsto (fun j => (μ j).normalize) atTop (𝓝 ν.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hweak hν
  have hb : ν.normalize (frontier s) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν]
    rw [(ν.null_iff_toMeasure_null _).mpr hboundary, mul_zero]
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hb
  have hmass : Tendsto (fun j => (μ j) s) atTop (𝓝 (ν s)) := by
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using! hweak.mass.mul hp
  exact NNReal.continuous_coe.continuousAt.tendsto.comp hmass

omit [OpensMeasurableSpace X] [Nonempty X] in
theorem null_frontier_inter (ν : Measure X) (s t : Set X)
    (hs : ν (frontier s) = 0) (ht : ν (frontier t) = 0) :
    ν (frontier (s ∩ t)) = 0 :=
  measure_mono_null (frontier_inter_subset s t)
    (measure_union_null (measure_mono_null inter_subset_left hs)
      (measure_mono_null inter_subset_right ht))

theorem finiteMeasure_cell_intersection_mass_tendsto
    (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (s t : Set X) (hs : (ν : Measure X) (frontier s) = 0)
    (ht : (ν : Measure X) (frontier t) = 0) :
    Tendsto (fun j => (μ j : Measure X).real (s ∩ t)) atTop
      (𝓝 ((ν : Measure X).real (s ∩ t))) :=
  finiteMeasure_cell_mass_tendsto μ ν hweak hν (s ∩ t) (null_frontier_inter _ s t hs ht)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measures on parametrized boxes

Restricting Lebesgue measure to a finite box and pushing it forward through a
parametrization defines the associated box-plane measure. Its finite-measure
packaging allows these parametrized cells to enter weak-convergence arguments.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

theorem boxPlaneMeasure_univ (I : Box ι) (e : (ι → ℝ) → X) (he : Measurable e) :
    boxPlaneMeasure I e univ = (volume : Measure (ι → ℝ)) I := by
  rw [boxPlaneMeasure, Measure.map_apply he MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

theorem boxPlaneFiniteMeasure_ne_zero (I : Box ι) (e : (ι → ℝ) → X)
    (he : Measurable e) : boxPlaneFiniteMeasure I e ≠ 0 := by
  intro h
  have heq : boxPlaneMeasure I e = 0 :=
    congrArg (fun ν : FiniteMeasure X => (ν : Measure X)) h
  have hv : (volume : Measure (ι → ℝ)).real I = 0 := by
    rw [Measure.real, ← boxPlaneMeasure_univ I e he, heq]
    simp
  exact (box_volume_real_pos I).ne' hv

theorem boxPlaneMeasure_preimage (I : Box ι) (e : (ι → ℝ) → X) (π : X → ι → ℝ)
    (he : Measurable e) (hπ : Measurable π) (hleft : LeftInverse π e)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    boxPlaneMeasure I e (π ⁻¹' s) = (volume : Measure (ι → ℝ)) (s ∩ I) := by
  rw [boxPlaneMeasure, Measure.map_apply he (hs.preimage hπ)]
  have hp : e ⁻¹' (π ⁻¹' s) = s := by
    ext x
    simp only [mem_preimage, hleft x]
  rw [hp, Measure.restrict_apply hs]

theorem dyadicProjectionCell_measurable (I : Box ι) (π : X → ι → ℝ)
    (hπ : Measurable π) (k : ℕ) (J : DyadicBoxIndex I k) :
    MeasurableSet (dyadicProjectionCell I π k J) :=
  (dyadicBoxCell_measurable I k J).preimage hπ

omit [MeasurableSpace X] in
theorem dyadicProjectionCell_disjoint (I : Box ι) (π : X → ι → ℝ) (k : ℕ) :
    Pairwise (Disjoint on dyadicProjectionCell I π k) := by
  intro J P hne
  apply Set.disjoint_left.mpr
  intro x hxJ hxP
  exact Set.disjoint_left.mp (dyadicBoxCell_disjoint I k hne) hxJ hxP

omit [MeasurableSpace X] in
theorem dyadicProjectionCell_cover (I : Box ι) (π : X → ι → ℝ) (k : ℕ) :
    (⋃ J : DyadicBoxIndex I k, dyadicProjectionCell I π k J) = π ⁻¹' (I : Set (ι → ℝ)) := by
  simp only [dyadicProjectionCell, ← preimage_iUnion, dyadicBoxCell_cover]

theorem dyadicProjectionCell_mass (I : Box ι) (e : (ι → ℝ) → X) (π : X → ι → ℝ)
    (he : Measurable e) (hπ : Measurable π) (hleft : LeftInverse π e)
    (k : ℕ) (J : DyadicBoxIndex I k) :
    (boxPlaneMeasure I e).real (dyadicProjectionCell I π k J) =
      (volume : Measure (ι → ℝ)).real I * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι := by
  have hJI : (J.val : Set (ι → ℝ)) ⊆ I :=
    (dyadicBoxPartition I k).le_of_mem J.property
  rw [Measure.real, dyadicProjectionCell, boxPlaneMeasure_preimage I e π he hπ hleft
    _ (dyadicBoxCell_measurable I k J)]
  change ((volume : Measure (ι → ℝ)) ((J.val : Set (ι → ℝ)) ∩ I)).toReal = _
  rw [inter_eq_left.mpr hJI]
  exact dyadicBoxPartition_volume I k J.val J.property

theorem boxPlaneMeasure_ae_coordinates (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Measurable e) (hπ : Measurable π) (hleft : LeftInverse π e) :
    ∀ᵐ x ∂boxPlaneMeasure I e, π x ∈ I := by
  apply (ae_map_iff he.aemeasurable (I.measurableSet_coe.preimage hπ)).mpr
  filter_upwards [self_mem_ae_restrict I.measurableSet_coe] with x hx
  simpa only [hleft x] using! hx

theorem dyadicProjectionCell_cover_ae (I : Box ι) (π : X → ι → ℝ)
    (μ : Measure X) (hcoords : ∀ᵐ x ∂μ, π x ∈ I) (k : ℕ) :
    ∀ᵐ x ∂μ, x ∈ ⋃ J : DyadicBoxIndex I k, dyadicProjectionCell I π k J := by
  rw [dyadicProjectionCell_cover]
  exact hcoords

variable [MetricSpace X] [BorelSpace X]

theorem dyadicProjectionCell_null_frontier (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (k : ℕ) (J : DyadicBoxIndex I k) :
    boxPlaneMeasure I e (frontier (dyadicProjectionCell I π k J)) = 0 := by
  apply measure_mono_null (hπ.frontier_preimage_subset (dyadicBoxCell I k J))
  rw [boxPlaneMeasure_preimage I e π he.measurable hπ.measurable hleft
    _ isClosed_frontier.measurableSet]
  exact measure_mono_null inter_subset_left (box_frontier_volume_zero J.val)

omit [MeasurableSpace X] [BorelSpace X] in

theorem dyadicProjectionCell_dist_reference (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (K : ℝ≥0) (he : LipschitzWith K e)
    (k : ℕ) (J : DyadicBoxIndex I k) (x : X)
    (hx : x ∈ dyadicProjectionCell I π k J)
    (hheight : dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k) :
    dist x (e J.val.upper) ≤ (1 + (K : ℝ) * boxWidthBound I) * (1 / 2 : ℝ) ^ k := by
  have hp := dyadicBoxPartition_dist_upper_le I k J.val J.property (π x) hx
  calc
    dist x (e J.val.upper) ≤ dist x (e (π x)) + dist (e (π x)) (e J.val.upper) :=
      dist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ k + (K : ℝ) * (boxWidthBound I * (1 / 2 : ℝ) ^ k) :=
      add_le_add hheight ((he.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left hp K.coe_nonneg))
    _ = _ := by ring

theorem boxPlaneMeasure_ae_section (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e) :
    ∀ᵐ x ∂boxPlaneMeasure I e, e (π x) = x := by
  apply (ae_map_iff he.measurable.aemeasurable
    (isClosed_eq (he.comp hπ) continuous_id).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun x => congrArg e (hleft x))

omit [BorelSpace X] in
theorem dyadicProjectionCell_ae_dist_reference (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (hπ : Measurable π) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : Measure X) (k : ℕ)
    (hheight : ∀ᵐ x ∂μ, dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (J : DyadicBoxIndex I k) :
    ∀ᵐ x ∂μ.restrict (dyadicProjectionCell I π k J),
      dist x (e J.val.upper) ≤ (1 + (K : ℝ) * boxWidthBound I) * (1 / 2 : ℝ) ^ k := by
  filter_upwards [ae_restrict_of_ae hheight,
    self_mem_ae_restrict (dyadicProjectionCell_measurable I π hπ k J)] with x hxh hxc
  exact dyadicProjectionCell_dist_reference I e π K he k J x hxc hxh

omit [BorelSpace X] in
theorem dyadicProjectionCell_ae_diameter (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (hπ : Measurable π) (K : ℝ≥0) (he : LipschitzWith K e)
    (μ : Measure X) (k : ℕ)
    (hheight : ∀ᵐ x ∂μ, dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (J : DyadicBoxIndex I k) :
    ∀ᵐ x ∂μ.restrict (dyadicProjectionCell I π k J),
      ∀ᵐ y ∂μ.restrict (dyadicProjectionCell I π k J),
        dist x y ≤ (2 * (1 + (K : ℝ) * boxWidthBound I)) * (1 / 2 : ℝ) ^ k := by
  have href := dyadicProjectionCell_ae_dist_reference I e π hπ K he μ k hheight J
  filter_upwards [href] with x hx
  filter_upwards [href] with y hy
  have ht := dist_triangle x (e J.val.upper) y
  rw [dist_comm (e J.val.upper) y] at ht
  linarith

variable [Nonempty X]

theorem dyadicProjectionCell_mass_tendsto (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (μ : ℕ → FiniteMeasure X) (hweak : Tendsto μ atTop (𝓝 (boxPlaneFiniteMeasure I e)))
    (k : ℕ) (J : DyadicBoxIndex I k) :
    Tendsto (fun j => (μ j : Measure X).real (dyadicProjectionCell I π k J)) atTop
      (𝓝 ((volume : Measure (ι → ℝ)).real I * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι)) := by
  have h := finiteMeasure_cell_mass_tendsto μ (boxPlaneFiniteMeasure I e) hweak
    (boxPlaneFiniteMeasure_ne_zero I e he.measurable) (dyadicProjectionCell I π k J)
    (dyadicProjectionCell_null_frontier I e π he hπ hleft k J)
  change Tendsto _ _ (𝓝 ((boxPlaneMeasure I e).real (dyadicProjectionCell I π k J))) at h
  rwa [dyadicProjectionCell_mass I e π he.measurable hπ.measurable hleft k J] at h

theorem dyadicProjectionCell_eventual_mass_lower (I : Box ι) (e : (ι → ℝ) → X)
    (π : X → ι → ℝ) (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (μ : ℕ → FiniteMeasure X) (hweak : Tendsto μ atTop (𝓝 (boxPlaneFiniteMeasure I e)))
    (k : ℕ) :
    ∀ᶠ j in atTop, ∀ J : DyadicBoxIndex I k,
      ((volume : Measure (ι → ℝ)).real I / 2) * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι ≤
        (μ j : Measure X).real (dyadicProjectionCell I π k J) := by
  apply Filter.eventually_all.mpr
  intro J
  have hpos : 0 < (volume : Measure (ι → ℝ)).real I *
      ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι :=
    mul_pos (box_volume_real_pos I) (by positivity)
  have h := (dyadicProjectionCell_mass_tendsto I e π he hπ hleft μ hweak k J).eventually
    (lt_mem_nhds (show ((volume : Measure (ι → ℝ)).real I / 2) *
      ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι <
      (volume : Measure (ι → ℝ)).real I * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι by
        nlinarith))
  exact h.mono (fun _ hj => hj.le)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneBoxGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function
open scoped NNReal ENNReal

theorem GlobalUpperGrowth.mono_constant {d n : ℕ} {C D : ℝ}
    {μ : Measure (Ambient d)} (h : GlobalUpperGrowth n C μ) (hCD : C ≤ D) :
    GlobalUpperGrowth n D μ := by
  refine ⟨h.1.trans hCD, ?_⟩
  intro x r hr
  exact (h.2 x r hr).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (pow_nonneg hr.le n)))

theorem boxPlaneMeasure_upper_growth {ι : Type*} [Fintype ι] {d : ℕ}
    (I : Box ι) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) :
    GlobalUpperGrowth (Fintype.card ι) ((2 * (Q : ℝ)) ^ Fintype.card ι)
      (boxPlaneMeasure I e) := by
  refine ⟨by positivity, ?_⟩
  intro x r hr
  rw [boxPlaneMeasure, Measure.map_apply he measurableSet_ball,
    Measure.restrict_apply (measurableSet_ball.preimage he)]
  calc
    volume ((e ⁻¹' ball x r) ∩ (I : Set (ι → ℝ))) ≤
        volume (closedBall (π x) ((Q : ℝ) * r)) := by
      apply measure_mono
      intro u hu
      apply mem_closedBall.mpr
      have hu' : dist (e u) x < r := hu.1
      calc
        dist u (π x) = dist (π (e u)) (π x) := by rw [hleft u]
        _ ≤ (Q : ℝ) * dist (e u) x := hπ.dist_le_mul _ _
        _ ≤ (Q : ℝ) * r := mul_le_mul_of_nonneg_left hu'.le Q.coe_nonneg
    _ = ENNReal.ofReal ((2 * ((Q : ℝ) * r)) ^ Fintype.card ι) :=
      Real.volume_pi_closedBall (π x) (mul_nonneg Q.coe_nonneg hr.le)
    _ = ENNReal.ofReal ((2 * (Q : ℝ)) ^ Fintype.card ι * r ^ Fintype.card ι) := by
      congr 1
      rw [← mul_assoc, mul_pow]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_OpenPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Open projection boxes and coordinate-plane measures

Pulling back open boxes along continuous coordinates gives open subsets of the
ambient space. Coordinate-plane measures satisfy upper growth bounds, which
in turn imply finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem openProjectionBox_isOpen {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (I : Box ι) (π : X → ι → ℝ) (hπ : Continuous π) : IsOpen (openProjectionBox I π) :=
  (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).preimage hπ

theorem coordinatePlaneMeasure_upper_growth {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) :
    GlobalUpperGrowth (Fintype.card ι) ((2 * (Q : ℝ)) ^ Fintype.card ι)
      (coordinatePlaneMeasure e) := by
  refine ⟨by positivity, ?_⟩
  intro x r hr
  rw [coordinatePlaneMeasure, Measure.map_apply he measurableSet_ball]
  calc
    volume (e ⁻¹' ball x r) ≤ volume (closedBall (π x) ((Q : ℝ) * r)) := by
      apply measure_mono
      intro u hu
      apply mem_closedBall.mpr
      have hu' : dist (e u) x < r := hu
      calc
        dist u (π x) = dist (π (e u)) (π x) := by rw [hleft u]
        _ ≤ (Q : ℝ) * dist (e u) x := hπ.dist_le_mul _ _
        _ ≤ (Q : ℝ) * r := mul_le_mul_of_nonneg_left hu'.le Q.coe_nonneg
    _ = ENNReal.ofReal ((2 * ((Q : ℝ) * r)) ^ Fintype.card ι) :=
      Real.volume_pi_closedBall (π x) (mul_nonneg Q.coe_nonneg hr.le)
    _ = ENNReal.ofReal ((2 * (Q : ℝ)) ^ Fintype.card ι * r ^ Fintype.card ι) := by
      congr 1
      rw [← mul_assoc, mul_pow]

theorem GlobalUpperGrowth.finite_on_compacts {d n : ℕ} {C : ℝ}
    {μ : Measure (Ambient d)} (h : GlobalUpperGrowth n C μ) : IsFiniteMeasureOnCompacts μ := by
  let : IsLocallyFiniteMeasure μ := ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num),
    (h.2 x 1 (by norm_num)).trans_lt ENNReal.ofReal_lt_top⟩⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem coordinatePlaneMeasure_finite_on_compacts {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Measurable e) (Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) :
    IsFiniteMeasureOnCompacts (coordinatePlaneMeasure e) :=
  (coordinatePlaneMeasure_upper_growth e π he Q hπ hleft).finite_on_compacts

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BoundedPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exhaustionBox_dist_zero_le {ι : Type*} [Fintype ι] (H : ℕ) (u : ι → ℝ)
    (hu : u ∈ exhaustionBox ι H) : dist u 0 ≤ (H : ℝ) + 1 := by
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ H + 1)).mpr
  intro i
  have hi := hu i
  change -((H : ℝ) + 1) < u i ∧ u i ≤ (H : ℝ) + 1 at hi
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using! abs_le.mpr ⟨hi.1.le, hi.2⟩

theorem mem_exhaustionBox_Ioo_of_norm_lt {ι : Type*} [Fintype ι]
    (H : ℕ) (u : ι → ℝ) (hu : ‖u‖ < (H : ℝ) + 1) : u ∈ Box.Ioo (exhaustionBox ι H) := by
  intro i _
  change -((H : ℝ) + 1) < u i ∧ u i < (H : ℝ) + 1
  apply abs_lt.mp
  exact (show |u i| ≤ ‖u‖ by simpa only [Real.norm_eq_abs] using! norm_le_pi_norm u i).trans_lt hu

theorem exhaustionBox_image_mem_outerBall {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (K : ℝ≥0) (he : LipschitzWith K e)
    (H : ℕ) (u : ι → ℝ) (hu : u ∈ exhaustionBox ι H) :
    e u ∈ ball (e 0) (planeBoxOuterRadius K H) := by
  apply mem_ball.mpr
  have hdist := (he.dist_le_mul u 0).trans
    (mul_le_mul_of_nonneg_left (exhaustionBox_dist_zero_le H u hu) K.coe_nonneg)
  dsimp [planeBoxOuterRadius]
  nlinarith

theorem boundedProjectionRegion_isOpen {ι : Type*} [Fintype ι] {d : ℕ}
    (π : Ambient d → ι → ℝ) (hπ : Continuous π) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsOpen (boundedProjectionRegion π a K H) :=
  (openProjectionBox_isOpen (exhaustionBox ι H) π hπ).inter isOpen_ball

theorem boundedProjectionRegion_cover {ι : Type*} [Fintype ι] {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (x : Ambient d) :
    ∃ H : ℕ, x ∈ boundedProjectionRegion π a K H := by
  obtain ⟨H, hH⟩ := exists_nat_gt (max ‖π x‖ (dist x a))
  have hnorm : ‖π x‖ < (H : ℝ) + 1 := by linarith [le_max_left ‖π x‖ (dist x a)]
  have hdist : dist x a < (H : ℝ) + 1 := by linarith [le_max_right ‖π x‖ (dist x a)]
  refine ⟨H, mem_exhaustionBox_Ioo_of_norm_lt H (π x) hnorm, ?_⟩
  apply mem_ball.mpr
  exact hdist.trans_le (by unfold planeBoxOuterRadius; nlinarith [K.coe_nonneg])

theorem coordinatePlaneMeasure_restrict_boundedRegion {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    (coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H) =
      boxPlaneMeasure (exhaustionBox ι H) e := by
  have hpre : e ⁻¹' boundedProjectionRegion π (e 0) K H = Box.Ioo (exhaustionBox ι H) := by
    ext u
    change (π (e u) ∈ Box.Ioo (exhaustionBox ι H) ∧
      e u ∈ ball (e 0) (planeBoxOuterRadius K H)) ↔ u ∈ Box.Ioo (exhaustionBox ι H)
    rw [hleft u]
    exact ⟨And.left, fun hu => ⟨hu, exhaustionBox_image_mem_outerBall e K he H u
      ((exhaustionBox ι H).Ioo_subset_coe hu)⟩⟩
  rw [coordinatePlaneMeasure, Measure.restrict_map he.continuous.measurable
    (boundedProjectionRegion_isOpen π hπ (e 0) K H).measurableSet, hpre,
    Measure.restrict_congr_set ((exhaustionBox ι H).Ioo_ae_eq_Icc.trans
      (exhaustionBox ι H).coe_ae_eq_Icc.symm)]
  rfl

theorem boundedProjectionRegion_ae_coordinates {ι : Type*} [Fintype ι] {d : ℕ}
    (μ : Measure (Ambient d)) (π : Ambient d → ι → ℝ) (hπ : Continuous π)
    (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    ∀ᵐ x ∂μ.restrict (boundedProjectionRegion π a K H), π x ∈ exhaustionBox ι H := by
  filter_upwards [ae_restrict_mem (boundedProjectionRegion_isOpen π hπ a K H).measurableSet]
    with x hx
  exact (exhaustionBox ι H).Ioo_subset_coe hx.1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MomentRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem integral_squared_difference (μ : Measure X) (w v : X → ℝ)
    (hww : Integrable (fun x => w x ^ 2) μ)
    (hwv : Integrable (fun x => w x * v x) μ)
    (hvv : Integrable (fun x => v x ^ 2) μ) :
    (∫ x, (w x - v x) ^ 2 ∂μ) =
      (∫ x, w x ^ 2 ∂μ) - 2 * (∫ x, w x * v x ∂μ) + (∫ x, v x ^ 2 ∂μ) := by
  have h : (fun x => (w x - v x) ^ 2) =
      (fun x => w x ^ 2 - 2 * (w x * v x) + v x ^ 2) := by
    funext x
    ring
  have hadd := integral_add (hww.sub (hwv.const_mul 2)) hvv
  have hsub := integral_sub hww (hwv.const_mul 2)
  simp only [Pi.sub_apply] at hadd hsub
  rw [h, hadd, hsub, integral_const_mul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem integral_sq_sub_const (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (a : ℝ) :
    (∫ x, (w x - a) ^ 2 ∂μ) = (∫ x, w x ^ 2 ∂μ) -
      2 * (∫ x, w x ∂μ) * a + μ.real univ * a ^ 2 := by
  have h := integral_squared_difference μ w (fun _ => a) hw.integrable_sq
    ((hw.integrable (by norm_num)).mul_const a) (integrable_const _)
  simpa only [integral_mul_const, integral_const, smul_eq_mul, mul_assoc] using! h

theorem pairwise_square_integrable_right (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (x : X) :
    Integrable (fun y => (w x - w y) ^ 2) μ :=
  ((memLp_const (w x)).sub hw).integrable_sq

theorem inner_pairwise_square_formula (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (x : X) :
    (∫ y, (w x - w y) ^ 2 ∂μ) = (∫ y, w y ^ 2 ∂μ) -
      2 * (∫ y, w y ∂μ) * w x + μ.real univ * w x ^ 2 := by
  have heq : (fun y => (w x - w y) ^ 2) = (fun y => (w y - w x) ^ 2) := by
    funext y
    ring
  rw [heq]
  exact integral_sq_sub_const μ w hw (w x)

theorem iterated_pairwise_square_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) :
    Integrable (fun x => ∫ y, (w x - w y) ^ 2 ∂μ) μ := by
  simp_rw [inner_pairwise_square_formula μ w hw]
  exact ((integrable_const _).sub ((hw.integrable (by norm_num)).const_mul _)).add
    (hw.integrable_sq.const_mul _)

theorem iterated_pairwise_square_formula (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) :
    (∫ x, ∫ y, (w x - w y) ^ 2 ∂μ ∂μ) =
      2 * μ.real univ * (∫ x, w x ^ 2 ∂μ) - 2 * (∫ x, w x ∂μ) ^ 2 := by
  simp_rw [inner_pairwise_square_formula μ w hw]
  have hsub := integral_sub (integrable_const (∫ y, w y ^ 2 ∂μ))
    ((hw.integrable (by norm_num)).const_mul (2 * (∫ y, w y ∂μ)))
  have hadd := integral_add
    ((integrable_const (∫ y, w y ^ 2 ∂μ)).sub
      ((hw.integrable (by norm_num)).const_mul (2 * (∫ y, w y ∂μ))))
    (hw.integrable_sq.const_mul (μ.real univ))
  simp only [Pi.sub_apply] at hadd
  rw [hadd, hsub, integral_const_mul, integral_const_mul, integral_const]
  simp only [smul_eq_mul]
  ring

theorem cell_variance_eq_half_pairwise (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : μ.real univ ≠ 0) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) =
      (∫ x, ∫ y, (w x - w y) ^ 2 ∂μ ∂μ) / (2 * μ.real univ) := by
  rw [integral_sq_sub_const μ w hw, iterated_pairwise_square_formula μ w hw]
  unfold cellMean
  field_simp [hμ]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

variable [MetricSpace X]

omit [MeasurableSpace X] in
theorem fractionalPairEnergy_nonneg (m : ℕ) (w : X → ℝ) (x y : X) :
    0 ≤ fractionalPairEnergy m w x y := by
  unfold fractionalPairEnergy
  positivity

omit [MeasurableSpace X] in
theorem square_le_radius_mul_fractional_energy (m : ℕ) (w : X → ℝ)
    (x y : X) (r : ℝ) (hxy : dist x y ≤ r) :
    (w x - w y) ^ 2 ≤ r ^ (m + 1) * fractionalPairEnergy m w x y := by
  by_cases heq : x = y
  · simp [heq, fractionalPairEnergy]
  have hd : 0 < dist x y := dist_pos.mpr heq
  have hp := pow_le_pow_left₀ (dist_nonneg (x := x) (y := y)) hxy (m + 1)
  unfold fractionalPairEnergy
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hd (m + 1))).2
  calc
    _ = dist x y ^ (m + 1) * (w x - w y) ^ 2 := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (sq_nonneg _)

theorem radius_mass_coefficient_le (m : ℕ) (a h c M : ℝ)
    (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c) (hM : c * h ^ m ≤ M) :
    (a * h) ^ (m + 1) / (2 * M) ≤ a ^ (m + 1) / (2 * c) * h := by
  calc
    _ ≤ (a * h) ^ (m + 1) / (2 * (c * h ^ m)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = _ := by
      rw [mul_pow, pow_succ h m]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_RestrictedCellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem cell_variance_le_energy_ae (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : 0 < μ.real univ)
    (E : X → X → ℝ) (C : ℝ)
    (hE : ∀ᵐ x ∂μ, Integrable (E x) μ)
    (hEE : Integrable (fun x => ∫ y, E x y ∂μ) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, (w x - w y) ^ 2 ≤ C * E x y) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      C / (2 * μ.real univ) * (∫ x, ∫ y, E x y ∂μ ∂μ) := by
  have hp : (∫ x, ∫ y, (w x - w y) ^ 2 ∂μ ∂μ) ≤
      C * (∫ x, ∫ y, E x y ∂μ ∂μ) := by
    calc
      _ ≤ ∫ x, C * (∫ y, E x y ∂μ) ∂μ := by
        apply integral_mono_ae (iterated_pairwise_square_integrable μ w hw) (hEE.const_mul C)
        filter_upwards [hE, hbound] with x hx hb
        calc
          _ ≤ ∫ y, C * E x y ∂μ :=
            integral_mono_ae (pairwise_square_integrable_right μ w hw x)
              (hx.const_mul C) hb
          _ = _ := integral_const_mul C (E x)
      _ = _ := integral_const_mul C _
  rw [cell_variance_eq_half_pairwise μ w hw hμ.ne']
  calc
    _ ≤ (C * (∫ x, ∫ y, E x y ∂μ ∂μ)) / (2 * μ.real univ) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PartitionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

theorem partitionMean_eq_cell (μ : Measure X) (s : ι → Set X) (w : X → ℝ)
    (hd : Pairwise (Disjoint on s)) (i : ι) (x : X) (hx : x ∈ s i) :
    partitionMean μ s w x = cellMean (μ.restrict (s i)) w := by
  classical
  unfold partitionMean
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    have hxj : x ∉ s j := fun hj => (Set.disjoint_left.mp (hd hji)) hj hx
    exact indicator_of_notMem hxj _
  · simp

theorem partition_error_eq_sum (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (w : X → ℝ) (hw : MemLp w 2 μ) :
    (∫ x in ⋃ i, s i, (w x - partitionMean μ s w x) ^ 2 ∂μ) =
      ∑ i, ∫ x in s i, (w x - cellMean (μ.restrict (s i)) w) ^ 2 ∂μ := by
  have heq (i : ι) : (fun x => (w x - partitionMean μ s w x) ^ 2) =ᵐ[μ.restrict (s i)]
      (fun x => (w x - cellMean (μ.restrict (s i)) w) ^ 2) := by
    filter_upwards [ae_restrict_mem (hs i)] with x hx
    rw [partitionMean_eq_cell μ s w hd i x hx]
  have hi (i : ι) : IntegrableOn (fun x => (w x - partitionMean μ s w x) ^ 2) (s i) μ :=
    (integrable_congr (heq i)).mpr
      (((hw.restrict (s i)).sub (memLp_const _)).integrable_sq)
  rw [integral_iUnion_fintype hs hd hi]
  exact Finset.sum_congr rfl fun i _ => integral_congr_ae (heq i)

theorem iterated_cell_energy_eq_product (μ : Measure X) [IsFiniteMeasure μ]
    (s : Set X) (E : X × X → ℝ) (hE : Integrable E (μ.prod μ)) :
    (∫ x in s, ∫ y in s, E (x, y) ∂μ ∂μ) = ∫ p in s ×ˢ s, E p ∂μ.prod μ := by
  have hi : Integrable E ((μ.restrict s).prod (μ.restrict s)) := by
    rw [Measure.prod_restrict]
    exact hE.restrict
  rw [← Measure.prod_restrict]
  exact (integral_prod E hi).symm

theorem sum_cell_energy_le (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (E : X × X → ℝ)
    (hE : Integrable E (μ.prod μ)) (hEpos : ∀ p, 0 ≤ E p) :
    (∑ i, ∫ x in s i, ∫ y in s i, E (x, y) ∂μ ∂μ) ≤ ∫ p, E p ∂μ.prod μ := by
  have hprod : Pairwise (Disjoint on (fun i => s i ×ˢ s i)) :=
    fun i j hij => Set.disjoint_prod.mpr (Or.inl (hd hij))
  calc
    _ = ∑ i, ∫ p in s i ×ˢ s i, E p ∂μ.prod μ :=
      Finset.sum_congr rfl fun i _ => iterated_cell_energy_eq_product μ (s i) E hE
    _ = ∫ p in ⋃ i, s i ×ˢ s i, E p ∂μ.prod μ :=
      (integral_iUnion_fintype (fun i => (hs i).prod (hs i)) hprod (fun i => hE.restrict)).symm
    _ ≤ _ := setIntegral_le_integral hE (Filter.Eventually.of_forall hEpos)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellMeanBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem cellMean_mul_mass (μ : Measure X) (w : X → ℝ) (hμ : μ.real univ ≠ 0) :
    μ.real univ * cellMean μ w = ∫ x, w x ∂μ := by
  unfold cellMean
  field_simp

theorem cellMean_sq_mass_le (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ) (hμ : μ.real univ ≠ 0) :
    μ.real univ * (cellMean μ w) ^ 2 ≤ ∫ x, w x ^ 2 ∂μ := by
  have hv := integral_sq_sub_const μ w hw (cellMean μ w)
  rw [← cellMean_mul_mass μ w hμ] at hv
  have hpos : 0 ≤ ∫ x, (w x - cellMean μ w) ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  nlinarith

theorem cellMean_abs_bound (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : MemLp w 2 μ)
    (c B : ℝ) (hc : 0 < c) (hmass : c ≤ μ.real univ)
    (hB : (∫ x, w x ^ 2 ∂μ) ≤ B) :
    |cellMean μ w| ≤ B / c + 1 := by
  have hμ : 0 < μ.real univ := lt_of_lt_of_le hc hmass
  have hs : (cellMean μ w) ^ 2 ≤ B / c := by
    apply (le_div_iff₀ hc).2
    calc
      _ = c * (cellMean μ w) ^ 2 := mul_comm _ _
      _ ≤ μ.real univ * (cellMean μ w) ^ 2 :=
        mul_le_mul_of_nonneg_right hmass (sq_nonneg _)
      _ ≤ _ := (cellMean_sq_mass_le μ w hw hμ.ne').trans hB
  have hsmall : |cellMean μ w| ≤ (cellMean μ w) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|cellMean μ w| - 1), sq_abs (cellMean μ w), sq_nonneg (cellMean μ w)]
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CellMeanSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology

theorem bounded_of_eventually_abs_le (a : ℕ → ℝ) (B : ℝ)
    (h : ∀ᶠ j in atTop, |a j| ≤ B) : ∃ C : ℝ, ∀ j, |a j| ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max B (∑ j ∈ Finset.range N, |a j|), ?_⟩
  intro j
  by_cases hj : N ≤ j
  · exact (hN j hj).trans (le_max_left _ _)
  · exact (Finset.single_le_sum (fun i _ => abs_nonneg (a i))
      (Finset.mem_range.mpr (lt_of_not_ge hj))).trans (le_max_right _ _)

theorem exists_common_subsequence_of_eventual_bounds {ι : Type*} [Countable ι]
    (a : ℕ → ι → ℝ) (h : ∀ i, ∃ B : ℝ, ∀ᶠ j in atTop, |a j i| ≤ B) :
    ∃ b : ι → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun j => a (φ j) i) atTop (𝓝 (b i)) := by
  classical
  have hb : ∀ i, ∃ B : ℝ, ∀ j, |a j i| ≤ B := by
    intro i
    obtain ⟨B, hB⟩ := h i
    exact bounded_of_eventually_abs_le (fun j => a j i) B hB
  choose B hB using hb
  have hc : IsCompact {b : ι → ℝ | ∀ i, b i ∈ Icc (-B i) (B i)} :=
    isCompact_pi_infinite (fun i => isCompact_Icc)
  obtain ⟨b, _, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (fun j i => abs_le.mp (hB i j))
  exact ⟨b, φ, hφ, fun i => (continuous_apply i).tendsto b |>.comp hlim⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteStepMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Moments of finite-step functions

Finite sums of cell indicators reduce first and second moments to weighted cell masses.
For disjoint cells, convergence of the coefficients and masses gives convergence of the
second moments and vanishing squared approximation error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

omit [MeasurableSpace X] in
theorem finiteStep_eq_cell (s : ι → Set X) (a : ι → ℝ)
    (hd : Pairwise (Disjoint on s)) (i : ι) (x : X) (hx : x ∈ s i) :
    finiteStep s a x = a i := by
  classical
  unfold finiteStep
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    have hxj : x ∉ s j := fun hj => (Set.disjoint_left.mp (hd hji)) hj hx
    exact indicator_of_notMem hxj _
  · simp

theorem partitionMean_eq_finiteStep (μ : Measure X) (s : ι → Set X) (w : X → ℝ) :
    partitionMean μ s w = finiteStep s (fun i => cellMean (μ.restrict (s i)) w) := rfl

omit [MeasurableSpace X] in
theorem finiteStep_sq (s : ι → Set X) (a : ι → ℝ)
    (hd : Pairwise (Disjoint on s)) :
    (fun x => finiteStep s a x ^ 2) = finiteStep s (fun i => a i ^ 2) := by
  classical
  funext x
  by_cases hx : ∃ i, x ∈ s i
  · obtain ⟨i, hi⟩ := hx
    rw [finiteStep_eq_cell s a hd i x hi, finiteStep_eq_cell s _ hd i x hi]
  · have hi : ∀ i, x ∉ s i := fun i h => hx ⟨i, h⟩
    simp [finiteStep, hi]

omit [MeasurableSpace X] in
theorem finiteStep_sub (s : ι → Set X) (a b : ι → ℝ) :
    finiteStep s a - finiteStep s b = finiteStep s (fun i => a i - b i) := by
  classical
  funext x
  change (∑ i, (s i).indicator (fun _ => a i) x) -
    (∑ i, (s i).indicator (fun _ => b i) x) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ s i <;> simp [hx]

theorem integral_finiteStep (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) (a : ι → ℝ) :
    (∫ x, finiteStep s a x ∂μ) = ∑ i, μ.real (s i) * a i := by
  classical
  unfold finiteStep
  rw [integral_finsetSum _ (fun i _ => (integrable_const (a i)).indicator (hs i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hs i), setIntegral_const, smul_eq_mul]

theorem integral_finiteStep_sq (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (a : ι → ℝ) :
    (∫ x, finiteStep s a x ^ 2 ∂μ) = ∑ i, μ.real (s i) * a i ^ 2 := by
  rw [finiteStep_sq s a hd]
  exact integral_finiteStep μ s hs _

theorem integral_finiteStep_sub_sq (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (a b : ι → ℝ) :
    (∫ x, (finiteStep s a x - finiteStep s b x) ^ 2 ∂μ) =
      ∑ i, μ.real (s i) * (a i - b i) ^ 2 := by
  have heq : (fun x => finiteStep s a x - finiteStep s b x) =
      finiteStep s (fun i => a i - b i) := finiteStep_sub s a b
  simp_rw [congrFun heq]
  exact integral_finiteStep_sq μ s hs hd _

theorem finiteStep_squared_error_tendsto_zero (μ : ℕ → Measure X)
    [∀ j, IsFiniteMeasure (μ j)] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (a : ℕ → ι → ℝ) (b M : ι → ℝ)
    (ha : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 (b i)))
    (hm : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (M i))) :
    Tendsto (fun j => ∫ x, (finiteStep s (a j) x - finiteStep s b x) ^ 2 ∂μ j)
      atTop (𝓝 0) := by
  simp_rw [integral_finiteStep_sub_sq _ s hs hd]
  have h := tendsto_finsetSum Finset.univ
    (fun i _ => (hm i).mul (((ha i).sub (tendsto_const_nhds (x := b i))).pow 2))
  simpa only [sub_self, zero_pow two_ne_zero, mul_zero, Finset.sum_const_zero] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteStepLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-step functions in L²

Finite-step functions on finite measures belong to L². Products are represented on
intersections of cells, expressing squared distances through cell masses and mixed moments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]

omit [MeasurableSpace X] in
theorem finiteStep_mul (s : ι → Set X) (t : κ → Set X)
    (a : ι → ℝ) (b : κ → ℝ) :
    finiteStep s a * finiteStep t b =
      finiteStep (fun p : ι × κ => s p.1 ∩ t p.2) (fun p => a p.1 * b p.2) := by
  classical
  funext x
  simp only [Pi.mul_apply, finiteStep, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : x ∈ s i <;> by_cases hy : x ∈ t j <;> simp [hx, hy]

theorem integral_finiteStep_mul (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (t : κ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ j, MeasurableSet (t j))
    (a : ι → ℝ) (b : κ → ℝ) :
    (∫ x, finiteStep s a x * finiteStep t b x ∂μ) =
      ∑ i, ∑ j, μ.real (s i ∩ t j) * (a i * b j) := by
  change (∫ x, (finiteStep s a * finiteStep t b) x ∂μ) = _
  rw [finiteStep_mul s t a b]
  rw [integral_finiteStep μ (fun p : ι × κ => s p.1 ∩ t p.2)
    (fun p => (hs p.1).inter (ht p.2))]
  exact Fintype.sum_prod_type _

theorem toLp_norm_sq_eq_integral (μ : Measure X) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem toLp_dist_sq_eq_integral (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    dist (hf.toLp f) (hg.toLp g) ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [dist_eq_norm]
  have heq : hf.toLp f - hg.toLp g = (hf.sub hg).toLp (f - g) := by
    exact (MemLp.toLp_sub hf hg).symm
  rw [heq, toLp_norm_sq_eq_integral]
  rfl

theorem finiteStep_cross_distance_tendsto (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (s : ι → Set X) (t : κ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ i, MeasurableSet (t i))
    (hds : Pairwise (Disjoint on s)) (hdt : Pairwise (Disjoint on t))
    (a : ι → ℝ) (b : κ → ℝ)
    (hms : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (ν.real (s i))))
    (hmt : ∀ i, Tendsto (fun j => (μ j).real (t i)) atTop (𝓝 (ν.real (t i))))
    (hmst : ∀ i k, Tendsto (fun j => (μ j).real (s i ∩ t k))
      atTop (𝓝 (ν.real (s i ∩ t k)))) :
    Tendsto (fun j => ∫ x, (finiteStep s a x - finiteStep t b x) ^ 2 ∂μ j)
      atTop (𝓝 (∫ x, (finiteStep s a x - finiteStep t b x) ^ 2 ∂ν)) := by
  have hformula (ρ : Measure X) [IsFiniteMeasure ρ] :
      (∫ x, (finiteStep s a x - finiteStep t b x) ^ 2 ∂ρ) =
        (∑ i, ρ.real (s i) * a i ^ 2) -
        2 * (∑ i, ∑ k, ρ.real (s i ∩ t k) * (a i * b k)) +
        (∑ k, ρ.real (t k) * b k ^ 2) := by
    have hprod : MemLp (fun x => finiteStep s a x * finiteStep t b x) 1 ρ :=
      MeasureTheory.MemLp.mul (hφ := (finiteStep_memLp ρ s hs a)) (hf := (finiteStep_memLp ρ t ht b))
    rw [integral_squared_difference ρ _ _
      (finiteStep_memLp ρ s hs a).integrable_sq
      (memLp_one_iff_integrable.mp hprod)
      (finiteStep_memLp ρ t ht b).integrable_sq,
      integral_finiteStep_sq ρ s hs hds, integral_finiteStep_sq ρ t ht hdt,
      integral_finiteStep_mul ρ s t hs ht]
  simp_rw [hformula]
  exact ((tendsto_finsetSum _ fun i _ => (hms i).mul_const _).sub
    ((tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun k _ => (hmst i k).mul_const _).const_mul 2)).add
    (tendsto_finsetSum _ fun k _ => (hmt k).mul_const _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ApproximationComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem integral_sq_four_step_bound (μ : Measure X) (f p w q g : X → ℝ)
    (hf : MemLp f 2 μ) (hp : MemLp p 2 μ) (hw : MemLp w 2 μ)
    (hq : MemLp q 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, (f x - g x) ^ 2 ∂μ) ≤
      4 * ((∫ x, (f x - p x) ^ 2 ∂μ) + (∫ x, (p x - w x) ^ 2 ∂μ) +
        (∫ x, (w x - q x) ^ 2 ∂μ) + (∫ x, (q x - g x) ^ 2 ∂μ)) := by
  have hpoint (x : X) : (f x - g x) ^ 2 ≤
      4 * ((f x - p x) ^ 2 + (p x - w x) ^ 2 +
        (w x - q x) ^ 2 + (q x - g x) ^ 2) := by
    nlinarith [sq_nonneg ((f x - p x) - (p x - w x)),
      sq_nonneg ((w x - q x) - (q x - g x)),
      sq_nonneg ((f x - w x) - (w x - g x))]
  have hsum := (((hf.sub hp).integrable_sq.add (hp.sub hw).integrable_sq).add
    (hw.sub hq).integrable_sq).add (hq.sub hg).integrable_sq
  have h := integral_mono (hf.sub hg).integrable_sq (hsum.const_mul 4) hpoint
  have h1 := integral_add (hf.sub hp).integrable_sq (hp.sub hw).integrable_sq
  have h2 := integral_add ((hf.sub hp).integrable_sq.add (hp.sub hw).integrable_sq)
    (hw.sub hq).integrable_sq
  have h3 := integral_add
    (((hf.sub hp).integrable_sq.add (hp.sub hw).integrable_sq).add
      (hw.sub hq).integrable_sq) (hq.sub hg).integrable_sq
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
  simp only [integral_const_mul, Pi.add_apply, Pi.sub_apply] at h
  rw [h3, h2, h1] at h
  exact h

theorem fixed_pair_bound_of_approximations (μ : ℕ → Measure X) (ν : Measure X)
    (f g : X → ℝ) (p w q : ℕ → X → ℝ)
    (hf : ∀ j, MemLp f 2 (μ j)) (hg : ∀ j, MemLp g 2 (μ j))
    (hp : ∀ j, MemLp (p j) 2 (μ j)) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (hq : ∀ j, MemLp (q j) 2 (μ j)) (d e : ℝ)
    (hwp : ∀ᶠ j in atTop, (∫ x, (w j x - p j x) ^ 2 ∂μ j) ≤ d)
    (hwq : ∀ᶠ j in atTop, (∫ x, (w j x - q j x) ^ 2 ∂μ j) ≤ e)
    (hpf : Tendsto (fun j => ∫ x, (p j x - f x) ^ 2 ∂μ j) atTop (𝓝 0))
    (hqg : Tendsto (fun j => ∫ x, (q j x - g x) ^ 2 ∂μ j) atTop (𝓝 0))
    (hfg : Tendsto (fun j => ∫ x, (f x - g x) ^ 2 ∂μ j) atTop
      (𝓝 (∫ x, (f x - g x) ^ 2 ∂ν))) :
    (∫ x, (f x - g x) ^ 2 ∂ν) ≤ 4 * d + 4 * e := by
  have hlim : Tendsto (fun j => 4 *
      ((∫ x, (p j x - f x) ^ 2 ∂μ j) + d + e +
        (∫ x, (q j x - g x) ^ 2 ∂μ j))) atTop (𝓝 (4 * d + 4 * e)) := by
    simpa only [zero_add, add_zero, mul_add] using!
      (((hpf.add_const d).add_const e).add hqg).const_mul 4
  apply le_of_tendsto_of_tendsto hfg hlim
  filter_upwards [hwp, hwq] with j hjp hjq
  have h := integral_sq_four_step_bound (μ j) f (p j) (w j) (q j) g
    (hf j) (hp j) (hw j) (hq j) (hg j)
  have hfp : (fun x => (f x - p j x) ^ 2) = (fun x => (p j x - f x) ^ 2) := by
    funext x
    ring
  have hpw : (fun x => (p j x - w j x) ^ 2) = (fun x => (w j x - p j x) ^ 2) := by
    funext x
    ring
  rw [hfp, hpw] at h
  linarith

theorem exists_L2_limit_of_sq_distance_bound (ν : Measure X)
    (v : ℕ → Lp ℝ 2 ν) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ k l, dist (v k) (v l) ^ 2 ≤ 4 * δ k + 4 * δ l) :
    ∃ limit : Lp ℝ 2 ν, Tendsto v atTop (𝓝 limit) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hδ.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 / 8 by positivity)))
  refine ⟨N, fun k hk l hl => ?_⟩
  have hb := hbound k l
  have hk' := hN k hk
  have hl' := hN l hl
  nlinarith [dist_nonneg (x := v k) (y := v l)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedBoxBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null boundaries of coordinate boxes

The frontier of an open coordinate box lies in the difference between its
closed and open versions. Their almost-everywhere equality for volume shows
that this frontier has measure zero.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem box_Ioo_frontier_volume_zero {ι : Type*} [Fintype ι] (I : Box ι) :
    (volume : Measure (ι → ℝ)) (frontier (Box.Ioo I)) = 0 := by
  have hopen : IsOpen (Box.Ioo I) := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : frontier (Box.Ioo I) ⊆ Box.Icc I \ Box.Ioo I := by
    rw [hopen.frontier_eq]
    exact sdiff_subset_sdiff_left (closure_minimal I.Ioo_subset_Icc I.isCompact_Icc.isClosed)
  have heq : (Box.Icc I \ Box.Ioo I) =ᵐ[volume] (∅ : Set (ι → ℝ)) := by
    filter_upwards [I.Ioo_ae_eq_Icc] with x hx
    apply propext
    change (x ∈ Box.Icc I ∧ x ∉ Box.Ioo I) ↔ False
    have hx' : x ∈ Box.Ioo I ↔ x ∈ Box.Icc I := iff_of_eq hx
    tauto
  exact measure_mono_null hsub ((measure_congr heq).trans measure_empty)

theorem exhaustionBox_Icc_dist_zero_le {ι : Type*} [Fintype ι] (H : ℕ) (u : ι → ℝ)
    (hu : u ∈ Box.Icc (exhaustionBox ι H)) : dist u 0 ≤ (H : ℝ) + 1 := by
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ H + 1)).mpr
  intro i
  have hi : -((H : ℝ) + 1) ≤ u i ∧ u i ≤ (H : ℝ) + 1 := ⟨hu.1 i, hu.2 i⟩
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using! abs_le.mpr hi

theorem exhaustionBox_Icc_image_mem_outerBall {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (K : ℝ≥0) (he : LipschitzWith K e)
    (H : ℕ) (u : ι → ℝ) (hu : u ∈ Box.Icc (exhaustionBox ι H)) :
    e u ∈ ball (e 0) (planeBoxOuterRadius K H) := by
  apply mem_ball.mpr
  have hdist := (he.dist_le_mul u 0).trans
    (mul_le_mul_of_nonneg_left (exhaustionBox_Icc_dist_zero_le H u hu) K.coe_nonneg)
  dsimp [planeBoxOuterRadius]
  nlinarith

theorem boundedProjectionRegion_preimage_frontier_subset {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    e ⁻¹' frontier (boundedProjectionRegion π (e 0) K H) ⊆
      frontier (Box.Ioo (exhaustionBox ι H)) := by
  intro u hu
  have hsplit := frontier_inter_subset (openProjectionBox (exhaustionBox ι H) π)
    (ball (e 0) (planeBoxOuterRadius K H)) hu
  rcases hsplit with hA | hB
  · have h := hπ.frontier_preimage_subset (Box.Ioo (exhaustionBox ι H)) hA.1
    simpa only [mem_preimage, hleft u] using! h
  · have hclos : closure (openProjectionBox (exhaustionBox ι H) π) ⊆
        π ⁻¹' Box.Icc (exhaustionBox ι H) :=
      closure_minimal (fun _ hx => (exhaustionBox ι H).Ioo_subset_Icc hx)
        ((exhaustionBox ι H).isCompact_Icc.isClosed.preimage hπ)
    have hucc : u ∈ Box.Icc (exhaustionBox ι H) := by
      simpa only [mem_preimage, hleft u] using! hclos hB.1
    have hin := exhaustionBox_Icc_image_mem_outerBall e K he H u hucc
    have hout := hB.2
    rw [isOpen_ball.frontier_eq] at hout
    exact False.elim (hout.2 hin)

theorem boundedProjectionRegion_null_frontier {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e) (H : ℕ) :
    coordinatePlaneMeasure e (frontier (boundedProjectionRegion π (e 0) K H)) = 0 := by
  rw [coordinatePlaneMeasure, Measure.map_apply he.continuous.measurable isClosed_frontier.measurableSet]
  exact measure_mono_null (boundedProjectionRegion_preimage_frontier_subset e π K he hπ hleft H)
    (box_Ioo_frontier_volume_zero (exhaustionBox ι H))

theorem boundedProjectionRegion_compact_closure {ι : Type*} {d : ℕ}
    (π : Ambient d → ι → ℝ) (a : Ambient d) (K : ℝ≥0) (H : ℕ) :
    IsCompact (closure (boundedProjectionRegion π a K H)) := by
  apply (isCompact_closedBall a (planeBoxOuterRadius K H)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  exact fun _ hx => mem_closedBall.mpr hx.2.le

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak convergence on continuity sets

Weak convergence of finite measures controls the masses of sets with null boundary.
Weighting by bounded continuous nonnegative functions transfers this control to restricted
integrals, providing continuity-set versions of the weak convergence estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem finiteMeasure_continuitySet_mass_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d))
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure (Ambient d)).real s) atTop
      (𝓝 ((ν : Measure (Ambient d)).real s)) := by
  by_cases hν : ν = 0
  · subst ν
    have ht : Tendsto (fun j => (μ j : Measure (Ambient d)).real univ) atTop (𝓝 0) := by
      simpa using! NNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
    simpa using! squeeze_zero (fun _ => measureReal_nonneg)
      (fun j => measureReal_mono (μ := (μ j : Measure (Ambient d))) (subset_univ s)) ht
  · exact finiteMeasure_cell_mass_tendsto μ ν hweak hν s hboundary

theorem weightedFiniteMeasure_integral {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(weightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂(μ : Measure (Ambient d)) := by
  exact integral_withDensity_eq_integral_smul (μ := (μ : Measure (Ambient d)))
    f.continuous.measurable g

theorem weightedFiniteMeasure_real_set {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (f : Ambient d →ᵇ ℝ≥0) (s : Set (Ambient d)) (hs : MeasurableSet s) :
    (weightedFiniteMeasure μ f : Measure (Ambient d)).real s =
      ∫ x in s, (f x : ℝ) ∂(μ : Measure (Ambient d)) := by
  change ((μ : Measure (Ambient d)).withDensity (fun x => (f x : ℝ≥0∞))).real s = _
  rw [Measure.real, withDensity_apply _ hs]
  exact f.toReal_lintegral_coe_eq_integral ((μ : Measure (Ambient d)).restrict s)

theorem weightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (f : Ambient d →ᵇ ℝ≥0) :
    Tendsto (fun j => weightedFiniteMeasure (μ j) f) atTop (𝓝 (weightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  simp only [weightedFiniteMeasure_integral]
  let f₀ : Ambient d →ᵇ ℝ := BoundedContinuousFunction.comp ((↑) : ℝ≥0 → ℝ)
    NNReal.isometry_coe.lipschitz f
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (f₀ * g)

theorem weak_setIntegral_nnreal_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) (f : Ambient d →ᵇ ℝ≥0) :
    Tendsto (fun j => ∫ x in s, (f x : ℝ) ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x in s, (f x : ℝ) ∂(ν : Measure (Ambient d)))) := by
  have hb : (weightedFiniteMeasure ν f : Measure (Ambient d)) (frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ hboundary
  have h := finiteMeasure_continuitySet_mass_tendsto (fun j => weightedFiniteMeasure (μ j) f)
    (weightedFiniteMeasure ν f) (weightedFiniteMeasure_tendsto μ ν hweak f) s hb
  simpa only [weightedFiniteMeasure_real_set _ f s hs] using! h

theorem weak_setIntegral_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) (f : Ambient d →ᵇ ℝ) :
    Tendsto (fun j => ∫ x in s, f x ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x in s, f x ∂(ν : Measure (Ambient d)))) := by
  have hp := weak_setIntegral_nnreal_tendsto μ ν hweak s hs hboundary f.nnrealPart
  have hn := weak_setIntegral_nnreal_tendsto μ ν hweak s hs hboundary (-f).nnrealPart
  simpa only [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub] using! hp.sub hn

theorem restrictedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => restrictedFiniteMeasure (μ j) s) atTop (𝓝 (restrictedFiniteMeasure ν s)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact fun f => weak_setIntegral_tendsto μ ν hweak s hs hboundary f

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactWeakConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction CompactlySupported

theorem compactWeightedFiniteMeasure_integral {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0)) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(compactWeightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂μ := by
  exact integral_withDensity_eq_integral_smul f.continuous.measurable g

theorem compactWeightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (f : C_c(Ambient d, ℝ≥0)) :
    Tendsto (fun j => compactWeightedFiniteMeasure (μ j) f) atTop
      (𝓝 (compactWeightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let test : C_c(Ambient d, ℝ) :=
    ⟨⟨fun x => f.toReal x * g x, f.toReal.continuous.mul g.continuous⟩,
      f.toReal.hasCompactSupport.mul_right⟩
  have ht := hlocal test
  change Tendsto (fun j => ∫ x, f.toReal x * g x ∂μ j) atTop
    (𝓝 (∫ x, f.toReal x * g x ∂ν)) at ht
  simpa only [compactWeightedFiniteMeasure_integral,
    CompactlySupportedContinuousMap.toReal_apply] using! ht

theorem exists_compact_nonneg_cutoff {d : ℕ} (s : Set (Ambient d)) (hs : IsCompact s) :
    ∃ f : C_c(Ambient d, ℝ≥0), (∀ x ∈ s, f x = 1) ∧ ∀ x, f x ≤ 1 := by
  obtain ⟨g, hgs, _, hgc, hg⟩ :=
    exists_continuous_one_zero_of_isCompact hs isClosed_empty (disjoint_empty s)
  let g₀ : C_c(Ambient d, ℝ) := ⟨g, hgc⟩
  refine ⟨g₀.nnrealPart, ?_, ?_⟩
  · intro x hx
    change Real.toNNReal (g x) = 1
    rw [show g x = 1 from hgs hx]
    simp
  · intro x
    change Real.toNNReal (g x) ≤ 1
    simpa using! Real.toNNReal_le_toNNReal (hg x).2

theorem compactWeightedFiniteMeasure_restrict {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x = 1) :
    (compactWeightedFiniteMeasure μ f : Measure (Ambient d)).restrict s = μ.restrict s := by
  change (μ.withDensity (fun x => (f x : ℝ≥0∞))).restrict s = _
  rw [restrict_withDensity hs]
  calc
    _ = (μ.restrict s).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      simp only [hf x hx, ENNReal.coe_one, Pi.one_apply]
    _ = _ := withDensity_one

theorem compactTestConvergence_restrict_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (s : Set (Ambient d))
    (hs : MeasurableSet s) (hc : IsCompact (closure s))
    (hboundary : ν (frontier s) = 0) :
    Tendsto (fun j => relativelyCompactFiniteMeasure (μ j) s hc) atTop
      (𝓝 (relativelyCompactFiniteMeasure ν s hc)) := by
  obtain ⟨f, hf, _⟩ := exists_compact_nonneg_cutoff (closure s) hc
  have hf' : ∀ x ∈ s, f x = 1 := fun x hx => hf x (subset_closure hx)
  have hb : (compactWeightedFiniteMeasure ν f : Measure (Ambient d)) (frontier s) = 0 :=
    withDensity_absolutelyContinuous _ _ hboundary
  have h := restrictedFiniteMeasure_tendsto (fun j => compactWeightedFiniteMeasure (μ j) f)
    (compactWeightedFiniteMeasure ν f) (compactWeightedFiniteMeasure_tendsto μ ν hlocal f) s hs hb
  have heq : ∀ (ρ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ρ],
      restrictedFiniteMeasure (compactWeightedFiniteMeasure ρ f) s =
        relativelyCompactFiniteMeasure ρ s hc := by
    intro ρ _
    apply Subtype.ext
    exact compactWeightedFiniteMeasure_restrict ρ f s hs hf'
  simpa only [heq] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_BoundedBoxConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Compact-test convergence to a coordinate-plane measure yields weak convergence of finite measures
on bounded projection regions, using compact closures and null frontiers.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem boundedProjectionFiniteMeasure_tendsto {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ (coordinatePlaneMeasure e)) (H : ℕ) :
    Tendsto (fun j => boundedProjectionFiniteMeasure (μ j) π (e 0) K H) atTop
      (𝓝 (boxPlaneFiniteMeasure (exhaustionBox ι H) e)) := by
  let : IsFiniteMeasureOnCompacts (coordinatePlaneMeasure e) :=
    coordinatePlaneMeasure_finite_on_compacts e π he.continuous.measurable Q hπ hleft
  let s := boundedProjectionRegion π (e 0) K H
  have hs : MeasurableSet s := (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet
  have hc : IsCompact (closure s) := boundedProjectionRegion_compact_closure π (e 0) K H
  have h := compactTestConvergence_restrict_tendsto μ (coordinatePlaneMeasure e) hlocal s hs hc
    (boundedProjectionRegion_null_frontier e π K he hπ.continuous hleft H)
  have heq : relativelyCompactFiniteMeasure (coordinatePlaneMeasure e) s hc =
      boxPlaneFiniteMeasure (exhaustionBox ι H) e := by
    apply Subtype.ext
    exact coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft H
  rw [heq] at h
  exact h

theorem coordinatePlaneMeasure_ae_section {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (he : Continuous e) (hπ : Continuous π) (hleft : LeftInverse π e) :
    ∀ᵐ x ∂coordinatePlaneMeasure e, e (π x) = x := by
  apply (ae_map_iff he.measurable.aemeasurable
    (isClosed_eq (he.comp hπ) continuous_id).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun u => congrArg e (hleft u))

theorem projectionHeight_lipschitz {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) :
    LipschitzWith (1 + K * Q) (fun x => dist x (e (π x))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have heπ := (he.comp hπ).dist_le_mul x y
  calc
    dist (dist x (e (π x))) (dist y (e (π y))) ≤ dist x y + dist (e (π x)) (e (π y)) :=
      dist_dist_dist_le _ _ _ _
    _ ≤ dist x y + ((K : ℝ) * Q) * dist x y := by
      simpa only [Function.comp_apply, NNReal.coe_mul] using! add_le_add (le_refl (dist x y)) heπ
    _ = ((1 + K * Q : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LocalSupportConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactWeightedFiniteMeasure_apply_eq {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x = 1) :
    (compactWeightedFiniteMeasure μ f : Measure (Ambient d)) s = μ s := by
  have h := congrArg (fun ρ : Measure (Ambient d) => ρ univ)
    (compactWeightedFiniteMeasure_restrict μ f s hs hf)
  simpa using! h

theorem compactTestConvergence_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν)
    (q : Ambient d → ℝ) (K : ℝ≥0) (hq : LipschitzWith K q)
    (hzero : ∀ᵐ x ∂ν, q x = 0) (a : Ambient d) (R ε r c : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hr : (K : ℝ) * r ≤ ε / 2)
    (hball : ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → q x < ε := by
  obtain ⟨f, hf, _⟩ := exists_compact_nonneg_cutoff (closedBall a (R + r))
    (isCompact_closedBall a (R + r))
  let νf := compactWeightedFiniteMeasure ν f
  let μf := fun j => compactWeightedFiniteMeasure (μ j) f
  let bad : Set (Ambient d) := {x | ε / 2 ≤ q x}
  have hclosed : IsClosed bad := isClosed_le continuous_const hq.continuous
  have hzero' : ∀ᵐ x ∂(νf : Measure (Ambient d)), q x = 0 :=
    (withDensity_absolutelyContinuous ν (fun x => (f x : ℝ≥0∞))).ae_le hzero
  have hbad : (νf : Measure (Ambient d)) bad = 0 := by
    have hnot : ∀ᵐ x ∂(νf : Measure (Ambient d)), x ∉ bad := by
      filter_upwards [hzero'] with x hx
      change ¬ ε / 2 ≤ q x
      rw [hx]
      linarith
    simpa only [ae_iff, not_not] using! hnot
  have hfront : (νf : Measure (Ambient d)) (frontier bad) = 0 :=
    measure_mono_null hclosed.frontier_subset hbad
  have hmass : Tendsto (fun j => (μf j : Measure (Ambient d)).real bad) atTop (𝓝 0) := by
    simpa only [Measure.real, hbad, ENNReal.toReal_zero] using!
      finiteMeasure_continuitySet_mass_tendsto μf νf
        (compactWeightedFiniteMeasure_tendsto μ ν hlocal f) bad hfront
  filter_upwards [hball, hmass.eventually (gt_mem_nhds hc)] with j hj hsmall
  intro x hx hxsupport
  by_contra hlarge
  have hlarge' : ε ≤ q x := le_of_not_gt hlarge
  have hsub : ball x r ⊆ bad := by
    intro y hy
    have hd : dist x y ≤ r := by
      simpa only [dist_comm] using! (show dist y x < r from hy).le
    have hdiff : q x - q y ≤ (K : ℝ) * dist x y := by
      have h := hq.dist_le_mul x y
      rw [Real.dist_eq] at h
      exact (le_abs_self _).trans h
    have hmul := mul_le_mul_of_nonneg_left hd K.coe_nonneg
    change ε / 2 ≤ q y
    linarith
  have hfone : ∀ y ∈ ball x r, f y = 1 := by
    intro y hy
    apply hf y
    apply mem_closedBall.mpr
    have hd := dist_triangle y x a
    have hy' : dist y x < r := hy
    have hx' : dist x a < R := hx
    linarith
  have heq : (μf j : Measure (Ambient d)).real (ball x r) = (μ j).real (ball x r) := by
    unfold Measure.real
    rw [show (μf j : Measure (Ambient d)) (ball x r) = (μ j) (ball x r) from
      compactWeightedFiniteMeasure_apply_eq (μ j) f (ball x r) measurableSet_ball hfone]
  have hmassge : c ≤ (μf j : Measure (Ambient d)).real bad := by
    calc
      c ≤ (μ j).real (ball x r) := hj x hx hxsupport
      _ = (μf j : Measure (Ambient d)).real (ball x r) := heq.symm
      _ ≤ _ := measureReal_mono hsub
  exact (not_lt_of_ge hmassge) hsmall

theorem compactTestConvergence_measure_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν)
    (q : Ambient d → ℝ) (K : ℝ≥0) (hq : LipschitzWith K q)
    (hzero : ∀ᵐ x ∂ν, q x = 0) (a : Ambient d) (R ε r c : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hr : (K : ℝ) * r ≤ ε / 2)
    (hball : ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ᶠ j in atTop, ∀ᵐ x ∂(μ j).restrict (ball a R), q x < ε := by
  filter_upwards [compactTestConvergence_support_tube μ ν hlocal q K hq hzero
    a R ε r c hε hc hr hball] with j hj
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae (μ j).support_mem_ae]
    with x hx hxsupport
  exact hj x hx hxsupport

theorem compactTestConvergence_dyadic_tubes {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν)
    (q : Ambient d → ℝ) (K : ℝ≥0) (hq : LipschitzWith K q)
    (hzero : ∀ᵐ x ∂ν, q x = 0) (a : Ambient d) (R : ℝ)
    (hball : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ k : ℕ, ∀ᶠ j in atTop, ∀ᵐ x ∂(μ j).restrict (ball a R), q x ≤ (1 / 2 : ℝ) ^ k := by
  intro k
  let ε : ℝ := (1 / 2 : ℝ) ^ k
  have hε : 0 < ε := by positivity
  let r : ℝ := ε / (2 * ((K : ℝ) + 1))
  have hr0 : 0 < r := by positivity
  obtain ⟨c, hc, hbc⟩ := hball r hr0
  have hr : (K : ℝ) * r ≤ ε / 2 := by
    dsimp [r]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
    have heq : ε / (2 * ((K : ℝ) + 1)) * (2 * ((K : ℝ) + 1)) = ε :=
      div_mul_cancel₀ ε hden.ne'
    nlinarith [le_of_lt hr0]
  filter_upwards [compactTestConvergence_measure_tube μ ν hlocal q K hq hzero
    a R ε r c hε hc hr hbc] with j hj
  exact hj.mono fun _ hx => hx.le

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedBoxHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection-height control on bounded boxes

Convergence to a coordinate-plane measure, together with local lower mass bounds, forces
the restricted measures into arbitrarily thin tubes about the coordinate plane. The height
estimate is stated almost everywhere for the bounded projection measures used in boxwise
kernel comparisons.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem boundedProjectionFiniteMeasure_height {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ (coordinatePlaneMeasure e)) (H : ℕ)
    (hball : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, ∀ x ∈ ball (e 0) (planeBoxOuterRadius K H),
        x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(boundedProjectionFiniteMeasure (μ j) π (e 0) K H : Measure (Ambient d)),
        dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k := by
  let : IsFiniteMeasureOnCompacts (coordinatePlaneMeasure e) :=
    coordinatePlaneMeasure_finite_on_compacts e π he.continuous.measurable Q hπ hleft
  have hzero : ∀ᵐ x ∂coordinatePlaneMeasure e, dist x (e (π x)) = 0 := by
    filter_upwards [coordinatePlaneMeasure_ae_section e π he.continuous hπ.continuous hleft]
      with x hx
    rw [hx, dist_self]
  have h := compactTestConvergence_dyadic_tubes μ (coordinatePlaneMeasure e) hlocal
    (fun x => dist x (e (π x))) (1 + K * Q) (projectionHeight_lipschitz e π K Q he hπ)
    hzero (e 0) (planeBoxOuterRadius K H) hball
  intro k
  filter_upwards [h k] with j hj
  exact ae_mono (Measure.restrict_mono_set (μ j)
    (show boundedProjectionRegion π (e 0) K H ⊆ ball (e 0) (planeBoxOuterRadius K H) from
      fun _ hx => hx.2)) hj

theorem eventual_lower_ball_mass_of_AD_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, ∀ x ∈ (μ j).support, c ≤ (μ j).real (ball x r) := by
  have hc : 0 < r ^ n / C := div_pos (pow_pos hr n) hC
  refine ⟨r ^ n / C, hc, ?_⟩
  filter_upwards [hdiam r hr] with j hj
  intro x hx
  have hfinite : (μ j) (ball x r) ≠ ∞ :=
    ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top)
  have h := ENNReal.toReal_mono hfinite (hlower j x hx r ⟨hr, hj⟩)
  simpa only [ENNReal.toReal_ofReal hc.le, Measure.real] using! h

theorem boundedProjectionFiniteMeasure_height_of_AD_lower {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (hlocal : CompactTestConvergence μ (coordinatePlaneMeasure e))
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ Fintype.card ι / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support) :
    ∀ H k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(boundedProjectionFiniteMeasure (μ j) π (e 0) K H : Measure (Ambient d)),
        dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k := by
  intro H
  apply boundedProjectionFiniteMeasure_height e π K Q he hπ hleft μ hlocal H
  intro r hr
  obtain ⟨c, hc, hbc⟩ := eventual_lower_ball_mass_of_AD_lower (Fintype.card ι) μ C hC hlower hdiam r hr
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbc] with j hj
  exact fun x _ hx => hj x hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LipschitzTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem lipschitz_bounded_product_real {f g : X → ℝ} {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  calc
    dist (f x * g x) (f y * g y) =
        |f x * (g x - g y) + (f x - f y) * g y| := by
      rw [Real.dist_eq]
      congr 1
      ring
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using! abs_add_le
        (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) +
        ((Kf : ℝ) * dist x y) * (Bg : ℝ) := by
      exact add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
        (mul_le_mul hf' (hBg y) (abs_nonneg _) (by positivity))
    _ = ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_L2Pairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral pairings of real L² functions

The L² inner product agrees with integration of pointwise products. Subtraction and
Cauchy–Schwarz then bound differences of pairings by squared L² errors.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem real_scalar_inner_mul (a b : ℝ) : inner ℝ a b = a * b := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  simp only [← pow_two, Real.norm_eq_abs, sq_abs]
  ring

theorem toLp_inner_eq_integral (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy, real_scalar_inner_mul]

theorem integral_mul_cauchy_schwarz_sq (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [toLp_norm_sq_eq_integral, toLp_norm_sq_eq_integral] at h
  simpa only [toLp_inner_eq_integral, pow_two] using! h

theorem integral_mul_sub_eq (μ : Measure X) (f g ψ : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hψ : MemLp ψ 2 μ) :
    (∫ x, (f x - g x) * ψ x ∂μ) =
      (∫ x, f x * ψ x ∂μ) - (∫ x, g x * ψ x ∂μ) := by
  have hfp : MemLp (fun x => f x * ψ x) 1 μ := MeasureTheory.MemLp.mul (hφ := hf) (hf := hψ)
  have hgp : MemLp (fun x => g x * ψ x) 1 μ := MeasureTheory.MemLp.mul (hφ := hg) (hf := hψ)
  simp_rw [sub_mul]
  exact integral_sub (memLp_one_iff_integrable.mp hfp) (memLp_one_iff_integrable.mp hgp)

theorem integral_pairing_difference_sq_le (μ : Measure X) (f g ψ : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hψ : MemLp ψ 2 μ) :
    ((∫ x, f x * ψ x ∂μ) - (∫ x, g x * ψ x ∂μ)) ^ 2 ≤
      (∫ x, (f x - g x) ^ 2 ∂μ) * (∫ x, ψ x ^ 2 ∂μ) := by
  rw [← integral_mul_sub_eq μ f g ψ hf hg hψ]
  exact integral_mul_cauchy_schwarz_sq μ (f - g) ψ (hf.sub hg) hψ

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LipschitzL2Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem bounded_lipschitz_L2_approximation {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : Ambient d → ℝ) (K B : ℝ≥0),
      HasCompactSupport g ∧ LipschitzWith K g ∧ (∀ x, |g x| ≤ (B : ℝ)) ∧
        MemLp g 2 μ ∧ eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hgcompact, hgsmooth, herror⟩ :=
    hf.exist_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hε
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgcompact hgsmooth (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hgcompact.exists_bound_of_continuous hgsmooth.continuous
  refine ⟨g, K, Real.toNNReal B, hgcompact, hK, ?_,
    hgsmooth.continuous.memLp_of_hasCompactSupport hgcompact, herror⟩
  intro x
  have hbound : |g x| ≤ B := by simpa only [Real.norm_eq_abs] using! hB x
  exact hbound.trans (Real.le_coe_toNNReal B)

theorem bounded_lipschitz_L2_squared_approximation {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : Ambient d → ℝ) (K B : ℝ≥0),
      HasCompactSupport g ∧ LipschitzWith K g ∧ (∀ x, |g x| ≤ (B : ℝ)) ∧
        MemLp g 2 μ ∧ (∫ x, (g x - f x) ^ 2 ∂μ) ≤ ε ^ 2 := by
  obtain ⟨g, K, B, hcomp, hLip, hbound, hg, he⟩ :=
    bounded_lipschitz_L2_approximation μ f hf ε hε
  refine ⟨g, K, B, hcomp, hLip, hbound, hg, ?_⟩
  have hnorm : ‖(hf.sub hg).toLp (f - g)‖ ≤ ε := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hε.le he
  have hsq := pow_le_pow_left₀ (norm_nonneg ((hf.sub hg).toLp (f - g))) hnorm 2
  rw [toLp_norm_sq_eq_integral] at hsq
  simpa only [Pi.sub_apply, sub_sq_comm] using! hsq

theorem exists_bounded_lipschitz_L2_sequence {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) :
    ∃ (g : ℕ → Ambient d → ℝ) (K B : ℕ → ℝ≥0),
      (∀ k, HasCompactSupport (g k)) ∧ (∀ k, LipschitzWith (K k) (g k)) ∧
      (∀ k x, |g k x| ≤ (B k : ℝ)) ∧ (∀ k, MemLp (g k) 2 μ) ∧
      Tendsto (fun k => ∫ x, (g k x - f x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have happrox : ∀ k : ℕ, ∃ (g : Ambient d → ℝ) (K B : ℝ≥0),
      HasCompactSupport g ∧ LipschitzWith K g ∧ (∀ x, |g x| ≤ (B : ℝ)) ∧
        MemLp g 2 μ ∧ (∫ x, (g x - f x) ^ 2 ∂μ) ≤ ((1 / 2 : ℝ) ^ k) ^ 2 := by
    intro k
    exact bounded_lipschitz_L2_squared_approximation μ f hf _ (by positivity)
  choose g K B hcomp hLip hbound hg herr using happrox
  refine ⟨g, K, B, hcomp, hLip, hbound, hg, ?_⟩
  apply squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) herr
  simpa only [zero_pow two_ne_zero] using!
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).pow 2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TestStepApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

theorem finiteStep_test_error_le (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (ψ : X → ℝ) (hψ : MemLp ψ 2 μ)
    (c : ι → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
    (hcell : ∀ i, ∀ᵐ x ∂μ.restrict (s i), |ψ x - c i| ≤ D) :
    (∫ x, (ψ x - finiteStep s c x) ^ 2 ∂μ) ≤ μ.real univ * D ^ 2 := by
  have hc : ∀ᵐ x ∂μ, ∀ i, x ∈ s i → |ψ x - c i| ≤ D :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hs i)).mp (hcell i))
  have hb : ∀ᵐ x ∂μ, (ψ x - finiteStep s c x) ^ 2 ≤ D ^ 2 := by
    filter_upwards [hcover, hc] with x hx hcx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [finiteStep_eq_cell s c hd i x hi]
    simpa only [sq_abs] using! (sq_le_sq₀ (abs_nonneg _) hD).mpr (hcx i hi)
  have h := integral_mono_ae ((hψ.sub (finiteStep_memLp μ s hs c)).integrable_sq)
    (integrable_const (D ^ 2)) hb
  simpa only [integral_const, smul_eq_mul] using! h

variable [MetricSpace X]

theorem lipschitz_step_test_error_le (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (ψ : X → ℝ) (hψ : MemLp ψ 2 μ)
    (K : ℝ≥0) (hLip : LipschitzWith K ψ) (z : ι → X)
    (r : ℝ) (hr : 0 ≤ r) (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, s i)
    (hcell : ∀ i, ∀ᵐ x ∂μ.restrict (s i), dist x (z i) ≤ r) :
    (∫ x, (ψ x - finiteStep s (fun i => ψ (z i)) x) ^ 2 ∂μ) ≤
      μ.real univ * ((K : ℝ) * r) ^ 2 := by
  apply finiteStep_test_error_le μ s hs hd ψ hψ _ _ (mul_nonneg K.coe_nonneg hr) hcover
  intro i
  filter_upwards [hcell i] with x hx
  have h := (hLip.dist_le_mul x (z i)).trans (mul_le_mul_of_nonneg_left hx K.coe_nonneg)
  simpa only [Real.dist_eq] using! h

omit [MetricSpace X] in

theorem L2_tendsto_of_squared_error (ν : Measure X) (f : ℕ → X → ℝ) (ψ : X → ℝ)
    (hf : ∀ k, MemLp (f k) 2 ν) (hψ : MemLp ψ 2 ν)
    (herror : Tendsto (fun k => ∫ x, (f k x - ψ x) ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 (hψ.toLp ψ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [herror.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 by positivity))]
    with k hk
  rw [← toLp_dist_sq_eq_integral ν (f k) ψ (hf k) hψ] at hk
  nlinarith [dist_nonneg (x := (hf k).toLp (f k)) (y := hψ.toLp ψ)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LocalLimitUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

theorem L2_ae_eq_of_compact_lipschitz_pairings {d : ℕ}
    (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (f g : Ambient d → ℝ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hpair : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) → MemLp ψ 2 ν →
      (∫ x, f x * ψ x ∂ν) = ∫ x, g x * ψ x ∂ν) : f =ᵐ[ν] g := by
  let h := fun x => f x - g x
  have hh : MemLp h 2 ν := hf.sub hg
  obtain ⟨ψ, K, B, hcomp, hLip, hbound, hψ, herror⟩ :=
    exists_bounded_lipschitz_L2_sequence ν h hh
  have hconv := L2_tendsto_of_squared_error ν ψ h hψ hh herror
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => hh.toLp h) atTop
    (𝓝 (hh.toLp h))).inner (𝕜 := ℝ) hconv
  simp only [toLp_inner_eq_integral] at hlim
  have hz : ∀ k, (∫ x, h x * ψ k x ∂ν) = 0 := by
    intro k
    rw [integral_mul_sub_eq ν f g (ψ k) hf hg (hψ k),
      hpair (ψ k) (K k) (B k) (hcomp k) (hLip k) (hbound k) (hψ k), sub_self]
  simp only [hz] at hlim
  have hsq : (∫ x, h x ^ 2 ∂ν) = 0 := by
    simpa only [pow_two] using! tendsto_nhds_unique hlim tendsto_const_nhds
  have hae : (fun x => h x ^ 2) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg (h x))
      hh.integrable_sq).mp hsq
  filter_upwards [hae] with x hx
  dsimp [h] at hx
  nlinarith [sq_nonneg (f x - g x)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OverlapCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatibility of local L² representatives

Bounded multipliers preserve L² integrability, and supported weighted tests remove measure
restrictions. Common limiting moments then identify local representatives on overlaps
where a Lipschitz cutoff is nonzero almost everywhere.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem memLp_bounded_multiplier {d : ℕ} (ν : Measure (Ambient d))
    (f χ : Ambient d → ℝ) (hf : MemLp f 2 ν) (hχ : Measurable χ)
    (B : ℝ) (hB : ∀ x, |χ x| ≤ B) : MemLp (fun x => χ x * f x) 2 ν := by
  apply hf.of_le_mul (c := B) (hχ.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)

theorem restricted_weighted_test_eq_integral {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : Set X) (f χ ψ : X → ℝ) (hχ : ∀ x, x ∉ s → χ x = 0) :
    (∫ x, f x * (χ x * ψ x) ∂ν.restrict s) = ∫ x, f x * (χ x * ψ x) ∂ν := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [hχ x hx, zero_mul, mul_zero]

theorem local_L2_agreement_from_common_moments {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (s t : Set (Ambient d))
    (f g : Ambient d → ℝ) (hf : MemLp f 2 (ν.restrict s)) (hg : MemLp g 2 (ν.restrict t))
    (χ : Ambient d → ℝ) (Kχ Bχ : ℝ≥0) (hχ : LipschitzWith Kχ χ)
    (hχB : ∀ x, |χ x| ≤ (Bχ : ℝ))
    (hχsupp : ∀ x, χ x ≠ 0 → x ∈ s ∩ t)
    (hχpos : ∀ᵐ x ∂ν.restrict (s ∩ t), χ x ≠ 0)
    (w : ℕ → Ambient d → ℝ)
    (hfirst : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict s) atTop
        (𝓝 (∫ x, f x * ψ x ∂ν.restrict s)))
    (hsecond : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict t) atTop
        (𝓝 (∫ x, g x * ψ x ∂ν.restrict t))) :
    f =ᵐ[ν.restrict (s ∩ t)] g := by
  have hzS : ∀ x, x ∉ s → χ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hχsupp x hne).1
  have hzT : ∀ x, x ∉ t → χ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hχsupp x hne).2
  have hzO : ∀ x, x ∉ s ∩ t → χ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hχsupp x hne)
  have hfO : MemLp f 2 (ν.restrict (s ∩ t)) :=
    hf.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hgO : MemLp g 2 (ν.restrict (s ∩ t)) :=
    hg.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have heq : (fun x => χ x * f x) =ᵐ[ν.restrict (s ∩ t)] (fun x => χ x * g x) := by
    apply L2_ae_eq_of_compact_lipschitz_pairings (ν.restrict (s ∩ t)) _ _
      (memLp_bounded_multiplier _ f χ hfO hχ.continuous.measurable Bχ hχB)
      (memLp_bounded_multiplier _ g χ hgO hχ.continuous.measurable Bχ hχB)
    intro ψ K B hc hLip hB _
    have htest : HasCompactSupport (fun x => χ x * ψ x) := hc.mul_left
    have htestLip := lipschitz_bounded_product_real hχ hLip hχB hB
    have htestB : ∀ x, |χ x * ψ x| ≤ ((Bχ * B : ℝ≥0) : ℝ) := by
      intro x
      simp only [abs_mul, NNReal.coe_mul]
      exact mul_le_mul (hχB x) (hB x) (abs_nonneg _) Bχ.coe_nonneg
    have h₁ := hfirst (fun x => χ x * ψ x) _ (Bχ * B) htest htestLip htestB
    have h₂ := hsecond (fun x => χ x * ψ x) _ (Bχ * B) htest htestLip htestB
    simp only [restricted_weighted_test_eq_integral _ s _ χ ψ hzS] at h₁
    simp only [restricted_weighted_test_eq_integral _ t _ χ ψ hzT] at h₂
    have hsame := tendsto_nhds_unique h₁ h₂
    have hleft : (fun x => (χ x * f x) * ψ x) = fun x => f x * (χ x * ψ x) := by
      funext x
      ring
    have hright : (fun x => (χ x * g x) * ψ x) = fun x => g x * (χ x * ψ x) := by
      funext x
      ring
    rw [hleft, hright, restricted_weighted_test_eq_integral _ (s ∩ t) f χ ψ hzO,
      restricted_weighted_test_eq_integral _ (s ∩ t) g χ ψ hzO]
    exact hsame
  filter_upwards [heq, hχpos] with x hx hpos
  exact (mul_left_cancel₀ hpos) hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OpenOverlapCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem exists_lipschitz_open_support {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (hs : IsOpen s) :
    ∃ χ : X → ℝ, LipschitzWith 1 χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ support χ = s := by
  classical
  by_cases hfull : s = univ
  · refine ⟨fun _ => 1, ?_, by simp, ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_self, NNReal.coe_one, one_mul] using! (dist_nonneg (x := x) (y := y))
    · ext x
      simp [Function.support, hfull]
  · have hne : sᶜ.Nonempty := ssubset_univ_iff_nonempty_compl.mp
      (ssubset_iff_subset_ne.mpr ⟨subset_univ s, hfull⟩)
    refine ⟨fun x => min 1 (infDist x sᶜ), (lipschitz_infDist_pt sᶜ).const_min 1, ?_, ?_⟩
    · intro x
      exact ⟨le_min (by norm_num) infDist_nonneg, min_le_left _ _⟩
    · ext x
      change min 1 (infDist x sᶜ) ≠ 0 ↔ x ∈ s
      constructor
      · intro hx
        by_contra hnot
        have hz : infDist x sᶜ = 0 := infDist_zero_of_mem hnot
        exact hx (by simp [hz])
      · intro hx
        have hpos : 0 < infDist x sᶜ := (hs.isClosed_compl.notMem_iff_infDist_pos hne).mp
          (by simpa only [mem_compl_iff, not_not] using! hx)
        exact (lt_min (by norm_num : (0 : ℝ) < 1) hpos).ne'

theorem local_L2_agreement_on_open_overlap {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (s t : Set (Ambient d)) (hs : IsOpen s) (ht : IsOpen t)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 (ν.restrict s)) (hg : MemLp g 2 (ν.restrict t))
    (w : ℕ → Ambient d → ℝ)
    (hfirst : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict s) atTop
        (𝓝 (∫ x, f x * ψ x ∂ν.restrict s)))
    (hsecond : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j).restrict t) atTop
        (𝓝 (∫ x, g x * ψ x ∂ν.restrict t))) :
    f =ᵐ[ν.restrict (s ∩ t)] g := by
  obtain ⟨χ, hχ, hbound, hsupp⟩ := exists_lipschitz_open_support (s ∩ t) (hs.inter ht)
  have hsupp' : ∀ x, χ x ≠ 0 ↔ x ∈ s ∩ t := by
    intro x
    change x ∈ support χ ↔ x ∈ s ∩ t
    rw [hsupp]
  apply local_L2_agreement_from_common_moments μ ν s t f g hf hg χ 1 1 hχ
    (fun x => by simpa only [abs_of_nonneg (hbound x).1, NNReal.coe_one] using! (hbound x).2)
    (fun x => (hsupp' x).mp) _ w hfirst hsecond
  filter_upwards [ae_restrict_mem (hs.inter ht).measurableSet] with x hx
  exact (hsupp' x).mpr hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_GlueLocalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter

theorem exists_measurable_glue_of_local_L2 {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (s : ℕ → Set X) (hs : ∀ H, MeasurableSet (s H))
    (hcover : ∀ x, ∃ H, x ∈ s H) (v : ℕ → X → ℝ)
    (hv : ∀ H, Measurable (v H)) (hL2 : ∀ H, MemLp (v H) 2 (ν.restrict (s H)))
    (hcompat : ∀ H K, v H =ᵐ[ν.restrict (s H ∩ s K)] v K) :
    ∃ f : X → ℝ, Measurable f ∧ ∀ H,
      f =ᵐ[ν.restrict (s H)] v H ∧ MemLp f 2 (ν.restrict (s H)) := by
  classical
  let f : X → ℝ := fun x => v (Nat.find (hcover x)) x
  have hfm : Measurable f := Measurable.find (p := fun n x => x ∈ s n) hv hs hcover
  have heq : ∀ H, f =ᵐ[ν.restrict (s H)] v H := by
    intro H
    apply (ae_restrict_iff' (hs H)).mpr
    have hgood : ∀ᵐ x ∂ν, ∀ K, x ∈ s K ∩ s H → v K x = v H x :=
      ae_all_iff.mpr (fun K => (ae_restrict_iff' ((hs K).inter (hs H))).mp (hcompat K H))
    filter_upwards [hgood] with x hx
    intro hxH
    exact hx (Nat.find (hcover x)) ⟨Nat.find_spec (hcover x), hxH⟩
  exact ⟨f, hfm, fun H => ⟨heq H, (memLp_congr_ae (heq H)).mpr (hL2 H)⟩⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_PartitionCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem exists_L2_limit_of_partition_approximations
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i))
    (hd : ∀ k, Pairwise (Disjoint on s k))
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (a : ℕ → ∀ k, ι k → ℝ) (b : ∀ k, ι k → ℝ)
    (ha : ∀ k i, Tendsto (fun j => a j k i) atTop (𝓝 (b k i)))
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (hinter : ∀ k l i t, Tendsto (fun j => (μ j).real (s k i ∩ s l t))
      atTop (𝓝 (ν.real (s k i ∩ s l t))))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (happrox : ∀ k, ∀ᶠ j in atTop,
      (∫ x, (w j x - finiteStep (s k) (a j k) x) ^ 2 ∂μ j) ≤ δ k) :
    ∃ limit : Lp ℝ 2 ν,
      Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
        (finiteStep (s k) (b k))) atTop (𝓝 limit) := by
  apply exists_L2_limit_of_sq_distance_bound ν _ δ hδ
  intro k l
  rw [toLp_dist_sq_eq_integral]
  apply fixed_pair_bound_of_approximations μ ν (finiteStep (s k) (b k))
    (finiteStep (s l) (b l)) (fun j => finiteStep (s k) (a j k)) w
    (fun j => finiteStep (s l) (a j l))
    (fun j => finiteStep_memLp (μ j) (s k) (hs k) (b k))
    (fun j => finiteStep_memLp (μ j) (s l) (hs l) (b l))
    (fun j => finiteStep_memLp (μ j) (s k) (hs k) (a j k)) hw
    (fun j => finiteStep_memLp (μ j) (s l) (hs l) (a j l))
    (δ k) (δ l) (happrox k) (happrox l)
  · exact finiteStep_squared_error_tendsto_zero μ (s k) (hs k) (hd k)
      (fun j => a j k) (b k) _ (ha k) (hm k)
  · exact finiteStep_squared_error_tendsto_zero μ (s l) (hs l) (hd l)
      (fun j => a j l) (b l) _ (ha l) (hm l)
  · exact finiteStep_cross_distance_tendsto μ ν (s k) (s l) (hs k) (hs l)
      (hd k) (hd l) (b k) (b l) (hm k) (hm l) (hinter k l)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PartitionSecondMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Second moments from partition approximations

Convergence of partition masses and coefficients gives convergence of finite-step L²
norms. Vanishing squared approximation errors then transfer this convergence to the
second moments of the original functions under varying measures.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

theorem tendsto_of_squared_approximation (u : ℕ → ℝ) (p : ℕ → ℕ → ℝ)
    (v δ : ℕ → ℝ) (L : ℝ) (hv : Tendsto v atTop (𝓝 L))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hp : ∀ k, Tendsto (fun j => p j k) atTop (𝓝 (v k)))
    (herr : ∀ k, ∀ᶠ j in atTop, (u j - p j k) ^ 2 ≤ δ k) :
    Tendsto u atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hsmall := hδ.eventually (gt_mem_nhds (show (0 : ℝ) < (ε / 3) ^ 2 by positivity))
  obtain ⟨k, hkδ, hkv⟩ := (hsmall.and (Metric.tendsto_nhds.mp hv _ hthird)).exists
  filter_upwards [herr k, Metric.tendsto_nhds.mp (hp k) _ hthird] with j hj hjp
  have hdist : dist (u j) (p j k) < ε / 3 := by
    rw [Real.dist_eq]
    nlinarith [sq_abs (u j - p j k), abs_nonneg (u j - p j k)]
  calc
    dist (u j) L ≤ dist (u j) (p j k) + dist (p j k) L := dist_triangle _ _ _
    _ ≤ dist (u j) (p j k) + (dist (p j k) (v k) + dist (v k) L) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by linarith

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

theorem finiteStep_L2_norm_tendsto (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (a : ℕ → ι → ℝ) (b : ι → ℝ)
    (ha : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 (b i)))
    (hm : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (ν.real (s i)))) :
    Tendsto (fun j => ‖(finiteStep_memLp (μ j) s hs (a j)).toLp (finiteStep s (a j))‖)
      atTop (𝓝 ‖(finiteStep_memLp ν s hs b).toLp (finiteStep s b)‖) := by
  have hsq : Tendsto
      (fun j => ‖(finiteStep_memLp (μ j) s hs (a j)).toLp (finiteStep s (a j))‖ ^ 2)
      atTop (𝓝 (‖(finiteStep_memLp ν s hs b).toLp (finiteStep s b)‖ ^ 2)) := by
    simp_rw [toLp_norm_sq_eq_integral, integral_finiteStep_sq _ s hs hd]
    exact tendsto_finsetSum _ fun i _ => (hm i).mul ((ha i).pow 2)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using! hsq.sqrt

theorem toLp_norm_difference_sq_le (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (‖hf.toLp f‖ - ‖hg.toLp g‖) ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← toLp_dist_sq_eq_integral μ f g hf hg, dist_eq_norm]
  have h := (sq_le_sq₀ (abs_nonneg (‖hf.toLp f‖ - ‖hg.toLp g‖))
    (norm_nonneg (hf.toLp f - hg.toLp g))).mpr (abs_norm_sub_norm_le _ _)
  simpa only [sq_abs] using! h

theorem partition_approximation_second_moments_tendsto
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i))
    (hd : ∀ k, Pairwise (Disjoint on s k))
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (a : ℕ → ∀ k, ι k → ℝ) (b : ∀ k, ι k → ℝ)
    (ha : ∀ k i, Tendsto (fun j => a j k i) atTop (𝓝 (b k i)))
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (happrox : ∀ k, ∀ᶠ j in atTop,
      (∫ x, (w j x - finiteStep (s k) (a j k) x) ^ 2 ∂μ j) ≤ δ k)
    (limit : Lp ℝ 2 ν)
    (hlimit : Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
      (finiteStep (s k) (b k))) atTop (𝓝 limit)) :
    Tendsto (fun j => ∫ x, w j x ^ 2 ∂μ j) atTop (𝓝 (‖limit‖ ^ 2)) := by
  have hnorm : Tendsto (fun j => ‖(hw j).toLp (w j)‖) atTop (𝓝 ‖limit‖) := by
    apply tendsto_of_squared_approximation _
      (fun j k => ‖(finiteStep_memLp (μ j) (s k) (hs k) (a j k)).toLp
        (finiteStep (s k) (a j k))‖)
      (fun k => ‖(finiteStep_memLp ν (s k) (hs k) (b k)).toLp
        (finiteStep (s k) (b k))‖) δ ‖limit‖ hlimit.norm hδ
      (fun k => finiteStep_L2_norm_tendsto μ ν (s k) (hs k) (hd k)
        (fun j => a j k) (b k) (ha k) (hm k))
    intro k
    filter_upwards [happrox k] with j hj
    exact (toLp_norm_difference_sq_le (μ j) (w j) (finiteStep (s k) (a j k))
      (hw j) (finiteStep_memLp (μ j) (s k) (hs k) (a j k))).trans hj
  simpa only [toLp_norm_sq_eq_integral] using! hnorm.pow 2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CountableLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

theorem exists_common_localized_L2_limits {X : Type*} [MeasurableSpace X]
    (μ : ℕ → ℕ → Measure X) (ν : ℕ → Measure X)
    [∀ H j, IsFiniteMeasure (μ H j)] [∀ H, IsFiniteMeasure (ν H)]
    (ι : ℕ → ℕ → Type*) [∀ H k, Fintype (ι H k)]
    (s : ∀ H k, ι H k → Set X)
    (hs : ∀ H k i, MeasurableSet (s H k i))
    (hd : ∀ H k, Pairwise (Disjoint on s H k))
    (w : ℕ → ℕ → X → ℝ) (hw : ∀ H j, MemLp (w H j) 2 (μ H j))
    (B : ℕ → ℝ) (hB : ∀ H j, (∫ x, w H j x ^ 2 ∂μ H j) ≤ B H)
    (hm : ∀ H k i, Tendsto (fun j => (μ H j).real (s H k i)) atTop
      (𝓝 ((ν H).real (s H k i))))
    (hmpos : ∀ H k i, 0 < (ν H).real (s H k i))
    (hinter : ∀ H k l i t, Tendsto (fun j => (μ H j).real (s H k i ∩ s H l t)) atTop
      (𝓝 ((ν H).real (s H k i ∩ s H l t))))
    (δ : ℕ → ℕ → ℝ) (hδ : ∀ H, Tendsto (δ H) atTop (𝓝 0))
    (happrox : ∀ H k, ∀ᶠ j in atTop,
      (∫ x, (w H j x - partitionMean (μ H j) (s H k) (w H j) x) ^ 2 ∂μ H j) ≤ δ H k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b : ∀ H k, ι H k → ℝ,
      (∀ H k i, Tendsto (fun j => cellMean ((μ H (φ j)).restrict (s H k i)) (w H (φ j)))
        atTop (𝓝 (b H k i))) ∧
      ∃ v : ∀ H, Lp ℝ 2 (ν H),
        (∀ H, Tendsto (fun k => (finiteStep_memLp (ν H) (s H k) (hs H k) (b H k)).toLp
          (finiteStep (s H k) (b H k))) atTop (𝓝 (v H))) ∧
        ∀ H, Tendsto (fun j => ∫ x, w H (φ j) x ^ 2 ∂μ H (φ j)) atTop (𝓝 (‖v H‖ ^ 2)) := by
  classical
  let A : Type _ := Σ H : ℕ, Σ k : ℕ, ι H k
  have hbounded : ∀ a : A, ∃ Z : ℝ, ∀ᶠ j in atTop,
      |cellMean ((μ a.1 j).restrict (s a.1 a.2.1 a.2.2)) (w a.1 j)| ≤ Z := by
    intro a
    let c := (ν a.1).real (s a.1 a.2.1 a.2.2) / 2
    have hc : 0 < c := half_pos (hmpos a.1 a.2.1 a.2.2)
    have hmass : ∀ᶠ j in atTop, c ≤ (μ a.1 j).real (s a.1 a.2.1 a.2.2) :=
      ((hm a.1 a.2.1 a.2.2).eventually
        (lt_mem_nhds (half_lt_self (hmpos a.1 a.2.1 a.2.2)))).mono (fun _ h => h.le)
    refine ⟨B a.1 / c + 1, ?_⟩
    filter_upwards [hmass] with j hj
    apply cellMean_abs_bound ((μ a.1 j).restrict (s a.1 a.2.1 a.2.2)) (w a.1 j)
      ((hw a.1 j).restrict _) c (B a.1) hc
    · simpa only [Measure.real, Measure.restrict_apply_univ] using! hj
    · exact (setIntegral_le_integral (hw a.1 j).integrable_sq
        (Filter.Eventually.of_forall fun x => sq_nonneg (w a.1 j x))).trans (hB a.1 j)
  obtain ⟨b, φ, hφ, hcoeff⟩ := exists_common_subsequence_of_eventual_bounds
    (fun j (a : A) => cellMean ((μ a.1 j).restrict (s a.1 a.2.1 a.2.2)) (w a.1 j)) hbounded
  let b' : ∀ H k, ι H k → ℝ := fun H k i => b ⟨H, k, i⟩
  have hb : ∀ H k i, Tendsto
      (fun j => cellMean ((μ H (φ j)).restrict (s H k i)) (w H (φ j))) atTop (𝓝 (b' H k i)) :=
    fun H k i => hcoeff ⟨H, k, i⟩
  have hL2 : ∀ H, ∃ v : Lp ℝ 2 (ν H),
      Tendsto (fun k => (finiteStep_memLp (ν H) (s H k) (hs H k) (b' H k)).toLp
        (finiteStep (s H k) (b' H k))) atTop (𝓝 v) := by
    intro H
    apply exists_L2_limit_of_partition_approximations (fun j => μ H (φ j)) (ν H)
      (ι H) (s H) (hs H) (hd H) (fun j => w H (φ j)) (fun j => hw H (φ j))
      (fun j k i => cellMean ((μ H (φ j)).restrict (s H k i)) (w H (φ j)))
      (b' H) (hb H) (fun k i => (hm H k i).comp hφ.tendsto_atTop)
      (fun k l i t => (hinter H k l i t).comp hφ.tendsto_atTop) (δ H) (hδ H)
    intro k
    simpa only [partitionMean_eq_finiteStep] using! hφ.tendsto_atTop.eventually (happrox H k)
  choose v hv using hL2
  refine ⟨φ, hφ, b', hb, v, hv, ?_⟩
  intro H
  apply partition_approximation_second_moments_tendsto (fun j => μ H (φ j)) (ν H)
    (ι H) (s H) (hs H) (hd H) (fun j => w H (φ j)) (fun j => hw H (φ j))
    (fun j k i => cellMean ((μ H (φ j)).restrict (s H k i)) (w H (φ j)))
    (b' H) (hb H) (fun k i => (hm H k i).comp hφ.tendsto_atTop)
    (δ H) (hδ H) _ (v H) (hv H)
  intro k
  simpa only [partitionMean_eq_finiteStep] using! hφ.tendsto_atTop.eventually (happrox H k)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_StepPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pairings with finite step functions reduce to sums of cell integrals and cell means.
Convergence of cell masses and means therefore gives convergence of these pairings.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

theorem integral_mul_finiteStep (μ : Measure X)
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (w : X → ℝ) (hw : Integrable w μ) (c : ι → ℝ) :
    (∫ x, w x * finiteStep s c x ∂μ) = ∑ i, (∫ x in s i, w x ∂μ) * c i := by
  classical
  have heq : (fun x => w x * finiteStep s c x) =
      (fun x => ∑ i, (s i).indicator (fun y => w y * c i) x) := by
    funext x
    simp only [finiteStep, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ s i <;> simp [hx]
  rw [heq, integral_finsetSum _ (fun i _ => (hw.mul_const (c i)).indicator (hs i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hs i), integral_mul_const]

theorem integral_mul_finiteStep_cellMeans (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (w : X → ℝ) (hw : MemLp w 2 μ) (c : ι → ℝ)
    (hm : ∀ i, μ.real (s i) ≠ 0) :
    (∫ x, w x * finiteStep s c x ∂μ) =
      ∑ i, μ.real (s i) * (cellMean (μ.restrict (s i)) w * c i) := by
  rw [integral_mul_finiteStep μ s hs w (hw.integrable (by norm_num)) c]
  apply Finset.sum_congr rfl
  intro i _
  have hmass : (μ.restrict (s i)).real univ ≠ 0 := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using! hm i
  have heq := cellMean_mul_mass (μ.restrict (s i)) w hmass
  simp only [Measure.real, Measure.restrict_apply_univ] at heq
  change (∫ x in s i, w x ∂μ) * c i = _
  rw [← heq]
  simp only [Measure.real]
  ring

theorem cellMean_step_pairing_tendsto (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (w : ℕ → X → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j)) (b c : ι → ℝ)
    (hb : ∀ i, Tendsto (fun j => cellMean ((μ j).restrict (s i)) (w j)) atTop (𝓝 (b i)))
    (hm : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (ν.real (s i))))
    (hpos : ∀ᶠ j in atTop, ∀ i, (μ j).real (s i) ≠ 0) :
    Tendsto (fun j => ∫ x, w j x * finiteStep s c x ∂μ j) atTop
      (𝓝 (∫ x, finiteStep s b x * finiteStep s c x ∂ν)) := by
  have hprod : (fun x => finiteStep s b x * finiteStep s c x) =
      finiteStep s (fun i => b i * c i) := by
    classical
    funext x
    by_cases hx : ∃ i, x ∈ s i
    · obtain ⟨i, hi⟩ := hx
      rw [finiteStep_eq_cell s b hd i x hi, finiteStep_eq_cell s c hd i x hi,
        finiteStep_eq_cell s _ hd i x hi]
    · have hn : ∀ i, x ∉ s i := fun i hi => hx ⟨i, hi⟩
      simp [finiteStep, hn]
  rw [hprod, integral_finiteStep ν s hs]
  have heq : (fun j => ∫ x, w j x * finiteStep s c x ∂μ j) =ᶠ[atTop]
      (fun j => ∑ i, (μ j).real (s i) * (cellMean ((μ j).restrict (s i)) (w j) * c i)) := by
    filter_upwards [hpos] with j hj
    exact integral_mul_finiteStep_cellMeans (μ j) s hs (w j) (hw j) c hj
  apply (tendsto_congr' heq).mpr
  exact tendsto_finsetSum _ fun i _ => (hm i).mul ((hb i).mul_const (c i))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SignedMomentConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem partition_signed_moment_tendsto
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i))
    (hd : ∀ k, Pairwise (Disjoint on s k))
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (B : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂μ j) ≤ B)
    (b c : ∀ k, ι k → ℝ)
    (hb : ∀ k i, Tendsto (fun j => cellMean ((μ j).restrict (s k i)) (w j))
      atTop (𝓝 (b k i)))
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (hpos : ∀ k, ∀ᶠ j in atTop, ∀ i, (μ j).real (s k i) ≠ 0)
    (limit : Lp ℝ 2 ν)
    (hlimit : Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
      (finiteStep (s k) (b k))) atTop (𝓝 limit))
    (ψ : X → ℝ) (hψ : MemLp ψ 2 ν) (hψj : ∀ j, MemLp ψ 2 (μ j))
    (htest : Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (c k)).toLp
      (finiteStep (s k) (c k))) atTop (𝓝 (hψ.toLp ψ)))
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (herr : ∀ k, ∀ᶠ j in atTop,
      (∫ x, (ψ x - finiteStep (s k) (c k) x) ^ 2 ∂μ j) ≤ η k) :
    Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop
      (𝓝 (∫ x, limit x * ψ x ∂ν)) := by
  have hpair : Tendsto (fun k => ∫ x, finiteStep (s k) (b k) x *
      finiteStep (s k) (c k) x ∂ν) atTop (𝓝 (∫ x, limit x * ψ x ∂ν)) := by
    have hl : inner ℝ limit (hψ.toLp ψ) = ∫ x, limit x * ψ x ∂ν := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with x hx
      rw [hx, real_scalar_inner_mul]
    have hinner := hlimit.inner (𝕜 := ℝ) htest
    simpa only [toLp_inner_eq_integral, hl] using! hinner
  apply tendsto_of_squared_approximation _
    (fun j k => ∫ x, w j x * finiteStep (s k) (c k) x ∂μ j)
    (fun k => ∫ x, finiteStep (s k) (b k) x * finiteStep (s k) (c k) x ∂ν)
    (fun k => B * η k) _ hpair
    (by simpa only [mul_zero] using! hη.const_mul B)
    (fun k => cellMean_step_pairing_tendsto μ ν (s k) (hs k) (hd k) w hw
      (b k) (c k) (hb k) (hm k) (hpos k))
  intro k
  filter_upwards [herr k] with j hj
  have htestNonneg : 0 ≤ ∫ x, (ψ x - finiteStep (s k) (c k) x) ^ 2 ∂μ j :=
    integral_nonneg fun x => sq_nonneg _
  have hworkNonneg : 0 ≤ ∫ x, w j x ^ 2 ∂μ j := integral_nonneg fun x => sq_nonneg _
  have hcs := integral_pairing_difference_sq_le (μ j) ψ (finiteStep (s k) (c k)) (w j)
    (hψj j) (finiteStep_memLp (μ j) (s k) (hs k) (c k)) (hw j)
  have hbound := hcs.trans (mul_le_mul hj (hB j) hworkNonneg (htestNonneg.trans hj))
  simpa only [mul_comm] using! hbound

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LipschitzMomentConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]

theorem lipschitz_partition_signed_moment_tendsto
    (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set X)
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ x ∂μ j, x ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ x ∂ν, x ∈ ⋃ i, s k i)
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (B : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂μ j) ≤ B)
    (b : ∀ k, ι k → ℝ)
    (hb : ∀ k i, Tendsto (fun j => cellMean ((μ j).restrict (s k i)) (w j))
      atTop (𝓝 (b k i)))
    (hm : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (hpos : ∀ k, ∀ᶠ j in atTop, ∀ i, (μ j).real (s k i) ≠ 0)
    (limit : Lp ℝ 2 ν)
    (hlimit : Tendsto (fun k => (finiteStep_memLp ν (s k) (hs k) (b k)).toLp
      (finiteStep (s k) (b k))) atTop (𝓝 limit))
    (z : ∀ k, ι k → X) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0)) (M : ℝ)
    (hmass : ∀ᶠ j in atTop, (μ j).real univ ≤ M)
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ x ∂(μ j).restrict (s k i),
      dist x (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ x ∂ν.restrict (s k i), dist x (z k i) ≤ r k)
    (ψ : X → ℝ) (K : ℝ≥0) (hLip : LipschitzWith K ψ)
    (hψ : MemLp ψ 2 ν) (hψj : ∀ j, MemLp ψ 2 (μ j)) :
    Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop
      (𝓝 (∫ x, limit x * ψ x ∂ν)) := by
  let c : ∀ k, ι k → ℝ := fun k i => ψ (z k i)
  have hscale (D : ℝ) : Tendsto (fun k => D * ((K : ℝ) * r k) ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using!
      ((hrzero.const_mul (K : ℝ)).pow 2).const_mul D
  have hνerror : Tendsto (fun k => ∫ x, (ψ x - finiteStep (s k) (c k) x) ^ 2 ∂ν)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg (fun x => sq_nonneg _))
      (fun k => lipschitz_step_test_error_le ν (s k) (hs k) (hd k) ψ hψ
        K hLip (z k) (r k) (hr k) (hcoverν k) (hcellν k))
      (hscale (ν.real univ))
  have hνerror' : Tendsto (fun k => ∫ x, (finiteStep (s k) (c k) x - ψ x) ^ 2 ∂ν)
      atTop (𝓝 0) := by
    convert! hνerror using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  have htest := L2_tendsto_of_squared_error ν (fun k => finiteStep (s k) (c k)) ψ
    (fun k => finiteStep_memLp ν (s k) (hs k) (c k)) hψ hνerror'
  apply partition_signed_moment_tendsto μ ν ι s hs hd w hw B hB b c hb hm hpos
    limit hlimit ψ hψ hψj htest (fun k => M * ((K : ℝ) * r k) ^ 2) (hscale M)
  intro k
  filter_upwards [hmass, hcell k] with j hjmass hjcell
  exact (lipschitz_step_test_error_le (μ j) (s k) (hs k) (hd k) ψ (hψj j)
    K hLip (z k) (r k) (hr k) (hcover k j) hjcell).trans
    (mul_le_mul_of_nonneg_right hjmass (sq_nonneg _))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CountableSignedLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem exists_common_localized_signed_limits {X : Type*} [MeasurableSpace X] [MetricSpace X]
    (μ : ℕ → ℕ → Measure X) (ν : ℕ → Measure X)
    [∀ H j, IsFiniteMeasure (μ H j)] [∀ H, IsFiniteMeasure (ν H)]
    (ι : ℕ → ℕ → Type*) [∀ H k, Fintype (ι H k)] (s : ∀ H k, ι H k → Set X)
    (hs : ∀ H k i, MeasurableSet (s H k i)) (hd : ∀ H k, Pairwise (Disjoint on s H k))
    (w : ℕ → ℕ → X → ℝ) (hw : ∀ H j, MemLp (w H j) 2 (μ H j))
    (B : ℕ → ℝ) (hB : ∀ H j, (∫ x, w H j x ^ 2 ∂μ H j) ≤ B H)
    (hm : ∀ H k i, Tendsto (fun j => (μ H j).real (s H k i)) atTop
      (𝓝 ((ν H).real (s H k i))))
    (hmpos : ∀ H k i, 0 < (ν H).real (s H k i))
    (hinter : ∀ H k l i t, Tendsto (fun j => (μ H j).real (s H k i ∩ s H l t)) atTop
      (𝓝 ((ν H).real (s H k i ∩ s H l t))))
    (δ : ℕ → ℕ → ℝ) (hδ : ∀ H, Tendsto (δ H) atTop (𝓝 0))
    (happrox : ∀ H k, ∀ᶠ j in atTop,
      (∫ x, (w H j x - partitionMean (μ H j) (s H k) (w H j) x) ^ 2 ∂μ H j) ≤ δ H k)
    (hcover : ∀ H k j, ∀ᵐ x ∂μ H j, x ∈ ⋃ i, s H k i)
    (hcoverν : ∀ H k, ∀ᵐ x ∂ν H, x ∈ ⋃ i, s H k i)
    (z : ∀ H k, ι H k → X) (r : ℕ → ℕ → ℝ) (hr : ∀ H k, 0 ≤ r H k)
    (hrzero : ∀ H, Tendsto (r H) atTop (𝓝 0)) (M : ℕ → ℝ)
    (htotal : ∀ H, ∀ᶠ j in atTop, (μ H j).real univ ≤ M H)
    (hcell : ∀ H k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ x ∂(μ H j).restrict (s H k i),
      dist x (z H k i) ≤ r H k)
    (hcellν : ∀ H k i, ∀ᵐ x ∂(ν H).restrict (s H k i), dist x (z H k i) ≤ r H k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ∀ H, Lp ℝ 2 (ν H),
      (∀ H, Tendsto (fun j => ∫ x, w H (φ j) x ^ 2 ∂μ H (φ j)) atTop (𝓝 (‖v H‖ ^ 2))) ∧
      ∀ H (ψ : X → ℝ) (L : ℝ≥0), LipschitzWith L ψ → MemLp ψ 2 (ν H) →
        (∀ j, MemLp ψ 2 (μ H (φ j))) →
        Tendsto (fun j => ∫ x, w H (φ j) x * ψ x ∂μ H (φ j)) atTop
          (𝓝 (∫ x, v H x * ψ x ∂ν H)) := by
  obtain ⟨φ, hφ, b, hb, v, hv, hsecond⟩ := exists_common_localized_L2_limits
    μ ν ι s hs hd w hw B hB hm hmpos hinter δ hδ happrox
  refine ⟨φ, hφ, v, hsecond, ?_⟩
  intro H ψ L hLip hψ hψj
  have hpos : ∀ k, ∀ᶠ j in atTop, ∀ i, (μ H (φ j)).real (s H k i) ≠ 0 := by
    intro k
    rw [Filter.eventually_all]
    intro i
    exact (((hm H k i).comp hφ.tendsto_atTop).eventually
      (lt_mem_nhds (hmpos H k i))).mono (fun _ hj => hj.ne')
  exact lipschitz_partition_signed_moment_tendsto (fun j => μ H (φ j)) (ν H)
    (ι H) (s H) (hs H) (hd H) (fun k j => hcover H k (φ j)) (hcoverν H)
    (fun j => w H (φ j)) (fun j => hw H (φ j)) (B H) (fun j => hB H (φ j))
    (b H) (hb H) (fun k i => (hm H k i).comp hφ.tendsto_atTop) hpos (v H) (hv H)
    (z H) (r H) (hr H) (hrzero H) (M H) (hφ.tendsto_atTop.eventually (htotal H))
    (fun k => hφ.tendsto_atTop.eventually (hcell H k)) (hcellν H) ψ L hLip hψ hψj

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellEnergyAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function

variable {X ι : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype ι]

theorem cell_variance_le_fractional_energy_of_ae_diameter (μ : Measure X)
    [IsFiniteMeasure μ] (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ)
    (hμ : 0 < μ.real univ) (r : ℝ)
    (hdiam : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, dist x y ≤ r)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2) (μ.prod μ)) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      r ^ (m + 1) / (2 * μ.real univ) *
        (∫ x, ∫ y, fractionalPairEnergy m w x y ∂μ ∂μ) := by
  apply cell_variance_le_energy_ae μ w hw hμ (fractionalPairEnergy m w)
    (r ^ (m + 1)) hE.prod_right_ae hE.integral_prod_left
  filter_upwards [hdiam] with x hx
  filter_upwards [hx] with y hy
  exact square_le_radius_mul_fractional_energy m w x y r hy

theorem cell_variance_le_scale_times_energy_ae (μ : Measure X)
    [IsFiniteMeasure μ] (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ)
    (a h c : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c)
    (hmass : c * h ^ m ≤ μ.real univ)
    (hdiam : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, dist x y ≤ a * h)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2) (μ.prod μ)) :
    (∫ x, (w x - cellMean μ w) ^ 2 ∂μ) ≤
      (a ^ (m + 1) / (2 * c) * h) *
        (∫ x, ∫ y, fractionalPairEnergy m w x y ∂μ ∂μ) := by
  have hμ : 0 < μ.real univ := lt_of_lt_of_le (by positivity) hmass
  exact (cell_variance_le_fractional_energy_of_ae_diameter μ m w hw hμ
    (a * h) hdiam hE).trans
    (mul_le_mul_of_nonneg_right (radius_mass_coefficient_le m a h c _ ha hh hc hmass)
      (integral_nonneg fun x => integral_nonneg fun y => fractionalPairEnergy_nonneg m w x y))

theorem partition_error_le_scale_times_energy_ae (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (m : ℕ) (w : X → ℝ) (hw : MemLp w 2 μ)
    (a h c : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hc : 0 < c)
    (hmass : ∀ i, c * h ^ m ≤ μ.real (s i))
    (hdiam : ∀ i, ∀ᵐ x ∂μ.restrict (s i), ∀ᵐ y ∂μ.restrict (s i), dist x y ≤ a * h)
    (hE : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2) (μ.prod μ)) :
    (∫ x in ⋃ i, s i, (w x - partitionMean μ s w x) ^ 2 ∂μ) ≤
      (a ^ (m + 1) / (2 * c) * h) *
        (∫ p : X × X, fractionalPairEnergy m w p.1 p.2 ∂μ.prod μ) := by
  have hi (i : ι) : Integrable (fun p : X × X => fractionalPairEnergy m w p.1 p.2)
      ((μ.restrict (s i)).prod (μ.restrict (s i))) := by
    rw [Measure.prod_restrict]
    exact hE.restrict
  have hm (i : ι) : c * h ^ m ≤ (μ.restrict (s i)).real univ := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using! hmass i
  rw [partition_error_eq_sum μ s hs hd w hw]
  calc
    _ ≤ ∑ i, (a ^ (m + 1) / (2 * c) * h) *
        (∫ x in s i, ∫ y in s i, fractionalPairEnergy m w x y ∂μ ∂μ) :=
      Finset.sum_le_sum fun i _ => cell_variance_le_scale_times_energy_ae
        (μ.restrict (s i)) m w (hw.restrict (s i)) a h c ha hh hc (hm i) (hdiam i) (hi i)
    _ = (a ^ (m + 1) / (2 * c) * h) *
        (∑ i, ∫ x in s i, ∫ y in s i, fractionalPairEnergy m w x y ∂μ ∂μ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_cell_energy_le μ s hs hd _ hE (fun p => fractionalPairEnergy_nonneg m w p.1 p.2))
      (by positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_CountableProjectionLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem exists_countable_projection_limits {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [Nonempty X]
    (I : ℕ → Box ι) (e : (ι → ℝ) → X) (π : X → ι → ℝ)
    (K : ℝ≥0) (he : LipschitzWith K e) (hπ : Continuous π) (hleft : LeftInverse π e)
    (μ : ℕ → ℕ → FiniteMeasure X)
    (hweak : ∀ H, Tendsto (μ H) atTop (𝓝 (boxPlaneFiniteMeasure (I H) e)))
    (hcoords : ∀ H j, ∀ᵐ x ∂(μ H j : Measure X), π x ∈ I H)
    (hheight : ∀ H k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(μ H j : Measure X), dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (w : ℕ → ℕ → X → ℝ) (hw : ∀ H j, MemLp (w H j) 2 (μ H j : Measure X))
    (B E : ℕ → ℝ) (hB : ∀ H j, (∫ x, w H j x ^ 2 ∂(μ H j : Measure X)) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : X × X => fractionalPairEnergy (Fintype.card ι) (w H j) q.1 q.2)
      ((μ H j : Measure X).prod (μ H j : Measure X)))
    (hE : ∀ H j, (∫ q : X × X, fractionalPairEnergy (Fintype.card ι) (w H j) q.1 q.2
      ∂(μ H j : Measure X).prod (μ H j : Measure X)) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ∀ H, Lp ℝ 2 (boxPlaneMeasure (I H) e),
      (∀ H, Tendsto (fun j => ∫ x, w H (φ j) x ^ 2 ∂(μ H (φ j) : Measure X)) atTop
        (𝓝 (‖v H‖ ^ 2))) ∧
      ∀ H (ψ : X → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
        MemLp ψ 2 (boxPlaneMeasure (I H) e) → (∀ j, MemLp ψ 2 (μ H (φ j) : Measure X)) →
        Tendsto (fun j => ∫ x, w H (φ j) x * ψ x ∂(μ H (φ j) : Measure X)) atTop
          (𝓝 (∫ x, v H x * ψ x ∂boxPlaneMeasure (I H) e)) := by
  let ν : ℕ → Measure X := fun H => boxPlaneMeasure (I H) e
  let s : ∀ H k, DyadicBoxIndex (I H) k → Set X := fun H => dyadicProjectionCell (I H) π
  let a : ℕ → ℝ := fun H => 2 * (1 + (K : ℝ) * boxWidthBound (I H))
  let c : ℕ → ℝ := fun H => (volume : Measure (ι → ℝ)).real (I H) / 2
  let δ : ℕ → ℕ → ℝ := fun H k =>
    (a H ^ (Fintype.card ι + 1) / (2 * c H) * (1 / 2 : ℝ) ^ k) * E H
  have ha : ∀ H, 0 ≤ a H := by
    intro H
    dsimp [a]
    positivity [boxWidthBound_nonneg (I H)]
  have hc : ∀ H, 0 < c H := fun H => half_pos (box_volume_real_pos (I H))
  have hδ : ∀ H, Tendsto (δ H) atTop (𝓝 0) := by
    intro H
    simpa only [mul_zero, zero_mul] using!
      (dyadic_box_scale_tendsto_zero.const_mul (a H ^ (Fintype.card ι + 1) / (2 * c H))).mul_const (E H)
  have hs : ∀ H k J, MeasurableSet (s H k J) :=
    fun H k J => dyadicProjectionCell_measurable (I H) π hπ.measurable k J
  have hd : ∀ H k, Pairwise (Disjoint on s H k) := fun H => dyadicProjectionCell_disjoint (I H) π
  have hcover : ∀ H k j, ∀ᵐ x ∂(μ H j : Measure X), x ∈ ⋃ J, s H k J :=
    fun H k j => dyadicProjectionCell_cover_ae (I H) π _ (hcoords H j) k
  have hboundary : ∀ H k J, ν H (frontier (s H k J)) = 0 :=
    fun H k J => dyadicProjectionCell_null_frontier (I H) e π he.continuous hπ hleft k J
  have hν : ∀ H, boxPlaneFiniteMeasure (I H) e ≠ 0 :=
    fun H => boxPlaneFiniteMeasure_ne_zero (I H) e he.continuous.measurable
  have hm : ∀ H k J, Tendsto (fun j => (μ H j : Measure X).real (s H k J)) atTop
      (𝓝 ((ν H).real (s H k J))) :=
    fun H k J => finiteMeasure_cell_mass_tendsto (μ H) (boxPlaneFiniteMeasure (I H) e)
      (hweak H) (hν H) (s H k J) (hboundary H k J)
  have hmpos : ∀ H k J, 0 < (ν H).real (s H k J) := by
    intro H k J
    change 0 < (boxPlaneMeasure (I H) e).real (dyadicProjectionCell (I H) π k J)
    rw [dyadicProjectionCell_mass (I H) e π he.continuous.measurable hπ.measurable hleft]
    exact mul_pos (box_volume_real_pos (I H)) (by positivity)
  have hinter : ∀ H k l J P, Tendsto (fun j => (μ H j : Measure X).real (s H k J ∩ s H l P))
      atTop (𝓝 ((ν H).real (s H k J ∩ s H l P))) :=
    fun H k l J P => finiteMeasure_cell_intersection_mass_tendsto (μ H)
      (boxPlaneFiniteMeasure (I H) e) (hweak H) (hν H) (s H k J) (s H l P)
      (hboundary H k J) (hboundary H l P)
  have hmass : ∀ H k, ∀ᶠ j in atTop, ∀ J : DyadicBoxIndex (I H) k,
      c H * ((1 / 2 : ℝ) ^ k) ^ Fintype.card ι ≤ (μ H j : Measure X).real (s H k J) :=
    fun H => dyadicProjectionCell_eventual_mass_lower (I H) e π he.continuous hπ hleft
      (μ H) (hweak H)
  have happrox : ∀ H k, ∀ᶠ j in atTop,
      (∫ x, (w H j x - partitionMean (μ H j : Measure X) (s H k) (w H j) x) ^ 2
        ∂(μ H j : Measure X)) ≤ δ H k := by
    intro H k
    filter_upwards [hmass H k, hheight H k] with j hjmass hjheight
    have hb := partition_error_le_scale_times_energy_ae (μ H j : Measure X) (s H k)
      (hs H k) (hd H k) (Fintype.card ι) (w H j) (hw H j) (a H) ((1 / 2 : ℝ) ^ k) (c H)
      (ha H) (by positivity) (hc H) hjmass
      (dyadicProjectionCell_ae_diameter (I H) e π hπ.measurable K he _ k hjheight) (henergy H j)
    rw [Measure.restrict_eq_self_of_ae_mem (hcover H k j)] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hE H j)
      (mul_nonneg (div_nonneg (pow_nonneg (ha H) _) (by positivity)) (by positivity)))
  let D : ℕ → ℝ := fun H => 1 + (K : ℝ) * boxWidthBound (I H)
  have hD : ∀ H, 0 ≤ D H := by
    intro H
    dsimp [D]
    positivity [boxWidthBound_nonneg (I H)]
  have hrzero : ∀ H, Tendsto (fun k : ℕ => D H * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    intro H
    simpa only [mul_zero] using! dyadic_box_scale_tendsto_zero.const_mul (D H)
  have htotal : ∀ H, ∀ᶠ j in atTop, (μ H j : Measure X).real univ ≤ (ν H).real univ + 1 := by
    intro H
    have ht : Tendsto (fun j => (μ H j : Measure X).real univ) atTop (𝓝 ((ν H).real univ)) :=
      NNReal.continuous_coe.continuousAt.tendsto.comp (hweak H).mass
    exact (ht.eventually (gt_mem_nhds (by linarith : (ν H).real univ <
      (ν H).real univ + 1))).mono (fun _ hj => hj.le)
  have hcoverν : ∀ H k, ∀ᵐ x ∂ν H, x ∈ ⋃ J, s H k J :=
    fun H k => dyadicProjectionCell_cover_ae (I H) π (ν H)
      (boxPlaneMeasure_ae_coordinates (I H) e π he.continuous.measurable hπ.measurable hleft) k
  have hcellν : ∀ H k J, ∀ᵐ x ∂(ν H).restrict (s H k J),
      dist x (e J.val.upper) ≤ D H * (1 / 2 : ℝ) ^ k := by
    intro H k J
    apply dyadicProjectionCell_ae_dist_reference (I H) e π hπ.measurable K he (ν H) k _ J
    filter_upwards [boxPlaneMeasure_ae_section (I H) e π he.continuous hπ hleft] with x hx
    rw [hx, dist_self]
    positivity
  apply exists_common_localized_signed_limits (fun H j => (μ H j : Measure X)) ν
    (fun H => DyadicBoxIndex (I H)) s hs hd w hw B hB hm hmpos hinter δ hδ happrox hcover hcoverν
    (fun _ _ J => e J.val.upper) (fun H k => D H * (1 / 2 : ℝ) ^ k)
    (fun H _ => mul_nonneg (hD H) (by positivity)) hrzero (fun H => (ν H).real univ + 1)
    htotal _ hcellν
  intro H k
  filter_upwards [hheight H k] with j hj
  exact dyadicProjectionCell_ae_dist_reference (I H) e π hπ.measurable K he _ k hj

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_GlobalProjectionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Global projection heights

Countable projection limits agree on open overlaps and glue to a measurable height on
the coordinate plane. The common subsequence preserves local second moments and
pairings with compactly supported Lipschitz tests.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem exists_global_projection_height {ι : Type*} [Fintype ι] {d : ℕ}
    (I : ℕ → Box ι) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) (s : ℕ → Set (Ambient d))
    (hs : ∀ H, IsOpen (s H)) (hcover : ∀ x, ∃ H, x ∈ s H)
    (μ : ℕ → ℕ → FiniteMeasure (Ambient d))
    (hrestrict : ∀ H j, (μ H j : Measure (Ambient d)) = (σ j).restrict (s H))
    (hplane : ∀ H, (coordinatePlaneMeasure e).restrict (s H) = boxPlaneMeasure (I H) e)
    (hweak : ∀ H, Tendsto (μ H) atTop (𝓝 (boxPlaneFiniteMeasure (I H) e)))
    (hcoords : ∀ H j, ∀ᵐ x ∂(μ H j : Measure (Ambient d)), π x ∈ I H)
    (hheight : ∀ H k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(μ H j : Measure (Ambient d)), dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (w : ℕ → Ambient d → ℝ) (hw : ∀ H j, MemLp (w j) 2 (μ H j : Measure (Ambient d)))
    (B E : ℕ → ℝ) (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(μ H j : Measure (Ambient d))) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (Fintype.card ι) (w j) q.1 q.2)
      ((μ H j : Measure (Ambient d)).prod (μ H j : Measure (Ambient d))))
    (hE : ∀ H j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (Fintype.card ι) (w j) q.1 q.2
      ∂(μ H j : Measure (Ambient d)).prod (μ H j : Measure (Ambient d))) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (s H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, w (φ j) x ^ 2 ∂(σ (φ j)).restrict (s H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (s H)))) ∧
      ∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(σ (φ j)).restrict (s H)) atTop
          (𝓝 (∫ x, f x * ψ x ∂(coordinatePlaneMeasure e).restrict (s H))) := by
  obtain ⟨φ, hφ, v, hsecond, hmoment⟩ := exists_countable_projection_limits I e π K he
    hπ.continuous hleft μ hweak hcoords hheight (fun _ j => w j) hw B E hB henergy hE
  let ν := coordinatePlaneMeasure e
  let : IsFiniteMeasureOnCompacts ν :=
    coordinatePlaneMeasure_finite_on_compacts e π he.continuous.measurable Q hπ hleft
  have hv : ∀ H, MemLp (fun x => v H x) 2 (ν.restrict (s H)) := by
    intro H
    rw [show ν.restrict (s H) = boxPlaneMeasure (I H) e from hplane H]
    exact Lp.memLp (v H)
  have hm : ∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
      Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(σ (φ j)).restrict (s H)) atTop
        (𝓝 (∫ x, v H x * ψ x ∂ν.restrict (s H))) := by
    intro H ψ L A _ hLip hA
    have hψ : MemLp ψ 2 (boxPlaneMeasure (I H) e) :=
      MemLp.of_bound hLip.continuous.aestronglyMeasurable A
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hA x)
    have hψj : ∀ j, MemLp ψ 2 (μ H (φ j) : Measure (Ambient d)) :=
      fun _ => MemLp.of_bound hLip.continuous.aestronglyMeasurable A
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hA x)
    rw [show ν.restrict (s H) = boxPlaneMeasure (I H) e from hplane H]
    simpa only [hrestrict] using! hmoment H ψ L hLip hψ hψj
  have hcompat : ∀ H J, (fun x => v H x) =ᵐ[ν.restrict (s H ∩ s J)] (fun x => v J x) := by
    intro H J
    exact local_L2_agreement_on_open_overlap (fun j => σ (φ j)) ν (s H) (s J) (hs H) (hs J)
      (v H) (v J) (hv H) (hv J) (fun j => w (φ j)) (hm H) (hm J)
  obtain ⟨f, hfm, hf⟩ := exists_measurable_glue_of_local_L2 ν s (fun H => (hs H).measurableSet)
    hcover (fun H x => v H x) (fun H => (Lp.stronglyMeasurable (v H)).measurable) hv hcompat
  refine ⟨φ, hφ, f, hfm, (fun H => (hf H).2), ?_, ?_⟩
  · intro H
    have hnorm : (∫ x, f x ^ 2 ∂ν.restrict (s H)) = ‖v H‖ ^ 2 := by
      calc
        _ = ∫ x, v H x ^ 2 ∂ν.restrict (s H) := by
          apply integral_congr_ae
          filter_upwards [(hf H).1] with x hx
          rw [hx]
        _ = ∫ x, v H x ^ 2 ∂boxPlaneMeasure (I H) e := by rw [hplane H]
        _ = ‖v H‖ ^ 2 := by
          symm
          simpa only [Lp.toLp_coeFn] using!
            toLp_norm_sq_eq_integral (boxPlaneMeasure (I H) e) (v H) (Lp.memLp (v H))
    rw [show (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (s H)) = ‖v H‖ ^ 2 from hnorm]
    simpa only [hrestrict] using! hsecond H
  · intro H ψ L A hc hLip hA
    have heq : (∫ x, f x * ψ x ∂ν.restrict (s H)) = ∫ x, v H x * ψ x ∂ν.restrict (s H) := by
      apply integral_congr_ae
      filter_upwards [(hf H).1] with x hx
      rw [hx]
    rw [show (∫ x, f x * ψ x ∂(coordinatePlaneMeasure e).restrict (s H)) =
      ∫ x, v H x * ψ x ∂ν.restrict (s H) from heq]
    exact hm H ψ L A hc hLip hA

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedGlobalHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_bounded_global_projection_height {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ Fintype.card ι / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (w : ℕ → Ambient d → ℝ)
    (hw : ∀ H j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B E : ℕ → ℝ)
    (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (Fintype.card ι) (w j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE : ∀ H j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (Fintype.card ι) (w j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, w (φ j) x ^ 2
        ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      ∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ x, w (φ j) x * ψ x
          ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) := by
  exact exists_global_projection_height (exhaustionBox ι) e π K Q he hπ hleft σ
    (boundedProjectionRegion π (e 0) K)
    (fun H => boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H)
    (boundedProjectionRegion_cover π (e 0) K)
    (fun H j => boundedProjectionFiniteMeasure (σ j) π (e 0) K H)
    (fun _ _ => rfl)
    (coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft)
    (boundedProjectionFiniteMeasure_tendsto e π K Q he hπ hleft σ hlocal)
    (fun H j => boundedProjectionRegion_ae_coordinates (σ j) π hπ.continuous (e 0) K H)
    (boundedProjectionFiniteMeasure_height_of_AD_lower e π K Q he hπ hleft σ hlocal C hC hlower hdiam)
    w hw B E hB henergy hE

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NearPairWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem nearPairSet_measurable {d : ℕ} (r : ℝ) :
    MeasurableSet (nearPairSet (d := d) r) :=
  measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const

theorem nearPairWeight_measurable {d : ℕ} (p : ℕ) (r : ℝ) :
    Measurable (nearPairWeight (d := d) p r) := by
  apply Measurable.indicator _ (nearPairSet_measurable r)
  unfold inverseDistancePow
  fun_prop

theorem nearPairWeight_nonneg {d : ℕ} (p : ℕ) (r : ℝ) (q : Ambient d × Ambient d) :
    0 ≤ nearPairWeight p r q :=
  indicator_nonneg (fun _ _ => inverseDistancePow_nonneg p _ _) q

theorem nearPairWeight_section {d : ℕ} (p : ℕ) (r : ℝ) (x : Ambient d) :
    (fun y => nearPairWeight p r (x, y)) =
      (closedBall x r).indicator (inverseDistancePow p x) := by
  funext y
  classical
  by_cases h : y ∈ closedBall x r
  · simp only [nearPairWeight, indicator_of_mem (show (x, y) ∈ nearPairSet r from h),
      indicator_of_mem h]
  · simp only [nearPairWeight, indicator_of_notMem (show (x, y) ∉ nearPairSet r from h),
      indicator_of_notMem h]

theorem nearPairWeight_section_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    Integrable (fun y => nearPairWeight p r (x, y)) μ := by
  rw [nearPairWeight_section]
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (inverseDistancePow_near_integrable_and_bound p C μ hg x r hr).1

theorem nearPairWeight_section_norm_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    (∫ y, ‖nearPairWeight p r (x, y)‖ ∂μ) ≤ 2 * (C * 2 ^ (p + 1) * 2 ^ p * r) := by
  simp_rw [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)]
  rw [nearPairWeight_section, integral_indicator measurableSet_closedBall]
  exact inverseDistancePow_near_integral_bound p C μ hg x r hr

theorem nearPairWeight_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) : Integrable (nearPairWeight p r) (μ.prod μ) := by
  have hmeas : AEStronglyMeasurable (nearPairWeight p r) (μ.prod μ) :=
    (nearPairWeight_measurable p r).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨Filter.Eventually.of_forall (nearPairWeight_section_integrable p C μ hg r hr), ?_⟩
  apply Integrable.of_bound hmeas.norm.integral_prod_right' (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact nearPairWeight_section_norm_bound p C μ hg r hr x

theorem nearPairWeight_integral_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) :
    (∫ q, nearPairWeight p r q ∂μ.prod μ) ≤
      μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) := by
  have hi := nearPairWeight_integrable p C μ hg r hr
  rw [integral_prod _ hi]
  have h := integral_mono hi.integral_prod_left
    (integrable_const (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))) (fun x => by
      simpa only [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)] using!
        nearPairWeight_section_norm_bound p C μ hg r hr x)
  simpa only [integral_const, smul_eq_mul] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function
open scoped NNReal

variable {d : ℕ}

theorem weightedDifference_measurable (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w) :
    Measurable (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) := by
  unfold weightedDifference
  fun_prop

theorem weightedDifference_sq (m : ℕ) (w : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y ^ 2 = fractionalPairEnergy m w x y := by
  rw [weightedDifference, div_pow, Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem weightedDifference_mul (m : ℕ) (w ψ : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y * weightedDifference m ψ x y = fractionalBilinear m w ψ x y := by
  rw [weightedDifference, weightedDifference, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem lipschitz_fractionalEnergy_bound (p : ℕ) (ψ : Ambient d → ℝ)
    (L : ℝ≥0) (hψ : LipschitzWith L ψ) (x y : Ambient d) :
    fractionalPairEnergy (p + 1) ψ x y ≤ (L : ℝ) ^ 2 * (dist x y ^ p)⁻¹ := by
  by_cases hxy : x = y
  · subst y
    simp only [fractionalPairEnergy, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    positivity
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hdiff : |ψ x - ψ y| ≤ (L : ℝ) * dist x y := by
      simpa only [Real.dist_eq] using! hψ.dist_le_mul x y
    have hsq : (ψ x - ψ y) ^ 2 ≤ (L : ℝ) ^ 2 * dist x y ^ 2 := by
      simpa only [sq_abs, mul_pow] using!
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg L.coe_nonneg dist_nonneg)).mpr hdiff
    calc
      _ ≤ ((L : ℝ) ^ 2 * dist x y ^ 2) / dist x y ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hsq (pow_nonneg dist_nonneg _)
      _ = _ := by
        rw [show p + 1 + 1 = p + 2 by omega, pow_add]
        field_simp

theorem weightedDifference_memLp (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w)
    (ρ : Measure (Ambient d × Ambient d))
    (hE : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m w q.1 q.2) ρ) :
    MemLp (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) 2 ρ := by
  apply (memLp_two_iff_integrable_sq (weightedDifference_measurable m w hw).aestronglyMeasurable).mpr
  simpa only [weightedDifference_sq] using! hE

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EnergyFromTruncations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

theorem nonnegative_integrable_of_exhaustion {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (s : ℕ → Set X) (hs : ∀ k, MeasurableSet (s k)) (hmono : Monotone s)
    (hcover : Function.support f ⊆ ⋃ k, s k)
    (hI : ∀ k, IntegrableOn f (s k) μ) (B : ℝ)
    (hB : ∀ k, (∫ x in s k, f x ∂μ) ≤ B) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hpos
  have hfull : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x in ⋃ k, s k, ENNReal.ofReal (f x) ∂μ := by
    rw [← lintegral_indicator (MeasurableSet.iUnion hs)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ⋃ k, s k
    · rw [indicator_of_mem hx]
    · have hfx : f x = 0 := by
        by_contra h
        exact hx (hcover h)
      rw [indicator_of_notMem hx, hfx, ENNReal.ofReal_zero]
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B := by
    rw [hfull, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    apply iSup_le
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hI k) (Filter.Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have hfin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ :=
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp hfin
  refine ⟨hint, ?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg hpos).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hbound

theorem fractionalEnergy_integrable_of_truncated_bounds {X : Type*}
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (ρ : Measure (X × X)) (m : ℕ) (w : X → ℝ) (hw : Measurable w)
    (hI : ∀ ε : ℝ, 0 < ε → IntegrableOn
      (fun q : X × X => fractionalPairEnergy m w q.1 q.2) {q | ε < dist q.1 q.2} ρ)
    (B : ℝ) (hB : ∀ ε : ℝ, 0 < ε →
      (∫ q in {q : X × X | ε < dist q.1 q.2}, fractionalPairEnergy m w q.1 q.2 ∂ρ) ≤ B) :
    Integrable (fun q : X × X => fractionalPairEnergy m w q.1 q.2) ρ ∧
      (∫ q : X × X, fractionalPairEnergy m w q.1 q.2 ∂ρ) ≤ B := by
  apply nonnegative_integrable_of_exhaustion ρ
    (fun q : X × X => fractionalPairEnergy m w q.1 q.2)
    (by unfold fractionalPairEnergy; fun_prop)
    (fun q => fractionalPairEnergy_nonneg m w q.1 q.2)
    (fun k : ℕ => {q : X × X | (1 / 2 : ℝ) ^ k < dist q.1 q.2})
    (fun _ => measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable)
    _ _ (fun k => hI _ (by positivity)) B (fun k => hB _ (by positivity))
  · intro k l hkl q hq
    have hp : (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl
    exact lt_of_le_of_lt hp hq
  · intro q hq
    have hne : q.1 ≠ q.2 := by
      intro h
      apply hq
      simp only [fractionalPairEnergy, h, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (dist_pos.mpr hne)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact mem_iUnion.mpr ⟨k, hk⟩

theorem pairwise_square_product_integrable {X : Type*}
    [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ) :
    Integrable (fun q : X × X => (w q.1 - w q.2) ^ 2) (μ.prod μ) := by
  have hdom := ((hL2.integrable_sq.comp_fst μ).add (hL2.integrable_sq.comp_snd μ)).const_mul 2
  apply hdom.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (w q.1 - w q.2) ^ 2 ≤ 2 * (w q.1 ^ 2 + w q.2 ^ 2)
  nlinarith [sq_nonneg (w q.1 + w q.2)]

theorem truncated_fractionalEnergy_integrable {X : Type*}
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] (m : ℕ)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun q : X × X => fractionalPairEnergy m w q.1 q.2)
      {q | ε < dist q.1 q.2} (μ.prod μ) := by
  have hs : MeasurableSet {q : X × X | ε < dist q.1 q.2} :=
    measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable
  have hm : Measurable (fun q : X × X => fractionalPairEnergy m w q.1 q.2) := by
    unfold fractionalPairEnergy
    fun_prop
  apply ((pairwise_square_product_integrable μ w hw hL2).const_mul ((ε ^ (m + 1))⁻¹)).restrict.mono'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs] with q hq
  rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _)]
  have hpow : (dist q.1 q.2 ^ (m + 1))⁻¹ ≤ (ε ^ (m + 1))⁻¹ := by
    simpa only [one_div] using! one_div_le_one_div_of_le (pow_pos hε (m + 1))
      (pow_le_pow_left₀ hε.le hq.le (m + 1))
  simpa only [fractionalPairEnergy, div_eq_mul_inv, mul_comm] using!
    mul_le_mul_of_nonneg_left hpow (sq_nonneg (w q.1 - w q.2))

theorem fractionalEnergy_integrable_of_uniform_bound {X : Type*}
    [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] (m : ℕ)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (B : ℝ) (hB : ∀ ε : ℝ, 0 < ε →
      (∫ q in {q : X × X | ε < dist q.1 q.2}, fractionalPairEnergy m w q.1 q.2
        ∂μ.prod μ) ≤ B) :
    Integrable (fun q : X × X => fractionalPairEnergy m w q.1 q.2) (μ.prod μ) ∧
      (∫ q : X × X, fractionalPairEnergy m w q.1 q.2 ∂μ.prod μ) ≤ B :=
  fractionalEnergy_integrable_of_truncated_bounds (μ.prod μ) m w hw
    (truncated_fractionalEnergy_integrable μ m w hw hL2) B hB

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ShellHeightL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# First-moment bounds on dyadic shells

Cauchy–Schwarz bounds an absolute first moment by the mass and second moment of
a finite measure. Applying this estimate to dyadic annuli combines upper growth
with shellwise second-moment decay to control the corresponding height integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem integral_abs_sq_le_mass_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w : X → ℝ) (hw : MemLp w 2 ν) :
    (∫ x, |w x| ∂ν) ^ 2 ≤ ν.real univ * (∫ x, w x ^ 2 ∂ν) := by
  have h := integral_mul_cauchy_schwarz_sq ν (fun x => ‖w x‖) (fun _ => (1 : ℝ))
    hw.norm (memLp_const 1)
  simpa only [mul_one, one_mul, one_pow, integral_const, smul_eq_mul, Real.norm_eq_abs,
    sq_abs, mul_comm] using! h

theorem integral_abs_le_of_mass_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w : X → ℝ) (hw : MemLp w 2 ν)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hmass : ν.real univ ≤ M) (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ M * A ^ 2) :
    (∫ x, |w x| ∂ν) ≤ M * A := by
  have hsq : (∫ x, |w x| ∂ν) ^ 2 ≤ (M * A) ^ 2 := by
    calc
      _ ≤ ν.real univ * (∫ x, w x ^ 2 ∂ν) := integral_abs_sq_le_mass_second_moment ν w hw
      _ ≤ M * (M * A ^ 2) := mul_le_mul hmass hsecond
        (integral_nonneg fun x => sq_nonneg _) hM
      _ = _ := by ring
  exact (sq_le_sq₀ (integral_nonneg fun x => abs_nonneg _) (mul_nonneg hM hA)).mp hsq

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalizedNormalTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem lipschitz_product_of_bound_on_support {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) (Kf Kg Bf Bg : ℝ≥0) (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, f x ≠ 0 → |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  by_cases hy : f y = 0
  · by_cases hx : f x = 0
    · simp only [hx, hy, zero_mul, dist_self]
      positivity
    · calc
        dist (f x * g x) (f y * g y) = |f x - f y| * |g x| := by
          simp only [hy, zero_mul, Real.dist_eq, sub_zero, abs_mul]
        _ ≤ ((Kf : ℝ) * dist x y) * (Bg : ℝ) :=
          mul_le_mul hf' (hBg x hx) (abs_nonneg _) (by positivity)
        _ ≤ ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          nlinarith [mul_nonneg (mul_nonneg Bf.coe_nonneg Kg.coe_nonneg) (dist_nonneg (x := x) (y := y))]
  · calc
      dist (f x * g x) (f y * g y) = |f x * (g x - g y) + (f x - f y) * g y| := by
        rw [Real.dist_eq]
        congr 1
        ring
      _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
        simpa only [abs_mul] using! abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
      _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) + ((Kf : ℝ) * dist x y) * (Bg : ℝ) :=
        add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
          (mul_le_mul hf' (hBg y hy) (abs_nonneg _) (by positivity))
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul] <;> ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedRegionTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem radialUnitCutoff_bounds {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d) :
    0 ≤ radialUnitCutoff a R x ∧ radialUnitCutoff a R x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem radialUnitCutoff_eq_one {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : dist x a ≤ R) : radialUnitCutoff a R x = 1 := by
  have h : (1 : ℝ) ≤ R + 1 - dist x a := by linarith
  simp only [radialUnitCutoff, min_eq_left h, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem radialUnitCutoff_support_bound {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : radialUnitCutoff a R x ≠ 0) : dist x a ≤ R + 1 := by
  by_contra h
  have hneg : R + 1 - dist x a < 0 := by linarith
  have hmin : min 1 (R + 1 - dist x a) ≤ 0 := (min_le_right _ _).trans hneg.le
  exact hx (max_eq_left hmin)

theorem radialUnitCutoff_lipschitz {d : ℕ} (a : Ambient d) (R : ℝ) :
    LipschitzWith 1 (radialUnitCutoff a R) := by
  have h : LipschitzWith 1 (fun x : Ambient d => R + 1 - dist x a) := by
    simpa using! (LipschitzWith.const (R + 1)).sub (LipschitzWith.dist_left a)
  exact (h.const_min 1).const_max 0

theorem radialUnitCutoff_hasCompactSupport {d : ℕ} (a : Ambient d) (R : ℝ) :
    HasCompactSupport (radialUnitCutoff a R) := by
  apply HasCompactSupport.intro (isCompact_closedBall a (R + 1))
  intro x hx
  by_contra h
  exact hx (radialUnitCutoff_support_bound a R x h)

theorem exists_compact_lipschitz_test_on_ball {d : ℕ} (a : Ambient d) (R : ℝ)
    (ψ : Ambient d → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) :
    ∃ (g : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport g ∧ LipschitzWith K g ∧
      (∀ x, |g x| ≤ (B : ℝ)) ∧ ∀ x ∈ ball a R, g x = ψ x := by
  let χ := radialUnitCutoff a R
  let B : ℝ≥0 := Real.toNNReal ((L : ℝ) * (R + 1) + |ψ a|)
  have hχ : LipschitzWith 1 χ := radialUnitCutoff_lipschitz a R
  have hχB : ∀ x, |χ x| ≤ (1 : ℝ≥0) := by
    intro x
    change |radialUnitCutoff a R x| ≤ 1
    rw [abs_of_nonneg (radialUnitCutoff_bounds a R x).1]
    exact (radialUnitCutoff_bounds a R x).2
  have hB : ∀ x, χ x ≠ 0 → |ψ x| ≤ (B : ℝ) := by
    intro x hx
    have hdist : dist x a ≤ R + 1 := radialUnitCutoff_support_bound a R x hx
    have hdiff : |ψ x - ψ a| ≤ (L : ℝ) * dist x a := by
      simpa only [Real.dist_eq] using! hψ.dist_le_mul x a
    calc
      |ψ x| ≤ |ψ x - ψ a| + |ψ a| := by simpa only [sub_add_cancel] using! abs_add_le (ψ x - ψ a) (ψ a)
      _ ≤ (L : ℝ) * (R + 1) + |ψ a| :=
        add_le_add (hdiff.trans (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)) le_rfl
      _ ≤ (B : ℝ) := Real.le_coe_toNNReal _
  refine ⟨fun x => χ x * ψ x, 1 * L + 1 * B, B,
    (radialUnitCutoff_hasCompactSupport a R).mul_right,
    lipschitz_product_of_bound_on_support χ ψ 1 L 1 B hχ hψ hχB hB, ?_, ?_⟩
  · intro x
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul, abs_zero]
      exact B.coe_nonneg
    · calc
        |χ x * ψ x| = |χ x| * |ψ x| := abs_mul _ _
        _ ≤ 1 * (B : ℝ) := mul_le_mul (hχB x) (hB x hx) (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
  · intro x hx
    change χ x * ψ x = ψ x
    rw [show χ x = 1 from radialUnitCutoff_eq_one a R x hx.le, one_mul]

theorem compact_moments_extend_on_ball {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (a : Ambient d) (R : ℝ)
    (hμ : ∀ j, ∀ᵐ x ∂μ j, x ∈ ball a R) (hν : ∀ᵐ x ∂ν, x ∈ ball a R)
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν))) :
    ∀ (ψ : Ambient d → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν)) := by
  intro ψ L hψ
  obtain ⟨g, K, B, hgc, hgLip, hgB, heq⟩ := exists_compact_lipschitz_test_on_ball a R ψ L hψ
  have hm : ∀ j, (∫ x, w j x * g x ∂μ j) = ∫ x, w j x * ψ x ∂μ j := by
    intro j
    apply integral_congr_ae
    filter_upwards [hμ j] with x hx
    rw [heq x hx]
  have hn : (∫ x, v x * g x ∂ν) = ∫ x, v x * ψ x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [heq x hx]
  simpa only [hm, hn] using! hmoment g K B hgc hgLip hgB

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NearBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Near-diagonal fractional bilinear bounds

On the near-pair region, Lipschitz control makes the test function's fractional energy
integrable under upper growth. Cauchy–Schwarz then bounds the absolute bilinear pairing
by the full energy of the other function and the near-pair inverse-distance integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem near_fractionalBilinear_integrable_and_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w ψ : Ambient d → ℝ) (hw : Measurable w) (L : ℝ≥0) (hψ : LipschitzWith L ψ)
    (henergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2) (μ.prod μ))
    (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w ψ q.1 q.2)
      (nearPairSet r) (μ.prod μ) ∧
      (∫ q in nearPairSet r, |fractionalBilinear (p + 1) w ψ q.1 q.2| ∂μ.prod μ) ^ 2 ≤
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) w q.1 q.2 ∂μ.prod μ) *
          ((L : ℝ) ^ 2 * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)))) := by
  let ρ : Measure (Ambient d × Ambient d) := (μ.prod μ).restrict (nearPairSet r)
  have hweak : Integrable (fun q : Ambient d × Ambient d => inverseDistancePow p q.1 q.2) ρ :=
    (integrable_indicator_iff (nearPairSet_measurable r)).mp
      (nearPairWeight_integrable p C μ hg r hr)
  have htestMeas : AEStronglyMeasurable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) ψ q.1 q.2) ρ := by
    have hψm : Measurable ψ := hψ.continuous.measurable
    apply Measurable.aestronglyMeasurable
    unfold fractionalPairEnergy
    fun_prop
  have htestEnergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) ψ q.1 q.2) ρ := by
    apply (hweak.const_mul ((L : ℝ) ^ 2)).mono' htestMeas
    apply Filter.Eventually.of_forall
    intro q
    rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _)]
    exact lipschitz_fractionalEnergy_bound p ψ L hψ q.1 q.2
  have hf := weightedDifference_memLp (p + 1) w hw ρ henergy.restrict
  have hgtest := weightedDifference_memLp (p + 1) ψ hψ.continuous.measurable ρ htestEnergy
  have hprod : MemLp (fun q : Ambient d × Ambient d =>
      weightedDifference (p + 1) w q.1 q.2 * weightedDifference (p + 1) ψ q.1 q.2) 1 ρ :=
    MemLp.mul' (hφ := hf) (hf := hgtest)
  have hcs := integral_mul_cauchy_schwarz_sq ρ
    (fun q => ‖weightedDifference (p + 1) w q.1 q.2‖)
    (fun q => ‖weightedDifference (p + 1) ψ q.1 q.2‖) hf.norm hgtest.norm
  simp only [Real.norm_eq_abs, ← abs_mul, weightedDifference_mul, sq_abs,
    weightedDifference_sq] at hcs
  have hwork : (∫ q, fractionalPairEnergy (p + 1) w q.1 q.2 ∂ρ) ≤
      ∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) w q.1 q.2 ∂μ.prod μ :=
    setIntegral_le_integral henergy
      (Filter.Eventually.of_forall fun q => fractionalPairEnergy_nonneg _ _ _ _)
  have hweakBound : (∫ q, inverseDistancePow p q.1 q.2 ∂ρ) ≤
      μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) := by
    change (∫ q in nearPairSet r, inverseDistancePow p q.1 q.2 ∂μ.prod μ) ≤ _
    rw [← integral_indicator (nearPairSet_measurable r)]
    exact nearPairWeight_integral_bound p C μ hg r hr
  have htestBound : (∫ q, fractionalPairEnergy (p + 1) ψ q.1 q.2 ∂ρ) ≤
      (L : ℝ) ^ 2 * (μ.real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))) := by
    have h := integral_mono htestEnergy (hweak.const_mul ((L : ℝ) ^ 2))
      (fun q => lipschitz_fractionalEnergy_bound p ψ L hψ q.1 q.2)
    rw [integral_const_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hweakBound (sq_nonneg _))
  refine ⟨?_, ?_⟩
  · simpa only [weightedDifference_mul] using! memLp_one_iff_integrable.mp hprod
  · exact hcs.trans (mul_le_mul hwork htestBound
      (integral_nonneg (fun q => fractionalPairEnergy_nonneg _ _ _ _))
      (integral_nonneg (fun q => fractionalPairEnergy_nonneg _ _ _ _)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_UniformNearBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped NNReal

theorem near_fractionalBilinear_uniformly_small {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasure (μ j)]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (w : ℕ → Ambient d → ℝ) (hw : ∀ j, Measurable (w j))
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j).prod (μ j)))
    (E M : ℝ)
    (hE : ∀ j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (w j) q.1 q.2 ∂(μ j).prod (μ j)) ≤ E)
    (hM : ∀ j, (μ j).real univ ≤ M)
    (ψ : Ambient d → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℕ, ∀ r : ℝ, 0 < r → r < δ →
      (∫ q in nearPairSet r, |fractionalBilinear (p + 1) (w j) ψ q.1 q.2|
        ∂(μ j).prod (μ j)) < ε := by
  have hC0 : 0 ≤ C := (hg 0).1
  have hE0 : 0 ≤ E :=
    (integral_nonneg (fun q => fractionalPairEnergy_nonneg (p + 1) (w 0) q.1 q.2)).trans (hE 0)
  have hM0 : 0 ≤ M := measureReal_nonneg.trans (hM 0)
  let D : ℝ := E * (L : ℝ) ^ 2 * M * (2 * C * 2 ^ (p + 1) * 2 ^ p)
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  intro ε hε
  refine ⟨ε ^ 2 / (D + 1), by positivity, ?_⟩
  intro j r hr hsmall
  have hb : (∫ q in nearPairSet r, |fractionalBilinear (p + 1) (w j) ψ q.1 q.2|
      ∂(μ j).prod (μ j)) ^ 2 ≤ D * r := by
    calc
      _ ≤ (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
          ∂(μ j).prod (μ j)) *
          ((L : ℝ) ^ 2 * ((μ j).real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)))) :=
        (near_fractionalBilinear_integrable_and_bound p C (μ j) (hg j) (w j) ψ (hw j)
          L hψ (henergy j) r hr).2
      _ ≤ E * ((L : ℝ) ^ 2 * (M * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)))) := by
        apply mul_le_mul (hE j) _ (by positivity) hE0
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hM j) (by positivity)) (sq_nonneg _)
      _ = _ := by dsimp [D] <;> ring
  have hs : r * (D + 1) < ε ^ 2 := (lt_div_iff₀ (by positivity : 0 < D + 1)).mp hsmall
  nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedBilinearKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Function
open scoped NNReal

theorem cappedInverseDistancePow_eq {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) (h : ε ≤ dist q.1 q.2) :
    cappedInverseDistancePow m ε q = (dist q.1 q.2 ^ m)⁻¹ := by
  simp only [cappedInverseDistancePow, max_eq_right h]

theorem cappedInverseDistancePow_swap {X : Type*} [PseudoMetricSpace X]
    (m : ℕ) (ε : ℝ) (q : X × X) :
    cappedInverseDistancePow m ε q.swap = cappedInverseDistancePow m ε q := by
  simp only [cappedInverseDistancePow, Prod.swap, dist_comm]

theorem cappedTestKernel_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (B : ℝ≥0) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (q : Ambient d × Ambient d) :
    |cappedTestKernel m ε φ q| ≤ (2 * (B : ℝ)) * (ε ^ (m + 1))⁻¹ := by
  unfold cappedTestKernel
  rw [abs_mul]
  have hd : |φ q.1 - φ q.2| ≤ 2 * (B : ℝ) := by
    have h := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith [hB q.1, hB q.2]
  exact mul_le_mul hd (cappedInverseDistancePow_bound (m + 1) ε hε q) (abs_nonneg _) (by positivity)

theorem cappedTestKernel_lipschitz {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    LipschitzWith
      ((2 * B) * Real.toNNReal (2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹) +
        (L + L) * Real.toNNReal ((ε ^ (m + 1))⁻¹)) (cappedTestKernel m ε φ) := by
  have hdiff : LipschitzWith (L + L) (fun q : Ambient d × Ambient d => φ q.1 - φ q.2) := by
    simpa only [mul_one] using! (hφ.comp LipschitzWith.prod_fst).sub (hφ.comp LipschitzWith.prod_snd)
  apply lipschitz_bounded_product_real hdiff (cappedInverseDistancePow_lipschitz m ε hε)
  · intro q
    have h := abs_sub_le (φ q.1) 0 (φ q.2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [hB q.1, hB q.2]
  · intro q
    exact (cappedInverseDistancePow_bound (m + 1) ε hε q).trans (Real.le_coe_toNNReal _)

theorem cappedTestKernel_antisymm {d : ℕ} (m : ℕ) (ε : ℝ) (φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : cappedTestKernel m ε φ q.swap = -cappedTestKernel m ε φ q := by
  unfold cappedTestKernel
  rw [cappedInverseDistancePow_swap]
  dsimp only [Prod.swap]
  ring

theorem capped_bilinear_eq_outside {d : ℕ} (m : ℕ) (ε : ℝ) (w φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) (h : ε ≤ dist q.1 q.2) :
    (w q.1 - w q.2) * cappedTestKernel m ε φ q = fractionalBilinear m w φ q.1 q.2 := by
  unfold cappedTestKernel fractionalBilinear
  rw [cappedInverseDistancePow_eq _ _ _ h]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SignedKernelConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of signed weighted kernel integrals

Finite step approximations in the second variable reduce weighted product
integrals to sums of weighted moments and cell masses. Integrable absolute
weights and Lipschitz kernel bounds control the approximation error, allowing
convergence of these finite sums to pass to the original kernel integrals.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integrable_weighted_bounded_function (μ : Measure X) (w f : X → ℝ)
    (hw : Integrable w μ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    Integrable (fun x => w x * f x) μ := by
  apply (hw.abs.mul_const B).mono' (hw.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖w x * f x‖ ≤ |w x| * B
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg (w x))

theorem integrable_weighted_product_kernel (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (F : X × Y → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    Integrable (fun q : X × Y => w q.1 * F q) (μ.prod ν) := by
  have hdom := (hw.abs.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const B
  apply hdom.mono' (hw.aestronglyMeasurable.comp_fst.mul hF.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro q
  change ‖w q.1 * F q‖ ≤ (|w q.1| * 1) * B
  rw [Real.norm_eq_abs, abs_mul, mul_one]
  exact mul_le_mul_of_nonneg_left (hB q) (abs_nonneg (w q.1))

variable [Fintype ι]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem weighted_secondVariableStep_eq_sum (s : ι → Set Y) (z : ι → Y)
    (w : X → ℝ) (F : X × Y → ℝ) (q : X × Y) :
    w q.1 * secondVariableStep s z F q =
      ∑ i, (w q.1 * F (q.1, z i)) * (s i).indicator (fun _ => (1 : ℝ)) q.2 := by
  classical
  unfold secondVariableStep finiteStep
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : q.2 ∈ s i
  · simp only [indicator_of_mem h, mul_one]
  · simp only [indicator_of_notMem h, mul_zero]

theorem integrable_weighted_secondVariableStep (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (s : ι → Set Y) (hs : ∀ i, MeasurableSet (s i)) (z : ι → Y)
    (F : X × Y → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    Integrable (fun q : X × Y => w q.1 * secondVariableStep s z F q) (μ.prod ν) := by
  classical
  simp_rw [weighted_secondVariableStep_eq_sum]
  apply integrable_finsetSum
  intro i _
  exact (integrable_weighted_bounded_function μ w (fun x => F (x, z i)) hw
    (hF.comp (measurable_id.prodMk measurable_const)) B (fun x => hB (x, z i))).mul_prod
      ((integrable_const (μ := ν) (1 : ℝ)).indicator (hs i))

theorem integral_weighted_secondVariableStep (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (s : ι → Set Y) (hs : ∀ i, MeasurableSet (s i)) (z : ι → Y)
    (F : X × Y → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    (∫ q : X × Y, w q.1 * secondVariableStep s z F q ∂μ.prod ν) =
      ∑ i, (∫ x, w x * F (x, z i) ∂μ) * ν.real (s i) := by
  classical
  simp_rw [weighted_secondVariableStep_eq_sum]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_weighted_bounded_function μ w (fun x => F (x, z i)) hw
      (hF.comp (measurable_id.prodMk measurable_const)) B (fun x => hB (x, z i))).mul_prod
        ((integrable_const (μ := ν) (1 : ℝ)).indicator (hs i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod_mul (fun x => w x * F (x, z i)) ((s i).indicator (fun _ => (1 : ℝ)))]
  simp only [integral_indicator (hs i), setIntegral_const, smul_eq_mul, mul_one]

variable [MetricSpace X] [MetricSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y]

theorem weighted_secondVariableStep_error (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [IsFiniteMeasure ν] (w : X → ℝ) (hw : Integrable w μ)
    (s : ι → Set Y) (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (z : ι → Y) (r : ℝ)
    (hcover : ∀ᵐ y ∂ν, y ∈ ⋃ i, s i)
    (hcell : ∀ i, ∀ᵐ y ∂ν.restrict (s i), dist y (z i) ≤ r)
    (F : X × Y → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F)
    (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    |(∫ q : X × Y, w q.1 * F q ∂μ.prod ν) -
      ∫ q : X × Y, w q.1 * secondVariableStep s z F q ∂μ.prod ν| ≤
        ((∫ x, |w x| ∂μ) * ν.real univ) * ((K : ℝ) * r) := by
  have hkernel := integrable_weighted_product_kernel μ ν w hw F hF.continuous.measurable B hB
  have hstep := integrable_weighted_secondVariableStep μ ν w hw s hs z F hF.continuous.measurable B hB
  have hdom := (hw.abs.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const ((K : ℝ) * r)
  have hcells : ∀ᵐ y ∂ν, ∀ i, y ∈ s i → dist y (z i) ≤ r :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hs i)).mp (hcell i))
  have hpoint : ∀ᵐ q : X × Y ∂μ.prod ν,
      |w q.1 * F q - w q.1 * secondVariableStep s z F q| ≤
        (|w q.1| * 1) * ((K : ℝ) * r) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hcover,
      Measure.quasiMeasurePreserving_snd.ae hcells] with q hq hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    have hdist : |F q - F (q.1, z i)| ≤ (K : ℝ) * r := by
      have h := hF.dist_le_mul q (q.1, z i)
      rw [show q = (q.1, q.2) from rfl, dist_prod_same_left] at h
      simpa only [Real.dist_eq] using! h.trans (mul_le_mul_of_nonneg_left (hc i hi) K.coe_nonneg)
    change |w q.1 * F q - w q.1 * finiteStep s (fun j => F (q.1, z j)) q.2| ≤ _
    rw [finiteStep_eq_cell s _ hd i q.2 hi, ← mul_sub, abs_mul, mul_one]
    exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
  rw [← integral_sub hkernel hstep]
  calc
    _ ≤ ∫ q : X × Y, |w q.1 * F q - w q.1 * secondVariableStep s z F q| ∂μ.prod ν :=
      abs_integral_le_integral_abs
    _ ≤ ∫ q : X × Y, (|w q.1| * 1) * ((K : ℝ) * r) ∂μ.prod ν :=
      integral_mono_ae (hkernel.sub hstep).abs hdom hpoint
    _ = _ := by
      rw [integral_mul_const, integral_prod_mul (fun x => |w x|) (fun _ : Y => (1 : ℝ)), integral_const]
      simp only [smul_eq_mul, mul_one]

omit [Fintype ι] in

theorem weighted_product_kernel_tendsto
    (μ : ℕ → Measure X) (μ₀ : Measure X) (ν : ℕ → Measure Y) (ν₀ : Measure Y)
    [∀ j, SFinite (μ j)] [SFinite μ₀] [∀ j, IsFiniteMeasure (ν j)] [IsFiniteMeasure ν₀]
    (w : ℕ → X → ℝ) (v : X → ℝ) (hw : ∀ j, Integrable (w j) (μ j)) (hv : Integrable v μ₀)
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set Y)
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂ν j, y ∈ ⋃ i, s k i)
    (hcover₀ : ∀ k, ∀ᵐ y ∂ν₀, y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Y) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(ν j).restrict (s k i), dist y (z k i) ≤ r k)
    (hcell₀ : ∀ k i, ∀ᵐ y ∂ν₀.restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (ν j).real (s k i)) atTop (𝓝 (ν₀.real (s k i))))
    (W M : ℝ) (hW : 0 ≤ W) (hM : 0 ≤ M)
    (hweight : ∀ᶠ j in atTop, (∫ x, |w j x| ∂μ j) ≤ W)
    (htotal : ∀ᶠ j in atTop, (ν j).real univ ≤ M)
    (F : X × Y → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F)
    (B : ℝ) (hB : ∀ q, |F q| ≤ B)
    (hmoment : ∀ y, Tendsto (fun j => ∫ x, w j x * F (x, y) ∂μ j) atTop
      (𝓝 (∫ x, v x * F (x, y) ∂μ₀))) :
    Tendsto (fun j => ∫ q : X × Y, w j q.1 * F q ∂(μ j).prod (ν j)) atTop
      (𝓝 (∫ q : X × Y, v q.1 * F q ∂μ₀.prod ν₀)) := by
  let P := fun j k => ∫ q : X × Y, w j q.1 * secondVariableStep (s k) (z k) F q
    ∂(μ j).prod (ν j)
  let V := fun k => ∫ q : X × Y, v q.1 * secondVariableStep (s k) (z k) F q ∂μ₀.prod ν₀
  have hV : Tendsto V atTop (𝓝 (∫ q : X × Y, v q.1 * F q ∂μ₀.prod ν₀)) := by
    have hscale : Tendsto (fun k => ((∫ x, |v x| ∂μ₀) * ν₀.real univ) * ((K : ℝ) * r k))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using! (hrzero.const_mul (K : ℝ)).const_mul
        ((∫ x, |v x| ∂μ₀) * ν₀.real univ)
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hscale.eventually (gt_mem_nhds hε)] with k hk
    rw [Real.dist_eq, abs_sub_comm]
    exact (weighted_secondVariableStep_error μ₀ ν₀ v hv (s k) (hs k) (hd k) (z k) (r k)
      (hcover₀ k) (hcell₀ k) F K hF B hB).trans_lt hk
  have hP : ∀ k, Tendsto (fun j => P j k) atTop (𝓝 (V k)) := by
    intro k
    dsimp only [P, V]
    simp_rw [integral_weighted_secondVariableStep _ _ _ (hw _) (s k) (hs k) (z k)
      F hF.continuous.measurable B hB,
      integral_weighted_secondVariableStep μ₀ ν₀ v hv (s k) (hs k) (z k)
        F hF.continuous.measurable B hB]
    exact tendsto_finsetSum _ fun i _ => (hmoment (z k i)).mul (hmass k i)
  apply tendsto_of_squared_approximation _ P V (fun k => (W * M * ((K : ℝ) * r k)) ^ 2) _ hV
    (by simpa only [mul_zero, zero_pow two_ne_zero] using!
      (((hrzero.const_mul (K : ℝ)).const_mul (W * M)).pow 2)) hP
  intro k
  filter_upwards [hweight, htotal, hcell k] with j hjW hjM hjcell
  have herr := weighted_secondVariableStep_error (μ j) (ν j) (w j) (hw j)
    (s k) (hs k) (hd k) (z k) (r k) (hcover k j) hjcell F K hF B hB
  have hcoef : ((∫ x, |w j x| ∂μ j) * (ν j).real univ) * ((K : ℝ) * r k) ≤
      W * M * ((K : ℝ) * r k) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul hjW hjM (by positivity) hW)
      (mul_nonneg K.coe_nonneg (hr k))
  have hnonneg : 0 ≤ W * M * ((K : ℝ) * r k) :=
    mul_nonneg (mul_nonneg hW hM) (mul_nonneg K.coe_nonneg (hr k))
  simpa only [sq_abs] using! (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr (herr.trans hcoef)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CappedBilinearConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem antisymmetric_kernel_pairing {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : X → ℝ) (hw : Integrable w μ)
    (F : X × X → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ q, |F q| ≤ B)
    (hanti : ∀ q, F q.swap = -F q) :
    Integrable (fun q : X × X => (w q.1 - w q.2) * F q) (μ.prod μ) ∧
      (∫ q : X × X, (w q.1 - w q.2) * F q ∂μ.prod μ) =
        2 * ∫ q : X × X, w q.1 * F q ∂μ.prod μ := by
  have hi := integrable_weighted_product_kernel μ μ w hw F hF B hB
  have hswap : Integrable (fun q : X × X => w q.2 * F q.swap) (μ.prod μ) := hi.swap
  have heq : (fun q : X × X => (w q.1 - w q.2) * F q) =
      fun q => w q.1 * F q + w q.2 * F q.swap := by
    funext q
    rw [hanti q]
    ring
  refine ⟨heq ▸ hi.add hswap, ?_⟩
  rw [heq, integral_add hi hswap]
  have hswapInt : (∫ q : X × X, w q.2 * F q.swap ∂μ.prod μ) =
      ∫ q : X × X, w q.1 * F q ∂μ.prod μ :=
    integral_prod_swap (fun q : X × X => w q.1 * F q)
  rw [hswapInt]
  ring

theorem capped_bilinear_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j)) (hv : MemLp v 2 ν)
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂μ j, y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂ν, y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j).restrict (s k i), dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂ν.restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j).real (s k i)) atTop (𝓝 (ν.real (s k i))))
    (M : ℝ) (hM : 0 ≤ M)
    (htotal : ∀ᶠ j in atTop, (μ j).real univ ≤ M)
    (hsecond : ∀ᶠ j in atTop, (∫ x, w j x ^ 2 ∂μ j) ≤ M)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (D : ℝ≥0), LipschitzWith D ψ →
      MemLp ψ 2 ν → (∀ j, MemLp ψ 2 (μ j)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν)))
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (φ : Ambient d → ℝ) (L B : ℝ≥0)
    (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ)) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      (w j q.1 - w j q.2) * cappedTestKernel m ε φ q ∂(μ j).prod (μ j)) atTop
      (𝓝 (∫ q : Ambient d × Ambient d,
        (v q.1 - v q.2) * cappedTestKernel m ε φ q ∂ν.prod ν)) := by
  let F := cappedTestKernel m ε φ
  let D := (2 * B) * Real.toNNReal (2 * (m + 1 : ℝ) * (ε ^ (m + 2))⁻¹) +
    (L + L) * Real.toNNReal ((ε ^ (m + 1))⁻¹)
  let Q := (2 * (B : ℝ)) * (ε ^ (m + 1))⁻¹
  have hF : LipschitzWith D F := cappedTestKernel_lipschitz m ε hε φ L B hφ hB
  have hQ : ∀ q, |F q| ≤ Q := cappedTestKernel_bound m ε hε φ B hB
  have hwI : ∀ j, Integrable (w j) (μ j) := fun j => (hw j).integrable (by norm_num)
  have hvI : Integrable v ν := hv.integrable (by norm_num)
  have hweight : ∀ᶠ j in atTop, (∫ x, |w j x| ∂μ j) ≤ M := by
    filter_upwards [htotal, hsecond] with j hjmass hjsecond
    simpa only [one_pow, mul_one] using! integral_abs_le_of_mass_second_moment
      (μ j) (w j) (hw j) M 1 hM (by norm_num) hjmass
        (by simpa only [one_pow, mul_one] using! hjsecond)
  have hslices : ∀ y, Tendsto (fun j => ∫ x, w j x * F (x, y) ∂μ j) atTop
      (𝓝 (∫ x, v x * F (x, y) ∂ν)) := by
    intro y
    have hLip : LipschitzWith D (fun x => F (x, y)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x x'
      simpa only [dist_prod_same_right] using! hF.dist_le_mul (x, y) (x', y)
    have hmem (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] : MemLp (fun x => F (x, y)) 2 ρ :=
      MemLp.of_bound hLip.continuous.measurable.aestronglyMeasurable Q
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hQ (x, y))
    exact hmoment (fun x => F (x, y)) D hLip (hmem ν) (fun j => hmem (μ j))
  have hprod := weighted_product_kernel_tendsto μ ν μ ν w v hwI hvI
    ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M M hM hM
    hweight htotal F D hF Q hQ hslices
  have hanti : ∀ q, F q.swap = -F q := cappedTestKernel_antisymm m ε φ
  have heq (ρ : Measure (Ambient d)) [IsFiniteMeasure ρ] (u : Ambient d → ℝ)
      (hu : Integrable u ρ) :
      (∫ q : Ambient d × Ambient d, (u q.1 - u q.2) * F q ∂ρ.prod ρ) =
        2 * ∫ q : Ambient d × Ambient d, u q.1 * F q ∂ρ.prod ρ :=
    (antisymmetric_kernel_pairing ρ u hu F hF.continuous.measurable Q hQ hanti).2
  have heqj : ∀ j, (∫ q : Ambient d × Ambient d,
      (w j q.1 - w j q.2) * cappedTestKernel m ε φ q ∂(μ j).prod (μ j)) =
        2 * ∫ q : Ambient d × Ambient d, w j q.1 * F q ∂(μ j).prod (μ j) :=
    fun j => heq (μ j) (w j) (hwI j)
  have heqν := heq ν v hvI
  change Tendsto (fun j => ∫ q : Ambient d × Ambient d,
    (w j q.1 - w j q.2) * F q ∂(μ j).prod (μ j)) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, (v q.1 - v q.2) * F q ∂ν.prod ν))
  rw [heqν]
  exact (hprod.const_mul 2).congr' (Filter.Eventually.of_forall fun j => (heqj j).symm)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedBilinearError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem capped_bilinear_error_pointwise {d : ℕ} (m : ℕ) (ε : ℝ)
    (w φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    |fractionalBilinear m w φ q.1 q.2 - (w q.1 - w q.2) * cappedTestKernel m ε φ q| ≤
      (nearPairSet ε).indicator (fun q => |fractionalBilinear m w φ q.1 q.2|) q := by
  classical
  by_cases hnear : q ∈ nearPairSet ε
  · rw [indicator_of_mem hnear]
    by_cases hdiag : q.1 = q.2
    · simp only [hdiag, fractionalBilinear, cappedTestKernel, sub_self, zero_mul, zero_div,
        abs_zero, le_refl]
    · have hd : 0 < dist q.1 q.2 := dist_pos.mpr hdiag
      have hcap : cappedInverseDistancePow (m + 1) ε q ≤ (dist q.1 q.2 ^ (m + 1))⁻¹ := by
        exact inv_anti₀ (pow_pos hd _) (pow_le_pow_left₀ hd.le (le_max_right _ _) _)
      have hdiff : 0 ≤ (dist q.1 q.2 ^ (m + 1))⁻¹ - cappedInverseDistancePow (m + 1) ε q :=
        sub_nonneg.mpr hcap
      have heq : fractionalBilinear m w φ q.1 q.2 - (w q.1 - w q.2) * cappedTestKernel m ε φ q =
          ((w q.1 - w q.2) * (φ q.1 - φ q.2)) *
            ((dist q.1 q.2 ^ (m + 1))⁻¹ - cappedInverseDistancePow (m + 1) ε q) := by
        unfold fractionalBilinear cappedTestKernel
        ring
      rw [heq, abs_mul, abs_of_nonneg hdiff]
      calc
        _ ≤ |(w q.1 - w q.2) * (φ q.1 - φ q.2)| * (dist q.1 q.2 ^ (m + 1))⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (sub_le_self _ (cappedInverseDistancePow_nonneg (m + 1) ε q)) (abs_nonneg _)
        _ = _ := by
          simp only [fractionalBilinear, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hd _))]
  · rw [indicator_of_notMem hnear]
    have hd : ε ≤ dist q.1 q.2 := by
      have hn : ¬dist q.2 q.1 ≤ ε := hnear
      simpa only [dist_comm q.2 q.1] using! (lt_of_not_ge hn).le
    rw [capped_bilinear_eq_outside m ε w φ q hd, sub_self, abs_zero]

theorem fractional_bilinear_integrable_and_cap_error {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w φ : Ambient d → ℝ) (hw : Measurable w) (hwI : Integrable w μ)
    (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (henergy : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2) (μ.prod μ))
    (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w φ q.1 q.2) (μ.prod μ) ∧
      |(∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) w φ q.1 q.2 ∂μ.prod μ) -
        ∫ q : Ambient d × Ambient d, (w q.1 - w q.2) * cappedTestKernel (p + 1) ε φ q ∂μ.prod μ| ≤
          ∫ q in nearPairSet ε, |fractionalBilinear (p + 1) w φ q.1 q.2| ∂μ.prod μ := by
  let F := fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w φ q.1 q.2
  let G := fun q : Ambient d × Ambient d => (w q.1 - w q.2) * cappedTestKernel (p + 1) ε φ q
  have hFmeas : Measurable F := by
    dsimp only [F]
    unfold fractionalBilinear
    have hφm := hφ.continuous.measurable
    fun_prop
  have hGkernel := cappedTestKernel_lipschitz (p + 1) ε hε φ L B hφ hB
  have hG : Integrable G (μ.prod μ) :=
    (antisymmetric_kernel_pairing μ w hwI (cappedTestKernel (p + 1) ε φ)
      hGkernel.continuous.measurable ((2 * (B : ℝ)) * (ε ^ (p + 1 + 1))⁻¹)
      (cappedTestKernel_bound (p + 1) ε hε φ B hB) (cappedTestKernel_antisymm (p + 1) ε φ)).1
  have hnear : IntegrableOn F (nearPairSet ε) (μ.prod μ) :=
    (near_fractionalBilinear_integrable_and_bound p C μ hg w φ hw L hφ henergy ε hε).1
  have hdom : Integrable ((nearPairSet ε).indicator (fun q => |F q|)) (μ.prod μ) :=
    (integrable_indicator_iff (nearPairSet_measurable ε)).mpr hnear.abs
  have herr : Integrable (fun q => F q - G q) (μ.prod μ) := by
    apply hdom.mono' (hFmeas.aestronglyMeasurable.sub hG.aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro q
    simpa only [Real.norm_eq_abs] using! capped_bilinear_error_pointwise (p + 1) ε w φ q
  have hF : Integrable F (μ.prod μ) := by
    have heq : F = fun q => (F q - G q) + G q := by funext q; ring
    rw [heq]
    exact herr.add hG
  refine ⟨hF, ?_⟩
  change |(∫ q, F q ∂μ.prod μ) - ∫ q, G q ∂μ.prod μ| ≤ ∫ q in nearPairSet ε, |F q| ∂μ.prod μ
  rw [← integral_sub hF hG, ← integral_indicator (nearPairSet_measurable ε)]
  calc
    _ ≤ ∫ q, |F q - G q| ∂μ.prod μ := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono_ae herr.abs hdom
      (Filter.Eventually.of_forall fun q => capped_bilinear_error_pointwise (p + 1) ε w φ q)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CappedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem cappedWeightedDifference_sq {d : ℕ} (m : ℕ) (ε : ℝ) (w : Ambient d → ℝ)
    (q : Ambient d × Ambient d) :
    cappedWeightedDifference m ε w q ^ 2 = cappedPairEnergy m ε w q := by
  rw [cappedWeightedDifference, mul_pow, Real.sq_sqrt (cappedInverseDistancePow_nonneg (m + 1) ε q)]
  exact mul_comm _ _

theorem cappedWeightedDifference_mul {d : ℕ} (m : ℕ) (ε : ℝ) (w g : Ambient d → ℝ)
    (q : Ambient d × Ambient d) :
    cappedWeightedDifference m ε w q * cappedWeightedDifference m ε g q =
      (w q.1 - w q.2) * cappedTestKernel m ε g q := by
  unfold cappedWeightedDifference cappedTestKernel
  have heq : Real.sqrt (cappedInverseDistancePow (m + 1) ε q) ^ 2 =
      cappedInverseDistancePow (m + 1) ε q := Real.sq_sqrt (cappedInverseDistancePow_nonneg (m + 1) ε q)
  calc
    _ = Real.sqrt (cappedInverseDistancePow (m + 1) ε q) ^ 2 *
        ((w q.1 - w q.2) * (g q.1 - g q.2)) := by ring
    _ = _ := by rw [heq]; ring

theorem cappedPairEnergy_integrable {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w : Ambient d → ℝ) (hw : MemLp w 2 μ) :
    Integrable (cappedPairEnergy m ε w) (μ.prod μ) := by
  simpa only [cappedWeightedDifference_sq] using!
    (cappedWeightedDifference_memLp m ε hε μ w hw).integrable_sq

theorem capped_bilinear_cauchy_schwarz {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w g : Ambient d → ℝ)
    (hw : MemLp w 2 μ) (hg : MemLp g 2 μ) :
    (∫ q : Ambient d × Ambient d, (w q.1 - w q.2) * cappedTestKernel m ε g q ∂μ.prod μ) ^ 2 ≤
      (∫ q, cappedPairEnergy m ε w q ∂μ.prod μ) * (∫ q, cappedPairEnergy m ε g q ∂μ.prod μ) := by
  simpa only [cappedWeightedDifference_mul, cappedWeightedDifference_sq] using!
    integral_mul_cauchy_schwarz_sq (μ.prod μ) (cappedWeightedDifference m ε w)
      (cappedWeightedDifference m ε g) (cappedWeightedDifference_memLp m ε hε μ w hw)
      (cappedWeightedDifference_memLp m ε hε μ g hg)

theorem cappedPairEnergy_le_fractional {d : ℕ} (m : ℕ) (ε : ℝ)
    (w : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedPairEnergy m ε w q ≤ fractionalPairEnergy m w q.1 q.2 := by
  by_cases hdiag : q.1 = q.2
  · simp only [cappedPairEnergy, fractionalPairEnergy, hdiag, sub_self,
      zero_pow two_ne_zero, zero_mul, zero_div, le_refl]
  · have hd : 0 < dist q.1 q.2 := dist_pos.mpr hdiag
    unfold cappedPairEnergy fractionalPairEnergy
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact inv_anti₀ (pow_pos hd _) (pow_le_pow_left₀ hd.le (le_max_right _ _) _)

theorem capped_bilinear_variational_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w g : Ambient d → ℝ)
    (hw : MemLp w 2 μ) (hg : MemLp g 2 μ)
    (henergy : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m w q.1 q.2) (μ.prod μ))
    (E : ℝ) (hE : (∫ q : Ambient d × Ambient d, fractionalPairEnergy m w q.1 q.2 ∂μ.prod μ) ≤ E) :
    (∫ q : Ambient d × Ambient d, (w q.1 - w q.2) * cappedTestKernel m ε g q ∂μ.prod μ) ^ 2 ≤
      E * (∫ q, cappedPairEnergy m ε g q ∂μ.prod μ) := by
  have hcap : (∫ q, cappedPairEnergy m ε w q ∂μ.prod μ) ≤ E := by
    apply (integral_mono (cappedPairEnergy_integrable m ε hε μ w hw) henergy
      (fun q => cappedPairEnergy_le_fractional m ε w q)).trans hE
  exact (capped_bilinear_cauchy_schwarz m ε hε μ w g hw hg).trans
    (mul_le_mul_of_nonneg_right hcap (integral_nonneg fun q =>
      mul_nonneg (sq_nonneg _) (cappedInverseDistancePow_nonneg (m + 1) ε q)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CappedEnergyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem cappedWeightedDifference_sub {d : ℕ} (m : ℕ) (ε : ℝ)
    (f g : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedWeightedDifference m ε f q - cappedWeightedDifference m ε g q =
      cappedWeightedDifference m ε (fun x => f x - g x) q := by
  unfold cappedWeightedDifference
  ring

theorem capped_self_bilinear_eq_energy {d : ℕ} (m : ℕ) (ε : ℝ)
    (f : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    (f q.1 - f q.2) * cappedTestKernel m ε f q = cappedPairEnergy m ε f q := by
  unfold cappedTestKernel cappedPairEnergy
  ring

theorem cappedPairEnergy_L2_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w : Ambient d → ℝ) (hw : MemLp w 2 μ) :
    (∫ q, cappedPairEnergy m ε w q ∂μ.prod μ) ≤
      (4 * μ.real univ * (ε ^ (m + 1))⁻¹) * ∫ x, w x ^ 2 ∂μ := by
  have hx : Integrable (fun q : Ambient d × Ambient d => w q.1 ^ 2) (μ.prod μ) :=
    hw.integrable_sq.comp_fst μ
  have hy : Integrable (fun q : Ambient d × Ambient d => w q.2 ^ 2) (μ.prod μ) :=
    hw.integrable_sq.comp_snd μ
  have hdom := ((hx.const_mul 2).add (hy.const_mul 2)).mul_const ((ε ^ (m + 1))⁻¹)
  calc
    _ ≤ ∫ q : Ambient d × Ambient d, (2 * w q.1 ^ 2 + 2 * w q.2 ^ 2) *
        (ε ^ (m + 1))⁻¹ ∂μ.prod μ := by
      apply integral_mono (cappedPairEnergy_integrable m ε hε μ w hw) hdom
      intro q
      change (w q.1 - w q.2) ^ 2 * cappedInverseDistancePow (m + 1) ε q ≤ _
      apply mul_le_mul
      · change (w q.1 - w q.2) ^ 2 ≤ 2 * w q.1 ^ 2 + 2 * w q.2 ^ 2
        nlinarith [sq_nonneg (w q.1 + w q.2)]
      · exact (le_abs_self _).trans (cappedInverseDistancePow_bound (m + 1) ε hε q)
      · exact cappedInverseDistancePow_nonneg _ _ _
      · change 0 ≤ 2 * w q.1 ^ 2 + 2 * w q.2 ^ 2
        positivity
    _ = _ := by
      rw [integral_mul_const, integral_add (hx.const_mul 2) (hy.const_mul 2)]
      simp only [integral_const_mul, integral_fun_fst (fun x => w x ^ 2),
        integral_fun_snd (fun x => w x ^ 2), smul_eq_mul]
      ring

theorem cappedWeightedDifference_L2_tendsto {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (herror : Tendsto (fun k => ∫ x, (f k x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => (cappedWeightedDifference_memLp m ε hε μ (f k) (hf k)).toLp
      (cappedWeightedDifference m ε (f k))) atTop
      (𝓝 ((cappedWeightedDifference_memLp m ε hε μ g hg).toLp (cappedWeightedDifference m ε g))) := by
  apply L2_tendsto_of_squared_error (μ.prod μ) (fun k => cappedWeightedDifference m ε (f k))
    (cappedWeightedDifference m ε g)
    (fun k => cappedWeightedDifference_memLp m ε hε μ (f k) (hf k))
    (cappedWeightedDifference_memLp m ε hε μ g hg)
  simp_rw [cappedWeightedDifference_sub, cappedWeightedDifference_sq]
  apply squeeze_zero (fun k => integral_nonneg fun q =>
    mul_nonneg (sq_nonneg _) (cappedInverseDistancePow_nonneg (m + 1) ε q))
    (fun k => cappedPairEnergy_L2_bound m ε hε μ (fun x => f k x - g x) ((hf k).sub hg))
  simpa only [mul_zero] using! herror.const_mul (4 * μ.real univ * (ε ^ (m + 1))⁻¹)

theorem capped_energy_tendsto_of_L2_error {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (herror : Tendsto (fun k => ∫ x, (f k x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ q, cappedPairEnergy m ε (f k) q ∂μ.prod μ) atTop
      (𝓝 (∫ q, cappedPairEnergy m ε g q ∂μ.prod μ)) := by
  have h := (cappedWeightedDifference_L2_tendsto m ε hε μ f g hf hg herror).norm.pow 2
  simpa only [toLp_norm_sq_eq_integral, cappedWeightedDifference_sq] using! h

theorem capped_pairing_tendsto_of_L2_error {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (herror : Tendsto (fun k => ∫ x, (f k x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ q : Ambient d × Ambient d,
      (g q.1 - g q.2) * cappedTestKernel m ε (f k) q ∂μ.prod μ) atTop
      (𝓝 (∫ q, cappedPairEnergy m ε g q ∂μ.prod μ)) := by
  have hconv := cappedWeightedDifference_L2_tendsto m ε hε μ f g hf hg herror
  have h := (tendsto_const_nhds (x :=
    (cappedWeightedDifference_memLp m ε hε μ g hg).toLp (cappedWeightedDifference m ε g))).inner
      (𝕜 := ℝ) hconv
  simpa only [toLp_inner_eq_integral, cappedWeightedDifference_mul, capped_self_bilinear_eq_energy] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CappedWeakConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak convergence of capped pair energies

Bounded continuous tests pass to weak limits of finite measures. Finite measurable
partitions with shrinking cells then control bounded Lipschitz tests on product
measures. The capped pair energy of a bounded Lipschitz function satisfies these
test bounds, giving convergence of its double integral at each positive cap.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal BoundedContinuousFunction

theorem bounded_continuous_integral_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (f : Ambient d → ℝ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    Tendsto (fun j => ∫ x, f x ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure (Ambient d)))) := by
  let F : Ambient d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * B) (by
    intro x y
    change dist (f x) (f y) ≤ 2 * B
    rw [Real.dist_eq]
    have h := abs_sub_le (f x) 0 (f y)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith [hB x, hB y])
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak F

theorem bounded_lipschitz_product_integral_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂(μ j : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂(ν : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j : Measure (Ambient d)).restrict (s k i),
      dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂(ν : Measure (Ambient d)).restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k i)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k i))))
    (M : ℝ) (hM : 0 ≤ M) (htotal : ∀ᶠ j in atTop, (μ j : Measure (Ambient d)).real univ ≤ M)
    (F : Ambient d × Ambient d → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F)
    (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    Tendsto (fun j => ∫ q, F q ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q, F q ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  have hweight : ∀ᶠ j in atTop, (∫ _ : Ambient d, |(1 : ℝ)| ∂(μ j : Measure (Ambient d))) ≤ M := by
    simpa only [abs_one, integral_const, smul_eq_mul, mul_one] using! htotal
  have hmoment : ∀ y, Tendsto (fun j => ∫ x, (1 : ℝ) * F (x, y) ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, (1 : ℝ) * F (x, y) ∂(ν : Measure (Ambient d)))) := by
    intro y
    simpa only [one_mul] using! bounded_continuous_integral_tendsto μ ν hweak
      (fun x => F (x, y)) (hF.continuous.comp (continuous_id.prodMk continuous_const)) B
      (fun x => hB (x, y))
  have h := weighted_product_kernel_tendsto (fun j => (μ j : Measure (Ambient d)))
    (ν : Measure (Ambient d)) (fun j => (μ j : Measure (Ambient d))) (ν : Measure (Ambient d))
    (fun _ _ => 1) (fun _ => 1) (fun _ => integrable_const 1) (integrable_const 1)
    ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M M hM hM hweight htotal
    F K hF B hB hmoment
  simpa only [one_mul] using! h

theorem cappedPairEnergy_bounded_lipschitz {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : Ambient d → ℝ) (L B : ℝ≥0) (hg : LipschitzWith L g) (hB : ∀ x, |g x| ≤ (B : ℝ)) :
    ∃ (K : ℝ≥0) (Q : ℝ), LipschitzWith K (cappedPairEnergy m ε g) ∧
      ∀ q, |cappedPairEnergy m ε g q| ≤ Q := by
  let δg := fun q : Ambient d × Ambient d => g q.1 - g q.2
  have hdiff : LipschitzWith (L + L) δg := by
    simpa only [mul_one] using! (hg.comp LipschitzWith.prod_fst).sub (hg.comp LipschitzWith.prod_snd)
  have hdiffbound : ∀ q, |δg q| ≤ ((2 * B : ℝ≥0) : ℝ) := by
    intro q
    have h := abs_sub_le (g q.1) 0 (g q.2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    simp only [δg, NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [hB q.1, hB q.2]
  have hsquare : LipschitzWith ((2 * B) * (L + L) + (L + L) * (2 * B))
      (fun q => δg q ^ 2) := by
    simpa only [pow_two] using! lipschitz_bounded_product_real hdiff hdiff hdiffbound hdiffbound
  have hsquarebound : ∀ q, |δg q ^ 2| ≤ (((2 * B : ℝ≥0) ^ 2) : ℝ) := by
    intro q
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using! pow_le_pow_left₀ (abs_nonneg _) (hdiffbound q) 2
  have hcap := cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε
  have hcapbound : ∀ q : Ambient d × Ambient d, |cappedInverseDistancePow (m + 1) ε q| ≤
      (Real.toNNReal ((ε ^ (m + 1))⁻¹) : ℝ) := fun q =>
    (cappedInverseDistancePow_bound (m + 1) ε hε q).trans (Real.le_coe_toNNReal _)
  refine ⟨_, (((2 * B : ℝ≥0) ^ 2) : ℝ) * (ε ^ (m + 1))⁻¹,
    lipschitz_bounded_product_real (Bf := (2 * B) ^ 2)
      (Bg := Real.toNNReal ((ε ^ (m + 1))⁻¹)) hsquare hcap
      (fun q => by simpa only [NNReal.coe_pow] using! hsquarebound q) hcapbound, ?_⟩
  intro q
  change |δg q ^ 2 * cappedInverseDistancePow (m + 1) ε q| ≤ _
  rw [abs_mul]
  exact mul_le_mul (hsquarebound q) (cappedInverseDistancePow_bound (m + 1) ε hε q)
    (abs_nonneg _) (by positivity)

theorem capped_energy_tendsto_of_weak {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂(μ j : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂(ν : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j : Measure (Ambient d)).restrict (s k i),
      dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂(ν : Measure (Ambient d)).restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k i)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k i))))
    (M : ℝ) (hM : 0 ≤ M) (htotal : ∀ᶠ j in atTop, (μ j : Measure (Ambient d)).real univ ≤ M)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (g : Ambient d → ℝ) (L B : ℝ≥0)
    (hg : LipschitzWith L g) (hB : ∀ x, |g x| ≤ (B : ℝ)) :
    Tendsto (fun j => ∫ q, cappedPairEnergy m ε g q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q, cappedPairEnergy m ε g q ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  obtain ⟨K, Q, hLip, hbound⟩ := cappedPairEnergy_bounded_lipschitz m ε hε g L B hg hB
  exact bounded_lipschitz_product_integral_tendsto μ ν hweak ι s hs hd hcover hcoverν z r hr hrzero
    hcell hcellν hmass M hM htotal (cappedPairEnergy m ε g) K hLip Q hbound

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LimitEnergyDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

theorem capped_energy_bound_from_lipschitz_tests {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (v : Ambient d → ℝ) (hv : MemLp v 2 μ)
    (E : ℝ) (hE : 0 ≤ E)
    (htests : ∀ (g : Ambient d → ℝ) (K B : ℝ≥0), LipschitzWith K g →
      (∀ x, |g x| ≤ (B : ℝ)) → MemLp g 2 μ →
      (∫ q : Ambient d × Ambient d, (v q.1 - v q.2) * cappedTestKernel m ε g q ∂μ.prod μ) ^ 2 ≤
        E * ∫ q, cappedPairEnergy m ε g q ∂μ.prod μ) :
    (∫ q, cappedPairEnergy m ε v q ∂μ.prod μ) ≤ E := by
  obtain ⟨g, K, B, _, hLip, hbound, hg, herror⟩ := exists_bounded_lipschitz_L2_sequence μ v hv
  have hpair := capped_pairing_tendsto_of_L2_error m ε hε μ g v hg hv herror
  have henergy := capped_energy_tendsto_of_L2_error m ε hε μ g v hg hv herror
  have hlim : (∫ q, cappedPairEnergy m ε v q ∂μ.prod μ) ^ 2 ≤
      E * ∫ q, cappedPairEnergy m ε v q ∂μ.prod μ :=
    le_of_tendsto_of_tendsto (hpair.pow 2) (henergy.const_mul E)
      (Filter.Eventually.of_forall fun k => htests (g k) (K k) (B k) (hLip k) (hbound k) (hg k))
  by_contra h
  have hgt : E < ∫ q, cappedPairEnergy m ε v q ∂μ.prod μ := lt_of_not_ge h
  have hpos := hE.trans_lt hgt
  nlinarith [mul_pos hpos (sub_pos.mpr hgt)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LimitEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem fractionalEnergy_integrable_of_capped_bounds {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (v : Ambient d → ℝ)
    (hv : Measurable v) (hvL2 : MemLp v 2 μ) (E : ℝ)
    (hcap : ∀ ε : ℝ, 0 < ε → (∫ q, cappedPairEnergy m ε v q ∂μ.prod μ) ≤ E) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m v q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy m v q.1 q.2 ∂μ.prod μ) ≤ E := by
  apply fractionalEnergy_integrable_of_uniform_bound μ m v hv hvL2 E
  intro ε hε
  have hs : MeasurableSet {q : Ambient d × Ambient d | ε < dist q.1 q.2} :=
    measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable
  have heq : (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
      fractionalPairEnergy m v q.1 q.2 ∂μ.prod μ) =
      ∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2}, cappedPairEnergy m ε v q ∂μ.prod μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hs] with q hq
    rw [cappedPairEnergy, cappedInverseDistancePow_eq _ _ _ hq.le]
    rfl
  rw [heq]
  exact (setIntegral_le_integral (cappedPairEnergy_integrable m ε hε μ v hvL2)
    (Filter.Eventually.of_forall fun q =>
      mul_nonneg (sq_nonneg _) (cappedInverseDistancePow_nonneg (m + 1) ε q))).trans (hcap ε hε)

theorem limiting_fractional_energy_bound {d : ℕ} (m : ℕ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j : Measure (Ambient d)))
    (hv : MemLp v 2 (ν : Measure (Ambient d))) (hvm : Measurable v)
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂(μ j : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂(ν : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j : Measure (Ambient d)).restrict (s k i),
      dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂(ν : Measure (Ambient d)).restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k i)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k i))))
    (M : ℝ) (hM : 0 ≤ M) (htotal : ∀ᶠ j in atTop, (μ j : Measure (Ambient d)).real univ ≤ M)
    (hsecond : ∀ᶠ j in atTop, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ M)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (D : ℝ≥0), LipschitzWith D ψ →
      MemLp ψ 2 (ν : Measure (Ambient d)) → (∀ j, MemLp ψ 2 (μ j : Measure (Ambient d))) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, v x * ψ x ∂(ν : Measure (Ambient d)))))
    (henergy : ∀ j, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m (w j) q.1 q.2)
      ((μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))))
    (E : ℝ) (hE : ∀ j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy m (w j) q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) ≤ E) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m v q.1 q.2)
      ((ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy m v q.1 q.2
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) ≤ E := by
  have hE0 : 0 ≤ E := (integral_nonneg fun q => fractionalPairEnergy_nonneg m (w 0) q.1 q.2).trans (hE 0)
  apply fractionalEnergy_integrable_of_capped_bounds m (ν : Measure (Ambient d)) v hvm hv E
  intro ε hε
  apply capped_energy_bound_from_lipschitz_tests m ε hε (ν : Measure (Ambient d)) v hv E hE0
  intro g K B hg hB _
  have hleft := capped_bilinear_tendsto (fun j => (μ j : Measure (Ambient d))) (ν : Measure (Ambient d))
    w v hw hv ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M hM htotal hsecond
    hmoment m ε hε g K B hg hB
  have hright := capped_energy_tendsto_of_weak μ ν hweak ι s hs hd hcover hcoverν z r hr hrzero
    hcell hcellν hmass M hM htotal m ε hε g K B hg hB
  apply le_of_tendsto_of_tendsto (hleft.pow 2) (hright.const_mul E)
  apply Filter.Eventually.of_forall
  intro j
  have hgL2 : MemLp g 2 (μ j : Measure (Ambient d)) :=
    MemLp.of_bound hg.continuous.measurable.aestronglyMeasurable (B : ℝ)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  exact capped_bilinear_variational_bound m ε hε (μ j : Measure (Ambient d)) (w j) g
    (hw j) hgL2 (henergy j) E (hE j)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LocalSingularLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem fractional_bilinear_tendsto_of_capped {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) C ν)
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, Measurable (w j)) (hv : Measurable v)
    (hwI : ∀ j, Integrable (w j) (μ j)) (hvI : Integrable v ν)
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j).prod (μ j)))
    (henergyν : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) v q.1 q.2) (ν.prod ν))
    (E M : ℝ)
    (hE : ∀ j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (w j) q.1 q.2 ∂(μ j).prod (μ j)) ≤ E)
    (hM : ∀ j, (μ j).real univ ≤ M)
    (φ : Ambient d → ℝ) (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (hcapped : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun j => ∫ q : Ambient d × Ambient d,
        (w j q.1 - w j q.2) * cappedTestKernel (p + 1) ε φ q ∂(μ j).prod (μ j)) atTop
      (𝓝 (∫ q : Ambient d × Ambient d,
        (v q.1 - v q.2) * cappedTestKernel (p + 1) ε φ q ∂ν.prod ν))) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (w j) φ q.1 q.2 ∂(μ j).prod (μ j)) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2 ∂ν.prod ν)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hthird : 0 < η / 3 := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := near_fractionalBilinear_uniformly_small p C μ hg w hw henergy
    E M hE hM φ L hφ (η / 3) hthird
  obtain ⟨δν, hδν, hsmallν⟩ := near_fractionalBilinear_uniformly_small p C
    (fun _ : ℕ => ν) (fun _ => hgν) (fun _ : ℕ => v) (fun _ => hv) (fun _ => henergyν)
    (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) v q.1 q.2 ∂ν.prod ν)
    (ν.real univ) (fun _ => le_rfl) (fun _ => le_rfl) φ L hφ (η / 3) hthird
  let ε := min δ δν / 2
  have hε : 0 < ε := half_pos (lt_min hδ hδν)
  have hεδ : ε < δ := by dsimp only [ε] <;> linarith [min_le_left δ δν, lt_min hδ hδν]
  have hεδν : ε < δν := by dsimp only [ε] <;> linarith [min_le_right δ δν, lt_min hδ hδν]
  filter_upwards [Metric.tendsto_nhds.mp (hcapped ε hε) (η / 3) hthird] with j hj
  have hjerr : dist
      (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) φ q.1 q.2 ∂(μ j).prod (μ j))
      (∫ q : Ambient d × Ambient d, (w j q.1 - w j q.2) * cappedTestKernel (p + 1) ε φ q
        ∂(μ j).prod (μ j)) < η / 3 := by
    rw [Real.dist_eq]
    exact (fractional_bilinear_integrable_and_cap_error p C (μ j) (hg j) (w j) φ
      (hw j) (hwI j) L B hφ hB (henergy j) ε hε).2.trans_lt (hsmall j ε hε hεδ)
  have hνerr : dist
      (∫ q : Ambient d × Ambient d, (v q.1 - v q.2) * cappedTestKernel (p + 1) ε φ q ∂ν.prod ν)
      (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2 ∂ν.prod ν) < η / 3 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact (fractional_bilinear_integrable_and_cap_error p C ν hgν v φ hv hvI
      L B hφ hB henergyν ε hε).2.trans_lt (hsmallν 0 ε hε hεδν)
  have htriangle := dist_triangle
    (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) φ q.1 q.2 ∂(μ j).prod (μ j))
    (∫ q : Ambient d × Ambient d, (w j q.1 - w j q.2) * cappedTestKernel (p + 1) ε φ q
      ∂(μ j).prod (μ j))
    (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2 ∂ν.prod ν)
  have htriangle' := dist_triangle
    (∫ q : Ambient d × Ambient d, (w j q.1 - w j q.2) * cappedTestKernel (p + 1) ε φ q
      ∂(μ j).prod (μ j))
    (∫ q : Ambient d × Ambient d, (v q.1 - v q.2) * cappedTestKernel (p + 1) ε φ q ∂ν.prod ν)
    (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2 ∂ν.prod ν)
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SingularCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem singular_compactness_of_weak_moments {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j : Measure (Ambient d)))
    (hgν : GlobalUpperGrowth (p + 1) C (ν : Measure (Ambient d)))
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j : Measure (Ambient d)))
    (hwm : ∀ j, Measurable (w j)) (hv : MemLp v 2 (ν : Measure (Ambient d))) (hvm : Measurable v)
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂(μ j : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂(ν : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j : Measure (Ambient d)).restrict (s k i),
      dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂(ν : Measure (Ambient d)).restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k i)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k i))))
    (M : ℝ) (htotal : ∀ j, (μ j : Measure (Ambient d)).real univ ≤ M)
    (hsecond : ∀ j, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ M)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (D : ℝ≥0), LipschitzWith D ψ →
      MemLp ψ 2 (ν : Measure (Ambient d)) → (∀ j, MemLp ψ 2 (μ j : Measure (Ambient d))) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, v x * ψ x ∂(ν : Measure (Ambient d)))))
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))))
    (E : ℝ) (hE : ∀ j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) ≤ E) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) v q.1 q.2)
      ((ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) v q.1 q.2
        ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d))) ≤ E ∧
      ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ → (∀ x, |φ x| ≤ (B : ℝ)) →
        Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) φ q.1 q.2
          ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
          (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2
            ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  have hM : 0 ≤ M := measureReal_nonneg.trans (htotal 0)
  have ht : ∀ᶠ j in atTop, (μ j : Measure (Ambient d)).real univ ≤ M :=
    Filter.Eventually.of_forall htotal
  have hsec : ∀ᶠ j in atTop, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ M :=
    Filter.Eventually.of_forall hsecond
  obtain ⟨hvE, hvEbound⟩ := limiting_fractional_energy_bound (p + 1) μ ν hweak w v hw hv hvm
    ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M hM ht hsec hmoment henergy E hE
  refine ⟨hvE, hvEbound, ?_⟩
  intro φ L B hφ hB
  apply fractional_bilinear_tendsto_of_capped p C (fun j => (μ j : Measure (Ambient d)))
    (ν : Measure (Ambient d)) hg hgν w v hwm hvm (fun j => (hw j).integrable (by norm_num))
    (hv.integrable (by norm_num)) henergy hvE E M hE htotal φ L B hφ hB
  intro ε hε
  exact capped_bilinear_tendsto (fun j => (μ j : Measure (Ambient d))) (ν : Measure (Ambient d))
    w v hw hv ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M hM ht hsec hmoment
    (p + 1) ε hε φ L B hφ hB

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionSingularMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem projection_singular_limit_of_moments {d : ℕ} (p : ℕ)
    (I : Box (Fin (p + 1))) (e : (Fin (p + 1) → ℝ) → Ambient d)
    (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π)
    (hleft : LeftInverse π e) (μ : ℕ → FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 (boxPlaneFiniteMeasure I e)))
    (C : ℝ) (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j : Measure (Ambient d)))
    (hcoords : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), π x ∈ I)
    (hheight : ∀ k : ℕ, ∀ᶠ j in atTop,
      ∀ᵐ x ∂(μ j : Measure (Ambient d)), dist x (e (π x)) ≤ (1 / 2 : ℝ) ^ k)
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j : Measure (Ambient d)))
    (hwm : ∀ j, Measurable (w j)) (hv : MemLp v 2 (boxPlaneMeasure I e)) (hvm : Measurable v)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (D : ℝ≥0), LipschitzWith D ψ →
      MemLp ψ 2 (boxPlaneMeasure I e) → (∀ j, MemLp ψ 2 (μ j : Measure (Ambient d))) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, v x * ψ x ∂boxPlaneMeasure I e)))
    (B E : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ B)
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))))
    (hE : ∀ j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) ≤ E) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) v q.1 q.2)
      ((boxPlaneMeasure I e).prod (boxPlaneMeasure I e)) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) v q.1 q.2
        ∂(boxPlaneMeasure I e).prod (boxPlaneMeasure I e)) ≤ E ∧
      ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) ψ q.1 q.2
          ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
          (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v ψ q.1 q.2
            ∂(boxPlaneMeasure I e).prod (boxPlaneMeasure I e))) := by
  let ν : FiniteMeasure (Ambient d) := boxPlaneFiniteMeasure I e
  let s : ∀ k, DyadicBoxIndex I k → Set (Ambient d) := dyadicProjectionCell I π
  let D : ℝ := 1 + (K : ℝ) * boxWidthBound I
  have hD : 0 ≤ D := by dsimp [D]; positivity [boxWidthBound_nonneg I]
  have hrzero : Tendsto (fun k : ℕ => D * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using! dyadic_box_scale_tendsto_zero.const_mul D
  have hs : ∀ k J, MeasurableSet (s k J) :=
    fun k J => dyadicProjectionCell_measurable I π hπ.continuous.measurable k J
  have hd : ∀ k, Pairwise (Disjoint on s k) := dyadicProjectionCell_disjoint I π
  have hcover : ∀ k j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), x ∈ ⋃ J, s k J :=
    fun k j => dyadicProjectionCell_cover_ae I π _ (hcoords j) k
  have hcoverν : ∀ k, ∀ᵐ x ∂(ν : Measure (Ambient d)), x ∈ ⋃ J, s k J :=
    fun k => dyadicProjectionCell_cover_ae I π _
      (boxPlaneMeasure_ae_coordinates I e π he.continuous.measurable
        hπ.continuous.measurable hleft) k
  have hcell : ∀ k, ∀ᶠ j in atTop, ∀ J : DyadicBoxIndex I k,
      ∀ᵐ x ∂(μ j : Measure (Ambient d)).restrict (s k J),
        dist x (e J.val.upper) ≤ D * (1 / 2 : ℝ) ^ k := by
    intro k
    filter_upwards [hheight k] with j hj
    exact dyadicProjectionCell_ae_dist_reference I e π hπ.continuous.measurable K he _ k hj
  have hcellν : ∀ k J, ∀ᵐ x ∂(ν : Measure (Ambient d)).restrict (s k J),
      dist x (e J.val.upper) ≤ D * (1 / 2 : ℝ) ^ k := by
    intro k J
    apply dyadicProjectionCell_ae_dist_reference I e π hπ.continuous.measurable K he _ k _ J
    filter_upwards [boxPlaneMeasure_ae_section I e π he.continuous hπ.continuous hleft] with x hx
    rw [hx, dist_self]
    positivity
  have hν : ν ≠ 0 := boxPlaneFiniteMeasure_ne_zero I e he.continuous.measurable
  have hmass : ∀ k J, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k J)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k J))) := by
    intro k J
    exact finiteMeasure_cell_mass_tendsto μ ν hweak hν (s k J)
      (dyadicProjectionCell_null_frontier I e π he.continuous hπ.continuous hleft k J)
  have htotal : Tendsto (fun j => (μ j : Measure (Ambient d)).real univ) atTop
      (𝓝 ((ν : Measure (Ambient d)).real univ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
  have heventual : ∀ᶠ j in atTop, |(μ j : Measure (Ambient d)).real univ| ≤
      (ν : Measure (Ambient d)).real univ + 1 := by
    filter_upwards [htotal.eventually (gt_mem_nhds
      (by linarith : (ν : Measure (Ambient d)).real univ <
        (ν : Measure (Ambient d)).real univ + 1))] with j hj
    simpa only [abs_of_nonneg measureReal_nonneg] using! hj.le
  obtain ⟨T, hT⟩ := bounded_of_eventually_abs_le
    (fun j => (μ j : Measure (Ambient d)).real univ)
    ((ν : Measure (Ambient d)).real univ + 1) heventual
  have htotalM : ∀ j, (μ j : Measure (Ambient d)).real univ ≤ max T B :=
    fun j => (le_abs_self _).trans ((hT j).trans (le_max_left _ _))
  have hsecondM : ∀ j, (∫ x, w j x ^ 2 ∂(μ j : Measure (Ambient d))) ≤ max T B :=
    fun j => (hB j).trans (le_max_right _ _)
  have hgν : GlobalUpperGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1))
      (ν : Measure (Ambient d)) := by
    simpa only [Fintype.card_fin] using! boxPlaneMeasure_upper_growth I e π
      he.continuous.measurable Q hπ hleft
  exact singular_compactness_of_weak_moments p (max C ((2 * (Q : ℝ)) ^ (p + 1))) μ ν hweak
    (fun j => (hg j).mono_constant (le_max_left _ _)) (hgν.mono_constant (le_max_right _ _))
    w v hw hwm hv hvm (DyadicBoxIndex I) s hs hd hcover hcoverν (fun _ J => e J.val.upper)
    (fun k => D * (1 / 2 : ℝ) ^ k) (fun _ => mul_nonneg hD (by positivity)) hrzero
    hcell hcellν hmass (max T B) htotalM hsecondM hmoment henergy E hE

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_GlobalSingularHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_global_height_with_local_singular_limits_oai {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (w : ℕ → Ambient d → ℝ) (hwm : ∀ j, Measurable (w j))
    (hw : ∀ H j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B E : ℕ → ℝ)
    (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE : ∀ H j, (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, w (φ j) x ^ 2
        ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ x, w (φ j) x * ψ x
          ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H ∧
        ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
          Tendsto (fun j => ∫ q : Ambient d × Ambient d,
            fractionalBilinear (p + 1) (w (φ j)) ψ q.1 q.2
            ∂(((σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)).prod
              ((σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)))) atTop
            (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) f ψ q.1 q.2
              ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
                ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))) := by
  obtain ⟨φ, hφ, f, hfm, hf, hsecond, hmoment⟩ := exists_bounded_global_projection_height
    e π K Q he hπ hleft σ hlocal C hC
    (by simpa only [Fintype.card_fin] using! hlower) hdiam w hw B E hB
    (by simpa only [Fintype.card_fin] using! henergy)
    (by simpa only [Fintype.card_fin] using! hE)
  refine ⟨φ, hφ, f, hfm, hf, hsecond, hmoment, ?_⟩
  intro H
  let s := boundedProjectionRegion π (e 0) K H
  let I := exhaustionBox (Fin (p + 1)) H
  let μ := fun j => boundedProjectionFiniteMeasure (σ (φ j)) π (e 0) K H
  have hplane : (coordinatePlaneMeasure e).restrict s = boxPlaneMeasure I e :=
    coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft H
  have hνball : ∀ᵐ x ∂boxPlaneMeasure I e, x ∈ ball (e 0) (planeBoxOuterRadius K H) := by
    rw [← hplane]
    filter_upwards [ae_restrict_mem (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet]
      with x hx
    exact hx.2
  have hμball : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), x ∈ ball (e 0) (planeBoxOuterRadius K H) := by
    intro j
    filter_upwards [ae_restrict_mem (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet]
      with x hx
    exact hx.2
  have hmcompact : ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
      Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(μ j : Measure (Ambient d))) atTop
        (𝓝 (∫ x, f x * ψ x ∂boxPlaneMeasure I e)) := by
    intro ψ L A hc hLip hA
    have hm := hmoment H ψ L A hc hLip hA
    change Tendsto (fun j => ∫ x, w (φ j) x * ψ x ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, f x * ψ x ∂(coordinatePlaneMeasure e).restrict s)) at hm
    rwa [hplane] at hm
  have hm := compact_moments_extend_on_ball (fun j => (μ j : Measure (Ambient d)))
    (boxPlaneMeasure I e) (e 0) (planeBoxOuterRadius K H) hμball hνball (fun j => w (φ j)) f hmcompact
  have hgμ : ∀ j, GlobalUpperGrowth (p + 1) G (μ j : Measure (Ambient d)) := by
    intro j
    refine ⟨(hg (φ j)).1, ?_⟩
    intro x r hr
    have hle : (μ j : Measure (Ambient d)) ≤ σ (φ j) := Measure.restrict_le_self
    exact (hle (ball x r)).trans ((hg (φ j)).2 x r hr)
  have hheight := boundedProjectionFiniteMeasure_height_of_AD_lower e π K Q he hπ hleft
    σ hlocal C hC (by simpa only [Fintype.card_fin] using! hlower) hdiam H
  have hfH : MemLp f 2 (boxPlaneMeasure I e) := by
    have h := hf H
    change MemLp f 2 ((coordinatePlaneMeasure e).restrict s) at h
    rwa [hplane] at h
  have hresult := projection_singular_limit_of_moments p I e π K Q he hπ hleft μ
    ((boundedProjectionFiniteMeasure_tendsto e π K Q he hπ hleft σ hlocal H).comp hφ.tendsto_atTop)
    G hgμ (fun j => boundedProjectionRegion_ae_coordinates (σ (φ j)) π hπ.continuous (e 0) K H)
    (fun k => hφ.tendsto_atTop.eventually (hheight k)) (fun j => w (φ j)) f
    (fun j => hw H (φ j)) (fun j => hwm (φ j)) hfH hfm (fun ψ D hLip _ _ => hm ψ D hLip)
    (B H) (E H) (fun j => hB H (φ j)) (fun j => henergy H (φ j)) (fun j => hE H (φ j))
  change _ ∧ _ ∧ _ at hresult
  simpa only [← hplane] using! hresult

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_global_height_with_local_singular_limits_oai := @OAI.RieszRectifiability.exists_global_height_with_local_singular_limits_oai
