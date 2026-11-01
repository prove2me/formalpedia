-- Prove2me | solution 1 for OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:48:40.197508+00:00
-- url     : https://prove2.me/submissions/684df2fc-47f3-4b02-8f91-67fefd430c49

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C007
import Definitions.Def_Q146C008

section
-- module Solutions.Q146_CD.CircleDomains_Selection_DustCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small disjoint neighborhoods of compact dust

A compact totally disconnected subset of a metric space admits finite
open covers with pairwise disjoint closures of arbitrarily small diameter.
-/

open Set Metric TopologicalSpace Filter Function
open scoped Topology

namespace CircleDomainRigidity

theorem exists_small_disjoint_open_cover_of_compact_dust
    {X : Type*} [MetricSpace X] {B : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (U : Fin n → Set X),
      (∀ i, IsOpen (U i)) ∧ B ⊆ ⋃ i, U i ∧
      Pairwise (Disjoint on fun i => closure (U i)) ∧
      ∀ i, diam (closure (U i)) < ε := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : TotallyDisconnectedSpace B := totallyDisconnectedSpace_subtype_iff.mpr hTD
  have hcover : IsOpenCover (fun b : B => (⟨ball b (ε / 4), isOpen_ball⟩ : Opens B)) := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro b
    exact mem_iUnion.mpr ⟨b, mem_ball_self (by positivity)⟩
  obtain ⟨n, C, hC, hCov, hDisj⟩ := hcover.exists_finite_nonempty_disjoint_clopen_cover
  let A : Fin n → Set X := fun i => Subtype.val '' (C i : Set B)
  have hAc (i) : IsCompact (A i) := (C i).isClosed.isCompact.image continuous_subtype_val
  have hAd : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    have heq : v = u := Subtype.ext huv
    subst v
    exact Set.disjoint_left.mp (Clopens.coe_disjoint.mpr (hDisj hij)) hu hv
  have hAn : Pairwise (Disjoint on fun i => 𝓝ˢ (A i)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet (hAc i).isClosed (hAc j).isClosed (hAd hij)
  obtain ⟨V, hV, hVd⟩ := hAn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (A i))
  have hsmall (i : Fin n) : ∃ b : B, A i ⊆ ball (b : X) (ε / 4) := by
    obtain ⟨b, hb⟩ := (hC i).2
    refine ⟨b, ?_⟩
    rintro z ⟨u, hu, rfl⟩
    exact hb hu
  choose b hb using hsmall
  have hshrink (i : Fin n) : ∃ U : Set X,
      IsOpen U ∧ A i ⊆ U ∧ closure U ⊆ V i ∩ ball (b i : X) (ε / 4) := by
    apply (hAc i).exists_isOpen_closure_subset
    exact ((hV i).1.inter isOpen_ball).mem_nhdsSet.mpr
      (subset_inter (hV i).2 (hb i))
  choose U hUo hAU hUV using hshrink
  refine ⟨n, U, hUo, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCov (mem_univ (⟨x, hx⟩ : B)))
    exact mem_iUnion.mpr ⟨i, hAU i ⟨⟨x, hx⟩, hi, rfl⟩⟩
  · intro i j hij
    exact (hVd hij).mono (fun _ hx => (hUV i hx).1) (fun _ hx => (hUV j hx).1)
  · intro i
    have hdiam : diam (closure (U i)) ≤ 2 * (ε / 4) :=
      diam_le_of_subset_closedBall (by positivity)
        (fun _ hx => ball_subset_closedBall ((hUV i hx).2))
    linarith

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RationalTimeIntervals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every open time interval is the directed union of the rational closed
intervals contained in it. This passes the coded constraints to open pieces. -/

open Set

noncomputable section

namespace CircleDomainRigidity

theorem rationalTime_toTime_monotone : Monotone RationalPathTime.toTime := by
  intro a b hab
  change (a.val : ℝ) ≤ (b.val : ℝ)
  exact_mod_cast hab

theorem rationalTime_toTime_min (a b : RationalPathTime) :
    (min a b).toTime = min a.toTime b.toTime := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (rationalTime_toTime_monotone h)]
  · rw [min_eq_right h, min_eq_right (rationalTime_toTime_monotone h)]

theorem rationalTime_toTime_max (a b : RationalPathTime) :
    (max a b).toTime = max a.toTime b.toTime := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (rationalTime_toTime_monotone h)]
  · rw [max_eq_left h, max_eq_left (rationalTime_toTime_monotone h)]

theorem innerRationalInterval_directed (a b : PathTime) :
    Directed (· ⊆ ·) (innerRationalInterval a b) := by
  intro p q
  let r : InnerRationalInterval a b := ⟨(min p.val.1 q.val.1, max p.val.2 q.val.2), by
    change a < (min p.val.1 q.val.1).toTime ∧ (max p.val.2 q.val.2).toTime < b
    simp only [rationalTime_toTime_min, rationalTime_toTime_max, lt_min_iff, max_lt_iff]
    exact ⟨⟨p.property.1, q.property.1⟩, ⟨p.property.2, q.property.2⟩⟩⟩
  refine ⟨r, ?_, ?_⟩
  · exact Icc_subset_Icc (rationalTime_toTime_monotone (min_le_left _ _))
      (rationalTime_toTime_monotone (le_max_left _ _))
  · exact Icc_subset_Icc (rationalTime_toTime_monotone (min_le_right _ _))
      (rationalTime_toTime_monotone (le_max_right _ _))

theorem iUnion_innerRationalInterval (a b : PathTime) :
    (⋃ p : InnerRationalInterval a b, innerRationalInterval a b p) = Ioo a b := by
  ext t
  constructor
  · intro ht
    obtain ⟨p, hp⟩ := mem_iUnion.mp ht
    exact ⟨p.property.1.trans_le hp.1, hp.2.trans_lt p.property.2⟩
  · intro ht
    obtain ⟨q, haq, hqt⟩ := exists_rat_btwn (show (a : ℝ) < (t : ℝ) from ht.1)
    obtain ⟨r, htr, hrb⟩ := exists_rat_btwn (show (t : ℝ) < (b : ℝ) from ht.2)
    have hq : q ∈ Icc (0 : ℚ) 1 := by
      constructor
      · exact_mod_cast a.property.1.trans haq.le
      · exact_mod_cast hqt.le.trans t.property.2
    have hr : r ∈ Icc (0 : ℚ) 1 := by
      constructor
      · exact_mod_cast t.property.1.trans htr.le
      · exact_mod_cast hrb.le.trans b.property.2
    let p : InnerRationalInterval a b := ⟨(⟨q, hq⟩, ⟨r, hr⟩), ⟨haq, hrb⟩⟩
    exact mem_iUnion.mpr ⟨p, hqt.le, htr.le⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AffinePathTime
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing affine restriction maps and their clipped inverse on the
standard path interval. Interior inequalities remain exact after clipping. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem rescalePathTime_lt_iff {a b : PathTime} (hab : a < b) (s t : PathTime)
    (ht : ⊥ < t ∧ t < ⊤) :
    rescalePathTime a b s < t ↔ s < affinePathTime a b t := by
  change (rescalePathTime a b s : ℝ) < (t : ℝ) ↔ (s : ℝ) < affinePathTime a b t
  rw [rescalePathTime_coe, max_lt_iff, affinePathTime_coe]
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : (t : ℝ) < 1 := ht.2
  have hd : 0 < (b : ℝ) - a := sub_pos.mpr hab
  rw [and_iff_right ht0, min_lt_iff, or_iff_right (not_lt.mpr ht1.le), div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem lt_rescalePathTime_iff {a b : PathTime} (hab : a < b) (s t : PathTime)
    (ht : ⊥ < t ∧ t < ⊤) :
    t < rescalePathTime a b s ↔ affinePathTime a b t < s := by
  change (t : ℝ) < (rescalePathTime a b s : ℝ) ↔ (affinePathTime a b t : ℝ) < s
  rw [rescalePathTime_coe, lt_max_iff, affinePathTime_coe]
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : (t : ℝ) < 1 := ht.2
  have hd : 0 < (b : ℝ) - a := sub_pos.mpr hab
  rw [or_iff_right (not_lt.mpr ht0.le), lt_min_iff, and_iff_right ht1, lt_div_iff₀ hd]
  constructor <;> intro h <;> nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountablePathTimes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Decreasing dyadic intervals for the countable collar concatenation. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem collarCell_disjoint_interiors :
    Pairwise (Disjoint on (fun n => Ioo (collarTime (n + 1)) (collarTime n))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hb := collarTime_strictAnti.antitone (Nat.succ_le_of_lt h)
    exact (hi.1.trans hj.2).not_ge hb
  · have hb := collarTime_strictAnti.antitone (Nat.succ_le_of_lt h)
    exact (hj.1.trans hi.2).not_ge hb

theorem collarCell_complement_countable :
    (⋃ n, Ioo (collarTime (n + 1)) (collarTime n))ᶜ.Countable := by
  apply (Set.countable_range collarTime |>.insert ⊥).mono
  intro t ht
  by_cases hzero : t = ⊥
  · exact Or.inl hzero
  · obtain ⟨n, hlow, hhigh⟩ := exists_collarTime_cell (bot_lt_iff_ne_bot.mpr hzero)
    have heq : t = collarTime n := by
      by_contra hne
      have hint : t ∈ Ioo (collarTime (n + 1)) (collarTime n) :=
        ⟨hlow, hhigh.lt_of_ne hne⟩
      exact ht (mem_iUnion.mpr ⟨n, hint⟩)
    exact Or.inr ⟨n, heq.symm⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CountablePathConcatenation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual countable path concatenation, including the new limiting endpoint.
The shrinking-tail hypothesis is the one supplied by nested dust collars. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

theorem collarConcatenation_zero (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail :
    collarConcatenation p γ hjoin htail ⊥ = p := by
  simp [collarConcatenation, collarConcatenationFun]

theorem collarConcatenation_one (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail :
    collarConcatenation p γ hjoin htail ⊤ = γ 0 ⊤ := by
  have h := collarConcatenation_affine p γ hjoin htail 0 ⊤
  rwa [affinePathTime_one, collarTime_zero] at h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PathOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation of a rectifiable metric path, and its mean under a law.
The measure records arclength with multiplicity, including repeated traversals. -/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem lintegral_pathOccupation (γ : RectifiablePath X) {g : X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂pathOccupation γ = ∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ :=
  lintegral_map hg γ.val.continuous.measurable

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalSubpaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual physical lifts of quotient paths on a compact time interval.
The quotient is inverted only where it is a homeomorphism. Constant extension
at the interval ends gives an ordinary continuous physical path. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem physicalSubpath_projects {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    (π : Y → X) (hπ : ∀ y : G, π y = (e y).val)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) (t : PathTime) :
    π (physicalSubpath e hab γ t) = γ.val (timeClip a b t) := by
  change π (e.symm ⟨γ.val (timeClip a b t), _⟩).val = _
  rw [hπ]
  simp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PhysicalDyadicLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Borel dyadic physical length and finite-stage occupation data.
Every length here uses the physical metric after inverting the quotient. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

variable [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem physicalStageOccupation_univ (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hγ : physicalDomainLength e y₀ γ < ∞) (n : ℕ) :
    physicalStageOccupation e y₀ n γ univ = physicalStageLength e y₀ n γ := by
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply,
    rectifiableOccupationCode_univ (physicalDyadicPath_rectifiable e y₀ hγ n _)]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DyadicPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Borel limit of the increasing dyadic physical occupation measures.
Its mass is the dyadic domain-length functional, and it is supported in the
physical domain. `PhysicalLengthCharacterization` identifies the associated
time measure with compact-interval arclength and componentwise exhaustion. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem dyadicPhysicalOccupation_apply (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    {s : Set Y} (hs : MeasurableSet s) :
    dyadicPhysicalOccupation e y₀ γ s = ⨆ n, physicalStageOccupation e y₀ n γ.val s :=
  increasingMeasureLimit_apply _ _ hs

theorem dyadicPhysicalOccupation_univ (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    dyadicPhysicalOccupation e y₀ γ univ = physicalDomainLength e y₀ γ.val := by
  rw [dyadicPhysicalOccupation_apply _ _ _ MeasurableSet.univ]
  simp only [physicalStageOccupation_univ e y₀ γ.property]
  rfl

instance instIsFiniteMeasureDyadicPhysicalOccupation (e : G ≃ₜ U) (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    IsFiniteMeasure (dyadicPhysicalOccupation e y₀ γ) :=
  ⟨by rw [dyadicPhysicalOccupation_univ]; exact γ.property⟩

theorem physicalStageOccupation_compl (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    physicalStageOccupation e y₀ n γ.val Gᶜ = 0 := by
  classical
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hrect := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hrect ⊢
    rw [rectifiableOccupationCode_eq hrect, pathOccupation,
      Measure.map_apply (physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩).continuous.measurable
        hG.measurableSet.compl]
    have heq : (physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩) ⁻¹' Gᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact ht (physicalSubpath_mem e _ _ t)
    rw [heq, measure_empty]
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi, rectifiableOccupationCode_const]

theorem dyadicPhysicalOccupation_compl (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) : dyadicPhysicalOccupation e y₀ γ Gᶜ = 0 := by
  rw [dyadicPhysicalOccupation_apply _ _ _ hG.measurableSet.compl]
  simp [physicalStageOccupation_compl e hG y₀ γ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PhysicalOccupationPushforward
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical occupation is the pushforward of domain-time arclength, with
parameter multiplicity retained. The value assigned at dust times is irrelevant. -/

open Set MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalValue_subpath (e : G ≃ₜ U) (y₀ : Y)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b)
    {t : PathTime} (ht : t ∈ Icc a b) :
    physicalValue e y₀ (γ.val t) = physicalSubpath e hab γ t := by
  simp only [physicalValue, dite_eq_left (γ.property ht), physicalSubpath,
    ContinuousMap.coe_mk, timeClip, min_eq_right ht.2, max_eq_right ht.1]

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem measurable_physicalValue (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalValue e y₀) :=
  (continuous_subtype_val.comp e.symm.continuous).measurable.dite
    measurable_const hU.measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
theorem physicalDyadicLength_map (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) (i : Fin (2 ^ n)) :
    (rectifiableLengthCode (physicalDyadicPath e y₀ n i γ.val)).map
        (physicalValue e y₀ ∘ γ.val) =
      rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ.val) := by
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [rectifiableLengthCode_eq hr, rectifiableOccupationCode_eq hr, pathOccupation]
    apply Measure.map_congr
    have hae : ∀ᵐ t ∂pathLengthMeasure
        ⟨physicalSubpath e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩, hr⟩,
        t ∈ Icc (dyadicLeft n i) (dyadicRight n i) := by
      have heq := physicalSubpath_timeLength_portion e (dyadicLeft_le_right n i) ⟨γ.val, hi⟩ hr
      rw [rectifiableLengthCode_eq hr] at heq
      rw [heq]
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hae] with t ht
    exact physicalValue_subpath e y₀ (dyadicLeft_le_right n i) ⟨γ.val, hi⟩ ht
  · simp [physicalDyadicPath, totalPhysicalSubpath, hi,
      rectifiableLengthCode_const, rectifiableOccupationCode_const]

theorem physicalStageTimeLength_map (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    (physicalStageTimeLength e y₀ n γ.val).map (physicalValue e y₀ ∘ γ.val) =
      physicalStageOccupation e y₀ n γ.val := by
  have hm := (measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  simp only [physicalStageTimeLength, physicalStageOccupation, Measure.coe_finsetSum,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← physicalDyadicLength_map e y₀ γ n i, Measure.map_apply hm hs]

theorem physicalTimeLength_map (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) :
    (physicalTimeLength e y₀ γ).map (physicalValue e y₀ ∘ γ.val) =
      dyadicPhysicalOccupation e y₀ γ := by
  have hm := (measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable
  ext s hs
  rw [Measure.map_apply hm hs, physicalTimeLength_apply _ _ _ (hm hs),
    dyadicPhysicalOccupation_apply _ _ _ hs]
  congr 1
  funext n
  rw [← physicalStageTimeLength_map e hU y₀ γ n, Measure.map_apply hm hs]

theorem physicalOccupation_integral (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ =
      ∫⁻ t, g (physicalValue e y₀ (γ.val t)) ∂physicalTimeLength e y₀ γ := by
  rw [← physicalTimeLength_map e hU y₀ γ]
  exact lintegral_map hg ((measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ResidualOpenIntervals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCountableElemFirstUncountableIio _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coded residual-contact inequalities extend from rational closed
intervals to every open time interval, by directed continuity from below. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace Z]

omit [MeasurableSpace Z] in
theorem residualIncidence_time_mono (B : Set X) (R : Set (Z × X)) (P : Set X)
    (Γ : TaggedPath X) {I J : Set PathTime} (hIJ : I ⊆ J) :
    {z | (Γ, z) ∈ residualIncidence B I R P} ⊆
      {z | (Γ, z) ∈ residualIncidence B J R P} := by
  rintro z ⟨t, ht, hI, hR, hP⟩
  exact ⟨t, ht, hIJ hI, hR, hP⟩

omit [MeasurableSpace Z] in
theorem residualToll_time_mono (B : Set X) (m : X → ℝ≥0∞) (Γ : TaggedPath X)
    {I J : Set PathTime} (hIJ : I ⊆ J) : residualToll B I m Γ ≤ residualToll B J m Γ := by
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases ht : t ∈ residualTimes B Γ ∧ t ∈ I
  · have htJ : t ∈ residualTimes B Γ ∧ t ∈ J := ⟨ht.1, hIJ ht.2⟩
    simp only [ite_eq_left ht, ite_eq_left htJ]
    exact le_rfl
  · simp only [ite_eq_right ht]
    exact bot_le

omit [MeasurableSpace Z] in
theorem residualIncidence_time_iUnion {ι : Type*} (B : Set X) (R : Set (Z × X))
    (P : Set X) (Γ : TaggedPath X) (I : ι → Set PathTime) :
    {z | (Γ, z) ∈ residualIncidence B (⋃ i, I i) R P} =
      ⋃ i, {z | (Γ, z) ∈ residualIncidence B (I i) R P} := by
  ext z
  constructor
  · rintro ⟨t, ht, hI, hR, hP⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hI
    exact mem_iUnion.mpr ⟨i, t, ht, hi, hR, hP⟩
  · intro h
    obtain ⟨i, t, ht, hi, hR, hP⟩ := mem_iUnion.mp h
    exact ⟨t, ht, mem_iUnion.mpr ⟨i, hi⟩, hR, hP⟩

theorem residualIncidenceBound_directed_union {ι : Type*} [Countable ι]
    (B : Set X) (R : Set (Z × X)) (P : Set X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (Γ : TaggedPath X) (I : ι → Set PathTime) (hd : Directed (· ⊆ ·) I)
    (h : ∀ i, ResidualIncidenceBound B (I i) R P ν m Γ) :
    ResidualIncidenceBound B (⋃ i, I i) R P ν m Γ := by
  have hdir : Directed (· ⊆ ·) (fun i => {z | (Γ, z) ∈ residualIncidence B (I i) R P}) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hd i j
    exact ⟨k, residualIncidence_time_mono B R P Γ hik, residualIncidence_time_mono B R P Γ hjk⟩
  unfold ResidualIncidenceBound
  rw [residualIncidence_time_iUnion, hdir.measure_iUnion]
  exact iSup_le fun i => (h i).trans
    (residualToll_time_mono B (deletedWeight P m) Γ (subset_iUnion I i))

theorem residualIncidenceBound_open_of_rational
    (B : Set X) (R : Set (Z × X)) (P : Set X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (Γ : TaggedPath X)
    (h : ∀ a b : RationalPathTime, ResidualIncidenceBound B (Icc a.toTime b.toTime) R P ν m Γ)
    (a b : PathTime) : ResidualIncidenceBound B (Ioo a b) R P ν m Γ := by
  rw [← iUnion_innerRationalInterval a b]
  exact residualIncidenceBound_directed_union B R P ν m Γ (innerRationalInterval a b)
    (innerRationalInterval_directed a b) (fun p => h p.val.1 p.val.2)

theorem residualConstraintFamily_open (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) (h : ResidualConstraintFamily B R P ν m Γ)
    (i n : ℕ) (a b : PathTime) :
    ResidualIncidenceBound B (Ioo a b) (R i) (P i n) (ν i) (m i) Γ :=
  residualIncidenceBound_open_of_rational B (R i) (P i n) (ν i) (m i) Γ (h i n) a b

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ResidualClosedIntervals
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton incidence estimates supply the endpoints omitted by open
pieces. The original rational constraints therefore hold on every closed
time interval, without a local finiteness assumption on the prior toll. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace Z]

omit [MeasurableSpace Z] in
theorem residualToll_union (B : Set X) (m : X → ℝ≥0∞) (Γ : TaggedPath X)
    {I J : Set PathTime} (hIJ : Disjoint I J) :
    residualToll B (I ∪ J) m Γ = residualToll B I m Γ + residualToll B J m Γ := by
  unfold residualToll
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro t
  by_cases hr : t ∈ residualTimes B Γ
  · by_cases hi : t ∈ I
    · have hj : t ∉ J := fun hj => Set.disjoint_left.mp hIJ hi hj
      simp [hr, hi, hj]
    · simp [hr, hi]
  · simp [hr]

omit [MeasurableSpace Z] in
theorem residualIncidence_time_union (B : Set X) (R : Set (Z × X)) (P : Set X)
    (Γ : TaggedPath X) (I J : Set PathTime) :
    {z | (Γ, z) ∈ residualIncidence B (I ∪ J) R P} =
      {z | (Γ, z) ∈ residualIncidence B I R P} ∪
      {z | (Γ, z) ∈ residualIncidence B J R P} := by
  ext z
  constructor
  · rintro ⟨t, ht, hi | hj, hR, hp⟩
    · exact Or.inl ⟨t, ht, hi, hR, hp⟩
    · exact Or.inr ⟨t, ht, hj, hR, hp⟩
  · rintro (⟨t, ht, hi, hR, hp⟩ | ⟨t, ht, hj, hR, hp⟩)
    · exact ⟨t, ht, Or.inl hi, hR, hp⟩
    · exact ⟨t, ht, Or.inr hj, hR, hp⟩

theorem residualIncidenceBound_union (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞) (Γ : TaggedPath X) {I J : Set PathTime}
    (hIJ : Disjoint I J) (hI : ResidualIncidenceBound B I R P ν m Γ)
    (hJ : ResidualIncidenceBound B J R P ν m Γ) :
    ResidualIncidenceBound B (I ∪ J) R P ν m Γ := by
  unfold ResidualIncidenceBound at *
  rw [residualIncidence_time_union, residualToll_union B (deletedWeight P m) Γ hIJ]
  exact (measure_union_le _ _).trans (add_le_add hI hJ)

omit [MeasurableSpace Z] in
theorem residualToll_singleton (B : Set X) (m : X → ℝ≥0∞) (Γ : TaggedPath X) (a : PathTime) :
    residualToll B {a} m Γ = if a ∈ residualTimes B Γ then m (Γ.1 a) else 0 := by
  unfold residualToll
  rw [tsum_eq_single a (fun t ht => by simp [ht])]
  simp

theorem residualIncidenceBound_singleton (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞) (Γ : TaggedPath X)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x) (a : PathTime) :
    ResidualIncidenceBound B {a} R P ν m Γ := by
  by_cases h : a ∈ residualTimes B Γ ∧ Γ.1 a ∉ P
  · unfold ResidualIncidenceBound
    rw [residualToll_singleton, ite_eq_left h.1]
    have hsub : {z | (Γ, z) ∈ residualIncidence B {a} R P} ⊆ {z | (z, Γ.1 a) ∈ R} := by
      rintro z ⟨t, _, ht, hr, _⟩
      have he : t = a := ht
      change (z, Γ.1 a) ∈ R
      simpa only [he] using hr
    exact (measure_mono hsub).trans (by simpa [deletedWeight, h.2] using hpoint (Γ.1 a))
  · have hz : {z | (Γ, z) ∈ residualIncidence B {a} R P} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨t, ht, ha, _, hp⟩
      have he : t = a := ha
      exact h (he ▸ ⟨ht, hp⟩)
    unfold ResidualIncidenceBound
    rw [hz, measure_empty]
    exact bot_le

theorem residualIncidenceBound_closed_of_open
    (B : Set X) (R : Set (Z × X)) (P : Set X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (Γ : TaggedPath X)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (h : ∀ a b : PathTime, ResidualIncidenceBound B (Ioo a b) R P ν m Γ)
    (a b : PathTime) : ResidualIncidenceBound B (Icc a b) R P ν m Γ := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hleft := residualIncidenceBound_singleton B R P ν m Γ hpoint a
    have hright := residualIncidenceBound_singleton B R P ν m Γ hpoint b
    have hopen := h a b
    have hdis : Disjoint ({a} : Set PathTime) (Ioo a b) := by simp
    have hfirst := residualIncidenceBound_union B R P ν m Γ hdis hleft hopen
    have hdis' : Disjoint (({a} : Set PathTime) ∪ Ioo a b) {b} := by simp [hab.ne']
    have hall := residualIncidenceBound_union B R P ν m Γ hdis' hfirst hright
    have he : (({a} : Set PathTime) ∪ Ioo a b) ∪ {b} = Icc a b := by
      rw [union_comm {a}, Ioo_union_left hab, Ico_union_right hab.le]
    rwa [he] at hall
  · simpa only [Icc_self] using residualIncidenceBound_singleton B R P ν m Γ hpoint a
  · simp [ResidualIncidenceBound, residualIncidence, residualToll, Icc_eq_empty_of_lt hba]

theorem residualIncidenceBound_closed_of_rational
    (B : Set X) (R : Set (Z × X)) (P : Set X) (ν : Measure Z) (m : X → ℝ≥0∞)
    (Γ : TaggedPath X)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (h : ∀ a b : RationalPathTime, ResidualIncidenceBound B (Icc a.toTime b.toTime) R P ν m Γ)
    (a b : PathTime) : ResidualIncidenceBound B (Icc a b) R P ν m Γ :=
  residualIncidenceBound_closed_of_open B R P ν m Γ hpoint
    (residualIncidenceBound_open_of_rational B R P ν m Γ h) a b

theorem residualConstraintFamily_closed (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) (h : ResidualConstraintFamily B R P ν m Γ)
    (hpoint : ∀ i x, ν i {z | (z, x) ∈ R i} ≤ m i x)
    (i n : ℕ) (a b : PathTime) :
    ResidualIncidenceBound B (Icc a b) (R i) (P i n) (ν i) (m i) Γ :=
  residualIncidenceBound_closed_of_rational B (R i) (P i n) (ν i) (m i) Γ
    (hpoint i) (h i n) a b

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CountableImageIncidence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence bounds for the countable image exposed by discarded constant
tags. The estimate charges parameter times, and hence retains multiplicity. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Z : Type*}

theorem timeToll_eq_indicator (γ : T → X) (A : Set T) (m : X → ℝ≥0∞) :
    timeToll γ A m = ∑' t, if t ∈ A then m (γ t) else 0 := by
  exact tsum_subtype A (fun t => m (γ t))

theorem timeIncidence_iUnion {ι : Type*} (R : Set (Z × X)) (γ : T → X)
    (A : ι → Set T) : timeIncidence R γ (⋃ i, A i) = ⋃ i, timeIncidence R γ (A i) := by
  ext z
  simp only [timeIncidence, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨t, ⟨i, hi⟩, ht⟩
    exact ⟨i, t, hi, ht⟩
  · rintro ⟨i, t, hi, ht⟩
    exact ⟨t, ⟨i, hi⟩, ht⟩

theorem timeToll_mono (γ : T → X) (m : X → ℝ≥0∞) {A C : Set T}
    (h : A ⊆ C) : timeToll γ A m ≤ timeToll γ C m :=
  ENNReal.tsum_mono_subtype (fun t => m (γ t)) h

theorem timeToll_iUnion {ι : Type*} (γ : T → X) (m : X → ℝ≥0∞)
    (A : ι → Set T) (hA : Pairwise (Disjoint on A)) :
    timeToll γ (⋃ i, A i) m = ∑' i, timeToll γ (A i) m := by
  exact ENNReal.tsum_biUnion (f := fun t => m (γ t)) (fun i _ j _ hij => hA hij)

variable [MeasurableSpace Z]

theorem countable_image_incidence_bound (R : Set (Z × X)) (γ : T → X)
    (A : Set T) (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x) (hA : (γ '' A).Countable) :
    ν (timeIncidence R γ A) ≤ timeToll γ A m := by
  let : Countable (γ '' A) := hA.to_subtype
  have he : timeIncidence R γ A = ⋃ x : γ '' A, {z | (z, x.val) ∈ R} := by
    ext z
    constructor
    · rintro ⟨t, ht, hr⟩
      exact mem_iUnion.mpr ⟨⟨γ t, ⟨t, ht, rfl⟩⟩, hr⟩
    · intro hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp hz
      obtain ⟨t, ht, he⟩ := x.property
      exact ⟨t, ht, he ▸ hx⟩
  let f : A → γ '' A := fun t => ⟨γ t, ⟨t, t.property, rfl⟩⟩
  have hf : Surjective f := by
    intro x
    obtain ⟨t, ht, he⟩ := x.property
    exact ⟨⟨t, ht⟩, Subtype.ext he⟩
  calc
    ν (timeIncidence R γ A) ≤ ∑' x : γ '' A, ν {z | (z, x.val) ∈ R} := by
      rw [he]
      exact measure_iUnion_le _
    _ ≤ ∑' x : γ '' A, m x := ENNReal.tsum_le_tsum fun x => hpoint x
    _ ≤ timeToll γ A m := ENNReal.tsum_le_tsum_comp_of_surjective hf (fun x => m x)

theorem countable_image_deleted_incidence_bound (R : Set (Z × X)) (P : Set X)
    (γ : T → X) (A : Set T) (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x) (hA : (γ '' A).Countable) :
    ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ A) ≤ timeToll γ A (deletedWeight P m) := by
  apply countable_image_incidence_bound _ γ A ν _ _ hA
  intro x
  by_cases hx : x ∈ P
  · simp [deletedWeight, hx]
  · simpa [deletedWeight, hx] using hpoint x

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ResidualPieceAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsCompletelyMetrizableSpaceTagSlot _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instPolishSpaceTagSlot _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assembly of residual-contact estimates on disjoint time pieces. No
disjointness of their images is required: a repeated visit is paid again. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Z : Type*}

theorem timeIncidence_union (R : Set (Z × X)) (γ : T → X) (A C : Set T) :
    timeIncidence R γ (A ∪ C) = timeIncidence R γ A ∪ timeIncidence R γ C := by
  ext z
  constructor
  · rintro ⟨t, ht | ht, hr⟩
    · exact Or.inl ⟨t, ht, hr⟩
    · exact Or.inr ⟨t, ht, hr⟩
  · rintro (⟨t, ht, hr⟩ | ⟨t, ht, hr⟩)
    · exact ⟨t, Or.inl ht, hr⟩
    · exact ⟨t, Or.inr ht, hr⟩

theorem timeToll_union (γ : T → X) (m : X → ℝ≥0∞) {A C : Set T}
    (hdis : Disjoint A C) : timeToll γ (A ∪ C) m = timeToll γ A m + timeToll γ C m := by
  simp only [timeToll_eq_indicator]
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro t
  by_cases ha : t ∈ A
  · have hc : t ∉ C := fun hc => disjoint_left.mp hdis ha hc
    simp [ha, hc]
  · simp [ha]

variable [MeasurableSpace Z]

theorem timeIncidence_bound_with_countable_remainder {ι : Type*} [Countable ι]
    (R : Set (Z × X)) (P : Set X) (γ : T → X) (A A₀ : Set T) (C : ι → Set T)
    (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hcover : A = A₀ ∪ ⋃ i, C i)
    (hdis : Pairwise (Disjoint on C)) (hdis₀ : Disjoint A₀ (⋃ i, C i))
    (hcount : (γ '' A₀).Countable)
    (hbound : ∀ i, ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ (C i)) ≤
      timeToll γ (C i) (deletedWeight P m)) :
    ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ A) ≤
      timeToll γ A (deletedWeight P m) := by
  rw [hcover, timeIncidence_union, timeToll_union γ _ hdis₀,
    timeIncidence_iUnion, timeToll_iUnion γ _ C hdis]
  exact (measure_union_le _ _).trans (add_le_add
    (countable_image_deleted_incidence_bound R P γ A₀ ν m hpoint hcount)
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hbound)))

variable [MetricSpace X]

omit [MeasurableSpace Z] in
theorem residualIncidence_eq_timeIncidence (B : Set X) (I : Set PathTime)
    (R : Set (Z × X)) (P : Set X) (Γ : TaggedPath X) :
    {z | (Γ, z) ∈ residualIncidence B I R P} =
      timeIncidence {q | q ∈ R ∧ q.2 ∉ P} Γ.1 (residualTimes B Γ ∩ I) := by
  ext z
  constructor
  · rintro ⟨t, ht, hi, hr, hp⟩
    exact ⟨t, ⟨ht, hi⟩, hr, hp⟩
  · rintro ⟨t, ⟨ht, hi⟩, hr, hp⟩
    exact ⟨t, ht, hi, hr, hp⟩

omit [MeasurableSpace Z] in
theorem residualToll_eq_timeToll (B : Set X) (I : Set PathTime)
    (m : X → ℝ≥0∞) (Γ : TaggedPath X) :
    residualToll B I m Γ = timeToll Γ.1 (residualTimes B Γ ∩ I) m := by
  rw [timeToll_eq_indicator]
  unfold residualToll
  apply tsum_congr
  intro t
  by_cases h : t ∈ residualTimes B Γ ∧ t ∈ I <;> simp [h]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_TagTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tag-tuple measures. Tuple components retain the label list;
slot weights depend only on the slot number and have finite total mass. -/

open Set MeasureTheory TopologicalSpace Topology
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem slotWeight_pos (k : ℕ) : 0 < slotWeight k := by
  unfold slotWeight
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))

theorem tsum_slotWeight : ∑' k, slotWeight k = 2 := ENNReal.tsum_geometric_two

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_NarrowedTagRules
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Narrowing a tag changes only its time interval. Every retained tag has
the original level tuple and continues to obey the level and null-set rules. -/

open Set
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

theorem active_mem_tagTupleExcluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (q : TagData) : (Sum.inr q : TagSlot) ∈ tagTupleExcluded N ↔ q.2.2.1 ∈ N q.1 q.2.1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    obtain ⟨l, p, hp, he⟩ := mem_iUnion.mp hn
    have hq : (⟨n, l, p⟩ : TagData) = q := Sum.inr.inj he
    cases hq
    exact hp.1
  · intro h
    exact mem_iUnion.mpr ⟨q.1, mem_iUnion.mpr ⟨q.2.1, q.2.2, ⟨h, mem_univ _⟩, rfl⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AffineTagRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual affine restriction of tagged paths. Reparameterized tags keep
their old tuples; empty and constant tag pieces become inactive. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

theorem affineRawTag_interval {a b : PathTime} (hab : a < b) (τ : TagSlot)
    {t : PathTime} (ht : ⊥ < t ∧ t < ⊤) :
    t ∈ Ioo (tagLeft (affineRawTag a b τ)) (tagRight (affineRawTag a b τ)) ↔
      affinePathTime a b t ∈ Ioo (tagLeft τ) (tagRight τ) := by
  cases τ with
  | inl u => simp [affineRawTag, tagLeft, tagRight]
  | inr q =>
    exact and_congr (rescalePathTime_lt_iff hab _ t ht) (lt_rescalePathTime_iff hab _ t ht)

theorem affineRawTag_tuple_excluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (a b : PathTime) (τ : TagSlot) :
    affineRawTag a b τ ∈ tagTupleExcluded N ↔ τ ∈ tagTupleExcluded N := by
  cases τ with
  | inl u => rfl
  | inr q =>
    exact (active_mem_tagTupleExcluded_iff N
      ⟨q.1, q.2.1, q.2.2.1, rescalePathTime a b q.2.2.2.1,
        rescalePathTime a b q.2.2.2.2⟩).trans (active_mem_tagTupleExcluded_iff N q).symm

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem affineRawTag_level_iff (H : ℕ → Set (UnitAddCircle × X))
    (a b : PathTime) (τ : TagSlot) (x : X) :
    (affineRawTag a b τ, x) ∈ tagLevelGraph H ↔ (τ, x) ∈ tagLevelGraph H := by
  cases τ <;> rfl

theorem affineRestrictedTag_rules (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {a b : PathTime} (hab : a < b) (γ : C(PathTime, X)) (τ : TagSlot)
    (hc : (γ, τ) ∈ tagContainment H) (hn : τ ∉ tagTupleExcluded N) :
    (affineRestrictedPath a b γ, affineRestrictedTag a b γ τ) ∈ validTagShape ∧
      (affineRestrictedPath a b γ, affineRestrictedTag a b γ τ) ∈ tagContainment H ∧
      affineRestrictedTag a b γ τ ∉ tagTupleExcluded N := by
  by_cases h : (affineRestrictedPath a b γ, affineRawTag a b τ) ∈ nonconstantTagSegment
  · rw [affineRestrictedTag, ite_eq_left h]
    refine ⟨Or.inr h, ?_, fun hN => hn ((affineRawTag_tuple_excluded_iff N a b τ).mp hN)⟩
    intro t hl hr
    have ht : ⊥ < t ∧ t < ⊤ := ⟨lt_of_le_of_lt bot_le hl, lt_of_lt_of_le hr le_top⟩
    have hold := (affineRawTag_interval hab τ ht).mp ⟨hl, hr⟩
    exact (affineRawTag_level_iff H a b τ _).mpr (hc _ hold.1 hold.2)
  · rw [affineRestrictedTag, ite_eq_right h]
    exact inactiveTag_rules H N _

theorem tagRules_affineRestricted (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {a b : PathTime} (hab : a < b) (Γ : TaggedPath X) (hΓ : TagRules H N Γ) :
    TagRules H N (affineRestrictedTaggedPath a b Γ) := by
  intro k
  exact affineRestrictedTag_rules H N hab Γ.1 (Γ.2 k) (hΓ k).2.1 (hΓ k).2.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AffineIntervalImages
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open-piece images under the affine parameter map, including clipping
of a test interval that crosses either endpoint of the piece. -/

open Set

noncomputable section

namespace CircleDomainRigidity

theorem rescalePathTime_mem_Ioo {a b : PathTime} (hab : a < b) {t : PathTime}
    (ht : t ∈ Ioo a b) : rescalePathTime a b t ∈ Ioo (⊥ : PathTime) ⊤ := by
  have hf := affinePathTime_strictMono hab
  have he := affine_rescalePathTime hab ⟨ht.1.le, ht.2.le⟩
  constructor
  · apply hf.lt_iff_lt.mp
    rw [affinePathTime_zero, he]
    exact ht.1
  · apply hf.lt_iff_lt.mp
    rw [affinePathTime_one, he]
    exact ht.2

theorem affinePathTime_mem_Ioo {a b : PathTime} (hab : a < b) {t : PathTime}
    (ht : t ∈ Ioo (⊥ : PathTime) ⊤) : affinePathTime a b t ∈ Ioo a b := by
  change a < affinePathTime a b t ∧ affinePathTime a b t < b
  simpa only [affinePathTime_zero, affinePathTime_one] using
    And.intro (affinePathTime_strictMono hab ht.1) (affinePathTime_strictMono hab ht.2)

theorem affine_image_rescaled_Ioo {a b : PathTime} (hab : a < b) (c d : PathTime) :
    affinePathTime a b '' Ioo (rescalePathTime a b c) (rescalePathTime a b d) =
      Ioo a b ∩ Ioo c d := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hti : t ∈ Ioo (⊥ : PathTime) ⊤ :=
      ⟨lt_of_le_of_lt bot_le ht.1, lt_of_lt_of_le ht.2 le_top⟩
    exact ⟨affinePathTime_mem_Ioo hab hti,
      (rescalePathTime_lt_iff hab c t hti).mp ht.1,
      (lt_rescalePathTime_iff hab d t hti).mp ht.2⟩
  · rintro ⟨hx, htest⟩
    have hti := rescalePathTime_mem_Ioo hab hx
    have he := affine_rescalePathTime hab ⟨hx.1.le, hx.2.le⟩
    refine ⟨rescalePathTime a b x, ?_, he⟩
    constructor
    · apply (rescalePathTime_lt_iff hab c _ hti).mpr
      rw [he]
      exact htest.1
    · apply (lt_rescalePathTime_iff hab d _ hti).mpr
      rw [he]
      exact htest.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CountablePhysicalCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical time and weighted occupation measures for collar
concatenations. Parameter multiplicity is preserved. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem physicalCost_collarPieces (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (η : FinitePhysicalPath e y₀) (γ : ℕ → FinitePhysicalPath e y₀)
    (hmatch : ∀ n s, η.val (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ η) =
      ∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (γ n) := by
  rw [physicalOccupation_integral e hU y₀ η g hg,
    physicalTimeLength_collarPieces e hU y₀ η γ hmatch, lintegral_sum_measure]
  apply tsum_congr
  intro n
  have hmeas : Measurable (fun t : PathTime => g (physicalValue e y₀ (η.val t))) :=
    hg.comp ((measurable_physicalValue e hU y₀).comp η.val.continuous.measurable)
  rw [lintegral_map hmeas
    (affinePathTime _ _).continuous.measurable, physicalOccupation_integral e hU y₀ (γ n) g hg]
  apply lintegral_congr
  intro t
  simp only [hmatch]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PositivePhysicalCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive physical density pays for the physical lengths of all
selected collar fragments. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem physicalCost_ge_length (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (c : ℝ≥0∞)
    (hpos : ∀ y ∈ G, c ≤ g y) :
    c * physicalDomainLength e y₀ γ.val ≤ ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ := by
  rw [← dyadicPhysicalOccupation_univ e y₀ γ, ← lintegral_const]
  apply lintegral_mono_ae
  have hmem : ∀ᵐ y ∂dyadicPhysicalOccupation e y₀ γ, y ∈ G := by
    rw [ae_iff]
    exact dyadicPhysicalOccupation_compl e hG y₀ γ
  filter_upwards [hmem] with y hy
  exact hpos y hy

theorem sum_physicalLength_finite_of_cost (e : G ≃ₜ U) (hG : IsOpen G) (y₀ : Y)
    (γ : ℕ → FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (c : ℝ≥0∞)
    (hc : c ≠ 0) (hpos : ∀ y ∈ G, c ≤ g y)
    (hcost : (∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (γ n)) < ∞) :
    (∑' n, physicalDomainLength e y₀ (γ n).val) < ∞ := by
  have hbound : c * (∑' n, physicalDomainLength e y₀ (γ n).val) ≤
      ∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (γ n) := by
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun n => physicalCost_ge_length e hG y₀ (γ n) g c hpos
  by_contra hn
  have htop : (∑' n, physicalDomainLength e y₀ (γ n).val) = ∞ :=
    top_le_iff.mp (not_lt.mp hn)
  rw [htop, ENNReal.mul_top hc] at hbound
  exact hcost.not_ge hbound

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TimeIncidenceReparametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence and multiplicity-sensitive tolls under an injective change
of path parameter. These formulas also apply to a restricted interval. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {S T X Z : Type*}

theorem timeIncidence_image (R : Set (Z × X)) (γ : T → X) (f : S → T) (A : Set S) :
    timeIncidence R γ (f '' A) = timeIncidence R (γ ∘ f) A := by
  ext z
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, hr⟩
    exact ⟨s, hs, hr⟩
  · rintro ⟨s, hs, hr⟩
    exact ⟨f s, ⟨s, hs, rfl⟩, hr⟩

theorem timeToll_image (γ : T → X) (f : S → T) (hf : Injective f)
    (A : Set S) (m : X → ℝ≥0∞) :
    timeToll γ (f '' A) m = timeToll (γ ∘ f) A m := by
  exact ((Equiv.Set.image f A hf).tsum_eq (fun t => m (γ t))).symm

theorem image_preimage_inter_eq (f : S → T) (A : Set T) (I : Set S) :
    f '' (f ⁻¹' A ∩ I) = A ∩ f '' I := by
  ext t
  constructor
  · rintro ⟨s, ⟨hs, hi⟩, rfl⟩
    exact ⟨hs, s, hi, rfl⟩
  · rintro ⟨ht, s, hi, rfl⟩
    exact ⟨s, ⟨ht, hi⟩, rfl⟩

theorem timeIncidence_restrict (R : Set (Z × X)) (γ : T → X)
    (f : S → T) (A : Set T) (I : Set S) :
    timeIncidence R γ (A ∩ f '' I) = timeIncidence R (γ ∘ f) (f ⁻¹' A ∩ I) := by
  rw [← image_preimage_inter_eq, timeIncidence_image]

theorem timeToll_restrict (γ : T → X) (f : S → T) (hf : Injective f)
    (A : Set T) (I : Set S) (m : X → ℝ≥0∞) :
    timeToll γ (A ∩ f '' I) m = timeToll (γ ∘ f) (f ⁻¹' A ∩ I) m := by
  rw [← image_preimage_inter_eq, timeToll_image γ f hf]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableTagAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put countably many tag lists into one list without losing any tag.
Unused code slots are inactive, so tuple exclusions are preserved exactly. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

theorem assembleTags_at {ι : Type*} [Encodable ι] (θ : ι → ℕ → TagSlot) (i : ι) (k : ℕ) :
    assembleTags θ (Encodable.encode (i, k)) = θ i k := by
  simp only [assembleTags, Encodable.encodek]

theorem assembleTags_value {ι : Type*} [Encodable ι] (θ : ι → ℕ → TagSlot) (k : ℕ) :
    assembleTags θ k = inactiveTag ∨ ∃ i j, assembleTags θ k = θ i j := by
  unfold assembleTags
  cases Encodable.decode (α := ι × ℕ) k with
  | none => exact Or.inl rfl
  | some p => exact Or.inr ⟨p.1, p.2, rfl⟩

variable {X : Type*} [MetricSpace X]

theorem tagRules_assemble {ι : Type*} [Encodable ι]
    (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (θ : ι → ℕ → TagSlot)
    (hθ : ∀ i, TagRules H N (γ, θ i)) : TagRules H N (γ, assembleTags θ) := by
  intro k
  rcases assembleTags_value θ k with hk | ⟨i, j, hk⟩
  · change (γ, assembleTags θ k) ∈ validTagShape ∧
      (γ, assembleTags θ k) ∈ tagContainment H ∧ assembleTags θ k ∉ tagTupleExcluded N
    rw [hk]
    exact inactiveTag_rules H N γ
  · change (γ, assembleTags θ k) ∈ validTagShape ∧
      (γ, assembleTags θ k) ∈ tagContainment H ∧ assembleTags θ k ∉ tagTupleExcluded N
    rw [hk]
    exact hθ i j

theorem residualTimes_assemble_iff {ι : Type*} [Encodable ι]
    (B : Set X) (γ : C(PathTime, X)) (θ : ι → ℕ → TagSlot) (t : PathTime) :
    t ∈ residualTimes B (γ, assembleTags θ) ↔
      γ t ∈ B ∧ ∀ i j, t ≤ tagLeft (θ i j) ∨ tagRight (θ i j) ≤ t := by
  constructor
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun i j => ?_⟩
    simpa only [assembleTags_at] using htags (Encodable.encode (i, j))
  · rintro ⟨ht, htags⟩
    refine ⟨ht, fun k => ?_⟩
    rcases assembleTags_value θ k with hk | ⟨i, j, hk⟩
    · change t ≤ tagLeft (assembleTags θ k) ∨ tagRight (assembleTags θ k) ≤ t
      rw [hk]
      exact Or.inl le_top
    · change t ≤ tagLeft (assembleTags θ k) ∨ tagRight (assembleTags θ k) ≤ t
      rw [hk]
      exact htags i j

theorem residualTimes_assemble_on_piece {ι : Type*} [Encodable ι]
    (B : Set X) (γ : C(PathTime, X)) (θ : ι → ℕ → TagSlot)
    (J : ι → Set PathTime) (hJ : Pairwise (Disjoint on J))
    (hθ : ∀ i k, Ioo (tagLeft (θ i k)) (tagRight (θ i k)) ⊆ J i)
    (i : ι) {t : PathTime} (ht : t ∈ J i) :
    t ∈ residualTimes B (γ, assembleTags θ) ↔ t ∈ residualTimes B (γ, θ i) := by
  rw [residualTimes_assemble_iff]
  constructor
  · rintro ⟨hdust, htags⟩
    exact ⟨hdust, htags i⟩
  · rintro ⟨hdust, htags⟩
    refine ⟨hdust, fun j k => ?_⟩
    by_cases hij : j = i
    · subst j
      exact htags k
    · have hn : t ∉ Ioo (tagLeft (θ j k)) (tagRight (θ j k)) :=
        fun h => disjoint_left.mp (hJ hij) (hθ j k h) ht
      exact (not_and_or.mp hn).imp le_of_not_gt le_of_not_gt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_EmbeddedPathTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the tags of one path into an open piece of a larger path.
Every transported tag stays inside that piece and retains its level tuple. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

theorem embeddedTag_interval {a b : PathTime} (hab : a < b) (τ : TagSlot) :
    Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) =
      affinePathTime a b '' Ioo (tagLeft τ) (tagRight τ) := by
  cases τ with
  | inl u => simp [embeddedTag, tagLeft, tagRight]
  | inr q => exact ((affinePathTime a b).continuous.image_Ioo_of_strictMono
      (affinePathTime_strictMono hab)).symm

theorem embeddedTag_interval_subset {a b : PathTime} (hab : a < b) (τ : TagSlot) :
    Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) ⊆ Ioo a b := by
  rw [embeddedTag_interval hab]
  rintro t ⟨s, hs, rfl⟩
  have hleft : (⊥ : PathTime) < s := lt_of_le_of_lt bot_le hs.1
  have hright : s < (⊤ : PathTime) := lt_of_lt_of_le hs.2 le_top
  change a < affinePathTime a b s ∧ affinePathTime a b s < b
  simpa only [affinePathTime_zero, affinePathTime_one] using
    And.intro (affinePathTime_strictMono hab hleft) (affinePathTime_strictMono hab hright)

theorem embeddedTag_tuple_excluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (a b : PathTime) (τ : TagSlot) :
    embeddedTag a b τ ∈ tagTupleExcluded N ↔ τ ∈ tagTupleExcluded N := by
  cases τ with
  | inl u => rfl
  | inr q =>
    exact (active_mem_tagTupleExcluded_iff N
      ⟨q.1, q.2.1, q.2.2.1, affinePathTime a b q.2.2.2.1,
        affinePathTime a b q.2.2.2.2⟩).trans (active_mem_tagTupleExcluded_iff N q).symm

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem embeddedTag_level_iff (H : ℕ → Set (UnitAddCircle × X))
    (a b : PathTime) (τ : TagSlot) (x : X) :
    (embeddedTag a b τ, x) ∈ tagLevelGraph H ↔ (τ, x) ∈ tagLevelGraph H := by
  cases τ <;> rfl

theorem embeddedTag_rules (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    {a b : PathTime} (hab : a < b) (γ η : C(PathTime, X))
    (he : ∀ t ∈ Ioo (⊥ : PathTime) ⊤, η (affinePathTime a b t) = γ t)
    (τ : TagSlot) (hshape : (γ, τ) ∈ validTagShape)
    (hcontain : (γ, τ) ∈ tagContainment H) (hN : τ ∉ tagTupleExcluded N) :
    (η, embeddedTag a b τ) ∈ validTagShape ∧
      (η, embeddedTag a b τ) ∈ tagContainment H ∧
      embeddedTag a b τ ∉ tagTupleExcluded N := by
  refine ⟨?_, ?_, fun hn => hN ((embeddedTag_tuple_excluded_iff N a b τ).mp hn)⟩
  · rcases hshape with hinactive | hnonconstant
    · obtain ⟨u, rfl⟩ := hinactive
      exact Or.inl ⟨u, rfl⟩
    · obtain ⟨s, t, hsl, hsr, htl, htr, hne⟩ := hnonconstant
      have hs : s ∈ Ioo (⊥ : PathTime) ⊤ :=
        ⟨lt_of_le_of_lt bot_le hsl, lt_of_lt_of_le hsr le_top⟩
      have ht : t ∈ Ioo (⊥ : PathTime) ⊤ :=
        ⟨lt_of_le_of_lt bot_le htl, lt_of_lt_of_le htr le_top⟩
      have hsi : affinePathTime a b s ∈
          Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) := by
        rw [embeddedTag_interval hab]
        exact ⟨s, ⟨hsl, hsr⟩, rfl⟩
      have hti : affinePathTime a b t ∈
          Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) := by
        rw [embeddedTag_interval hab]
        exact ⟨t, ⟨htl, htr⟩, rfl⟩
      exact Or.inr ⟨_, _, hsi.1, hsi.2, hti.1, hti.2, by rwa [he s hs, he t ht]⟩
  · intro t hl hr
    have ht : t ∈ Ioo (tagLeft (embeddedTag a b τ)) (tagRight (embeddedTag a b τ)) := ⟨hl, hr⟩
    rw [embeddedTag_interval hab] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have hsi : s ∈ Ioo (⊥ : PathTime) ⊤ :=
      ⟨lt_of_le_of_lt bot_le hs.1, lt_of_lt_of_le hs.2 le_top⟩
    rw [he s hsi]
    exact (embeddedTag_level_iff H a b τ _).mpr (hcontain s hs.1 hs.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ConcatenatedTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous path assembled from countably many open pieces receives
the transported tags of each piece. Disjointness prevents interference. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

variable {ι X : Type*} [Encodable ι] [MetricSpace X]

theorem tagRules_concatenated (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hΓ : ∀ i, TagRules H N (Γ i)) :
    TagRules H N (concatenatedTaggedPath γ a b Γ) := by
  apply tagRules_assemble
  intro i k
  exact embeddedTag_rules H N (hab i) (Γ i).1 γ (hmatch i) ((Γ i).2 k)
    (hΓ i k).1 (hΓ i k).2.1 (hΓ i k).2.2

theorem residualTimes_embedded_piece (B : Set X)
    (γ : C(PathTime, X)) {a b : PathTime} (hab : a < b) (Γ : TaggedPath X)
    (hmatch : ∀ t ∈ Ioo (⊥ : PathTime) ⊤, γ (affinePathTime a b t) = Γ.1 t)
    {t : PathTime} (ht : t ∈ Ioo a b) :
    t ∈ residualTimes B (γ, fun k => embeddedTag a b (Γ.2 k)) ↔
      rescalePathTime a b t ∈ residualTimes B Γ := by
  have hti := rescalePathTime_mem_Ioo hab ht
  have he := affine_rescalePathTime hab ⟨ht.1.le, ht.2.le⟩
  have hv : γ t = Γ.1 (rescalePathTime a b t) := by simpa only [he] using hmatch _ hti
  constructor
  · rintro ⟨hdust, htags⟩
    refine ⟨hv ▸ hdust, fun k => ?_⟩
    by_contra h
    push Not at h
    have himage : t ∈ Ioo (tagLeft (embeddedTag a b (Γ.2 k)))
        (tagRight (embeddedTag a b (Γ.2 k))) := by
      rw [embeddedTag_interval hab]
      exact ⟨rescalePathTime a b t, h, he⟩
    exact (htags k).elim (not_le_of_gt himage.1) (not_le_of_gt himage.2)
  · rintro ⟨hdust, htags⟩
    refine ⟨hv.symm ▸ hdust, fun k => ?_⟩
    by_contra h
    push Not at h
    have himage : t ∈ affinePathTime a b '' Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) := by
      rwa [← embeddedTag_interval hab]
    obtain ⟨s, hs, hsval⟩ := himage
    have hst : s = rescalePathTime a b t := (affinePathTime_strictMono hab).injective
      (hsval.trans he.symm)
    subst s
    exact (htags k).elim (not_le_of_gt hs.1) (not_le_of_gt hs.2)

theorem residualTimes_concatenated_piece (B : Set X)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (i : ι) {t : PathTime} (ht : t ∈ Ioo (a i) (b i)) :
    t ∈ residualTimes B (concatenatedTaggedPath γ a b Γ) ↔
      rescalePathTime (a i) (b i) t ∈ residualTimes B (Γ i) := by
  exact (residualTimes_assemble_on_piece B γ _ (fun i => Ioo (a i) (b i)) hdis
    (fun i k => embeddedTag_interval_subset (hab i) ((Γ i).2 k)) i ht).trans
      (residualTimes_embedded_piece B γ (hab i) (Γ i) (hmatch i) ht)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ConcatenatedResidualPieces
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact old-parameter descriptions of the residual times in each open
piece of a concatenated path, including a clipped global test interval. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem timeIncidence_congr_path {T X Z : Type*} (R : Set (Z × X))
    {γ η : T → X} {A : Set T} (h : EqOn γ η A) :
    timeIncidence R γ A = timeIncidence R η A := by
  ext z
  constructor
  · rintro ⟨t, ht, hr⟩
    exact ⟨t, ht, (h ht) ▸ hr⟩
  · rintro ⟨t, ht, hr⟩
    exact ⟨t, ht, (h ht).symm ▸ hr⟩

theorem timeToll_congr_path {T X : Type*} (m : X → ℝ≥0∞)
    {γ η : T → X} {A : Set T} (h : EqOn γ η A) :
    timeToll γ A m = timeToll η A m := by
  exact tsum_congr fun t => congrArg m (h t.property)

variable {ι X : Type*} [Encodable ι] [MetricSpace X]

theorem concatenated_piece_times (B : Set X)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (i : ι) (c d : PathTime) :
    residualTimes B (concatenatedTaggedPath γ a b Γ) ∩ (Ioo (a i) (b i) ∩ Ioo c d) =
      affinePathTime (a i) (b i) '' (residualTimes B (Γ i) ∩
        Ioo (rescalePathTime (a i) (b i) c) (rescalePathTime (a i) (b i) d)) := by
  ext t
  constructor
  · rintro ⟨hr, hj, ht⟩
    have himage : t ∈ affinePathTime (a i) (b i) ''
        Ioo (rescalePathTime (a i) (b i) c) (rescalePathTime (a i) (b i) d) := by
      rw [affine_image_rescaled_Ioo (hab i)]
      exact ⟨hj, ht⟩
    obtain ⟨s, hs, he⟩ := himage
    refine ⟨s, ⟨?_, hs⟩, he⟩
    have hold := (residualTimes_concatenated_piece B γ a b hab hdis Γ hmatch i hj).mp hr
    rwa [← he, rescale_affinePathTime (hab i)] at hold
  · rintro ⟨s, ⟨hr, hs⟩, rfl⟩
    have hpiece : affinePathTime (a i) (b i) s ∈ Ioo (a i) (b i) ∩ Ioo c d := by
      rw [← affine_image_rescaled_Ioo (hab i)]
      exact ⟨s, hs, rfl⟩
    refine ⟨?_, hpiece⟩
    apply (residualTimes_concatenated_piece B γ a b hab hdis Γ hmatch i hpiece.1).mpr
    rwa [rescale_affinePathTime (hab i)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PreterminalTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! True boundary tolls with exactly the final parameter omitted, retaining
all multiplicities at earlier times. Positive added weights control code mass. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem preterminalToll_mono (γ : C(PathTime, X)) {m n : X → ℝ≥0∞}
    (hmn : m ≤ n) : preterminalToll γ m ≤ preterminalToll γ n := by
  unfold preterminalToll
  apply ENNReal.tsum_le_tsum
  intro t
  split_ifs
  · exact le_rfl
  · exact hmn _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AffineBoundaryTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact dust tolls of an affine path restriction. The preterminal cost
corresponds to a half-open old interval, so cut points are never charged twice. -/

open Set Function
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem preterminalToll_eq_timeToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    preterminalToll γ m = timeToll γ (Iio (⊤ : PathTime)) m := by
  rw [timeToll_eq_indicator]
  unfold preterminalToll
  apply tsum_congr
  intro t
  by_cases ht : t = ⊤ <;> simp [ht, lt_top_iff_ne_top]

theorem boundaryToll_eq_timeToll (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll γ m = timeToll γ univ m := by
  rw [timeToll_eq_indicator]
  simp only [mem_univ, ite_true, if_true]
  rfl

theorem boundaryToll_affine (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    {a b : PathTime} (hab : a < b) :
    boundaryToll (affineRestrictedPath a b γ) m = timeToll γ (Icc a b) m := by
  rw [boundaryToll_eq_timeToll, ← range_affinePathTime hab, ← image_univ,
    timeToll_image γ _ (affinePathTime_strictMono hab).injective]
  rfl

theorem interiorToll_affine (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    {a b : PathTime} (hab : a < b) :
    timeToll (affineRestrictedPath a b γ) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll γ (Ioo a b) m := by
  have he := (affinePathTime a b).continuous.image_Ioo_of_strictMono
    (affinePathTime_strictMono hab) (a := ⊥) (b := ⊤)
  rw [affinePathTime_zero, affinePathTime_one] at he
  rw [← he, timeToll_image γ _ (affinePathTime_strictMono hab).injective]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CountableConcatenationTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact toll addition for collar pieces. Junctions lie in the physical
 domain, hence carry zero dust toll; the new limiting endpoint is omitted. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem timeToll_eq_of_zero_difference {T : Type*} (γ : T → X) (m : X → ℝ≥0∞)
    {A B : Set T} (hBA : B ⊆ A) (hz : ∀ t ∈ A \ B, m (γ t) = 0) :
    timeToll γ A m = timeToll γ B m := by
  rw [timeToll_eq_indicator, timeToll_eq_indicator]
  apply tsum_congr
  intro t
  by_cases ht : t ∈ B
  · simp only [ht, hBA ht, ite_true, if_true]
  · by_cases ha : t ∈ A
    · simp only [ha, ht, ite_true, if_true, ite_false, if_false, hz t ⟨ha, ht⟩]
    · simp only [ha, ht, ite_false, if_false]

theorem timeToll_eq_interior_of_zero_endpoints (γ : C(PathTime, X))
    (m : X → ℝ≥0∞) (hzero : m (γ ⊥) = 0) (hone : m (γ ⊤) = 0) :
    boundaryToll γ m = timeToll γ (Ioo (⊥ : PathTime) ⊤) m := by
  rw [boundaryToll_eq_timeToll]
  apply timeToll_eq_of_zero_difference γ m (subset_univ _)
  intro t ht
  have he : t = ⊥ ∨ t = ⊤ := by
    by_contra h
    push Not at h
    exact ht.2 ⟨bot_lt_iff_ne_bot.mpr h.1, lt_top_iff_ne_top.mpr h.2⟩
  rcases he with rfl | rfl
  · exact hzero
  · exact hone

theorem collarConcatenation_cell_toll (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail
    (m : X → ℝ≥0∞) (n : ℕ) :
    timeToll (collarConcatenation p γ hjoin htail)
        (Ioo (collarTime (n + 1)) (collarTime n)) m =
      timeToll (γ n) (Ioo (⊥ : PathTime) ⊤) m := by
  have he := interiorToll_affine (collarConcatenation p γ hjoin htail) m
    (collarTime_strictAnti (Nat.lt_succ_self n))
  rw [← he]
  apply timeToll_congr_path
  intro t _
  exact collarConcatenation_affine p γ hjoin htail n t

theorem collarConcatenation_interior_toll (p : X) (γ : ℕ → C(PathTime, X)) hjoin htail
    (m : X → ℝ≥0∞) (hzero : ∀ n, m (γ n ⊥) = 0) (hone : ∀ n, m (γ n ⊤) = 0) :
    timeToll (collarConcatenation p γ hjoin htail) (Ioo (⊥ : PathTime) ⊤) m =
      ∑' n, boundaryToll (γ n) m := by
  let η := collarConcatenation p γ hjoin htail
  have hsub : (⋃ n, Ioo (collarTime (n + 1)) (collarTime n)) ⊆ Ioo (⊥ : PathTime) ⊤ := by
    intro t ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact ⟨(collarTime_pos (n + 1)).trans hn.1, hn.2.trans_le le_top⟩
  have hz : ∀ t ∈ Ioo (⊥ : PathTime) ⊤ \ (⋃ n, Ioo (collarTime (n + 1)) (collarTime n)),
      m (η t) = 0 := by
    intro t ht
    obtain ⟨n, hl, hr⟩ := exists_collarTime_cell ht.1.1
    have he : t = collarTime n := by
      by_contra hne
      exact ht.2 (mem_iUnion.mpr ⟨n, hl, hr.lt_of_ne hne⟩)
    have hf := collarConcatenation_affine p γ hjoin htail n ⊤
    rw [affinePathTime_one] at hf
    change m (collarConcatenation p γ hjoin htail t) = 0
    rw [he, hf]
    exact hone n
  rw [timeToll_eq_of_zero_difference η m hsub hz,
    timeToll_iUnion η m _ collarCell_disjoint_interiors]
  apply tsum_congr
  intro n
  exact (collarConcatenation_cell_toll p γ hjoin htail m n).trans
    (timeToll_eq_interior_of_zero_endpoints (γ n) m (hzero n) (hone n)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ConcatenatedIncidenceBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable concatenation preserves each residual incidence inequality.
Only the complement of the open pieces must be countable; the pieces'
images may overlap and every parameter visit is still charged. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {ι X Z : Type*} [Encodable ι] [MetricSpace X] [MeasurableSpace Z]

theorem concatenated_piece_incidence_bound (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (i : ι) (c d : PathTime)
    (hbound : ResidualIncidenceBound B
      (Ioo (rescalePathTime (a i) (b i) c) (rescalePathTime (a i) (b i) d)) R P ν m (Γ i)) :
    ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ
      (residualTimes B (concatenatedTaggedPath γ a b Γ) ∩ (Ioo (a i) (b i) ∩ Ioo c d))) ≤
      timeToll γ (residualTimes B (concatenatedTaggedPath γ a b Γ) ∩
        (Ioo (a i) (b i) ∩ Ioo c d)) (deletedWeight P m) := by
  rw [concatenated_piece_times B γ a b hab hdis Γ hmatch i c d,
    timeIncidence_image, timeToll_image γ _ (affinePathTime_strictMono (hab i)).injective]
  have he : EqOn (γ ∘ affinePathTime (a i) (b i)) (Γ i).1
      (residualTimes B (Γ i) ∩
        Ioo (rescalePathTime (a i) (b i) c) (rescalePathTime (a i) (b i) d)) := by
    intro t ht
    exact hmatch i t ⟨lt_of_le_of_lt bot_le ht.2.1, lt_of_lt_of_le ht.2.2 le_top⟩
  rw [timeIncidence_congr_path _ he, timeToll_congr_path _ he]
  simpa only [ResidualIncidenceBound, residualIncidence_eq_timeIncidence,
    residualToll_eq_timeToll] using hbound

theorem residualIncidenceBound_concatenated_open (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hΓ : ∀ i c d, ResidualIncidenceBound B (Ioo c d) R P ν m (Γ i))
    (c d : PathTime) :
    ResidualIncidenceBound B (Ioo c d) R P ν m (concatenatedTaggedPath γ a b Γ) := by
  let S := residualTimes B (concatenatedTaggedPath γ a b Γ) ∩ Ioo c d
  let J := fun i => Ioo (a i) (b i)
  let A₀ := S \ ⋃ i, J i
  let C := fun i => S ∩ J i
  have hcover : S = A₀ ∪ ⋃ i, C i := by
    ext t
    simp only [A₀, C, mem_union, mem_sdiff, mem_iUnion, mem_inter_iff]
    tauto
  have hC : Pairwise (Disjoint on C) := by
    intro i j hij
    exact (hdis hij).mono inter_subset_right inter_subset_right
  have hd₀ : Disjoint A₀ (⋃ i, C i) := by
    apply disjoint_left.mpr
    rintro t ht hc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hc
    exact ht.2 (mem_iUnion.mpr ⟨i, hi.2⟩)
  have hc₀ : (γ '' A₀).Countable := (hcount.mono (fun _ ht => ht.2)).image γ
  unfold ResidualIncidenceBound
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll]
  apply timeIncidence_bound_with_countable_remainder R P γ S A₀ C ν m hpoint hcover hC hd₀ hc₀
  intro i
  have he : C i = residualTimes B (concatenatedTaggedPath γ a b Γ) ∩ (J i ∩ Ioo c d) := by
    ext t
    simp only [C, S, mem_inter_iff]
    tauto
  rw [he]
  exact concatenated_piece_incidence_bound B R P ν m γ a b hab hdis Γ hmatch i c d (hΓ i _ _)

theorem residualConstraintFamily_concatenated (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hpoint : ∀ k x, ν k {z | (z, x) ∈ R k} ≤ m k x)
    (hΓ : ∀ i, ResidualConstraintFamily B R P ν m (Γ i)) :
    ResidualConstraintFamily B R P ν m (concatenatedTaggedPath γ a b Γ) := by
  intro k n c d
  apply residualIncidenceBound_closed_of_open B (R k) (P k n) (ν k) (m k)
    (concatenatedTaggedPath γ a b Γ) (hpoint k) _ c.toTime d.toTime
  intro s t
  exact residualIncidenceBound_concatenated_open B (R k) (P k n) (ν k) (m k)
    γ a b hab hdis hcount Γ hmatch (hpoint k)
      (fun i => residualConstraintFamily_open B R P ν m (Γ i) (hΓ i) k n) s t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ConcatenatedResidualNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many junction times and null residual images in the open
pieces give a null residual image for the concatenated path. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {ι X : Type*} [Encodable ι] [MetricSpace X]

theorem residualImage_concatenated_subset (B : Set X)
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t) :
    residualImage B (concatenatedTaggedPath γ a b Γ) ⊆
      γ '' (⋃ i, Ioo (a i) (b i))ᶜ ∪ ⋃ i, residualImage B (Γ i) := by
  rintro x ⟨t, ht, rfl⟩
  by_cases hpiece : t ∈ ⋃ i, Ioo (a i) (b i)
  · right
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpiece
    apply mem_iUnion.mpr
    refine ⟨i, rescalePathTime (a i) (b i) t, ?_, ?_⟩
    · exact (residualTimes_concatenated_piece B γ a b hab hdis Γ hmatch i hi).mp ht
    · have he := hmatch i _ (rescalePathTime_mem_Ioo (hab i) hi)
      rw [affine_rescalePathTime (hab i) ⟨hi.1.le, hi.2.le⟩] at he
      exact he.symm
  · exact Or.inl ⟨t, hpiece, rfl⟩

theorem residualImage_concatenated_null [MeasurableSpace X] [MeasurableSingletonClass X]
    (B : Set X) (ν : Measure X) [NullSingletonClass ν]
    (γ : C(PathTime, X)) (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X)
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hnull : ∀ i, ν (residualImage B (Γ i)) = 0) :
    ν (residualImage B (concatenatedTaggedPath γ a b Γ)) = 0 :=
  measure_mono_null (residualImage_concatenated_subset B γ a b hab hdis Γ hmatch)
    (measure_union_null ((hcount.image γ).measure_zero ν) (measure_iUnion_null hnull))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AllowedCountableConcatenation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous concatenation of countably many allowed paths is allowed
when its remaining parameter times are countable and its physical length is
finite. All tags and incidence estimates are constructed explicitly. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {ι X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_concatenated [Encodable ι]
    (d : PathCodeData X Y) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfinite : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X) (hΓ : ∀ i, AllowedTaggedPath d ν N (Γ i))
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    AllowedTaggedPath d ν N (concatenatedTaggedPath γ a b Γ) := by
  refine ⟨hfinite, tagRules_concatenated d.levels N γ a b hab Γ hmatch
    (fun i => (hΓ i).2.1), ?_, ?_, ?_⟩
  · apply residualConstraintFamily_concatenated d.dust (fun _ => pathHitSet)
      d.priorDeletions d.priorLaws (fun i => priorHitMass (d.priorLaws i))
      γ a b hab hdis hcount Γ hmatch _ (fun i => (hΓ i).2.2.1)
    intro i x
    exact le_rfl
  · exact residualConstraintFamily_concatenated d.dust d.levels (fun _ => d.flagDeletions)
      (fun _ => volume) d.levelWeights γ a b hab hdis hcount Γ hmatch hpoint
        (fun i => (hΓ i).2.2.2.1)
  · exact residualImage_concatenated_null d.dust ν γ a b hab hdis hcount Γ hmatch
      (fun i => (hΓ i).2.2.2.2)

theorem exists_allowed_countable_concatenation [Countable ι]
    (d : PathCodeData X Y) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfinite : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (a b : ι → PathTime) (hab : ∀ i, a i < b i)
    (hdis : Pairwise (Disjoint on (fun i => Ioo (a i) (b i))))
    (hcount : (⋃ i, Ioo (a i) (b i))ᶜ.Countable)
    (Γ : ι → TaggedPath X) (hΓ : ∀ i, AllowedTaggedPath d ν N (Γ i))
    (hmatch : ∀ i t, t ∈ Ioo (⊥ : PathTime) ⊤ →
      γ (affinePathTime (a i) (b i) t) = (Γ i).1 t)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ θ : ℕ → TagSlot, AllowedTaggedPath d ν N (γ, θ) := by
  let : Encodable ι := Encodable.ofCountable ι
  exact ⟨_, allowedTaggedPath_concatenated d ν N γ hfinite a b hab hdis hcount Γ hΓ hmatch hpoint⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AllowedCollarConcatenation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed countable collar path is allowed when its actual
physical lengths are summable. No path-stability input is assumed. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_collar (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (p : X) (Γ : ℕ → TaggedPath X)
    (hjoin : ∀ n, (Γ (n + 1)).1 ⊤ = (Γ n).1 ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ k : ℕ, ∀ n ≥ k, ∀ s, (Γ n).1 s ∈ V)
    (hΓ : ∀ n, AllowedTaggedPath d ν N (Γ n))
    (hfinite : (∑' n, physicalDomainLength d.domainEquiv d.basePoint (Γ n).1) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    AllowedTaggedPath d ν N (collarTaggedPath p Γ hjoin htail) := by
  let γ : ℕ → FinitePhysicalPath d.domainEquiv d.basePoint := fun n => ⟨(Γ n).1, (hΓ n).1⟩
  apply allowedTaggedPath_concatenated d ν N
    (collarConcatenation p (fun n => (Γ n).1) hjoin htail)
    ((physicalDomainLength_collarPieces_le d.domainEquiv hU d.basePoint γ _
      (collarConcatenation_affine p (fun n => (Γ n).1) hjoin htail)).trans_lt hfinite)
    (fun n => collarTime (n + 1)) collarTime
    (fun n => collarTime_strictAnti (Nat.lt_succ_self n))
    collarCell_disjoint_interiors collarCell_complement_countable Γ hΓ
  · intro n s _
    exact collarConcatenation_affine p (fun n => (Γ n).1) hjoin htail n s
  · exact hpoint

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CollarConcatenationCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual allowed collar concatenation with its complete cost identity.
Summable cost and a positive density supply the required physical finiteness. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_collar_of_summable_cost
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (p : X) (γ : ℕ → FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → ℕ → TagSlot)
    (hΓ : ∀ n, AllowedTaggedPath d ν N ((γ n).val, θ n))
    (hjoin : ∀ n, (γ (n + 1)).val ⊤ = (γ n).val ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ k : ℕ, ∀ n ≥ k, ∀ s, (γ n).val s ∈ V)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hpos : ∀ y ∈ d.physicalDomain, c ≤ g y)
    (hzero : ∀ n, m ((γ n).val ⊥) = 0) (hone : ∀ n, m ((γ n).val ⊤) = 0)
    (hcost : (∑' n, ((∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) +
      boundaryToll (γ n).val m)) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (η : FinitePhysicalPath d.domainEquiv d.basePoint) (tags : ℕ → TagSlot),
      AllowedTaggedPath d ν N (η.val, tags) ∧ η.val ⊥ = p ∧ η.val ⊤ = (γ 0).val ⊤ ∧
      (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint η) +
        timeToll η.val (Ioo (⊥ : PathTime) ⊤) m =
      ∑' n, ((∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) +
        boundaryToll (γ n).val m) := by
  have hphys : (∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) < ∞ :=
    (ENNReal.tsum_le_tsum (fun n => show
      (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) ≤
        (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) +
          boundaryToll (γ n).val m from le_self_add)).trans_lt hcost
  have hlen := sum_physicalLength_finite_of_cost d.domainEquiv hG d.basePoint γ g c hc hpos hphys
  let η := finitePhysicalCollarConcatenation d.domainEquiv hU d.basePoint p γ hjoin htail hlen
  let Γ : ℕ → TaggedPath X := fun n => ((γ n).val, θ n)
  refine ⟨η, (collarTaggedPath p Γ hjoin htail).2, ?_, ?_, ?_, ?_⟩
  · exact allowedTaggedPath_collar d hU ν N p Γ hjoin htail hΓ hlen hpoint
  · exact collarConcatenation_zero p (fun n => (γ n).val) hjoin htail
  · exact collarConcatenation_one p (fun n => (γ n).val) hjoin htail
  · have hmatch : ∀ n s, η.val (affinePathTime (collarTime (n + 1)) (collarTime n) s) =
        (γ n).val s := collarConcatenation_affine p (fun n => (γ n).val) hjoin htail
    rw [physicalCost_collarPieces d.domainEquiv hU d.basePoint η γ hmatch g hg]
    change (∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) +
      timeToll (collarConcatenation p (fun n => (γ n).val) hjoin htail) (Ioo ⊥ ⊤) m = _
    rw [collarConcatenation_interior_toll p (fun n => (γ n).val) hjoin htail m hzero hone,
      ENNReal.tsum_add]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_InterleavedCollarPieces
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interleaving actual retained fragments with their joining arcs preserves
the endpoint matches and adds exactly the two series of costs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem interleavePieces_join {X : Type*}
    (a b : ℕ → PathTime → X)
    (hleft : ∀n, b n ⊥ = a (n+1) ⊤) (hright : ∀n, b n ⊤ = a n ⊥) :
    ∀n, interleavePieces a b (n+1) ⊤ = interleavePieces a b n ⊥ := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn : n = 2 * (n/2) := by omega
    rw [hn]
    simpa only [interleavePieces_odd, interleavePieces_even] using hright (n/2)
  · have hn : n = 2 * (n/2)+1 := by omega
    rw [hn]
    have he : 2*(n/2)+1+1 = 2*(n/2+1) := by omega
    rw [he]
    simpa only [interleavePieces_even, interleavePieces_odd] using (hleft (n/2)).symm

theorem interleavePieces_tail {X : Type*} [TopologicalSpace X]
    (a b : ℕ → PathTime → X) (p : X)
    (ha : ∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, ∀t, a n t ∈ V)
    (hb : ∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, ∀t, b n t ∈ V) :
    ∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, ∀t, interleavePieces a b n t ∈ V := by
  intro V hV
  obtain ⟨N, hN⟩ := ha V hV
  obtain ⟨M, hM⟩ := hb V hV
  refine ⟨2 * max N M, ?_⟩
  intro n hn t
  have hNn : N ≤ n/2 := by omega
  have hMn : M ≤ n/2 := by omega
  unfold interleavePieces
  split
  · exact hN _ hNn t
  · exact hM _ hMn t

theorem tsum_cost_interleavePieces {α : Type*} (a b : ℕ → α) (c : α → ℝ≥0∞) :
    (∑' n, c (interleavePieces a b n)) = (∑'n, c (a n)) + ∑'n, c (b n) := by
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]
  simp only [interleavePieces_even, interleavePieces_odd]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_InterleavedCollarCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing retained fragments and genuine short joining arcs into one
allowed collar path, with the sum of their actual costs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_interleaved_collar
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (p : X) (a b : ℕ → TaggedPhysicalPath d)
    (ha : ∀n, AllowedTaggedPath d ν N ((a n).1.val, (a n).2))
    (hb : ∀n, AllowedTaggedPath d ν N ((b n).1.val, (b n).2))
    (hleft : ∀n, (b n).1.val ⊥ = (a (n+1)).1.val ⊤)
    (hright : ∀n, (b n).1.val ⊤ = (a n).1.val ⊥)
    (hatail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, ∀s, (a n).1.val s ∈ V)
    (hbtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, ∀s, (b n).1.val s ∈ V)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hpos : ∀y ∈ d.physicalDomain, c ≤ g y)
    (ha0 : ∀n, m ((a n).1.val ⊥) = 0) (ha1 : ∀n, m ((a n).1.val ⊤) = 0)
    (hb0 : ∀n, m ((b n).1.val ⊥) = 0) (hb1 : ∀n, m ((b n).1.val ⊤) = 0)
    (A E : ℝ≥0∞) (hA : A < ∞) (hE : E < ∞)
    (hacost : (∑'n, physicalTollCost d g m (a n).1) ≤ A)
    (hbcost : (∑'n, physicalTollCost d g m (b n).1) ≤ E)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (η : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (η.val, θ) ∧ η.val ⊥ = p ∧ η.val ⊤ = (a 0).1.val ⊤ ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint η) +
        timeToll η.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + E := by
  let Γ := interleavePieces a b
  have hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2) := by
    intro n
    dsimp [Γ, interleavePieces]
    split
    · exact ha _
    · exact hb _
  have hΓ0 : ∀n, m ((Γ n).1.val ⊥) = 0 := by
    intro n
    dsimp [Γ, interleavePieces]
    split
    · exact ha0 _
    · exact hb0 _
  have hΓ1 : ∀n, m ((Γ n).1.val ⊤) = 0 := by
    intro n
    dsimp [Γ, interleavePieces]
    split
    · exact ha1 _
    · exact hb1 _
  have hpath (n : ℕ) (s : PathTime) : (Γ n).1.val s =
      interleavePieces (fun n => ((a n).1.val : PathTime → X))
        (fun n => ((b n).1.val : PathTime → X)) n s := by
    dsimp [Γ, interleavePieces]
    split <;> rfl
  have hsum : (∑'n, physicalTollCost d g m (Γ n).1) ≤ A + E := by
    have he := tsum_cost_interleavePieces a b (fun γ => physicalTollCost d g m γ.1)
    exact he.le.trans (add_le_add hacost hbcost)
  have hjoin : ∀n, (Γ (n+1)).1.val ⊤ = (Γ n).1.val ⊥ := by
    intro n
    rw [hpath, hpath]
    exact interleavePieces_join (fun n => (a n).1.val) (fun n => (b n).1.val) hleft hright n
  have htail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, ∀s, (Γ n).1.val s ∈ V := by
    intro V hV
    obtain ⟨k, hk⟩ := interleavePieces_tail
      (fun n => (a n).1.val) (fun n => (b n).1.val) p hatail hbtail V hV
    refine ⟨k, ?_⟩
    intro n hn s
    rw [hpath]
    exact hk n hn s
  obtain ⟨η, θ, hη, hη0, hη1, hcost⟩ := exists_allowed_collar_of_summable_cost d hU hG ν N
    p (fun n => (Γ n).1) (fun n => (Γ n).2) hΓ hjoin htail g hg m c hc hpos hΓ0 hΓ1
    (hsum.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, hE⟩)) hpoint
  refine ⟨η, θ, hη, hη0, ?_, hcost.le.trans hsum⟩
  simpa [Γ, interleavePieces] using hη1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AffinePhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted physical costs of restricted paths are the old costs on the
retained interval, with full multiplicity and no endpoint atoms. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalOccupation_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab) =
      ((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (physicalValue e y₀ ∘ γ.val) := by
  have hf := (measurable_physicalValue e hU y₀).comp
    (affineRestrictedPath a b γ.val).continuous.measurable
  rw [← physicalTimeLength_map e hU y₀, physicalTimeLength_affine e hU y₀ γ hab]
  change (((physicalTimeLength e y₀ γ).restrict (Icc a b)).map (rescalePathTime a b)).map
    (physicalValue e y₀ ∘ affineRestrictedPath a b γ.val) = _
  rw [Measure.map_map hf (rescalePathTime a b).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change physicalValue e y₀ (γ.val (affinePathTime a b (rescalePathTime a b t))) =
    physicalValue e y₀ (γ.val t)
  rw [affine_rescalePathTime hab ht]

theorem physicalCost_affine (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hab)) =
      ∫⁻ t in Icc a b, g (physicalValue e y₀ (γ.val t)) ∂physicalTimeLength e y₀ γ := by
  rw [physicalOccupation_affine e hU y₀ γ hab]
  exact lintegral_map hg ((measurable_physicalValue e hU y₀).comp γ.val.continuous.measurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RestrictedFragmentCosts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint restricted original fragments never exceed the original cost.
The physical arclength measure has no atoms and the collar cut tolls vanish. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)] in
theorem timeToll_Icc_eq_Ioo (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    {a b : PathTime} (ha : m (γ a) = 0) (hb : m (γ b) = 0) :
    timeToll γ (Icc a b) m = timeToll γ (Ioo a b) m := by
  apply timeToll_eq_of_zero_difference γ m Ioo_subset_Icc_self
  intro t ht
  by_cases hta : t = a
  · simpa only [hta] using ha
  by_cases htb : t = b
  · simpa only [htb] using hb
  exact (ht.2 ⟨lt_of_le_of_ne ht.1.1 (Ne.symm hta), lt_of_le_of_ne ht.1.2 htb⟩).elim

theorem physicalTollCost_affine (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (ha : m (γ.val a) = 0) (hb : m (γ.val b) = 0) :
    physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hab) =
      (∫⁻t in Ioo a b, g (physicalValue d.domainEquiv d.basePoint (γ.val t))
        ∂physicalTimeLength d.domainEquiv d.basePoint γ) + timeToll γ.val (Ioo a b) m := by
  unfold physicalTollCost
  rw [physicalCost_affine d.domainEquiv hU d.basePoint γ hab g hg]
  have hphys : (∫⁻t in Icc a b, g (physicalValue d.domainEquiv d.basePoint (γ.val t))
        ∂physicalTimeLength d.domainEquiv d.basePoint γ) =
      ∫⁻t in Ioo a b, g (physicalValue d.domainEquiv d.basePoint (γ.val t))
        ∂physicalTimeLength d.domainEquiv d.basePoint γ :=
    setLIntegral_congr (Ioo_ae_eq_Icc.symm)
  rw [hphys]
  change _ + boundaryToll (affineRestrictedPath a b γ.val) m = _
  rw [boundaryToll_affine γ.val m hab, timeToll_Icc_eq_Ioo γ.val m ha hb]

theorem sum_restricted_physicalTollCost_le {ι : Type*} [Countable ι]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (a b : ι → PathTime)
    (hab : ∀i, a i < b i) (hdis : Pairwise (Disjoint on fun i => Ioo (a i) (b i)))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (ha : ∀i, m (γ.val (a i)) = 0) (hb : ∀i, m (γ.val (b i)) = 0) :
    (∑'i, physicalTollCost d g m
      (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ (hab i))) ≤
      physicalTollCost d g m γ := by
  simp_rw [physicalTollCost_affine d hU γ (hab _) g hg m (ha _) (hb _)]
  rw [ENNReal.tsum_add,
    ← lintegral_iUnion (fun _ => measurableSet_Ioo) hdis,
    ← timeToll_iUnion γ.val m _ hdis]
  unfold physicalTollCost
  rw [physicalOccupation_integral d.domainEquiv hU d.basePoint γ g hg,
    boundaryToll_eq_timeToll]
  apply add_le_add
  · simpa only [Measure.restrict_univ] using
      (lintegral_mono_set (μ := physicalTimeLength d.domainEquiv d.basePoint γ)
        (f := fun t => g (physicalValue d.domainEquiv d.basePoint (γ.val t))) (subset_univ _))
  · exact timeToll_mono γ.val m (subset_univ _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ReversedTags
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversal of a tagged path retains every level tuple and reverses its
open time interval. Residual times and images are transported exactly. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

theorem tagLeft_reversed (τ : TagSlot) :
    tagLeft (reversedTag τ) = unitInterval.symm (tagRight τ) := by
  cases τ with
  | inl u =>
    apply Subtype.ext
    change (1 : ℝ) = 1 - 0
    norm_num
  | inr q => rfl

theorem tagRight_reversed (τ : TagSlot) :
    tagRight (reversedTag τ) = unitInterval.symm (tagLeft τ) := by
  cases τ with
  | inl u =>
    apply Subtype.ext
    change (0 : ℝ) = 1 - 1
    norm_num
  | inr q => rfl

theorem reversedTag_tuple_excluded_iff
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (τ : TagSlot) : reversedTag τ ∈ tagTupleExcluded N ↔ τ ∈ tagTupleExcluded N := by
  cases τ with
  | inl u => rfl
  | inr q =>
    exact (active_mem_tagTupleExcluded_iff N
      ⟨q.1, q.2.1, q.2.2.1, unitInterval.symm q.2.2.2.2,
        unitInterval.symm q.2.2.2.1⟩).trans (active_mem_tagTupleExcluded_iff N q).symm

variable {X : Type*} [MetricSpace X]

omit [MetricSpace X] in
theorem reversedTag_level_iff (H : ℕ → Set (UnitAddCircle × X)) (τ : TagSlot) (x : X) :
    (reversedTag τ, x) ∈ tagLevelGraph H ↔ (τ, x) ∈ tagLevelGraph H := by
  cases τ <;> rfl

theorem tagRules_reversed (H : ℕ → Set (UnitAddCircle × X))
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) (hΓ : TagRules H N Γ) : TagRules H N (reversedTaggedPath Γ) := by
  intro k
  refine ⟨?_, ?_, fun hn => (hΓ k).2.2 ((reversedTag_tuple_excluded_iff N (Γ.2 k)).mp hn)⟩
  · rcases (hΓ k).1 with hinactive | hnonconstant
    · obtain ⟨u, hu⟩ := hinactive
      change (Sum.inl u : TagSlot) = Γ.2 k at hu
      change (reversedPath Γ.1, reversedTag (Γ.2 k)) ∈ validTagShape
      rw [← hu]
      exact Or.inl ⟨u, rfl⟩
    · obtain ⟨s, t, hsl, hsr, htl, htr, hne⟩ := hnonconstant
      refine Or.inr ⟨unitInterval.symm s, unitInterval.symm t, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [reversedTaggedPath, tagLeft_reversed, unitInterval.symm_lt_symm] using hsr
      · simpa only [reversedTaggedPath, tagRight_reversed, unitInterval.symm_lt_symm] using hsl
      · simpa only [reversedTaggedPath, tagLeft_reversed, unitInterval.symm_lt_symm] using htr
      · simpa only [reversedTaggedPath, tagRight_reversed, unitInterval.symm_lt_symm] using htl
      · simpa only [reversedTaggedPath, reversedPath, ContinuousMap.comp_apply,
          ContinuousMap.coe_mk, unitInterval.symm_symm] using hne
  · intro t hl hr
    change tagLeft (reversedTag (Γ.2 k)) < t at hl
    change t < tagRight (reversedTag (Γ.2 k)) at hr
    rw [tagLeft_reversed, unitInterval.symm_lt_comm] at hl
    rw [tagRight_reversed, unitInterval.lt_symm_comm] at hr
    exact (reversedTag_level_iff H (Γ.2 k) _).mpr ((hΓ k).2.1 _ hr hl)

theorem residualTimes_reversed (B : Set X) (Γ : TaggedPath X) :
    residualTimes B (reversedTaggedPath Γ) = unitInterval.symm ⁻¹' residualTimes B Γ := by
  ext t
  change (Γ.1 (unitInterval.symm t) ∈ B ∧ ∀ k,
    t ≤ tagLeft (reversedTag (Γ.2 k)) ∨ tagRight (reversedTag (Γ.2 k)) ≤ t) ↔
    (Γ.1 (unitInterval.symm t) ∈ B ∧ ∀ k,
      unitInterval.symm t ≤ tagLeft (Γ.2 k) ∨ tagRight (Γ.2 k) ≤ unitInterval.symm t)
  simp only [tagLeft_reversed, tagRight_reversed, unitInterval.le_symm_comm,
    unitInterval.symm_le_comm, or_comm]

theorem residualImage_reversed (B : Set X) (Γ : TaggedPath X) :
    residualImage B (reversedTaggedPath Γ) = residualImage B Γ := by
  rw [residualImage, residualTimes_reversed]
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨unitInterval.symm t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨unitInterval.symm t, ?_, ?_⟩
    · simpa only [mem_preimage, unitInterval.symm_symm] using ht
    · simpa only [reversedTaggedPath, reversedPath, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, unitInterval.symm_symm] using hx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstExitCuts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first-exit cuts for the collar-splicing construction. Every
retained initial fragment lies in the corresponding closed collar disk. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

theorem firstExitTime_le (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : γ t ∉ V) : firstExitTime γ V ≤ t :=
  sInf_le ht

theorem mem_before_firstExit (γ : C(PathTime, X)) (V : Set X) {t : PathTime}
    (ht : t < firstExitTime γ V) : γ t ∈ V := by
  by_contra hn
  exact ht.not_ge (firstExitTime_le γ V hn)

theorem firstExit_notMem (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hend : γ ⊤ ∉ V) : γ (firstExitTime γ V) ∉ V := by
  exact (hV.isClosed_compl.preimage γ.continuous).isCompact.sInf_mem ⟨⊤, hend⟩

theorem firstExit_pos (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) : ⊥ < firstExitTime γ V := by
  apply bot_lt_iff_ne_bot.mpr
  intro he
  exact firstExit_notMem γ hV hend (he ▸ hstart)

theorem firstExit_frontier (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) : γ (firstExitTime γ V) ∈ frontier V := by
  have hpos := firstExit_pos γ hV hstart hend
  have hcl : firstExitTime γ V ∈ closure (Iio (firstExitTime γ V)) := by
    rw [closure_Iio' ⟨⊥, hpos⟩]
    exact (le_rfl : firstExitTime γ V ≤ firstExitTime γ V)
  have hmap : MapsTo γ (Iio (firstExitTime γ V)) V := fun _ ht => mem_before_firstExit γ V ht
  rw [frontier, hV.interior_eq]
  exact ⟨hmap.closure γ.continuous hcl, firstExit_notMem γ hV hend⟩

theorem firstExit_initial_segment (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ V) :
    MapsTo γ (Iic (firstExitTime γ V)) (closure V) := by
  intro t ht
  change t ≤ firstExitTime γ V at ht
  rcases ht.eq_or_lt with rfl | hlt
  · exact frontier_subset_closure (firstExit_frontier γ hV hstart hend)
  · exact subset_closure (mem_before_firstExit γ V hlt)

theorem firstExit_nested (γ : C(PathTime, X)) {V W : Set X}
    (hW : IsOpen W) (hVW : V ⊆ W) (hend : γ ⊤ ∉ W) :
    firstExitTime γ V ≤ firstExitTime γ W := by
  apply firstExitTime_le
  exact fun h => firstExit_notMem γ hW hend (hVW h)

theorem firstExit_strict_nested (γ : C(PathTime, X)) {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hVW : closure V ⊆ W)
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∉ W) :
    firstExitTime γ V < firstExitTime γ W := by
  have hsub : V ⊆ W := subset_closure.trans hVW
  have hvend : γ ⊤ ∉ V := fun h => hend (hsub h)
  apply lt_of_le_of_ne (firstExit_nested γ hW hsub hend)
  intro he
  have hv := hVW (frontier_subset_closure (firstExit_frontier γ hV hstart hvend))
  rw [he] at hv
  exact firstExit_notMem γ hW hend hv

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AffineResidualExposure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Under affine restriction, old residual times remain residual. Discarded
constant tags expose only countably many image points in the open piece. -/

open Set Function
open scoped Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem affine_old_residual_subset (B : Set X) {a b : PathTime} (hab : a < b)
    (Γ : TaggedPath X) :
    affinePathTime a b ⁻¹' residualTimes B Γ ⊆
      residualTimes B (affineRestrictedTaggedPath a b Γ) := by
  intro t ht
  refine ⟨ht.1, fun k => ?_⟩
  by_cases hn : (affineRestrictedPath a b Γ.1, affineRawTag a b (Γ.2 k)) ∈ nonconstantTagSegment
  · change t ≤ tagLeft (affineRestrictedTag a b Γ.1 (Γ.2 k)) ∨
      tagRight (affineRestrictedTag a b Γ.1 (Γ.2 k)) ≤ t
    rw [affineRestrictedTag, ite_eq_left hn]
    by_contra h
    push Not at h
    have htime : ⊥ < t ∧ t < ⊤ := ⟨lt_of_le_of_lt bot_le h.1, lt_of_lt_of_le h.2 le_top⟩
    have hold := (affineRawTag_interval hab (Γ.2 k) htime).mp h
    exact (ht.2 k).elim (not_le_of_gt hold.1) (not_le_of_gt hold.2)
  · left
    change t ≤ tagLeft (affineRestrictedTag a b Γ.1 (Γ.2 k))
    rw [affineRestrictedTag, ite_eq_right hn]
    exact le_top

theorem affine_discarded_image_countable (a b : PathTime) (Γ : TaggedPath X)
    (k : ℕ)
    (hn : (affineRestrictedPath a b Γ.1, affineRawTag a b (Γ.2 k)) ∉ nonconstantTagSegment) :
    (affineRestrictedPath a b Γ.1 '' Ioo (tagLeft (affineRawTag a b (Γ.2 k)))
      (tagRight (affineRawTag a b (Γ.2 k)))).Countable := by
  apply Set.Subsingleton.countable
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
  by_contra hne
  exact hn ⟨s, t, hs.1, hs.2, ht.1, ht.2, hne⟩

theorem affine_exposed_image_countable (B : Set X) {a b : PathTime} (hab : a < b)
    (Γ : TaggedPath X) :
    (affineRestrictedPath a b Γ.1 ''
      ((residualTimes B (affineRestrictedTaggedPath a b Γ) ∩ Ioo ⊥ ⊤) \
        (affinePathTime a b ⁻¹' residualTimes B Γ))).Countable := by
  let A : ℕ → Set X := fun k =>
    if (affineRestrictedPath a b Γ.1, affineRawTag a b (Γ.2 k)) ∈ nonconstantTagSegment
    then ∅ else affineRestrictedPath a b Γ.1 ''
      Ioo (tagLeft (affineRawTag a b (Γ.2 k))) (tagRight (affineRawTag a b (Γ.2 k)))
  have hA : (⋃ k, A k).Countable := by
    apply Set.countable_iUnion
    intro k
    dsimp only [A]
    split_ifs with hk
    · exact countable_empty
    · exact affine_discarded_image_countable a b Γ k hk
  apply hA.mono
  rintro x ⟨t, ⟨⟨ht, htime⟩, hold⟩, rfl⟩
  have hdust : Γ.1 (affinePathTime a b t) ∈ B := ht.1
  have hcovered : ∃ k, affinePathTime a b t ∈ Ioo (tagLeft (Γ.2 k)) (tagRight (Γ.2 k)) := by
    by_contra h
    apply hold
    refine ⟨hdust, fun k => ?_⟩
    have hk : ¬ (tagLeft (Γ.2 k) < affinePathTime a b t ∧
        affinePathTime a b t < tagRight (Γ.2 k)) := fun hk => h ⟨k, hk⟩
    exact (not_and_or.mp hk).imp le_of_not_gt le_of_not_gt
  obtain ⟨k, hk⟩ := hcovered
  have hc := (affineRawTag_interval hab (Γ.2 k) htime).mpr hk
  have hn : (affineRestrictedPath a b Γ.1, affineRawTag a b (Γ.2 k)) ∉ nonconstantTagSegment := by
    intro hn
    have ht' := ht.2 k
    change t ≤ tagLeft (affineRestrictedTag a b Γ.1 (Γ.2 k)) ∨
      tagRight (affineRestrictedTag a b Γ.1 (Γ.2 k)) ≤ t at ht'
    rw [affineRestrictedTag, ite_eq_left hn] at ht'
    exact ht'.elim (not_le_of_gt hc.1) (not_le_of_gt hc.2)
  apply mem_iUnion.mpr
  refine ⟨k, ?_⟩
  dsimp only [A]
  rw [ite_eq_right hn]
  exact ⟨t, hc, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AffineResidualNull
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.Graph.instFiniteElemEdgeSetOfFinite _root_.Graph.instFiniteElemVertexSetOfFinite _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine restriction preserves the atomless residual-image condition.
The two new endpoints are included explicitly among the countable additions. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem affine_exposed_full_image_countable (B : Set X) {a b : PathTime}
    (hab : a < b) (Γ : TaggedPath X) :
    (affineRestrictedPath a b Γ.1 ''
      (residualTimes B (affineRestrictedTaggedPath a b Γ) \
        (affinePathTime a b ⁻¹' residualTimes B Γ))).Countable := by
  have hc := (affine_exposed_image_countable B hab Γ).union
    (toFinite ({affineRestrictedPath a b Γ.1 ⊥, affineRestrictedPath a b Γ.1 ⊤} : Set X)).countable
  apply hc.mono
  rintro x ⟨t, ⟨ht, hold⟩, rfl⟩
  by_cases hzero : t = ⊥
  · right
    simp [hzero]
  by_cases hone : t = ⊤
  · right
    simp [hone]
  left
  exact ⟨t, ⟨⟨ht, bot_lt_iff_ne_bot.mpr hzero, lt_top_iff_ne_top.mpr hone⟩, hold⟩, rfl⟩

theorem residualImage_affine_null [MeasurableSpace X] [MeasurableSingletonClass X]
    (B : Set X) {a b : PathTime} (hab : a < b) (Γ : TaggedPath X)
    (ν : Measure X) [NullSingletonClass ν] (hnull : ν (residualImage B Γ) = 0) :
    ν (residualImage B (affineRestrictedTaggedPath a b Γ)) = 0 := by
  have hsub : residualImage B (affineRestrictedTaggedPath a b Γ) ⊆
      residualImage B Γ ∪ affineRestrictedPath a b Γ.1 ''
        (residualTimes B (affineRestrictedTaggedPath a b Γ) \
          (affinePathTime a b ⁻¹' residualTimes B Γ)) := by
    rintro x ⟨t, ht, rfl⟩
    by_cases hold : affinePathTime a b t ∈ residualTimes B Γ
    · exact Or.inl ⟨affinePathTime a b t, hold, rfl⟩
    · exact Or.inr ⟨t, ⟨ht, hold⟩, rfl⟩
  exact measure_mono_null hsub (measure_union_null hnull
    ((affine_exposed_full_image_countable B hab Γ).measure_zero ν))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_NarrowedResidualBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The countable image exposed by discarding constant tag pieces is paid
by singleton bounds. This preserves all incidence constraints on the retained
open interval, even if the new residual set has uncountably many times. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Z : Type*} [MeasurableSpace Z]

theorem timeIncidence_bound_of_countable_difference
    (R : Set (Z × X)) (P : Set X) (γ : T → X) (A C : Set T)
    (ν : Measure Z) (m : X → ℝ≥0∞)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x) (hAC : A ⊆ C)
    (hcount : (γ '' (C \ A)).Countable)
    (hbound : ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ A) ≤
      timeToll γ A (deletedWeight P m)) :
    ν (timeIncidence {q | q ∈ R ∧ q.2 ∉ P} γ C) ≤
      timeToll γ C (deletedWeight P m) := by
  have he : (C \ A) ∪ A = C := sdiff_union_of_subset hAC
  rw [← he, timeIncidence_union, timeToll_union γ _ disjoint_sdiff_left]
  exact (measure_union_le _ _).trans (add_le_add
    (countable_image_deleted_incidence_bound R P γ (C \ A) ν m hpoint hcount) hbound)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AffineResidualBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine restriction preserves the full family of residual incidence
inequalities. Rational tests in the old parameter suffice, despite the
generally irrational endpoints of the retained interval. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace Z]

theorem residualIncidenceBound_affine_open (B : Set X) (R : Set (Z × X)) (P : Set X)
    (Γ : TaggedPath X) (ν : Measure Z) (m : X → ℝ≥0∞)
    {a b : PathTime} (hab : a < b) (c d : PathTime)
    (hpoint : ∀ x, ν {z | (z, x) ∈ R} ≤ m x)
    (hbound : ResidualIncidenceBound B
      (Ioo (affinePathTime a b c) (affinePathTime a b d)) R P ν m Γ) :
    ResidualIncidenceBound B (Ioo c d) R P ν m (affineRestrictedTaggedPath a b Γ) := by
  have hi : Ioo c d ⊆ Ioo (⊥ : PathTime) ⊤ := fun _ ht =>
    ⟨lt_of_le_of_lt bot_le ht.1, lt_of_lt_of_le ht.2 le_top⟩
  have he := (affinePathTime a b).continuous.image_Ioo_of_strictMono
    (affinePathTime_strictMono hab) (a := c) (b := d)
  unfold ResidualIncidenceBound at hbound ⊢
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll] at hbound ⊢
  rw [← he, timeIncidence_restrict, timeToll_restrict _ _ (affinePathTime_strictMono hab).injective]
    at hbound
  apply timeIncidence_bound_of_countable_difference R P (affineRestrictedPath a b Γ.1)
    ((affinePathTime a b ⁻¹' residualTimes B Γ) ∩ Ioo c d)
    (residualTimes B (affineRestrictedTaggedPath a b Γ) ∩ Ioo c d) ν m hpoint _ _ hbound
  · exact inter_subset_inter_left _ (affine_old_residual_subset B hab Γ)
  · apply (affine_exposed_image_countable B hab Γ).mono
    rintro x ⟨t, ⟨ht, hnot⟩, rfl⟩
    exact ⟨t, ⟨⟨ht.1, hi ht.2⟩, fun hold => hnot ⟨hold, ht.2⟩⟩, rfl⟩

theorem residualConstraintFamily_affine (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) (hΓ : ResidualConstraintFamily B R P ν m Γ)
    (hpoint : ∀ i x, ν i {z | (z, x) ∈ R i} ≤ m i x)
    {a b : PathTime} (hab : a < b) :
    ResidualConstraintFamily B R P ν m (affineRestrictedTaggedPath a b Γ) := by
  intro i n c d
  apply residualIncidenceBound_closed_of_open B (R i) (P i n) (ν i) (m i)
    (affineRestrictedTaggedPath a b Γ) (hpoint i) _ c.toTime d.toTime
  intro s t
  exact residualIncidenceBound_affine_open B (R i) (P i n) Γ (ν i) (m i) hab s t
    (hpoint i) (residualConstraintFamily_open B R P ν m Γ hΓ i n _ _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AllowedPathRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual affine restriction of an allowed tagged path is allowed.
The only level hypothesis is the pointwise incidence bound already required
of the level weights. No path-stability statement is assumed. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_affine (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) (hΓ : AllowedTaggedPath d ν N Γ)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {a b : PathTime} (hab : a < b) :
    AllowedTaggedPath d ν N (affineRestrictedTaggedPath a b Γ) := by
  refine ⟨physicalDomainLength_affine_finite d.domainEquiv hU d.basePoint
    ⟨Γ.1, hΓ.1⟩ hab, tagRules_affineRestricted d.levels N hab Γ hΓ.2.1, ?_, ?_, ?_⟩
  · apply residualConstraintFamily_affine d.dust (fun _ => pathHitSet) d.priorDeletions
      d.priorLaws (fun i => priorHitMass (d.priorLaws i)) Γ hΓ.2.2.1 _ hab
    intro i x
    exact le_rfl
  · exact residualConstraintFamily_affine d.dust d.levels (fun _ => d.flagDeletions)
      (fun _ => volume) d.levelWeights Γ hΓ.2.2.2.1 hpoint hab
  · exact residualImage_affine_null d.dust hab Γ ν hΓ.2.2.2.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TaggedPhysicalRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual affine restrictions of tagged finite-physical paths, retaining
all the tag and physical-cost information used by the collar fragments. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] in
theorem restrictTaggedPhysicalPath_range (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (Γ : TaggedPhysicalPath d)
    {a b : PathTime} (hab : a < b) :
    range (restrictTaggedPhysicalPath d hU Γ hab).1.val = Γ.1.val '' Icc a b := by
  change range (Γ.1.val ∘ affinePathTime a b) = _
  rw [range_comp, range_affinePathTime hab]

variable [MeasurableSingletonClass X]

theorem restrictTaggedPhysicalPath_allowed (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {a b : PathTime} (hab : a < b) :
    AllowedTaggedPath d ν N ((restrictTaggedPhysicalPath d hU Γ hab).1.val,
      (restrictTaggedPhysicalPath d hU Γ hab).2) :=
  allowedTaggedPath_affine d hU ν N (Γ.1.val, Γ.2) hΓ hpoint hab

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstExitFragmentGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordering and support of the actual first-exit fragments in nested
collars. The order gives disjoint open time intervals for the cost budget. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem antitone_interval_interiors {α : Type*} [LinearOrder α] (a : ℕ → α) (ha : Antitone a) :
    Pairwise (Disjoint on fun j => Ioo (a (j+1)) (a j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (hj.2.trans_le (ha (Nat.add_one_le_iff.mpr hlt))).not_ge hi.1.le
  · exact (hi.2.trans_le (ha (Nat.add_one_le_iff.mpr hgt))).not_ge hj.1.le

variable {X : Type*} [TopologicalSpace X]

theorem firstExitTime_antitone (γ : C(PathTime, X)) (V : ℕ → Set X)
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V) (hend : γ ⊤ ∉ V 0) :
    Antitone (fun j => firstExitTime γ (V j)) := by
  intro i j hij
  apply firstExit_nested γ (hV i) (hanti hij)
  exact fun h => hend (hanti (Nat.zero_le i) h)

theorem firstExitFragments_strict (γ : C(PathTime, X)) (V : ℕ → Set X)
    (hV : ∀j, IsOpen (V j)) (hnest : ∀j, closure (V (j+1)) ⊆ V j)
    {n : ℕ} (hstart : γ ⊥ ∈ V (n+1)) (hend : γ ⊤ ∉ V 0) {j : ℕ} (hj : j ≤ n) :
    firstExitTime γ (V (j+1)) < firstExitTime γ (V j) := by
  have hanti : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  exact firstExit_strict_nested γ (hV (j+1)) (hV j) (hnest j)
    (hanti (Nat.add_le_add_right hj 1) hstart)
    (fun h => hend (hanti (Nat.zero_le j) h))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LastEntryCuts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Last-entry collar cuts and the strict separation of the retained
middle fragment from the two endpoint tails. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem reversedPath_zero (γ : C(PathTime, X)) : reversedPath γ ⊥ = γ ⊤ := by
  apply congrArg γ
  apply Subtype.ext
  change (1 : ℝ) - 0 = 1
  norm_num

theorem reversedPath_one (γ : C(PathTime, X)) : reversedPath γ ⊤ = γ ⊥ := by
  apply congrArg γ
  apply Subtype.ext
  change (1 : ℝ) - 1 = 0
  norm_num

theorem lastEntry_frontier (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) : γ (lastEntryTime γ V) ∈ frontier V := by
  exact firstExit_frontier (reversedPath γ) hV
    ((reversedPath_zero γ).symm ▸ hend) ((reversedPath_one γ).symm ▸ hstart)

theorem lastEntry_final_segment (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) :
    MapsTo γ (Ici (lastEntryTime γ V)) (closure V) := by
  intro t ht
  have hle : unitInterval.symm t ≤ firstExitTime (reversedPath γ) V :=
    unitInterval.symm_le_comm.mpr ht
  have hm := firstExit_initial_segment (reversedPath γ) hV
    ((reversedPath_zero γ).symm ▸ hend) ((reversedPath_one γ).symm ▸ hstart) hle
  change γ (unitInterval.symm (unitInterval.symm t)) ∈ closure V at hm
  simpa only [unitInterval.symm_symm] using hm

theorem lastEntry_strict_nested (γ : C(PathTime, X)) {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hVW : closure V ⊆ W)
    (hstart : γ ⊥ ∉ W) (hend : γ ⊤ ∈ V) :
    lastEntryTime γ W < lastEntryTime γ V := by
  exact unitInterval.symm_lt_symm.mpr
    (firstExit_strict_nested (reversedPath γ) hV hW hVW
      ((reversedPath_zero γ).symm ▸ hend) ((reversedPath_one γ).symm ▸ hstart))

theorem firstExit_lt_lastEntry (γ : C(PathTime, X)) {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hdis : Disjoint (closure V) (closure W))
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∈ W) :
    firstExitTime γ V < lastEntryTime γ W := by
  have hstartW : γ ⊥ ∉ W := by
    intro h
    exact disjoint_left.mp hdis (subset_closure hstart) (subset_closure h)
  have hendV : γ ⊤ ∉ V := by
    intro h
    exact disjoint_left.mp hdis (subset_closure h) (subset_closure hend)
  by_contra hn
  exact disjoint_left.mp hdis
    (frontier_subset_closure (firstExit_frontier γ hV hstart hendV))
    (lastEntry_final_segment γ hW hstartW hend (le_of_not_gt hn))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TwoEndedFragmentGeometry
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The middle interval and both families of endpoint fragments are
pairwise disjoint. This is the common budget geometry for two-ended splicing. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem monotone_interval_interiors {α : Type*} [LinearOrder α] (b : ℕ → α) (hb : Monotone b) :
    Pairwise (Disjoint on fun j => Ioo (b j) (b (j+1))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (hi.2.trans_le (hb (Nat.add_one_le_iff.mpr hlt))).not_ge hj.1.le
  · exact (hj.2.trans_le (hb (Nat.add_one_le_iff.mpr hgt))).not_ge hi.1.le

theorem twoEnded_interval_interiors_disjoint {α : Type*} [LinearOrder α]
    (a b : ℕ → α) (ha : Antitone a) (hb : Monotone b) (hab : a 0 < b 0) :
    Pairwise (Disjoint on fun i => Ioo (collarFragmentLeft a b i) (collarFragmentRight a b i)) := by
  intro i j hij
  have hleft (k : ℕ) : a k ≤ a 0 := ha (Nat.zero_le k)
  have hright (k : ℕ) : b 0 ≤ b k := hb (Nat.zero_le k)
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases j with
      | inl k =>
        exact disjoint_left.mpr (fun _ ht hs =>
          (hs.2.trans_le (hleft k)).not_ge ht.1.le)
      | inr k =>
        exact disjoint_left.mpr (fun _ ht hs =>
          (ht.2.trans_le (hright k)).not_ge hs.1.le)
  | some i =>
    cases i with
    | inl k =>
      cases j with
      | none =>
        exact disjoint_left.mpr (fun _ ht hs =>
          (ht.2.trans_le (hleft k)).not_ge hs.1.le)
      | some j =>
        cases j with
        | inl l =>
          exact antitone_interval_interiors a ha (fun h => hij (by rw [h]))
        | inr l =>
          exact disjoint_left.mpr (fun _ ht hs =>
            (ht.2.trans_le ((hleft k).trans (hab.le.trans (hright l)))).not_ge hs.1.le)
    | inr k =>
      cases j with
      | none =>
        exact disjoint_left.mpr (fun _ ht hs =>
          (hs.2.trans_le (hright k)).not_ge ht.1.le)
      | some j =>
        cases j with
        | inl l =>
          exact disjoint_left.mpr (fun _ ht hs =>
            (hs.2.trans_le ((hleft l).trans (hab.le.trans (hright k)))).not_ge ht.1.le)
        | inr l =>
          exact monotone_interval_interiors b hb (fun h => hij (by rw [h]))

variable {X : Type*} [MetricSpace X]

theorem lastEntryTime_monotone (γ : C(PathTime, X)) (W : ℕ → Set X)
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W) (hstart : γ ⊥ ∉ W 0) :
    Monotone (fun j => lastEntryTime γ (W j)) := by
  have h := firstExitTime_antitone (reversedPath γ) W hW hanti
    ((reversedPath_one γ).symm ▸ hstart)
  intro i j hij
  exact unitInterval.symm_le_symm.mpr (h hij)

theorem lastEntryFragments_strict (γ : C(PathTime, X)) (W : ℕ → Set X)
    (hW : ∀j, IsOpen (W j)) (hnest : ∀j, closure (W (j+1)) ⊆ W j)
    {n : ℕ} (hstart : γ ⊥ ∉ W 0) (hend : γ ⊤ ∈ W (n+1)) {j : ℕ} (hj : j ≤ n) :
    lastEntryTime γ (W j) < lastEntryTime γ (W (j+1)) := by
  have hanti : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  exact lastEntry_strict_nested γ (hW (j+1)) (hW j) (hnest j)
    (fun h => hstart (hanti (Nat.zero_le j) h)) (hanti (Nat.add_le_add_right hj 1) hend)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_TwoEndedFragmentBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single original path pays simultaneously for its retained middle
and both endpoint fragment families. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem twoEnded_restricted_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (a b : ℕ → PathTime)
    (ha : Antitone a) (hb : Monotone b) (hab : a 0 < b 0)
    (F : Finset ℕ) (hleft : ∀j ∈ F, a (j+1) < a j) (hright : ∀j ∈ F, b j < b (j+1))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmiddle : m (γ.val (a 0)) = 0 ∧ m (γ.val (b 0)) = 0)
    (ham : ∀j ∈ F, m (γ.val (a j)) = 0 ∧ m (γ.val (a (j+1))) = 0)
    (hbm : ∀j ∈ F, m (γ.val (b j)) = 0 ∧ m (γ.val (b (j+1))) = 0) :
    physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hab) +
      (∑j : F, (physicalTollCost d g m
        (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ (hleft j j.property)) +
        physicalTollCost d g m
        (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ (hright j j.property)))) ≤
      physicalTollCost d g m γ := by
  classical
  let emb : F ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  let index : Option (F ⊕ F) ↪ CollarFragmentIndex := (emb.sumMap emb).optionMap
  let l : Option (F ⊕ F) → PathTime := fun i => collarFragmentLeft a b (index i)
  let r : Option (F ⊕ F) → PathTime := fun i => collarFragmentRight a b (index i)
  have hlr (i : Option (F ⊕ F)) : l i < r i := by
    cases i with
    | none => exact hab
    | some i =>
      cases i with
      | inl j => exact hleft j j.property
      | inr j => exact hright j j.property
  have hd : Pairwise (Disjoint on fun i => Ioo (l i) (r i)) := by
    intro i j hij
    exact twoEnded_interval_interiors_disjoint a b ha hb hab (fun h => hij (index.injective h))
  have hml (i : Option (F ⊕ F)) : m (γ.val (l i)) = 0 := by
    cases i with
    | none => exact hmiddle.1
    | some i => cases i with
      | inl j => exact (ham j j.property).2
      | inr j => exact (hbm j j.property).1
  have hmr (i : Option (F ⊕ F)) : m (γ.val (r i)) = 0 := by
    cases i with
    | none => exact hmiddle.2
    | some i => cases i with
      | inl j => exact (ham j j.property).1
      | inr j => exact (hbm j j.property).2
  have h := sum_restricted_physicalTollCost_le d hU γ l r hlr hd g hg m hml hmr
  simpa only [tsum_fintype, Fintype.sum_option, Fintype.sum_sum_type,
    l, r, index, emb, Function.Embedding.optionMap, Function.Embedding.sumMap,
    Function.Embedding.coeFn_mk, Option.map_none, Option.map_some, Sum.map_inl, Sum.map_inr,
    collarFragmentLeft, collarFragmentRight,
    ← Finset.sum_add_distrib] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_OneEndedFragmentBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A retained prefix and all final collar fragments share the original
path budget; no initial endpoint toll is discarded. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem oneEnded_restricted_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (b : ℕ → PathTime)
    (hb : Monotone b) (hprefix : ⊥ < b 0) (F : Finset ℕ)
    (hright : ∀j ∈ F, b j < b (j+1))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hzero : m (γ.val ⊥) = 0) (hb0 : m (γ.val (b 0)) = 0)
    (hbm : ∀j ∈ F, m (γ.val (b j)) = 0 ∧ m (γ.val (b (j+1))) = 0) :
    physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hprefix) +
      (∑j : F, physicalTollCost d g m
        (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ (hright j j.property))) ≤
      physicalTollCost d g m γ := by
  classical
  let emb : F ↪ ℕ ⊕ ℕ := ⟨fun j => .inr j, fun _ _ h => Subtype.ext (Sum.inr.inj h)⟩
  let index : Option F ↪ CollarFragmentIndex := emb.optionMap
  let a : ℕ → PathTime := fun _ => ⊥
  let l : Option F → PathTime := fun i => collarFragmentLeft a b (index i)
  let r : Option F → PathTime := fun i => collarFragmentRight a b (index i)
  have hlr (i : Option F) : l i < r i := by
    cases i with
    | none => exact hprefix
    | some j => exact hright j j.property
  have hd : Pairwise (Disjoint on fun i => Ioo (l i) (r i)) := by
    intro i j hij
    exact twoEnded_interval_interiors_disjoint a b antitone_const hb hprefix
      (fun h => hij (index.injective h))
  have hml (i : Option F) : m (γ.val (l i)) = 0 := by
    cases i with
    | none => exact hzero
    | some j => exact (hbm j j.property).1
  have hmr (i : Option F) : m (γ.val (r i)) = 0 := by
    cases i with
    | none => exact hb0
    | some j => exact (hbm j j.property).2
  have h := sum_restricted_physicalTollCost_le d hU γ l r hlr hd g hg m hml hmr
  simpa only [tsum_fintype, Fintype.sum_option, l, r, index, emb, a,
    Function.Embedding.optionMap, Function.Embedding.coeFn_mk, Option.map_none, Option.map_some,
    collarFragmentLeft, collarFragmentRight] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstExitFragmentArray
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual triangular array of initial collar fragments. Entries before
the relevant collar is reached use the old path and are never selected. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] in
theorem firstExitFragmentArray_eq (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j)) {n j : ℕ} (hj : j ≤ n) :
    firstExitFragmentArray d hU Γ V hcut n j =
      restrictTaggedPhysicalPath d hU (Γ n) (hcut n j hj) := by
  simp only [firstExitFragmentArray, dite_eq_left hj]

omit [MeasurableSpace X] in
theorem firstExitFragmentArray_endpoints (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j)) {n j : ℕ} (hj : j ≤ n) :
    (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊥ =
      (Γ n).1.val (firstExitTime (Γ n).1.val (V (j+1))) ∧
    (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊤ =
      (Γ n).1.val (firstExitTime (Γ n).1.val (V j)) := by
  rw [firstExitFragmentArray_eq d hU Γ V hcut hj]
  exact ⟨restrictTaggedPhysicalPath_zero _ _ _ _, restrictTaggedPhysicalPath_one _ _ _ _⟩

omit [MeasurableSpace X] in
theorem firstExitFragmentArray_support (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    {n j : ℕ} (hj : j ≤ n) :
    range (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊆ closure (V j) := by
  rw [firstExitFragmentArray_eq d hU Γ V hcut hj, restrictTaggedPhysicalPath_range]
  rintro x ⟨t, ht, rfl⟩
  apply firstExit_initial_segment (Γ n).1.val (hV j)
    (hanti (show j ≤ n+1 by omega) (hstart n))
    (fun h => hend n (hanti (Nat.zero_le j) h))
  exact ht.2

variable [MeasurableSingletonClass X]

theorem firstExitFragmentArray_allowed (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {n j : ℕ} (hj : j ≤ n) :
    AllowedTaggedPath d ν N ((firstExitFragmentArray d hU Γ V hcut n j).1.val,
      (firstExitFragmentArray d hU Γ V hcut n j).2) := by
  rw [firstExitFragmentArray_eq d hU Γ V hcut hj]
  exact restrictTaggedPhysicalPath_allowed d hU ν N (Γ n) (hΓ n) hpoint (hcut n j hj)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LastEntryFragmentArray
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual final collar fragments, in the original time direction. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] in
theorem lastEntryFragmentArray_eq (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1))) {n j : ℕ} (hj : j ≤ n) :
    lastEntryFragmentArray d hU Γ W hcut n j =
      restrictTaggedPhysicalPath d hU (Γ n) (hcut n j hj) := by
  simp only [lastEntryFragmentArray, dite_eq_left hj]

omit [MeasurableSpace X] in
theorem lastEntryFragmentArray_endpoints (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1))) {n j : ℕ} (hj : j ≤ n) :
    (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊥ =
      (Γ n).1.val (lastEntryTime (Γ n).1.val (W j)) ∧
    (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊤ =
      (Γ n).1.val (lastEntryTime (Γ n).1.val (W (j+1))) := by
  rw [lastEntryFragmentArray_eq d hU Γ W hcut hj]
  exact ⟨restrictTaggedPhysicalPath_zero _ _ _ _, restrictTaggedPhysicalPath_one _ _ _ _⟩

omit [MeasurableSpace X] in
theorem lastEntryFragmentArray_support (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1)))
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    {n j : ℕ} (hj : j ≤ n) :
    range (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊆ closure (W j) := by
  rw [lastEntryFragmentArray_eq d hU Γ W hcut hj, restrictTaggedPhysicalPath_range]
  rintro x ⟨t, ht, rfl⟩
  apply lastEntry_final_segment (Γ n).1.val (hW j)
    (fun h => hstart n (hanti (Nat.zero_le j) h))
    (hanti (hj.trans (Nat.le_succ n)) (hend n))
  exact ht.1

variable [MeasurableSingletonClass X]

theorem lastEntryFragmentArray_allowed (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1)))
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {n j : ℕ} (hj : j ≤ n) :
    AllowedTaggedPath d ν N ((lastEntryFragmentArray d hU Γ W hcut n j).1.val,
      (lastEntryFragmentArray d hU Γ W hcut n j).2) := by
  rw [lastEntryFragmentArray_eq d hU Γ W hcut hj]
  exact restrictTaggedPhysicalPath_allowed d hU ν N (Γ n) (hΓ n) hpoint (hcut n j hj)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LastEntryFragmentProperties
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Final fragment endpoints lie on their actual collars and carry zero
cut toll whenever the collars do. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem lastEntryFragmentArray_frontiers
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    {n j : ℕ} (hj : j ≤ n) :
    (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊥ ∈ frontier (W j) ∧
    (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊤ ∈ frontier (W (j+1)) := by
  rw [(lastEntryFragmentArray_endpoints d hU Γ W hcut hj).1,
    (lastEntryFragmentArray_endpoints d hU Γ W hcut hj).2]
  constructor
  · exact lastEntry_frontier (Γ n).1.val (hW j)
      (fun h => hstart n (hanti (Nat.zero_le j) h))
      (hanti (hj.trans (Nat.le_succ n)) (hend n))
  · exact lastEntry_frontier (Γ n).1.val (hW (j+1))
      (fun h => hstart n (hanti (Nat.zero_le (j+1)) h))
      (hanti (Nat.add_le_add_right hj 1) (hend n))

theorem lastEntry_toll_zero
    (d : PathCodeData X Y) (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (m : X → ℝ≥0∞) (hm : ∀j x, x ∈ frontier (W j) → m x = 0)
    (n j : ℕ) (hj : j ≤ n+1) :
    m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0 := by
  apply hm j
  exact lastEntry_frontier (Γ n).1.val (hW j)
    (fun h => hstart n (hanti (Nat.zero_le j) h)) (hanti hj (hend n))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DelayedTupleMeasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Delaying tags scales their weighted tuple measure, allowing every finite
tuple cost of a fixed allowed path to become arbitrarily small. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem slotWeight_add (N k : ℕ) : slotWeight (N + k) = slotWeight N * slotWeight k :=
  pow_add _ _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PositiveCountableWeights
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive weights of total mass at most one on the prescribed countable
point and tuple-type sets. Their squares have the same upper bound. -/

open Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem sum_slotWeight_succ : (∑' k, slotWeight (k + 1)) = 1 := by
  simp_rw [Nat.add_comm _ 1, slotWeight_add]
  rw [ENNReal.tsum_mul_left, tsum_slotWeight]
  simpa only [slotWeight, pow_one] using
    (ENNReal.inv_mul_cancel (a := 2) (by norm_num) (by norm_num))

theorem exists_positive_summable_weights (D : Type*) [Countable D] :
    ∃ c : D → ℝ≥0∞, (∀ s, 0 < c s) ∧ (∑' s, c s) ≤ 1 := by
  classical
  let := Encodable.ofCountable D
  refine ⟨fun s => slotWeight (Encodable.encode s + 1), fun s => slotWeight_pos _, ?_⟩
  exact (ENNReal.tsum_comp_le_tsum_of_injective Encodable.encode_injective
    (fun k => slotWeight (k + 1))).trans_eq sum_slotWeight_succ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CollarFragmentSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness and cost bounds for selecting fragments in collar splicing. -/

open Set Function Filter
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem exists_close_fragment_selection {X : Type*} [TopologicalSpace X]
    (p q : ℕ → ℕ → X) (c : ℕ → ℕ → ℝ≥0∞)
    (p₀ q₀ : ℕ → X) (c₀ ε : ℕ → ℝ≥0∞)
    (hp : ∀ j, Tendsto (fun n => p n j) atTop (𝓝 (p₀ j)))
    (hq : ∀ j, Tendsto (fun n => q n j) atTop (𝓝 (q₀ j)))
    (hc : ∀ j, Tendsto (fun n => c n j) atTop (𝓝 (c₀ j)))
    (hfinite : ∀ j, c₀ j ≠ ∞) (hε : ∀ j, ε j ≠ 0)
    (U V : ℕ → Set X) (hU : ∀ j, U j ∈ 𝓝 (p₀ j)) (hV : ∀ j, V j ∈ 𝓝 (q₀ j)) :
    ∃ N : ℕ → ℕ, ∀ j, j ≤ N j ∧ p (N j) j ∈ U j ∧ q (N j) j ∈ V j ∧
      c (N j) j ≤ c₀ j + ε j := by
  have hchoose : ∀ j, ∃ n, j ≤ n ∧ p n j ∈ U j ∧ q n j ∈ V j ∧ c n j ≤ c₀ j + ε j := by
    intro j
    have hcost : ∀ᶠ n in atTop, c n j < c₀ j + ε j :=
      (tendsto_order.mp (hc j)).2 _ (ENNReal.lt_add_right (hfinite j) (hε j))
    have hevent : ∀ᶠ n in atTop, j ≤ n ∧ p n j ∈ U j ∧ q n j ∈ V j ∧
        c n j ≤ c₀ j + ε j := by
      filter_upwards [eventually_ge_atTop j, (hp j).eventually (hU j),
        (hq j).eventually (hV j), hcost] with n hn hp' hq' hc'
      exact ⟨hn, hp', hq', hc'.le⟩
    exact hevent.exists
  choose N hN using hchoose
  exact ⟨N, hN⟩

theorem selected_fragment_total_cost (c : ℕ → ℕ → ℝ≥0∞) (N : ℕ → ℕ)
    (c₀ ε : ℕ → ℝ≥0∞) (A η : ℝ≥0∞)
    (hselection : ∀ j, c (N j) j ≤ c₀ j + ε j)
    (hc : (∑' j, c₀ j) ≤ A) (hε : (∑' j, ε j) ≤ η) :
    (∑' j, c (N j) j) ≤ A + η :=
  (ENNReal.tsum_le_tsum hselection).trans
    ((ENNReal.tsum_add).le.trans (add_le_add hc hε))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_TwoEndedFragmentLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common subsequence for both endpoint collars and the retained middle,
with the full limiting cost budget. -/

open Set Function Filter
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_twoEnded_fragment_limits {X : Type*} [MetricSpace X] [CompactSpace X]
    (x y : ℕ → ℕ → X) (c d : ℕ → ℕ → ℝ≥0∞) (m : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → ℕ) (x₀ y₀ : ℕ → X) (c₀ d₀ : ℕ → ℝ≥0∞) (m₀ : ℝ≥0∞),
      StrictMono s ∧
      (∀j, Tendsto (fun n => x (s n) j) atTop (𝓝 (x₀ j))) ∧
      (∀j, Tendsto (fun n => y (s n) j) atTop (𝓝 (y₀ j))) ∧
      (∀j, Tendsto (fun n => c (s n) j) atTop (𝓝 (c₀ j))) ∧
      (∀j, Tendsto (fun n => d (s n) j) atTop (𝓝 (d₀ j))) ∧
      Tendsto (fun n => m (s n)) atTop (𝓝 m₀) := by
  let v : ℕ → (ℕ → X × X × ℝ≥0∞ × ℝ≥0∞) × ℝ≥0∞ :=
    fun n => (fun j => (x n j, y n j, c n j, d n j), m n)
  obtain ⟨v₀, _, s, hs, hv⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (v n))
  have hfirst : Tendsto (fun n => (v (s n)).1) atTop (𝓝 v₀.1) :=
    (continuous_fst.tendsto v₀).comp hv
  have hj (j : ℕ) := tendsto_pi_nhds.mp hfirst j
  have hlast (j : ℕ) := (continuous_snd.tendsto (v₀.1 j)).comp (hj j)
  have hcost (j : ℕ) := (continuous_snd.tendsto (v₀.1 j).2).comp (hlast j)
  exact ⟨s, fun j => (v₀.1 j).1, fun j => (v₀.1 j).2.1,
    fun j => (v₀.1 j).2.2.1, fun j => (v₀.1 j).2.2.2, v₀.2, hs,
    fun j => (continuous_fst.tendsto (v₀.1 j)).comp (hj j),
    fun j => (continuous_fst.tendsto (v₀.1 j).2).comp (hlast j),
    fun j => (continuous_fst.tendsto (v₀.1 j).2.2).comp (hcost j),
    fun j => (continuous_snd.tendsto (v₀.1 j).2.2).comp (hcost j),
    (continuous_snd.tendsto v₀).comp hv⟩

theorem twoEnded_limit_budget_of_eventually
    (c d : ℕ → ℕ → ℝ≥0∞) (m A : ℕ → ℝ≥0∞)
    (c₀ d₀ : ℕ → ℝ≥0∞) (m₀ A₀ : ℝ≥0∞)
    (hc : ∀j, Tendsto (fun n => c n j) atTop (𝓝 (c₀ j)))
    (hd : ∀j, Tendsto (fun n => d n j) atTop (𝓝 (d₀ j)))
    (hm : Tendsto m atTop (𝓝 m₀)) (hA : Tendsto A atTop (𝓝 A₀))
    (hbudget : ∀F : Finset ℕ, ∀ᶠn in atTop, m n + ∑j ∈ F, (c n j + d n j) ≤ A n) :
    m₀ + (∑'j, c₀ j) + (∑'j, d₀ j) ≤ A₀ := by
  rw [add_assoc, ← ENNReal.tsum_add, ENNReal.tsum_eq_iSup_sum, ENNReal.add_iSup]
  apply iSup_le
  intro F
  exact le_of_tendsto_of_tendsto
    (hm.add (tendsto_finsetSum F (fun j _ => (hc j).add (hd j)))) hA (hbudget F)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ActualOneEndedBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual retained prefixes and final fragments, with one common
subsequence and the correct one-ended limiting budget. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem actual_oneEnded_finite_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hprefix : ∀n, ⊥ < lastEntryTime (Γ n).1.val (W 0))
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W) (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    (hm : ∀n j, j ≤ n+1 → m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0)
    (F : Finset ℕ) {n : ℕ} (hn : ∀j ∈ F, j ≤ n) :
    physicalTollCost d g m (prefixFragment d hU Γ W hprefix n).1 +
      (∑j ∈ F, physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1) ≤
      physicalTollCost d g m (Γ n).1 := by
  classical
  have h := oneEnded_restricted_budget d hU (Γ n).1
    (fun j => lastEntryTime (Γ n).1.val (W j))
    (lastEntryTime_monotone (Γ n).1.val W hW hanti (hstart n)) (hprefix n) F
    (fun j hj => hcut n j (hn j hj)) g hg m (hzero n) (hm n 0 (Nat.zero_le _))
    (fun j hj => ⟨hm n j ((hn j hj).trans (Nat.le_succ _)),
      hm n (j+1) (Nat.add_le_add_right (hn j hj) 1)⟩)
  have hc (j : F) : physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1 =
      physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint
        (Γ n).1 (hcut n j (hn j j.property))) := by
    rw [lastEntryFragmentArray_eq d hU Γ W hcut (hn j j.property)]
    rfl
  rw [← Finset.sum_coe_sort F]
  simp_rw [hc]
  exact h

variable [CompactSpace X]

theorem exists_actual_oneEnded_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hprefix : ∀n, ⊥ < lastEntryTime (Γ n).1.val (W 0))
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W) (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    (hm : ∀n j, j ≤ n+1 → m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0)
    (A : ℝ≥0∞) (hA : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A)) :
    ∃ (s : ℕ → ℕ) (x : ℕ → X) (c : ℕ → ℝ≥0∞) (M : ℝ≥0∞), StrictMono s ∧
      (∀j, Tendsto (fun n => (Γ (s n)).1.val (lastEntryTime (Γ (s n)).1.val (W j))) atTop (𝓝 (x j))) ∧
      (∀j, Tendsto (fun n => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut (s n) j).1) atTop (𝓝 (c j))) ∧
      Tendsto (fun n => physicalTollCost d g m (prefixFragment d hU Γ W hprefix (s n)).1) atTop (𝓝 M) ∧
      M + (∑'j, c j) ≤ A := by
  obtain ⟨s, x, _, c, _, M, hs, hx, _, hc, _, hM⟩ := exists_twoEnded_fragment_limits
    (fun n j => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j)))
    (fun n j => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j)))
    (fun n j => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1)
    (fun _ _ => 0) (fun n => physicalTollCost d g m (prefixFragment d hU Γ W hprefix n).1)
  refine ⟨s, x, c, M, hs, hx, hc, hM, ?_⟩
  have hb := twoEnded_limit_budget_of_eventually
    (fun n j => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut (s n) j).1)
    (fun _ _ => 0) (fun n => physicalTollCost d g m (prefixFragment d hU Γ W hprefix (s n)).1)
    (fun n => physicalTollCost d g m (Γ (s n)).1) c (fun _ => 0) M A
    hc (fun _ => tendsto_const_nhds) hM (hA.comp hs.tendsto_atTop) ?_
  · simpa only [tsum_zero, add_zero] using hb
  · intro F
    filter_upwards [hs.tendsto_atTop.eventually_ge_atTop (F.sup id)] with n hn
    simp only [add_zero]
    apply actual_oneEnded_finite_budget d hU Γ W hcut hprefix hW hanti hstart g hg m hzero hm F
    intro j hj
    exact (Finset.le_sup (f := id) hj).trans hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ActualTwoEndedBudget
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common limiting budget for actual first-exit, middle, and last-entry
restrictions of the original paths. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem actual_twoEnded_finite_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V W : ℕ → Set X)
    (hleft : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) < firstExitTime (Γ n).1.val (V j))
    (hright : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hmid : ∀n, firstExitTime (Γ n).1.val (V 0) < lastEntryTime (Γ n).1.val (W 0))
    (hV : ∀j, IsOpen (V j)) (hW : ∀j, IsOpen (W j))
    (hantiV : Antitone V) (hantiW : Antitone W)
    (hendV : ∀n, (Γ n).1.val ⊤ ∉ V 0) (hstartW : ∀n, (Γ n).1.val ⊥ ∉ W 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmV : ∀n j, j ≤ n+1 → m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0)
    (hmW : ∀n j, j ≤ n+1 → m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0)
    (F : Finset ℕ) {n : ℕ} (hn : ∀j ∈ F, j ≤ n) :
    physicalTollCost d g m (middleFragment d hU Γ V W hmid n).1 +
      (∑j ∈ F, (physicalTollCost d g m (firstExitFragmentArray d hU Γ V hleft n j).1 +
        physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hright n j).1)) ≤
      physicalTollCost d g m (Γ n).1 := by
  classical
  have h := twoEnded_restricted_budget d hU (Γ n).1
    (fun j => firstExitTime (Γ n).1.val (V j)) (fun j => lastEntryTime (Γ n).1.val (W j))
    (firstExitTime_antitone (Γ n).1.val V hV hantiV (hendV n))
    (lastEntryTime_monotone (Γ n).1.val W hW hantiW (hstartW n)) (hmid n) F
    (fun j hj => hleft n j (hn j hj)) (fun j hj => hright n j (hn j hj)) g hg m
    ⟨hmV n 0 (Nat.zero_le _), hmW n 0 (Nat.zero_le _)⟩
    (fun j hj => ⟨hmV n j ((hn j hj).trans (Nat.le_succ _)),
      hmV n (j+1) (Nat.add_le_add_right (hn j hj) 1)⟩)
    (fun j hj => ⟨hmW n j ((hn j hj).trans (Nat.le_succ _)),
      hmW n (j+1) (Nat.add_le_add_right (hn j hj) 1)⟩)
  have hcost (j : F) :
      physicalTollCost d g m (firstExitFragmentArray d hU Γ V hleft n j).1 +
        physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hright n j).1 =
      physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint
        (Γ n).1 (hleft n j (hn j j.property))) +
      physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint
        (Γ n).1 (hright n j (hn j j.property))) := by
    rw [firstExitFragmentArray_eq d hU Γ V hleft (hn j j.property),
      lastEntryFragmentArray_eq d hU Γ W hright (hn j j.property)]
    rfl
  rw [← Finset.sum_coe_sort F]
  simp_rw [hcost]
  exact h

variable [CompactSpace X]

theorem exists_actual_twoEnded_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V W : ℕ → Set X)
    (hleft : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) < firstExitTime (Γ n).1.val (V j))
    (hright : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hmid : ∀n, firstExitTime (Γ n).1.val (V 0) < lastEntryTime (Γ n).1.val (W 0))
    (hV : ∀j, IsOpen (V j)) (hW : ∀j, IsOpen (W j))
    (hantiV : Antitone V) (hantiW : Antitone W)
    (hendV : ∀n, (Γ n).1.val ⊤ ∉ V 0) (hstartW : ∀n, (Γ n).1.val ⊥ ∉ W 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmV : ∀n j, j ≤ n+1 → m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0)
    (hmW : ∀n j, j ≤ n+1 → m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0)
    (A : ℝ≥0∞) (hA : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A)) :
    ∃ (s : ℕ → ℕ) (x y : ℕ → X) (c e : ℕ → ℝ≥0∞) (M : ℝ≥0∞), StrictMono s ∧
      (∀j, Tendsto (fun n => (Γ (s n)).1.val (firstExitTime (Γ (s n)).1.val (V j))) atTop (𝓝 (x j))) ∧
      (∀j, Tendsto (fun n => (Γ (s n)).1.val (lastEntryTime (Γ (s n)).1.val (W j))) atTop (𝓝 (y j))) ∧
      (∀j, Tendsto (fun n => physicalTollCost d g m (firstExitFragmentArray d hU Γ V hleft (s n) j).1) atTop (𝓝 (c j))) ∧
      (∀j, Tendsto (fun n => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hright (s n) j).1) atTop (𝓝 (e j))) ∧
      Tendsto (fun n => physicalTollCost d g m (middleFragment d hU Γ V W hmid (s n)).1) atTop (𝓝 M) ∧
      M + (∑'j, c j) + (∑'j, e j) ≤ A := by
  obtain ⟨s, x, y, c, e, M, hs, hx, hy, hc, he, hM⟩ := exists_twoEnded_fragment_limits
    (fun n j => (Γ n).1.val (firstExitTime (Γ n).1.val (V j)))
    (fun n j => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j)))
    (fun n j => physicalTollCost d g m (firstExitFragmentArray d hU Γ V hleft n j).1)
    (fun n j => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hright n j).1)
    (fun n => physicalTollCost d g m (middleFragment d hU Γ V W hmid n).1)
  refine ⟨s, x, y, c, e, M, hs, hx, hy, hc, he, hM, ?_⟩
  apply twoEnded_limit_budget_of_eventually _ _ _ _ c e M A hc he hM (hA.comp hs.tendsto_atTop)
  intro F
  filter_upwards [hs.tendsto_atTop.eventually_ge_atTop (F.sup id)] with n hn
  apply actual_twoEnded_finite_budget d hU Γ V W hleft hright hmid hV hW hantiV hantiW
    hendV hstartW g hg m hmV hmW F
  intro j hj
  exact (Finset.le_sup (f := id) hj).trans hn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BarrierJumpLosses
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed summable loss schedule for the compatible-barrier chain distance.
Its retained lower bound stays strictly above one quarter at every stage. -/

noncomputable section

namespace CircleDomainRigidity

theorem barrierStageLower_sub_loss (n : ℕ) :
    barrierStageLower n - barrierStageLoss n = barrierStageLower (n+1) := by
  simp only [barrierStageLower, barrierStageLoss, pow_succ]
  ring

theorem barrierStageLoss_pos (n : ℕ) : 0 < barrierStageLoss n := by
  unfold barrierStageLoss
  positivity

theorem barrierStageLoss_lt (n : ℕ) : barrierStageLoss n < barrierStageLower n := by
  have h : (0 : ℝ) < (1/2)^n := pow_pos (by norm_num) _
  unfold barrierStageLoss barrierStageLower
  nlinarith

theorem quarter_lt_barrierStageLower (n : ℕ) : (1 : ℝ)/4 < barrierStageLower n := by
  have h : (0 : ℝ) < (1/2)^n := pow_pos (by norm_num) _
  unfold barrierStageLower
  nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzArclengthBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathOccupation _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Lipschitz parameterization has arclength measure dominated by
its Lipschitz constant times one-dimensional Hausdorff measure on time. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem lipschitz_pathLength_Icc_le (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) {a b : PathTime} (hab : a ≤ b) :
    pathLengthMeasure γ (Icc a b) ≤ L * edist b a := by
  rw [pathLengthMeasure_Icc γ hab]
  have h := hL.lipschitzOnWith.comp_eVariationOn_le (g := id) (s := Icc a b)
    (fun _ _ => mem_univ _)
  simpa only [Function.comp_id, variation_time_identity hab] using h

theorem lipschitz_pathLength_le_diameter (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) (s : Set PathTime) :
    pathLengthMeasure γ s ≤ L * ediam s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : IsCompact (closure s) := isClosed_closure.isCompact
  obtain ⟨a, ha⟩ := hc.exists_isLeast hne.closure
  obtain ⟨b, hb⟩ := hc.exists_isGreatest hne.closure
  have hab : a ≤ b := ha.2 hb.1
  have hs : s ⊆ Icc a b := fun t ht => ⟨ha.2 (subset_closure ht), hb.2 (subset_closure ht)⟩
  calc
    pathLengthMeasure γ s ≤ pathLengthMeasure γ (Icc a b) := measure_mono hs
    _ ≤ L * edist b a := lipschitz_pathLength_Icc_le γ hL hab
    _ ≤ L * ediam (closure s) := mul_le_mul' le_rfl (edist_le_ediam_of_mem hb.1 ha.1)
    _ = _ := by rw [ediam_closure]

theorem lipschitz_pathLength_le_hausdorff (γ : RectifiablePath X) {L : ℝ≥0}
    (hL : LipschitzWith L γ.val) (hL0 : L ≠ 0) :
    pathLengthMeasure γ ≤ (L : ℝ≥0∞) • (μH[1] : Measure PathTime) := by
  have hL0' : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL0
  let μ : Measure PathTime := (L : ℝ≥0∞)⁻¹ • pathLengthMeasure γ
  have hμ : μ ≤ (μH[1] : Measure PathTime) := by
    apply Measure.le_hausdorffMeasure 1 μ ∞ (by simp)
    intro s _
    change (L : ℝ≥0∞)⁻¹ * pathLengthMeasure γ s ≤ ediam s ^ (1 : ℝ)
    rw [ENNReal.rpow_one]
    calc
      _ ≤ (L : ℝ≥0∞)⁻¹ * ((L : ℝ≥0∞) * ediam s) :=
        mul_le_mul' le_rfl (lipschitz_pathLength_le_diameter γ hL s)
      _ = ediam s := by rw [← mul_assoc, ENNReal.inv_mul_cancel hL0' ENNReal.coe_ne_top, one_mul]
  apply Measure.le_iff.mpr
  intro s hs
  have h := mul_le_mul' (le_refl (L : ℝ≥0∞)) (hμ s)
  change (L : ℝ≥0∞) * ((L : ℝ≥0∞)⁻¹ * pathLengthMeasure γ s) ≤
    (L : ℝ≥0∞) * (μH[1] : Measure PathTime) s at h
  rwa [← mul_assoc, ENNReal.mul_inv_cancel hL0' ENNReal.coe_ne_top, one_mul] at h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_BilipschitzPathCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted Hausdorff length pays for an actual embedded path
whenever the chosen parameter is Lipschitz in both directions. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem bilipschitz_pathOccupation_le (γ : RectifiablePath X) {L K : ℝ≥0}
    (hL : LipschitzWith L γ.val) (hL0 : L ≠ 0)
    (hK : AntilipschitzWith K γ.val) :
    pathOccupation γ ≤ ((L : ℝ≥0∞) * K) •
      (μH[1] : Measure X).restrict (range γ.val) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [pathOccupation_apply γ hs]
  have he : γ.val ⁻¹' s = γ.val ⁻¹' (s ∩ range γ.val) := by
    ext t
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h => ⟨h, mem_range_self t⟩, And.left⟩
  calc
    pathLengthMeasure γ (γ.val ⁻¹' s) ≤
        (L : ℝ≥0∞) * (μH[1] : Measure PathTime) (γ.val ⁻¹' s) :=
      lipschitz_pathLength_le_hausdorff γ hL hL0 _
    _ = (L : ℝ≥0∞) * (μH[1] : Measure PathTime)
        (γ.val ⁻¹' (s ∩ range γ.val)) := by rw [he]
    _ ≤ (L : ℝ≥0∞) * ((K : ℝ≥0∞) * (μH[1] : Measure X) (s ∩ range γ.val)) := by
      apply mul_le_mul' le_rfl
      simpa only [ENNReal.rpow_one] using
        hK.hausdorffMeasure_preimage_le (show (0 : ℝ) ≤ 1 by norm_num) (s ∩ range γ.val)
    _ = _ := by rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, mul_assoc]

theorem bilipschitz_pathCost_lt_top (γ : RectifiablePath X) {L K : ℝ≥0}
    (hL : LipschitzWith L γ.val) (hL0 : L ≠ 0)
    (hK : AntilipschitzWith K γ.val) (g : X → ℝ≥0∞)
    (hfinite : (∫⁻ x in range γ.val, g x ∂(μH[1] : Measure X)) < ∞) :
    (∫⁻ x, g x ∂pathOccupation γ) < ∞ := by
  calc
    (∫⁻ x, g x ∂pathOccupation γ) ≤
        ∫⁻ x, g x ∂(((L : ℝ≥0∞) * K) •
          (μH[1] : Measure X).restrict (range γ.val)) :=
      lintegral_mono' (bilipschitz_pathOccupation_le γ hL hL0 hK) (fun _ => le_rfl)
    _ = ((L : ℝ≥0∞) * K) *
        ∫⁻ x in range γ.val, g x ∂(μH[1] : Measure X) := lintegral_smul_measure _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) hfinite

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteChainPotential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-chain infimum used in the compatible barrier construction.
Costs may be infinite. In particular, truncation remains valid on components
unreachable by finite-cost chains. -/

open Set
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} (R : X → X → ℝ≥0∞ → Prop)

namespace PaidChain

variable {R}

theorem single {x y : X} {a : ℝ≥0∞} (h : R x y a) : PaidChain R x y a := by
  simpa using cons h (refl y)

theorem append {x y z : X} {a b : ℝ≥0∞}
    (h : PaidChain R x y a) (k : PaidChain R y z b) : PaidChain R x z (a + b) := by
  induction h with
  | refl => simpa using k
  | cons h _ ih => simpa only [add_assoc] using cons h (ih k)

end PaidChain

theorem chainDistance_le {E : Set X} {x y : X} {a : ℝ≥0∞}
    (hx : x ∈ E) (h : PaidChain R x y a) : chainDistance R E y ≤ a :=
  iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le a (iInf_le_of_le h le_rfl)))

theorem chainDistance_anchor {E : Set X} {x : X} (hx : x ∈ E) :
    chainDistance R E x = 0 :=
  bot_unique (chainDistance_le R hx (PaidChain.refl x))

theorem le_chainDistance {E : Set X} {y : X} {b : ℝ≥0∞}
    (h : ∀ x ∈ E, ∀ a, PaidChain R x y a → b ≤ a) : b ≤ chainDistance R E y :=
  le_iInf fun x => le_iInf fun hx => le_iInf fun a => le_iInf fun ha => h x hx a ha

theorem chainDistance_extend {E : Set X} {x y : X} {a : ℝ≥0∞}
    (h : R x y a) : chainDistance R E y ≤ chainDistance R E x + a := by
  change chainDistance R E y ≤
    (⨅ (z : X) (_ : z ∈ E) (b : ℝ≥0∞) (_ : PaidChain R z x b), b) + a
  simp only [ENNReal.iInf_add]
  refine le_iInf fun z => le_iInf fun hz => le_iInf fun b => le_iInf fun hb => ?_
  exact chainDistance_le R hz (hb.append (PaidChain.single h))

theorem chainPotential_le_one (E : Set X) (x : X) : chainPotential R E x ≤ 1 := min_le_left _ _

theorem chainPotential_anchor {E : Set X} {x : X} (hx : x ∈ E) :
    chainPotential R E x = 0 := by simp [chainPotential, chainDistance_anchor R hx]

theorem chainPotential_separated {E : Set X} {y : X}
    (h : ∀ x ∈ E, ∀ a, PaidChain R x y a → (1 / 4 : ℝ≥0∞) ≤ a) :
    chainPotential R E y = 1 := by
  apply min_eq_left
  have hd := mul_le_mul' (show (4 : ℝ≥0∞) ≤ 4 from le_rfl) (le_chainDistance R h)
  rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)] at hd
  exact hd

private theorem min_one_add_le (a b : ℝ≥0∞) : min 1 (a + b) ≤ min 1 a + b := by
  by_cases ha : 1 ≤ a
  · rw [min_eq_left ha]
    exact (min_le_left _ _).trans le_self_add
  · rw [min_eq_right (le_of_not_ge ha)]
    exact min_le_right _ _

theorem chainPotential_extend {E : Set X} {x y : X} {a : ℝ≥0∞}
    (h : R x y a) : chainPotential R E y ≤ chainPotential R E x + 4 * a := by
  have hd := mul_le_mul' (show (4 : ℝ≥0∞) ≤ 4 from le_rfl) (chainDistance_extend R (E := E) h)
  rw [mul_add] at hd
  exact (min_le_min_left 1 hd).trans (min_one_add_le _ _)

theorem chainPotential_two_sided (hR : ∀ x y a, R x y a → R y x a)
    {E : Set X} {x y : X} {a : ℝ≥0∞} (h : R x y a) :
    chainPotential R E y ≤ chainPotential R E x + 4 * a ∧
      chainPotential R E x ≤ chainPotential R E y + 4 * a :=
  ⟨chainPotential_extend R h, chainPotential_extend R (hR x y a h)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ChainPotentialOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-valued oscillation and topological bands of the truncated chain
distance. The closure argument retains all cluster values. -/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

theorem chainPotential_ne_top (R : X → X → ℝ≥0∞ → Prop) (E : Set X) (x : X) :
    chainPotential R E x ≠ ∞ :=
  (lt_of_le_of_lt (chainPotential_le_one R E x) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).ne

theorem realChainPotential_mem_Icc (R : X → X → ℝ≥0∞ → Prop) (E : Set X) (x : X) :
    realChainPotential R E x ∈ Icc 0 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  change (chainPotential R E x).toReal ≤ 1
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) (chainPotential_le_one R E x)

theorem realChainPotential_difference (R : X → X → ℝ≥0∞ → Prop)
    (hR : ∀ x y a, R x y a → R y x a) {E : Set X} {x y : X} {a : ℝ≥0∞}
    (h : R x y a) : ENNReal.ofReal |realChainPotential R E y - realChainPotential R E x| ≤ 4 * a := by
  by_cases ha : a = ∞
  · simp [ha]
  have hcost : (4 : ℝ≥0∞) * a ≠ ∞ := ENNReal.mul_ne_top (by simp) ha
  obtain ⟨hyx, hxy⟩ := chainPotential_two_sided R hR (E := E) h
  have hyxr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨chainPotential_ne_top R E x, hcost⟩) hyx
  have hxyr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨chainPotential_ne_top R E y, hcost⟩) hxy
  rw [ENNReal.toReal_add (chainPotential_ne_top R E x) hcost] at hyxr
  rw [ENNReal.toReal_add (chainPotential_ne_top R E y) hcost] at hxyr
  apply (ENNReal.ofReal_le_iff_le_toReal hcost).mpr
  apply abs_le.mpr
  change -(4 * a).toReal ≤ (chainPotential R E y).toReal - (chainPotential R E x).toReal ∧
    (chainPotential R E y).toReal - (chainPotential R E x).toReal ≤ (4 * a).toReal
  constructor <;> linarith

variable [TopologicalSpace X] [FirstCountableTopology X]

theorem clusterGraph_oscillation_of_neighborhood {G V : Set X} {f : X → ℝ}
    {s : X} {a b : ℝ} {c : ℝ≥0∞} (hV : V ∈ 𝓝 s)
    (hbound : ∀ x ∈ G ∩ V, ∀ y ∈ G ∩ V, ENNReal.ofReal |f x - f y| ≤ c)
    (ha : (s, a) ∈ clusterGraph G f) (hb : (s, b) ∈ clusterGraph G f) :
    ENNReal.ofReal |a - b| ≤ c := by
  obtain ⟨v, hfv, hv⟩ := (mem_clusterGraph_iff_mapClusterPt.mp ha).exists_seq_tendsto
  obtain ⟨w, hfw, hw⟩ := (mem_clusterGraph_iff_mapClusterPt.mp hb).exists_seq_tendsto
  have hvg := (tendsto_nhdsWithin_iff.mp hv).2
  have hwg := (tendsto_nhdsWithin_iff.mp hw).2
  have hvv := (tendsto_nhdsWithin_iff.mp hv).1.eventually hV
  have hwv := (tendsto_nhdsWithin_iff.mp hw).1.eventually hV
  apply le_of_tendsto (ENNReal.tendsto_ofReal ((hfv.sub hfw).abs))
  filter_upwards [hvg, hwg, hvv, hwv] with n hvg hwg hvv hwv
  exact hbound (v n) ⟨hvg, hvv⟩ (w n) ⟨hwg, hwv⟩

theorem clusterGraph_oscillation_of_jumps (R : X → X → ℝ≥0∞ → Prop)
    (hR : ∀ x y a, R x y a → R y x a) (E G : Set X)
    {s : X} {V : ℕ → Set X} (hV : ∀ j, V j ∈ 𝓝 s) (c : ℕ → ℝ≥0∞)
    (hj : ∀ j, ∀ x ∈ G ∩ V j, ∀ y ∈ G ∩ V j, R x y (c j))
    {a b : ℝ} (ha : (s, a) ∈ clusterGraph G (realChainPotential R E))
    (hb : (s, b) ∈ clusterGraph G (realChainPotential R E)) :
    ENNReal.ofReal |a - b| ≤ 4 * limsup c atTop := by
  have hc (j : ℕ) : ENNReal.ofReal |a - b| ≤ 4 * c j :=
    clusterGraph_oscillation_of_neighborhood (hV j)
      (fun x hx y hy => realChainPotential_difference R hR (hj j y hy x hx)) ha hb
  have hl : ENNReal.ofReal |a - b| ≤ limsup (fun j => (4 : ℝ≥0∞) * c j) atTop := by
    apply le_limsup_of_le (h := ?_)
    intro t ht
    obtain ⟨j, hj⟩ := ht.exists
    exact (hc j).trans hj
  have hm := ENNReal.limsup_mul_le' (f := atTop)
    (u := fun _ : ℕ => (4 : ℝ≥0∞)) (v := c)
    (Or.inl (by simp)) (Or.inl (by simp))
  simp only [limsup_const] at hm
  exact hl.trans hm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ReversedResidualBounds
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversal preserves the residual inequalities, with exactly reversed
test intervals and unchanged parameter multiplicity. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem image_symm_Icc (a b : PathTime) :
    unitInterval.symm '' Icc a b = Icc (unitInterval.symm b) (unitInterval.symm a) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨unitInterval.symm_le_symm.mpr hs.2, unitInterval.symm_le_symm.mpr hs.1⟩
  · intro ht
    refine ⟨unitInterval.symm t, ?_, unitInterval.symm_symm t⟩
    exact ⟨unitInterval.le_symm_comm.mpr ht.2, unitInterval.symm_le_comm.mpr ht.1⟩

variable {X Z : Type*} [MetricSpace X] [MeasurableSpace Z]

theorem residualIncidenceBound_reversed (B : Set X) (R : Set (Z × X)) (P : Set X)
    (ν : Measure Z) (m : X → ℝ≥0∞) (Γ : TaggedPath X) (a b : PathTime)
    (h : ResidualIncidenceBound B (Icc (unitInterval.symm b) (unitInterval.symm a)) R P ν m Γ) :
    ResidualIncidenceBound B (Icc a b) R P ν m (reversedTaggedPath Γ) := by
  unfold ResidualIncidenceBound at h ⊢
  rw [residualIncidence_eq_timeIncidence, residualToll_eq_timeToll] at h ⊢
  rw [← image_symm_Icc, timeIncidence_restrict,
    timeToll_restrict _ _ unitInterval.symm_bijective.injective] at h
  rw [residualTimes_reversed]
  exact h

theorem residualConstraintFamily_reversed (B : Set X) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞)
    (Γ : TaggedPath X) (hΓ : ResidualConstraintFamily B R P ν m Γ)
    (hpoint : ∀ i x, ν i {z | (z, x) ∈ R i} ≤ m i x) :
    ResidualConstraintFamily B R P ν m (reversedTaggedPath Γ) := by
  intro i n a b
  exact residualIncidenceBound_reversed B (R i) (P i n) (ν i) (m i) Γ a.toTime b.toTime
    (residualConstraintFamily_closed B R P ν m Γ hΓ hpoint i n _ _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ReversedArclength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing an ordinary rectifiable arc preserves its full occupation
measure, hence every measurable weighted arclength. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem preimage_symm_Icc (a b : PathTime) :
    unitInterval.symm ⁻¹' Icc a b = Icc (unitInterval.symm b) (unitInterval.symm a) := by
  ext s
  simp only [mem_preimage, mem_Icc, unitInterval.le_symm_comm, unitInterval.symm_le_comm,
    and_comm]

theorem pathLengthMeasure_reversed (γ : RectifiablePath X) :
    pathLengthMeasure (reversedRectifiablePath γ) =
      (pathLengthMeasure γ).map unitInterval.symm := by
  apply Measure.ext_of_Icc
  intro a b hab
  rw [pathLengthMeasure_Icc _ hab,
    Measure.map_apply unitInterval.continuous_symm.measurable measurableSet_Icc,
    preimage_symm_Icc, pathLengthMeasure_Icc _ (unitInterval.symm_le_symm.mpr hab)]
  change eVariationOn (γ.val ∘ unitInterval.symm) (Icc a b) = _
  rw [eVariationOn.comp_eq_of_antitoneOn γ.val unitInterval.symm
    (unitInterval.strictAnti_symm.antitone.antitoneOn _), image_symm_Icc]

variable [MeasurableSpace X] [BorelSpace X]

theorem pathOccupation_reversed (γ : RectifiablePath X) :
    pathOccupation (reversedRectifiablePath γ) = pathOccupation γ := by
  rw [pathOccupation, pathLengthMeasure_reversed]
  change ((pathLengthMeasure γ).map unitInterval.symm).map (reversedPath γ.val) = _
  rw [Measure.map_map (reversedPath γ.val).continuous.measurable unitInterval.continuous_symm.measurable]
  change (pathLengthMeasure γ).map ((reversedPath γ.val) ∘ unitInterval.symm) = _
  have he : ((reversedPath γ.val) ∘ unitInterval.symm) = γ.val := by
    funext t
    change γ.val (unitInterval.symm (unitInterval.symm t)) = γ.val t
    rw [unitInterval.symm_symm]
  rw [he]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AllowedPathReversal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversal stability of allowed paths, including the physical metric,
both incidence families, retained tuples, and residual-image nullity. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_reversed (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (Γ : TaggedPath X) (hΓ : AllowedTaggedPath d ν N Γ)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    AllowedTaggedPath d ν N (reversedTaggedPath Γ) := by
  refine ⟨?_, tagRules_reversed d.levels N Γ hΓ.2.1, ?_, ?_, ?_⟩
  · change physicalDomainLength d.domainEquiv d.basePoint (reversedPath Γ.1) < ∞
    rw [physicalDomainLength_reversed]
    exact hΓ.1
  · apply residualConstraintFamily_reversed d.dust (fun _ => pathHitSet)
      d.priorDeletions d.priorLaws (fun i => priorHitMass (d.priorLaws i)) Γ hΓ.2.2.1
    intro i x
    exact le_rfl
  · exact residualConstraintFamily_reversed d.dust d.levels (fun _ => d.flagDeletions)
      (fun _ => volume) d.levelWeights Γ hΓ.2.2.2.1 hpoint
  · rw [residualImage_reversed]
    exact hΓ.2.2.2.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ReversedBoundaryTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dust tolls under reversal, including the two distinct endpoint
conventions used for collar fragments and one-ended paths. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem boundaryToll_reversed (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryToll (reversedPath γ) m = boundaryToll γ m := by
  exact unitInterval.symmHomeomorph.toEquiv.tsum_eq (fun t => m (γ t))

theorem interiorToll_reversed (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    timeToll (reversedPath γ) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll γ (Ioo (⊥ : PathTime) ⊤) m := by
  have hmap : ∀ s ∈ Ioo (⊥ : PathTime) ⊤, unitInterval.symm s ∈ Ioo (⊥ : PathTime) ⊤ := by
    intro s hs
    constructor
    · change (0 : ℝ) < 1 - (s : ℝ)
      exact sub_pos.mpr hs.2
    · change 1 - (s : ℝ) < (1 : ℝ)
      have hpos : (0 : ℝ) < s := hs.1
      linarith
  have he : unitInterval.symm '' Ioo (⊥ : PathTime) ⊤ = Ioo ⊥ ⊤ := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hmap s hs
    · intro ht
      refine ⟨unitInterval.symm t, ?_, unitInterval.symm_symm t⟩
      exact hmap t ht
  exact (timeToll_image γ unitInterval.symm unitInterval.symm_bijective.injective
    (Ioo (⊥ : PathTime) ⊤) m).symm.trans (congrArg (fun A => timeToll γ A m) he)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ReversedPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time reversal preserves the actual dyadic physical occupation measure
and its weighted cost, including the endpoint conventions used in splicing. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem rectifiableOccupationCode_reversed (γ : C(PathTime, Y)) :
    rectifiableOccupationCode (reversedPath γ) = rectifiableOccupationCode γ := by
  have hiff : BoundedVariationOn (reversedPath γ) univ ↔ BoundedVariationOn γ univ := by
    change eVariationOn (reversedPath γ) univ ≠ ∞ ↔ eVariationOn γ univ ≠ ∞
    rw [variation_reversedPath]
  by_cases hγ : BoundedVariationOn γ univ
  · rw [rectifiableOccupationCode_eq (hiff.mpr hγ), rectifiableOccupationCode_eq hγ]
    exact pathOccupation_reversed ⟨γ, hγ⟩
  · simp only [rectifiableOccupationCode, dite_eq_right hγ, dite_eq_right (hiff.not.mpr hγ)]

theorem physicalStageOccupation_reversed {G : Set Y} {U : Set X} (e : G ≃ₜ U) (y₀ : Y)
    (γ : C(PathTime, X)) (n : ℕ) :
    physicalStageOccupation e y₀ n (reversedPath γ) = physicalStageOccupation e y₀ n γ := by
  unfold physicalStageOccupation
  simp_rw [physicalDyadicPath_reversed, rectifiableOccupationCode_reversed]
  exact Equiv.sum_comp (Fin.revPerm (n := 2 ^ n))
    (fun i => rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ))

theorem dyadicPhysicalOccupation_reversed {G : Set Y} {U : Set X} (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) :
    dyadicPhysicalOccupation e y₀ (reversedFinitePhysicalPath e y₀ γ) =
      dyadicPhysicalOccupation e y₀ γ := by
  ext S hS
  rw [dyadicPhysicalOccupation_apply e y₀ _ hS, dyadicPhysicalOccupation_apply e y₀ _ hS]
  simp only [reversedFinitePhysicalPath, physicalStageOccupation_reversed]

variable [MeasurableSpace C(PathTime, X)]

theorem physicalTollCost_reversed (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (γ : FinitePhysicalPath d.domainEquiv d.basePoint) :
    physicalTollCost d g m (reversedFinitePhysicalPath d.domainEquiv d.basePoint γ) =
      physicalTollCost d g m γ := by
  unfold physicalTollCost
  rw [dyadicPhysicalOccupation_reversed]
  exact congrArg _ (boundaryToll_reversed γ.val m)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedDensityEnergy
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adding a bounded nonnegative penalty preserves finite quadratic energy
on a finite measure space, including densities with null-set infinities. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace CircleDomainRigidity

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a+b)^2 ≤ 2 * (a^2+b^2) := by
  by_cases ha : a = ∞
  · simp [ha]
  by_cases hb : b = ∞
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  exact_mod_cast (add_sq_le : (a+b)^2 ≤ 2 * (a^2+b^2))

theorem lintegral_add_sq_lt_top_of_bounded
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (g h : X → ℝ≥0∞) (hg : Measurable g)
    (hg₂ : (∫⁻x, g x ^ 2 ∂μ) < ∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hh : ∀x, h x ≤ C) : (∫⁻x, (g x + h x)^2 ∂μ) < ∞ := by
  have hpoint (x : X) : (g x + h x)^2 ≤ 2 * (g x ^ 2 + C^2) :=
    (ennreal_add_sq_le _ _).trans (mul_le_mul' le_rfl (add_le_add le_rfl (pow_le_pow_left' (hh x) 2)))
  have hbound : (∫⁻x, (g x + h x)^2 ∂μ) ≤ 2 * ((∫⁻x, g x ^ 2 ∂μ) + C^2 * μ Set.univ) := by
    calc
      _ ≤ ∫⁻x, 2 * (g x ^ 2 + C^2) ∂μ := lintegral_mono hpoint
      _ = _ := by
        have hm : Measurable (fun x => g x ^ 2 + C^2) := (hg.pow_const 2).add measurable_const
        rw [lintegral_const_mul 2 hm, lintegral_add_left (hg.pow_const 2), lintegral_const]
  exact hbound.trans_lt (ENNReal.mul_lt_top (by norm_num)
    (ENNReal.add_lt_top.mpr ⟨hg₂, ENNReal.mul_lt_top (ENNReal.pow_lt_top hC.lt_top) (measure_lt_top μ _)⟩))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClopenNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating a component by a clopen neighborhood

This is the compact-space step before the smooth contour construction:
a neighborhood containing a whole component contains a clopen
neighborhood of that component's base point. Applied in a closed
obstacle set, it isolates a singleton dust component.
-/

open Set

namespace CircleDomainRigidity

theorem exists_clopen_between_component_and_open
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) {O : Set X} (hO : IsOpen O) (hC : connectedComponent x ⊆ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O := by
  classical
  have hd : Disjoint Oᶜ (connectedComponent x) :=
    Set.disjoint_left.mpr (fun y hy hyC => hy (hC hyC))
  rw [connectedComponent_eq_iInter_isClopen x] at hd
  obtain ⟨s, hs⟩ := hO.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun V : {V : Set X // IsClopen V ∧ x ∈ V} => V.val)
    (fun V => V.property.1.isClosed) (Set.disjoint_iff_inter_eq_empty.mp hd)
  refine ⟨⋂ V ∈ s, (V : Set X), isClopen_biInter_finset (fun V _ => V.property.1),
    mem_iInter₂.mpr (fun V _ => V.property.2), ?_⟩
  intro y hy
  by_contra hyO
  exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hs) hyO hy

/-- In particular, singleton components in a compact closed obstacle
have arbitrarily small relatively clopen neighborhoods. -/
theorem exists_clopen_neighborhood_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (x : X) (hC : connectedComponent x = {x}) {O : Set X}
    (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ O :=
  exists_clopen_between_component_and_open x hO (by simpa only [hC, singleton_subset_iff] using hx)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallPhysicalDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small physical disks at singleton quotient components

A singleton component of a closed quotient obstacle has a compact relatively
clopen neighborhood inside any prescribed open neighborhood. Pulling it back
and applying the proved smooth contour construction gives actual physical
Jordan disks. The boundaries avoid the entire quotient obstacle, and hence
lie in the physical domain whenever that obstacle contains the collapsed
complementary components.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- The compact relatively clopen obstacle piece used before smoothing. -/
theorem exists_compact_piece_of_singleton_component
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ A : Set X, IsCompact A ∧ x ∈ A ∧ A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let xf : F := ⟨x, hx⟩
  have hcomp : connectedComponent xf = {xf} := by
    apply Set.Subset.antisymm
    · intro y hy
      have hy' : y.val ∈ connectedComponentIn F x := by
        rw [connectedComponentIn_eq_image hx]
        exact ⟨y, hy, rfl⟩
      rw [hcomponent] at hy'
      exact mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hy'))
    · exact singleton_subset_iff.mpr mem_connectedComponent
  obtain ⟨B, hB, hxB, hBV⟩ := exists_clopen_neighborhood_of_singleton_component xf hcomp
    (hV.preimage continuous_subtype_val) hxV
  let A : Set X := Subtype.val '' B
  have hdiff : F \ A = Subtype.val '' Bᶜ := by
    ext y
    constructor
    · rintro ⟨hyF, hyA⟩
      exact ⟨⟨y, hyF⟩, fun h => hyA ⟨⟨y, hyF⟩, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have hzy' : z = y := Subtype.ext hzy
      exact hy (hzy' ▸ hz)
  refine ⟨A, hB.isClosed.isCompact.image continuous_subtype_val,
    ⟨xf, hxB, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.property
  · rintro _ ⟨y, hy, rfl⟩
    exact hBV hy
  · rw [hdiff]
    exact hF.isClosedMap_subtype_val _ hB.isOpen.isClosed_compl

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphericalAreaLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local planar square integrability from spherical area. Spherical area
is written in its finite stereographic chart, with density 4/(1+|z|²)². -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_1
theorem lintegral_sphericalArea (g : Sphere → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻x, g x ∂sphericalArea =
      ∫⁻z : ℂ, ENNReal.ofReal (sphericalAreaDensity z) * g (z : Sphere) := by
  rw [sphericalArea, lintegral_map hg OnePoint.continuous_coe.measurable]
  exact lintegral_withDensity_eq_lintegral_mul _
    continuous_sphericalAreaDensity.measurable.ennreal_ofReal
    (hg.comp OnePoint.continuous_coe.measurable)

theorem planar_energy_on_compact_finite {K : Set ℂ} (hK : IsCompact K)
    (g : ℂ → ℝ≥0∞)
    (henergy : (∫⁻z, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2) < ∞) :
    (∫⁻z in K, g z ^ 2) < ∞ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_sphericalAreaDensity.continuousOn
  let c := ENNReal.ofReal (sphericalAreaDensity z₀)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (sphericalAreaDensity_pos z₀)).ne'
  have hcle (z : ℂ) (hz : z ∈ K) : c ≤ ENNReal.ofReal (sphericalAreaDensity z) :=
    ENNReal.ofReal_le_ofReal (hmin hz)
  have hbound : c * (∫⁻z in K, g z ^ 2) < ∞ := by
    rw [← lintegral_const_mul' c _ (by exact ENNReal.ofReal_ne_top)]
    apply lt_of_le_of_lt _ henergy
    calc
      (∫⁻z in K, c * g z ^ 2) ≤
          ∫⁻z in K, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2 := by
        apply setLIntegral_mono' hK.measurableSet
        intro z hz
        exact mul_le_mul' (hcle z hz) le_rfl
      _ ≤ ∫⁻z, ENNReal.ofReal (sphericalAreaDensity z) * g z ^ 2 :=
        lintegral_mono' Measure.restrict_le_self le_rfl
  by_contra h
  have heq : (∫⁻z in K, g z ^ 2) = ∞ := top_unique (not_lt.mp h)
  simp [heq, ENNReal.mul_top hc] at hbound

theorem planar_energy_quotient_neighborhood_finite
    (π : Sphere → Sphere) (hπ : Continuous π) {O : Set Sphere}
    (hinfty : π OnePoint.infty ∉ closure O)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g (z : Sphere) ^ 2) < ∞ := by
  have hK : IsCompact (((↑) : ℂ → Sphere) ⁻¹' (π ⁻¹' closure O)) :=
    isCompact_finite_preimage (isClosed_closure.preimage hπ) hinfty
  have he := planar_energy_on_compact_finite hK (fun z => g (z : Sphere))
  rw [lintegral_sphericalArea _ (hg.pow_const 2)] at henergy
  exact (lintegral_mono_set (preimage_mono subset_closure)).trans_lt (he henergy)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstEntryRestriction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cut a path at its first arrival in a closed collar. The retained
prefix avoids the open collar and has no greater full cost. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem physicalTollCost_affine_le (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞) :
    physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hab) ≤
      physicalTollCost d g m γ := by
  unfold physicalTollCost
  rw [physicalCost_affine d.domainEquiv hU d.basePoint γ hab g hg]
  change _ + boundaryToll (affineRestrictedPath a b γ.val) m ≤ _
  rw [boundaryToll_affine γ.val m hab,
    physicalOccupation_integral d.domainEquiv hU d.basePoint γ g hg, boundaryToll_eq_timeToll]
  exact add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl)
    (timeToll_mono γ.val m (subset_univ _))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DomainPathAdmissibility
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every path of finite physical length which stays off the dust is
allowed with inactive tags, for every residual measure and tuple exclusion. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem residualTimes_empty_of_avoids {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) : residualTimes B Γ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact h t ht.1

theorem residualImage_empty_of_avoids {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) : residualImage B Γ = ∅ := by
  rw [residualImage, residualTimes_empty_of_avoids h, image_empty]

theorem residualIncidence_empty_of_avoids {Z : Type*} [TopologicalSpace Z]
    {B : Set X} {Γ : TaggedPath X} (h : ∀ t, Γ.1 t ∉ B)
    (I : Set PathTime) (R : Set (Z × X)) (P : Set X) :
    {z | (Γ, z) ∈ residualIncidence B I R P} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro z ⟨t, ht, _⟩
  rw [residualTimes_empty_of_avoids h] at ht
  exact ht

theorem residualConstraintFamily_of_avoids {Z : Type*} [TopologicalSpace Z]
    [MeasurableSpace Z] {B : Set X} {Γ : TaggedPath X}
    (h : ∀ t, Γ.1 t ∉ B) (R : ℕ → Set (Z × X))
    (P : ℕ → ℕ → Finset X) (ν : ℕ → Measure Z) (m : ℕ → X → ℝ≥0∞) :
    ResidualConstraintFamily B R P ν m Γ := by
  intro i n a b
  unfold ResidualIncidenceBound
  rw [residualIncidence_empty_of_avoids h, measure_empty]
  exact bot_le

variable {Y : Type*} [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_of_avoids (d : PathCodeData X Y)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (havoid : ∀ t, γ t ∉ d.dust) : AllowedTaggedPath d ν N (γ, fun _ => inactiveTag) := by
  refine ⟨hfin, ?_, ?_, ?_, ?_⟩
  · intro k
    exact inactiveTag_rules d.levels N γ
  · exact residualConstraintFamily_of_avoids havoid _ _ _ _
  · exact residualConstraintFamily_of_avoids havoid _ _ _ _
  · rw [residualImage_empty_of_avoids havoid, measure_empty]

theorem domainPath_allowed (d : PathCodeData X Y)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (γ : C(PathTime, X)) (hfin : physicalDomainLength d.domainEquiv d.basePoint γ < ∞)
    (hγ : ∀ t, γ t ∈ d.quotientDomain) : AllowedTaggedPath d ν N (γ, fun _ => inactiveTag) :=
  allowedTaggedPath_of_avoids d ν N γ hfin
    (fun t ht => Set.disjoint_left.mp hdisj (hγ t) ht)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DomainPhysicalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rectifiable physical path entirely in the original domain projects
to an allowed quotient path, with exactly its original physical length. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

variable [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem projected_physical_path_allowed (d : PathCodeData X Y)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ d.physicalDomain) :
    AllowedTaggedPath d ν N (projectDomainPath d.domainEquiv β.val hβ, fun _ => inactiveTag) := by
  apply domainPath_allowed d hdisj ν N _ _ (projectDomainPath_mem d.domainEquiv β.val hβ)
  rw [physicalDomainLength_project]
  exact lt_top_iff_ne_top.mpr β.property

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_DomainPhysicalOccupation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a path contained in the physical domain, the dyadic occupation
kernel is exactly ordinary arclength occupation, with multiplicity. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem physicalStageOccupation_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) (n : ℕ) :
    physicalStageOccupation e y₀ n (projectDomainPath e β.val hβ) = pathOccupation β := by
  have he (i : Fin (2 ^ n)) :
      rectifiableOccupationCode (physicalDyadicPath e y₀ n i (projectDomainPath e β.val hβ)) =
        pathPortionOccupation β (dyadicLeft n i) (dyadicRight n i) := by
    rw [physicalDyadicPath_project]
    change rectifiableOccupationCode (clippedPath β (dyadicLeft_le_right n i)).val = _
    rw [rectifiableOccupationCode_eq (clippedPath β (dyadicLeft_le_right n i)).property]
    exact pathOccupation_clipped β (dyadicLeft_le_right n i)
  ext E hE
  have hsum := congrArg (fun ν : Measure PathTime => ν (β.val ⁻¹' E))
    (sum_dyadic_restrict (pathLengthMeasure β) n)
  simp only [Measure.coe_finsetSum, Finset.sum_apply] at hsum
  simpa only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply, he,
    pathPortionOccupation, Measure.map_apply β.val.continuous.measurable hE,
    pathOccupation_apply β hE] using hsum

theorem dyadicPhysicalOccupation_project (e : G ≃ₜ U) (y₀ : Y)
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ G) :
    dyadicPhysicalOccupation e y₀ (finiteProjectedPhysicalPath e y₀ β hβ) = pathOccupation β := by
  ext E hE
  rw [dyadicPhysicalOccupation_apply e y₀ _ hE]
  change (⨆ n, physicalStageOccupation e y₀ n (projectDomainPath e β.val hβ) E) = _
  simp only [physicalStageOccupation_project, iSup_const]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FullDomainPhysicalLift
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An arbitrary finite physical path wholly in the quotient domain has
an actual rectifiable physical lift with exactly the original occupation. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  in
theorem fullDomainPhysicalLift_value (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) (t : PathTime) :
    (fullDomainPhysicalLift d hU γ hγ).val t = (d.domainEquiv.symm ⟨γ.val t, hγ t⟩).val := by
  simp [fullDomainPhysicalLift, physicalSubpath, timeClip]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  in
theorem fullDomainPhysicalLift_project (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) :
    finiteProjectedPhysicalPath d.domainEquiv d.basePoint
      (fullDomainPhysicalLift d hU γ hγ) (fullDomainPhysicalLift_mem d hU γ hγ) = γ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change (d.domainEquiv ⟨(fullDomainPhysicalLift d hU γ hγ).val t, _⟩).val = γ.val t
  simp only [fullDomainPhysicalLift_value]
  exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨γ.val t, hγ t⟩)

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem fullDomainPhysicalLift_projects
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain)
    (π : Y → X) (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (t : PathTime) : π ((fullDomainPhysicalLift d hU γ hγ).val t) = γ.val t := by
  simpa [fullDomainPhysicalLift, timeClip] using
    physicalSubpath_projects d.domainEquiv π (fun y => (he y).symm)
      (show (⊥ : PathTime) ≤ ⊤ from bot_le) ⟨γ.val, fun t _ => hγ t⟩ t

omit [MeasurableSpace X] [BorelSpace X] in
theorem dyadicPhysicalOccupation_fullDomainLift
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hγ : ∀t, γ.val t ∈ d.quotientDomain) :
    dyadicPhysicalOccupation d.domainEquiv d.basePoint γ =
      pathOccupation (fullDomainPhysicalLift d hU γ hγ) := by
  calc
    _ = dyadicPhysicalOccupation d.domainEquiv d.basePoint
        (finiteProjectedPhysicalPath d.domainEquiv d.basePoint
          (fullDomainPhysicalLift d hU γ hγ) (fullDomainPhysicalLift_mem d hU γ hγ)) :=
      congrArg (dyadicPhysicalOccupation d.domainEquiv d.basePoint)
        (fullDomainPhysicalLift_project d hU γ hγ).symm
    _ = _ := dyadicPhysicalOccupation_project _ _ _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_IndicatorPathPenalty
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A constant density on an open region pays the length of a rectifiable
passage that lies in that region apart from its last endpoint. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem indicator_occupation_of_interior_passage
    (γ : RectifiablePath Y) (O : Set Y) (hO : MeasurableSet O)
    (hinside : ∀t < (⊤ : PathTime), γ.val t ∈ O) (a : ℝ≥0∞) :
    (∫⁻y, O.indicator (fun _ => a) y ∂pathOccupation γ) = a * eVariationOn γ.val univ := by
  rw [lintegral_pathOccupation γ (measurable_const.indicator hO)]
  have hae : ∀ᵐ t ∂pathLengthMeasure γ, O.indicator (fun _ => a) (γ.val t) = a := by
    have hn := (measure_eq_zero_iff_ae_notMem).mp
      (measure_singleton (μ := pathLengthMeasure γ) (⊤ : PathTime))
    filter_upwards [hn] with t ht
    have hne : t ≠ ⊤ := by simpa only [mem_singleton_iff] using ht
    exact Set.indicator_of_mem (hinside t (lt_top_iff_ne_top.mpr hne)) (fun _ => a)
  rw [lintegral_congr_ae hae, lintegral_const, pathLengthMeasure_univ]

theorem indicator_occupation_pays_endpoint_distance
    (γ : RectifiablePath Y) (O : Set Y) (hO : MeasurableSet O)
    (hinside : ∀t < (⊤ : PathTime), γ.val t ∈ O)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : δ ≤ edist (γ.val ⊥) (γ.val ⊤)) :
    1 ≤ ∫⁻y, O.indicator (fun _ => δ⁻¹) y ∂pathOccupation γ := by
  rw [indicator_occupation_of_interior_passage γ O hO hinside]
  calc
    1 = δ⁻¹ * δ := (ENNReal.inv_mul_cancel hδ hδfin).symm
    _ ≤ δ⁻¹ * eVariationOn γ.val univ :=
      mul_le_mul' le_rfl (hsep.trans (eVariationOn.edist_le γ.val (mem_univ _) (mem_univ _)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PhysicalExitPenalty
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine bounded indicator density pays for a first-exit passage
through a relatively compact domain region. The estimate uses physical
arclength and remains valid for paths with arbitrary dust contacts elsewhere. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem first_exit_indicator_cost_lower_bound
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain)
    (A : Set Y) {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : ∀a ∈ A, ∀b ∉ π ⁻¹' O, δ ≤ edist a b)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hstart : γ.val ⊥ ∈ O) (hend : γ.val ⊤ ∉ O)
    (hA : (d.domainEquiv.symm ⟨γ.val ⊥, hOU (subset_closure hstart)⟩).val ∈ A)
    (m : X → ℝ≥0∞) :
    1 ≤ physicalTollCost d ((π ⁻¹' O).indicator (fun _ => δ⁻¹)) m γ := by
  let t := firstExitTime γ.val O
  have ht : (⊥ : PathTime) < t := firstExit_pos γ.val hO hstart hend
  let ρ := affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ ht
  have hρU (s : PathTime) : ρ.val s ∈ d.quotientDomain := by
    apply hOU
    apply firstExit_initial_segment γ.val hO hstart hend
    exact (affinePathTime_mem_Icc ht.le s).2
  let β := fullDomainPhysicalLift d hU ρ hρU
  have hproject (s : PathTime) : π (β.val s) = ρ.val s :=
    fullDomainPhysicalLift_projects d hU ρ hρU π he s
  have hβA : β.val ⊥ ∈ A := by
    simpa only [β, fullDomainPhysicalLift_value, ρ, affineFinitePhysicalPath,
      affineRestrictedPath, ContinuousMap.comp_apply, affinePathTime_zero] using hA
  have hβout : β.val ⊤ ∉ π ⁻¹' O := by
    change π (β.val ⊤) ∉ O
    rw [hproject]
    change γ.val (affinePathTime ⊥ t ⊤) ∉ O
    rw [affinePathTime_one]
    exact firstExit_notMem γ.val hO hend
  have hβin (s : PathTime) (hs : s < ⊤) : β.val s ∈ π ⁻¹' O := by
    change π (β.val s) ∈ O
    rw [hproject]
    apply mem_before_firstExit γ.val O
    have h := affinePathTime_strictMono ht hs
    rwa [affinePathTime_one] at h
  let h : Y → ℝ≥0∞ := (π ⁻¹' O).indicator (fun _ => δ⁻¹)
  have hh : Measurable h := measurable_const.indicator (hO.preimage hπ).measurableSet
  have hpay : 1 ≤ ∫⁻y, h y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ := by
    rw [dyadicPhysicalOccupation_fullDomainLift d hU ρ hρU]
    exact indicator_occupation_pays_endpoint_distance β _ (hO.preimage hπ).measurableSet
      hβin hδ hδfin (hsep _ hβA _ hβout)
  have hfull : 1 ≤ physicalTollCost d h m ρ := hpay.trans le_self_add
  exact hfull.trans (physicalTollCost_affine_le d hU γ ht h hh m)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactExitPenalty
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact separation supplies the positive physical width and hence an
actual bounded indicator penalty. No path-cost lower bound is assumed. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_compact_exit_penalty
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain)
    (A : Set Y) (hA : IsCompact A) (hAO : A ⊆ π ⁻¹' O) :
    ∃h : Y → ℝ≥0∞, ∃C : ℝ≥0∞,
      Measurable h ∧ C ≠ ∞ ∧ (∀y, h y ≤ C) ∧ (∀y ∉ π ⁻¹' O, h y = 0) ∧
      ∀γ : FinitePhysicalPath d.domainEquiv d.basePoint,
        ∀hs : γ.val ⊥ ∈ O, γ.val ⊤ ∉ O →
        (d.domainEquiv.symm ⟨γ.val ⊥, hOU (subset_closure hs)⟩).val ∈ A →
        ∀m : X → ℝ≥0∞, 1 ≤ physicalTollCost d h m γ := by
  have hd : Disjoint A (π ⁻¹' O)ᶜ := Set.disjoint_left.mpr fun _ ha hn => hn (hAO ha)
  obtain ⟨δ, hδ, hsep⟩ := Metric.exists_pos_forall_lt_edist hA (hO.preimage hπ).isClosed_compl hd
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hδ.ne'
  let C : ℝ≥0∞ := (δ : ℝ≥0∞)⁻¹
  let h : Y → ℝ≥0∞ := (π ⁻¹' O).indicator (fun _ => C)
  refine ⟨h, C, measurable_const.indicator (hO.preimage hπ).measurableSet,
    ENNReal.inv_ne_top.mpr hδ0, ?_, ?_, ?_⟩
  · intro y
    change (π ⁻¹' O).indicator (fun _ => C) y ≤ C
    by_cases hy : y ∈ π ⁻¹' O
    · exact le_of_eq (Set.indicator_of_mem hy _)
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  · intro y hy
    exact Set.indicator_of_notMem hy _
  · intro γ hs ht ha m
    exact first_exit_indicator_cost_lower_bound d hU π hπ he O hO hOU A hδ0 (by simp)
      (fun a ha b hb => (hsep a ha b hb).le) γ hs ht ha m

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GatePenaltyDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly many forbidden gate hits admit a bounded penalty density in
a safe relatively compact domain region. Adding it preserves finite energy
and leaves the original density unchanged outside that region. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_1 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_gate_penalty_density
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (F S : Set Sphere) (hF : IsCompact F) (hS : IsOpen S) (hFS : F ⊆ S)
    (hSU : S ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg₂ : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) :
    ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞,
      IsOpen O ∧ F ⊆ O ∧ closure O ⊆ S ∧ Measurable g₁ ∧
      (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      ∀γ : FinitePhysicalPath d.domainEquiv d.basePoint,
        γ.val ⊥ ∉ O → γ.val ⊤ ∈ F → ∀m : Sphere → ℝ≥0∞,
          1 ≤ physicalTollCost d g₁ m γ := by
  obtain ⟨O, hOo, hFO, hOS⟩ := hF.exists_isOpen_closure_subset (hS.mem_nhdsSet.mpr hFS)
  have hOU : closure O ⊆ d.quotientDomain := hOS.trans hSU
  let A := π ⁻¹' F
  have hA : IsCompact A := (hF.isClosed.preimage hπ).isCompact
  obtain ⟨h, C, hh, hC, hbound, hzero, hpay⟩ := exists_compact_exit_penalty
    d hU π hπ he O hOo hOU A hA (preimage_mono hFO)
  let g₁ : Sphere → ℝ≥0∞ := fun y => g y + h y
  refine ⟨O, g₁, hOo, hFO, hOS, hg.add hh, fun y => le_self_add, ?_, ?_, ?_⟩
  · intro y hy
    change g y + h y = g y
    rw [hzero y hy, add_zero]
  · exact lintegral_add_sq_lt_top_of_bounded sphericalArea g h hg hg₂ C hC hbound
  · intro γ hstart hend m
    let ρ := reversedFinitePhysicalPath d.domainEquiv d.basePoint γ
    have hρ0 : ρ.val ⊥ ∈ O := by
      change reversedPath γ.val ⊥ ∈ O
      rw [reversedPath_zero]
      exact hFO hend
    have hρ1 : ρ.val ⊤ ∉ O := by
      change reversedPath γ.val ⊤ ∉ O
      rwa [reversedPath_one]
    have hρA : (d.domainEquiv.symm ⟨ρ.val ⊥, hOU (subset_closure hρ0)⟩).val ∈ A := by
      change π (d.domainEquiv.symm ⟨ρ.val ⊥, _⟩).val ∈ F
      rw [← he]
      simp only [Homeomorph.apply_symm_apply]
      change reversedPath γ.val ⊥ ∈ F
      rwa [reversedPath_zero]
    have hp := hpay ρ hρ0 hρ1 hρA m
    rw [physicalTollCost_reversed] at hp
    apply hp.trans
    apply add_le_add _ le_rfl
    apply lintegral_mono
    intro y
    change h y ≤ g y + h y
    calc
      h y = 0 + h y := (zero_add _).symm
      _ ≤ g y + h y := add_le_add bot_le le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GateForbiddenSet
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hit-location restrictions are avoidance of the union of forbidden
parts of the prescribed contours. No closedness is needed for this identity. -/

open Set Function

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem gateRules_iff_avoids (C K : ℕ → Set X) (γ : C(PathTime, X)) :
    GateRules C K γ ↔ ∀t, γ t ∉ gateForbiddenSet C K := by
  constructor
  · intro h t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact hi.2 (h i t hi.1)
  · intro h i t ht
    by_contra hn
    exact h t (mem_iUnion.mpr ⟨i, ht, hn⟩)

omit [MetricSpace X] in
theorem avoids_gateForbiddenSet_of_avoids_contours
    (C K : ℕ → Set X) {x : X} (h : ∀i, x ∉ C i) : x ∉ gateForbiddenSet C K := by
  intro hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact h i hi.1

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteGateObstacles
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The forbidden portions of finitely many prescribed gates form a compact
obstacle, and failure of those gates is exactly a hit of this obstacle. -/

open Set Function

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem isCompact_finiteGateForbiddenSet (k : ℕ) (C K : ℕ → Set X)
    (hC : ∀j ≤ k, IsCompact (C j)) (hK : ∀j ≤ k, IsOpen (K j)) :
    IsCompact (finiteGateForbiddenSet k C K) := by
  apply isCompact_iUnion
  intro i
  exact (hC i.val (by omega)).inter_right (hK i.val (by omega)).isClosed_compl

theorem finiteGateRules_iff_avoids (k : ℕ) (C K : ℕ → Set X) (γ : C(PathTime, X)) :
    (∀j ≤ k, GateRule (C j) (K j) γ) ↔ ∀t, γ t ∉ finiteGateForbiddenSet k C K := by
  constructor
  · intro h t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact hi.2 (h i.val (by omega) t hi.1)
  · intro h j hj t ht
    by_contra hn
    exact h t (mem_iUnion.mpr ⟨⟨j, by omega⟩, ht, hn⟩)

theorem exists_forbidden_hit_of_not_finiteGateRules
    (k : ℕ) (C K : ℕ → Set X) (γ : C(PathTime, X))
    (h : ¬ ∀j ≤ k, GateRule (C j) (K j) γ) :
    ∃t, γ t ∈ finiteGateForbiddenSet k C K := by
  classical
  rw [finiteGateRules_iff_avoids] at h
  simpa only [not_forall, not_not] using h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GatePenaltySeparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Step 2 of the compatible-barrier construction: replace the finitely many
gate restrictions by a bounded penalty. Good paths retain the original
half-unit separation; every bad path pays at least one unit. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_2 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_ungated_half_separation
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E H : Set Sphere) (k : ℕ) (C K : ℕ → Set Sphere)
    (hC : ∀j ≤ k, IsCompact (C j)) (hK : ∀j ≤ k, IsOpen (K j))
    (S : Set Sphere) (hS : IsOpen S) (hSU : S ⊆ d.quotientDomain)
    (hFS : finiteGateForbiddenSet k C K ⊆ S) (hES : Disjoint E S)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg₂ : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) (m : Sphere → ℝ≥0∞)
    (hgood : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H → (∀j ≤ k, GateRule (C j) (K j) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1) :
    ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞,
      IsOpen O ∧ closure O ⊆ S ∧ Measurable g₁ ∧
      (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H →
          ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g₁ m Γ.1 := by
  obtain ⟨O, g₁, hOo, _, hOS, hg₁, hgg₁, hoff, henergy, hpay⟩ :=
    exists_gate_penalty_density d hU π hπ he (finiteGateForbiddenSet k C K) S
      (isCompact_finiteGateForbiddenSet k C K hC hK) hS hFS hSU g hg hg₂
  refine ⟨O, g₁, hOo, hOS, hg₁, hgg₁, hoff, henergy, ?_⟩
  intro Γ hΓ hΓ0 hΓ1
  by_cases hgates : ∀j ≤ k, GateRule (C j) (K j) Γ.1.val
  · apply (hgood Γ hΓ hΓ0 hΓ1 hgates).trans
    exact add_le_add (lintegral_mono hgg₁) le_rfl
  · obtain ⟨t, ht⟩ := exists_forbidden_hit_of_not_finiteGateRules k C K Γ.1.val hgates
    have htpos : (⊥ : PathTime) < t := by
      apply bot_lt_iff_ne_bot.mpr
      intro heq
      exact Set.disjoint_left.mp hES hΓ0 (heq ▸ hFS ht)
    let ρ := affineFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 htpos
    have hρ0 : ρ.val ⊥ ∉ O := by
      change Γ.1.val (affinePathTime ⊥ t ⊥) ∉ O
      rw [affinePathTime_zero]
      intro h
      exact Set.disjoint_left.mp hES hΓ0 (hOS (subset_closure h))
    have hρ1 : ρ.val ⊤ ∈ finiteGateForbiddenSet k C K := by
      change Γ.1.val (affinePathTime ⊥ t ⊤) ∈ _
      rwa [affinePathTime_one]
    have hp := hpay ρ hρ0 hρ1 m
    have hwhole : (1 : ℝ≥0∞) ≤ physicalTollCost d g₁ m Γ.1 :=
      hp.trans (physicalTollCost_affine_le d hU Γ.1 htpos g₁ hg₁ m)
    exact (show ENNReal.ofReal ((1 : ℝ)/2) ≤ 1 by norm_num).trans hwhole

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SafeGateNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact forbidden-hit set has a relatively compact neighborhood that
avoids both the anchor and the closed target gate. The map is only required
to be continuous on the actual domain. -/

open Set Function

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]

theorem exists_safe_gate_neighborhood
    (U E F : Set X) (hU : IsOpen U) (hE : IsClosed E) (hF : IsCompact F)
    (hFU : F ⊆ U) (hEF : Disjoint E F)
    (f : U → Y) (hf : Continuous f) (Q : Set Y) (hQ : IsClosed Q)
    (hFQ : ∀x : U, x.val ∈ F → f x ∉ Q) :
    ∃S : Set X, IsOpen S ∧ F ⊆ S ∧ closure S ⊆ U ∧
      Disjoint E (closure S) ∧ ∀x : U, x.val ∈ closure S → f x ∉ Q := by
  let V : Set X := Subtype.val '' ((f ⁻¹' Qᶜ) ∩ (Subtype.val ⁻¹' Eᶜ))
  have hVo : IsOpen V := hU.isOpenMap_subtype_val _
    ((hQ.isOpen_compl.preimage hf).inter (hE.isOpen_compl.preimage continuous_subtype_val))
  have hFV : F ⊆ V := by
    intro x hx
    refine ⟨⟨x, hFU hx⟩, ?_, rfl⟩
    exact ⟨hFQ _ hx, fun hxE => Set.disjoint_left.mp hEF hxE hx⟩
  obtain ⟨S, hSo, hFS, hSV⟩ := hF.exists_isOpen_closure_subset (hVo.mem_nhdsSet.mpr hFV)
  refine ⟨S, hSo, hFS, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hSV hx
    exact y.property
  · apply Set.disjoint_left.mpr
    intro x hxE hxS
    obtain ⟨y, hy, heq⟩ := hSV hxS
    exact hy.2 (heq.symm ▸ hxE)
  · intro x hx
    obtain ⟨y, hy, heq⟩ := hSV hx
    have hyx : y = x := Subtype.ext heq
    exact hyx ▸ hy.1

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_GeometricGatePenalty
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-gate penalties for a domain map and nested target gates. Compact
separation supplies a penalty region disjoint from the retained compact sets. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_3 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_geometric_gate_penalty
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E H : Set Sphere) (hE : IsClosed E) (k : ℕ) (C : ℕ → Set Sphere)
    (hC : ∀j ≤ k, IsCompact (C j)) (hCU : ∀j ≤ k, C j ⊆ d.quotientDomain)
    (hEC : ∀j ≤ k, Disjoint E (C j))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hg₂ : (∫⁻y, g y ^ 2 ∂sphericalArea) < ∞) (m : Sphere → ℝ≥0∞)
    (hgood : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H →
      (∀j ≤ k, GateRule (C j) (Subtype.val '' (f ⁻¹' W₂)) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1) :
    ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞,
      IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H →
          ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g₁ m Γ.1 := by
  let K : ℕ → Set Sphere := fun _ => Subtype.val '' (f ⁻¹' W₂)
  have hK : ∀j ≤ k, IsOpen (K j) := fun _ _ =>
    hU.isOpenMap_subtype_val _ (hW₂.preimage hf)
  let F := finiteGateForbiddenSet k C K
  have hF : IsCompact F := isCompact_finiteGateForbiddenSet k C K hC hK
  have hFU : F ⊆ d.quotientDomain := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hCU i.val (by omega) hi.1
  have hEF : Disjoint E F := by
    apply Set.disjoint_left.mpr
    intro x hxE hxF
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxF
    exact Set.disjoint_left.mp (hEC i.val (by omega)) hxE hi.1
  have hFQ (x : d.quotientDomain) (hx : x.val ∈ F) : f x ∉ W₁ := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    intro h
    exact hi.2 ⟨x, hW₁₂ h, rfl⟩
  obtain ⟨S, hSo, hFS, hSU, hES, hSW⟩ := exists_safe_gate_neighborhood
    d.quotientDomain E F hU hE hF hFU hEF f hf W₁ hW₁ hFQ
  obtain ⟨O, g₁, hOo, hOS, hg₁, hgg₁, hoff, henergy, hlower⟩ :=
    exists_ungated_half_separation d hU π hπ he ν N E H k C K hC hK S hSo
      (subset_closure.trans hSU) hFS (hES.mono_right subset_closure) g hg hg₂ m hgood
  exact ⟨O, g₁, hOo, hOS.trans (subset_closure.trans hSU),
    hES.mono_right (hOS.trans subset_closure), fun x hx => hSW x (subset_closure (hOS hx)),
    hg₁, hgg₁, hoff, henergy, hlower⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ShrinkingJumpTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square-summable dust tolls are upper semicontinuous in every T1
topology. Consequently, the supremum toll on shrinking jump neighborhoods
has limit superior at most the toll at the limiting dust point. -/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T1Space X]

omit [TopologicalSpace X] [T1Space X] in
theorem finite_toll_superlevel {m : X → ℝ≥0∞} (hm : (∑' x, m x ^ 2) ≠ ∞)
    {a : ℝ≥0∞} (ha : a ≠ 0) : {x | a ≤ m x}.Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm (pow_ne_zero 2 ha)).subset
  intro x hx
  change a ≤ m x at hx
  exact pow_le_pow_left' hx 2

theorem square_summable_toll_upperSemicontinuous {m : X → ℝ≥0∞}
    (hm : (∑' x, m x ^ 2) ≠ ∞) : UpperSemicontinuous m := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a = 0
  · simp [ha]
  · exact (finite_toll_superlevel hm ha).isClosed

omit [T1Space X] in
theorem eventually_neighborhoodTollSup_le {m : X → ℝ≥0∞}
    (hm : UpperSemicontinuous m) {s : X} {U : ℕ → Set X}
    (hU : ∀ V ∈ 𝓝 s, ∀ᶠ j in atTop, U j ⊆ V)
    {a : ℝ≥0∞} (ha : m s < a) :
    ∀ᶠ j in atTop, neighborhoodTollSup m (U j) ≤ a := by
  have hv : {x | m x < a} ∈ 𝓝 s := hm s a ha
  filter_upwards [hU _ hv] with j hj
  exact iSup_le fun x => iSup_le fun hx => (hj hx).le

theorem shrinking_jump_toll_limsup {m : X → ℝ≥0∞}
    (hm : (∑' x, m x ^ 2) ≠ ∞) {s : X} {U : ℕ → Set X}
    (hU : ∀ V ∈ 𝓝 s, ∀ᶠ j in atTop, U j ⊆ V)
    {ρ : ℕ → ℝ≥0∞} (hρ : Tendsto ρ atTop (𝓝 0)) :
    limsup (fun j => max (ρ j) (neighborhoodTollSup m (U j))) atTop ≤ m s := by
  apply le_of_forall_gt
  intro a ha
  obtain ⟨b, hb, hba⟩ := exists_between ha
  have ht := eventually_neighborhoodTollSup_le
    (square_summable_toll_upperSemicontinuous hm) hU hb
  have hr : ∀ᶠ j in atTop, ρ j < b := hρ.eventually (gt_mem_nhds (lt_of_le_of_lt bot_le hb))
  apply lt_of_le_of_lt (limsup_le_of_le (a := b) (h := ?_)) hba
  filter_upwards [ht, hr] with j hj hρj
  exact max_le hρj.le hj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ShrinkingJumpNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric thickenings of shrinking jump disks converge to the containing
dust point, so the abstract toll estimate applies to the actual jump costs. -/

open Set Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem shrinking_thickenings {s : X} {V : ℕ → Set X} {r τ : ℕ → ℝ}
    (hV : ∀ j, V j ⊆ ball s (r j)) (hr : Tendsto r atTop (𝓝 0))
    (hτ : Tendsto τ atTop (𝓝 0)) :
    ∀ W ∈ 𝓝 s, ∀ᶠ j in atTop, thickening (τ j) (V j) ⊆ W := by
  intro W hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
  have hsmall : ∀ᶠ j in atTop, r j + τ j < ε := by
    have hsum : Tendsto (fun j => r j + τ j) atTop (𝓝 0) := by simpa using hr.add hτ
    exact hsum.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with j hj
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  apply hball
  have hy' : dist y s < r j := hV j hy
  change dist x s < ε
  exact (dist_triangle x y s).trans_lt ((add_lt_add hxy hy').trans_eq (add_comm _ _)) |>.trans hj

theorem shrinking_thickening_toll_limsup {m : X → ℝ≥0∞}
    (hm : (∑' x, m x ^ 2) ≠ ∞) {s : X} {V : ℕ → Set X} {r τ : ℕ → ℝ}
    (hV : ∀ j, V j ⊆ ball s (r j)) (hr : Tendsto r atTop (𝓝 0))
    (hτ : Tendsto τ atTop (𝓝 0)) {ρ : ℕ → ℝ≥0∞} (hρ : Tendsto ρ atTop (𝓝 0)) :
    limsup (fun j => max (ρ j) (neighborhoodTollSup m (thickening (τ j) (V j)))) atTop ≤ m s :=
  shrinking_jump_toll_limsup hm (shrinking_thickenings hV hr hτ) hρ

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ChainPotentialBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The topological band of the actual chain potential is controlled by
the dust toll at its center, once the shrinking jump levels are installed. -/

open Set Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem chainPotential_cluster_bound
    (R : X → X → ℝ≥0∞ → Prop) (hR : ∀ x y a, R x y a → R y x a)
    (E G : Set X) {m : X → ℝ≥0∞} (hm : (∑' x, m x ^ 2) ≠ ∞)
    {s : X} {V : ℕ → Set X} (hV : ∀ j, V j ∈ 𝓝 s)
    {r τ : ℕ → ℝ} (hVr : ∀ j, V j ⊆ ball s (r j))
    (hr : Tendsto r atTop (𝓝 0)) (hτ : Tendsto τ atTop (𝓝 0))
    {ρ : ℕ → ℝ≥0∞} (hρ : Tendsto ρ atTop (𝓝 0))
    (hj : ∀ j, ∀ x ∈ G ∩ V j, ∀ y ∈ G ∩ V j,
      R x y (max (ρ j) (neighborhoodTollSup m (thickening (τ j) (V j)))))
    {a b : ℝ} (ha : (s, a) ∈ clusterGraph G (realChainPotential R E))
    (hb : (s, b) ∈ clusterGraph G (realChainPotential R E)) :
    ENNReal.ofReal |a - b| ≤ 4 * m s :=
  (clusterGraph_oscillation_of_jumps R hR E G hV _ hj ha hb).trans
    (mul_le_mul' le_rfl (shrinking_thickening_toll_limsup hm hVr hr hτ hρ))

theorem chainPotential_boundary_band
    (R : X → X → ℝ≥0∞ → Prop) (hR : ∀ x y a, R x y a → R y x a)
    (E G : Set X) {m : X → ℝ≥0∞} (hm : (∑' x, m x ^ 2) ≠ ∞)
    {s : X} (hs : s ∈ closure G) {V : ℕ → Set X} (hV : ∀ j, V j ∈ 𝓝 s)
    {r τ : ℕ → ℝ} (hVr : ∀ j, V j ⊆ ball s (r j))
    (hr : Tendsto r atTop (𝓝 0)) (hτ : Tendsto τ atTop (𝓝 0))
    {ρ : ℕ → ℝ≥0∞} (hρ : Tendsto ρ atTop (𝓝 0))
    (hj : ∀ j, ∀ x ∈ G ∩ V j, ∀ y ∈ G ∩ V j,
      R x y (max (ρ j) (neighborhoodTollSup m (thickening (τ j) (V j))))) :
    ENNReal.ofReal (limsup (realChainPotential R E) (𝓝[G] s) -
      liminf (realChainPotential R E) (𝓝[G] s)) ≤ 4 * m s := by
  let : NeBot (𝓝[G] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  have he : ∀ᶠ x in 𝓝[G] s, 0 ≤ realChainPotential R E x ∧ realChainPotential R E x ≤ 1 :=
    Eventually.of_forall (realChainPotential_mem_Icc R E)
  have hlo := isBoundedUnder_of_eventually_ge (he.mono fun _ h => h.1)
  have hhi := isBoundedUnder_of_eventually_le (he.mono fun _ h => h.2)
  have ha : (s, limsup (realChainPotential R E) (𝓝[G] s)) ∈
      clusterGraph G (realChainPotential R E) :=
    mem_clusterGraph_iff_mapClusterPt.mpr
      (isGreatest_mapClusterPt_limsup hlo.isCoboundedUnder_le hhi).1
  have hb : (s, liminf (realChainPotential R E) (𝓝[G] s)) ∈
      clusterGraph G (realChainPotential R E) :=
    mem_clusterGraph_iff_mapClusterPt.mpr
      (isLeast_mapClusterPt_liminf hhi.isCoboundedUnder_ge hlo).1
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    (chainPotential_cluster_bound R hR E G hm hV hVr hr hτ hρ hj ha hb)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JoinedPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A binary continuous join with exact affine parametrizations of both
halves, for attaching collar tails to retained fragments. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

theorem joinedPath_zero (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) :
    joinedPath γ δ h ⊥ = γ ⊥ := by
  simpa only [affinePathTime_zero] using joinedPath_first γ δ h ⊥

theorem joinedPath_one (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) :
    joinedPath γ δ h ⊤ = δ ⊤ := by
  simpa only [affinePathTime_one] using joinedPath_second γ δ h ⊤

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JoinedPhysicalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary joining preserves finite physical length and adds the exact
physical occupation costs. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem collarRestrictions_cost_sum (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∑'n, ∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ (collarRestrictions e hU y₀ γ n)) =
      ∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ γ :=
  (physicalCost_collarPieces e hU y₀ γ (collarRestrictions e hU y₀ γ)
    (fun _ _ => rfl) g hg).symm

theorem physicalCost_joined (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) (h : γ.val ⊤ = δ.val ⊥)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ (joinedFinitePhysicalPath e hU y₀ γ δ h)) =
      (∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ γ) +
        (∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ δ) := by
  rw [physicalCost_collarPieces e hU y₀ _ (joinedPhysicalPieces e hU y₀ γ δ)
    (joinedPhysicalPieces_match e hU y₀ γ δ h) g hg, tsum_eq_zero_add' ENNReal.summable]
  change (∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ δ) +
    (∑'n, ∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ (collarRestrictions e hU y₀ γ n)) = _
  rw [collarRestrictions_cost_sum e hU y₀ γ g hg, add_comm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JoinedAllowedPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The binary join is allowed, with its tags constructed from one original
path and affine restrictions of the other. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_joined_path
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ Δ : TaggedPhysicalPath d)
    (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2))
    (h : Γ.1.val ⊤ = Δ.1.val ⊥)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃θ : ℕ → TagSlot, AllowedTaggedPath d ν N (joinedPath Γ.1.val Δ.1.val h, θ) := by
  let P : ℕ → TaggedPath X := fun n => match n with
    | 0 => (Δ.1.val, Δ.2)
    | j+1 => affineRestrictedTaggedPath (collarTime (j+1)) (collarTime j) (Γ.1.val, Γ.2)
  have hP (n : ℕ) : AllowedTaggedPath d ν N (P n) := by
    cases n with
    | zero => exact hΔ
    | succ j =>
      exact allowedTaggedPath_affine d hU ν N (Γ.1.val, Γ.2) hΓ hpoint
        (collarTime_strictAnti (Nat.lt_succ_self j))
  have hfinite : physicalDomainLength d.domainEquiv d.basePoint
      (joinedPath Γ.1.val Δ.1.val h) < ∞ :=
    (joinedFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 Δ.1 h).property
  apply exists_allowed_countable_concatenation d ν N _ hfinite
    (fun n => collarTime (n+1)) collarTime
    (fun n => collarTime_strictAnti (Nat.lt_succ_self n))
    collarCell_disjoint_interiors collarCell_complement_countable P hP
  · intro n s _
    cases n with
    | zero =>
      change joinedPath Γ.1.val Δ.1.val h
        (affinePathTime (collarTime 1) (collarTime 0) s) = Δ.1.val s
      rw [collarTime_zero]
      exact joinedPath_second Γ.1.val Δ.1.val h s
    | succ j => exact joinedPath_collar_succ Γ.1.val Δ.1.val h j s
  · exact hpoint

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JoinedPathTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two endpoint tolls remain omitted after joining at a point with
zero dust weight. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem joinedPath_interior_toll (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥)
    (m : X → ℝ≥0∞) (hm : m (γ ⊤) = 0) :
    timeToll (joinedPath γ δ h) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll γ (Ioo (⊥ : PathTime) ⊤) m + timeToll δ (Ioo (⊥ : PathTime) ⊤) m := by
  let c := collarTime 1
  have hmid : joinedPath γ δ h c = γ ⊤ := by
    simpa only [affinePathTime_one] using joinedPath_first γ δ h ⊤
  have hsplit : timeToll (joinedPath γ δ h) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll (joinedPath γ δ h) (Ioo ⊥ c ∪ Ioo c ⊤) m := by
    apply timeToll_eq_of_zero_difference
    · rintro t (ht | ht)
      · exact ⟨ht.1, ht.2.trans_le le_top⟩
      · exact ⟨lt_of_le_of_lt bot_le ht.1, ht.2⟩
    · intro t ht
      have he : t = c := by
        rcases lt_trichotomy t c with hlt | he | hgt
        · exact (ht.2 (Or.inl ⟨ht.1.1, hlt⟩)).elim
        · exact he
        · exact (ht.2 (Or.inr ⟨hgt, ht.1.2⟩)).elim
      rw [he, hmid, hm]
  rw [hsplit, timeToll_union _ _ (by
    apply disjoint_left.mpr
    intro t ht hs
    exact ht.2.not_gt hs.1)]
  congr 1
  · rw [← interiorToll_affine (joinedPath γ δ h) m (collarTime_pos 1)]
    apply timeToll_congr_path
    intro t _
    exact joinedPath_first γ δ h t
  · have hc : c < (⊤ : PathTime) := by
      exact (collarTime_zero ▸ collarTime_strictAnti (by omega : 0 < 1))
    rw [← interiorToll_affine (joinedPath γ δ h) m hc]
    apply timeToll_congr_path
    intro t _
    exact joinedPath_second γ δ h t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_JoinedPhysicalCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact interior cost addition for the allowed binary join. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem interiorPhysicalTollCost_joined (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (γ δ : FinitePhysicalPath d.domainEquiv d.basePoint) (h : γ.val ⊤ = δ.val ⊥)
    (hm : m (γ.val ⊤) = 0) :
    interiorPhysicalTollCost (X := X) (Y := Y) d g m (joinedFinitePhysicalPath d.domainEquiv hU d.basePoint γ δ h) =
      interiorPhysicalTollCost (X := X) (Y := Y) d g m γ + interiorPhysicalTollCost (X := X) (Y := Y) d g m δ := by
  unfold interiorPhysicalTollCost
  rw [physicalCost_joined d.domainEquiv hU d.basePoint γ δ h g hg]
  change _ + timeToll (joinedPath γ.val δ.val h) (Ioo (⊥ : PathTime) ⊤) m = _
  rw [joinedPath_interior_toll γ.val δ.val h m hm]
  ac_rfl


theorem exists_allowed_joined_interior_cost (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ Δ : TaggedPhysicalPath d)
    (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2))
    (h : Γ.1.val ⊤ = Δ.1.val ⊥)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞) (hm : m (Γ.1.val ⊤) = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = Γ.1.val ⊥ ∧ ρ.val ⊤ = Δ.1.val ⊤ ∧
      interiorPhysicalTollCost (X := X) (Y := Y) d g m ρ =
        interiorPhysicalTollCost (X := X) (Y := Y) d g m Γ.1 + interiorPhysicalTollCost (X := X) (Y := Y) d g m Δ.1 := by
  obtain ⟨θ, hθ⟩ := exists_allowed_joined_path d hU ν N Γ Δ hΓ hΔ h hpoint
  exact ⟨joinedFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 Δ.1 h, θ, hθ,
    joinedPath_zero _ _ h, joinedPath_one _ _ h,
    interiorPhysicalTollCost_joined d hU g hg m Γ.1 Δ.1 h hm⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_InteriorPhysicalCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior cost, full fragment cost, and the endpoint convention for a
one-ended path are related without losing or duplicating a dust toll. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] [BorelSpace X] in
theorem interiorPhysicalTollCost_le_full (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (γ : FinitePhysicalPath d.domainEquiv d.basePoint) :
    interiorPhysicalTollCost d g m γ ≤ physicalTollCost d g m γ := by
  unfold interiorPhysicalTollCost physicalTollCost
  apply add_le_add le_rfl
  rw [boundaryToll_eq_timeToll]
  exact timeToll_mono γ.val m (subset_univ _)

omit [MeasurableSpace X] [BorelSpace X] in
theorem interiorPhysicalTollCost_eq_full (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hzero : m (γ.val ⊥) = 0) (hone : m (γ.val ⊤) = 0) :
    interiorPhysicalTollCost (X := X) (Y := Y) d g m γ = physicalTollCost d g m γ := by
  unfold interiorPhysicalTollCost physicalTollCost
  rw [timeToll_eq_interior_of_zero_endpoints γ.val m hzero hone]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)] in
theorem preterminalToll_eq_interior_of_initial_zero
    (γ : C(PathTime, X)) (m : X → ℝ≥0∞) (hzero : m (γ ⊥) = 0) :
    preterminalToll γ m = timeToll γ (Ioo (⊥ : PathTime) ⊤) m := by
  rw [preterminalToll_eq_timeToll]
  apply timeToll_eq_of_zero_difference
  · exact fun _ h => h.2
  · intro t ht
    have he : t = ⊥ := by
      by_contra hn
      exact ht.2 ⟨bot_lt_iff_ne_bot.mpr hn, ht.1⟩
    exact he ▸ hzero

omit [MeasurableSpace X] [BorelSpace X] in
theorem interiorPhysicalTollCost_reversed (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (γ : FinitePhysicalPath d.domainEquiv d.basePoint) :
    interiorPhysicalTollCost (X := X) (Y := Y) d g m (reversedFinitePhysicalPath d.domainEquiv d.basePoint γ) =
      interiorPhysicalTollCost (X := X) (Y := Y) d g m γ := by
  unfold interiorPhysicalTollCost
  rw [dyadicPhysicalOccupation_reversed]
  exact congrArg _ (interiorToll_reversed γ.val m)


omit [BorelSpace X] in
theorem exists_allowed_reversed_interior_cost
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = Γ.1.val ⊤ ∧ ρ.val ⊤ = Γ.1.val ⊥ ∧
      interiorPhysicalTollCost (X := X) (Y := Y) d g m ρ = interiorPhysicalTollCost (X := X) (Y := Y) d g m Γ.1 := by
  refine ⟨reversedFinitePhysicalPath d.domainEquiv d.basePoint Γ.1,
    fun k => reversedTag (Γ.2 k), ?_, ?_, ?_, ?_⟩
  · exact allowedTaggedPath_reversed d ν N (Γ.1.val, Γ.2) hΓ hpoint
  · exact reversedPath_zero Γ.1.val
  · exact reversedPath_one Γ.1.val
  · exact interiorPhysicalTollCost_reversed d g m Γ.1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_JoinedJunctionCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joining at a dust point incurs exactly one junction toll. This is
the accounting used to replace collapsing jumps by actual paths. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem joinedPath_interior_toll_with_junction
    (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) (m : X → ℝ≥0∞) :
    timeToll (joinedPath γ δ h) (Ioo (⊥ : PathTime) ⊤) m =
      timeToll γ (Ioo (⊥ : PathTime) ⊤) m +
        timeToll δ (Ioo (⊥ : PathTime) ⊤) m + m (γ ⊤) := by
  let c := collarTime 1
  have hc0 : (⊥ : PathTime) < c := collarTime_pos 1
  have hc1 : c < (⊤ : PathTime) :=
    collarTime_zero ▸ collarTime_strictAnti (by omega : 0 < 1)
  have hmid : joinedPath γ δ h c = γ ⊤ := by
    simpa only [affinePathTime_one] using joinedPath_first γ δ h ⊤
  have hset : Ioo (⊥ : PathTime) ⊤ = (Ioo ⊥ c ∪ Ioo c ⊤) ∪ {c} := by
    ext t
    constructor
    · intro ht
      rcases lt_trichotomy t c with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨ht.1, hlt⟩)
      · exact Or.inr heq
      · exact Or.inl (Or.inr ⟨hgt, ht.2⟩)
    · rintro ((ht | ht) | ht)
      · exact ⟨ht.1, ht.2.trans hc1⟩
      · exact ⟨hc0.trans ht.1, ht.2⟩
      · exact ht.symm ▸ ⟨hc0, hc1⟩
  have hd : Disjoint (Ioo (⊥ : PathTime) c) (Ioo c ⊤) := by
    apply disjoint_left.mpr
    intro t ht hs
    exact ht.2.not_gt hs.1
  have hdc : Disjoint (Ioo (⊥ : PathTime) c ∪ Ioo c ⊤) {c} := by
    apply disjoint_singleton_right.mpr
    simp
  have hsingle : timeToll (joinedPath γ δ h) {c} m = m (γ ⊤) := by
    rw [timeToll_eq_indicator]
    simp [hmid]
  conv_lhs => rw [hset]
  rw [timeToll_union _ _ hdc, timeToll_union _ _ hd, hsingle]
  congr 1
  congr 1
  · rw [← interiorToll_affine (joinedPath γ δ h) m hc0]
    exact timeToll_congr_path m (fun t _ => joinedPath_first γ δ h t)
  · rw [← interiorToll_affine (joinedPath γ δ h) m hc1]
    exact timeToll_congr_path m (fun t _ => joinedPath_second γ δ h t)

variable {Y : Type*} [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem interiorPhysicalTollCost_joined_with_junction (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (γ δ : FinitePhysicalPath d.domainEquiv d.basePoint) (h : γ.val ⊤ = δ.val ⊥) :
    interiorPhysicalTollCost d g m (joinedFinitePhysicalPath d.domainEquiv hU d.basePoint γ δ h) =
      interiorPhysicalTollCost d g m γ + interiorPhysicalTollCost d g m δ + m (γ.val ⊤) := by
  unfold interiorPhysicalTollCost
  rw [physicalCost_joined d.domainEquiv hU d.basePoint γ δ h g hg]
  change _ + timeToll (joinedPath γ.val δ.val h) (Ioo (⊥ : PathTime) ⊤) m = _
  rw [joinedPath_interior_toll_with_junction γ.val δ.val h m]
  ac_rfl

theorem exists_allowed_joined_junction_cost (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ Δ : TaggedPhysicalPath d)
    (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2))
    (h : Γ.1.val ⊤ = Δ.1.val ⊥)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = Γ.1.val ⊥ ∧ ρ.val ⊤ = Δ.1.val ⊤ ∧
      interiorPhysicalTollCost d g m ρ =
        interiorPhysicalTollCost d g m Γ.1 + interiorPhysicalTollCost d g m Δ.1 + m (Γ.1.val ⊤) := by
  obtain ⟨θ, hθ⟩ := exists_allowed_joined_path d hU ν N Γ Δ hΓ hΔ h hpoint
  exact ⟨joinedFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 Δ.1 h, θ, hθ,
    joinedPath_zero _ _ h, joinedPath_one _ _ h,
    interiorPhysicalTollCost_joined_with_junction d hU g hg m Γ.1 Δ.1 h⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_JoinedDomainCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Join two allowed true pieces at a domain point, retaining their
full costs. This is the normalization step between successive jumps. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_joined_full_cost
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (Γ Δ : TaggedPhysicalPath d)
    (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2))
    (hΓ0 : Γ.1.val ⊥ ∈ d.quotientDomain) (hΓ1 : Γ.1.val ⊤ ∈ d.quotientDomain)
    (hΔ1 : Δ.1.val ⊤ ∈ d.quotientDomain) (hjoin : Γ.1.val ⊤ = Δ.1.val ⊥)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ = Γ.1.val ⊥ ∧ ρ.1.val ⊤ = Δ.1.val ⊤ ∧
      physicalTollCost d g m ρ.1 = physicalTollCost d g m Γ.1 + physicalTollCost d g m Δ.1 := by
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_joined_junction_cost
    d hU ν N Γ Δ hΓ hΔ hjoin g hg m hpoint
  refine ⟨(ρ, θ), hρ, hρ0, hρ1, ?_⟩
  rw [← interiorPhysicalTollCost_eq_full d g m ρ (hm _ (hρ0.symm ▸ hΓ0))
    (hm _ (hρ1.symm ▸ hΔ1)), hc, hm _ hΓ1, add_zero,
    interiorPhysicalTollCost_eq_full d g m Γ.1 (hm _ hΓ0) (hm _ hΓ1),
    interiorPhysicalTollCost_eq_full d g m Δ.1 (hm _ (hjoin ▸ hΓ1)) (hm _ hΔ1)]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PaidBlockAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reconnect finitely many approximating true blocks using unchanged
old jump edges. The block endpoints may vary within each old jump disk. -/

open Set
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

theorem exists_paid_chain_from_approximate_blocks
    (R : X → X → ℝ≥0∞ → Prop) (n : ℕ)
    (E : Fin (n+2) → Set X) (A : Fin (n+1) → ℝ≥0∞) (J : Fin n → ℝ≥0∞)
    (hjump : ∀i : Fin n, ∀x ∈ E i.succ.castSucc, ∀y ∈ E i.succ.castSucc, R x y (J i))
    (hblock : ∀i : Fin (n+1), ∀ε : ℝ, 0 < ε →
      ∃x ∈ E i.castSucc, ∃y ∈ E i.succ, ∃c : ℝ≥0∞,
        PaidChain R x y c ∧ c ≤ A i + ENNReal.ofReal ε)
    {η : ℝ} (hη : 0 < η) :
    ∃x ∈ E 0, ∃y ∈ E (Fin.last (n+1)), ∃c : ℝ≥0∞,
      PaidChain R x y c ∧ c ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  induction n generalizing η with
  | zero =>
      obtain ⟨x, hx, y, hy, c, hc, hcost⟩ := hblock 0 η hη
      exact ⟨x, hx, y, hy, c, hc, by simpa using hcost⟩
  | succ n ih =>
      have hh : 0 < η/2 := by positivity
      let E' : Fin (n+2) → Set X := fun i => E i.castSucc
      let A' : Fin (n+1) → ℝ≥0∞ := fun i => A i.castSucc
      let J' : Fin n → ℝ≥0∞ := fun i => J i.castSucc
      have hj' (i : Fin n) (x : X) (hx : x ∈ E' i.succ.castSucc)
          (y : X) (hy : y ∈ E' i.succ.castSucc) : R x y (J' i) :=
        hjump i.castSucc x hx y hy
      have hb' (i : Fin (n+1)) (ε : ℝ) (hε : 0 < ε) :
          ∃x ∈ E' i.castSucc, ∃y ∈ E' i.succ, ∃c : ℝ≥0∞,
            PaidChain R x y c ∧ c ≤ A' i + ENNReal.ofReal ε :=
        hblock i.castSucc ε hε
      obtain ⟨x, hx, z, hz, a, hα, hαc⟩ := ih E' A' J' hj' hb' hh
      obtain ⟨z', hz', y, hy, b, hβ, hβc⟩ := hblock (Fin.last (n+1)) (η/2) hh
      have hbridge := hjump (Fin.last n) z hz z' hz'
      refine ⟨x, hx, y, hy, (a + J (Fin.last n)) + b,
        (hα.append (PaidChain.single hbridge)).append hβ, ?_⟩
      have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add hh.le hh.le]
        congr 1
        ring
      have hsA := Fin.sum_univ_castSucc A
      have hsJ := Fin.sum_univ_castSucc J
      calc
        a + J (Fin.last n) + b ≤
            ((∑i, A' i) + (∑i, J' i) + ENNReal.ofReal (η/2)) + J (Fin.last n) +
              (A (Fin.last (n+1)) + ENNReal.ofReal (η/2)) :=
          add_le_add (add_le_add hαc le_rfl) hβc
        _ = (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
          rw [hsA, hsJ, ← herr]
          dsimp [A', J']
          ac_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PositiveJumpCount
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite cost and a positive floor bound the number of jumps.
This supplies the finite pattern extraction in jump-level removal. -/

open Set
open scoped ENNReal

namespace CircleDomainRigidity

theorem exists_uniform_jump_count_bound
    {δ : ℝ} (hδ : 0 < δ) {M : ℝ≥0∞} (hM : M < ∞) :
    ∃N : ℕ, ∀n : ℕ, ∀c : Fin n → ℝ≥0∞,
      (∀i, ENNReal.ofReal δ ≤ c i) → (∑i, c i) ≤ M → n ≤ N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (M.toReal / δ)
  refine ⟨N, fun n c hc hsum => ?_⟩
  have hfloor : (n : ℝ≥0∞) * ENNReal.ofReal δ ≤ M := by
    calc
      (n : ℝ≥0∞) * ENNReal.ofReal δ = ∑_i : Fin n, ENNReal.ofReal δ := by simp
      _ ≤ ∑i, c i := Finset.sum_le_sum (fun i _ => hc i)
      _ ≤ M := hsum
  have hreal : (n : ℝ) * δ ≤ M.toReal := by
    have h := ENNReal.toReal_mono hM.ne hfloor
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le] using h
  have hn : (n : ℝ) < N := (le_div_iff₀ hδ).mpr hreal |>.trans_lt hN
  exact (Nat.cast_lt.mp hn).le

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteJumpPattern
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded number of jumps and finite set of old disk labels admit
a subsequence with one fixed pattern. New disk labels are not frozen. -/

open Set Function Filter

namespace CircleDomainRigidity

theorem exists_constant_finite_pattern_subsequence
    {I : Type*} [Finite I] (f : ℕ → I) :
    ∃p : I, ∃s : ℕ → ℕ, StrictMono s ∧ ∀k, f (s k) = p := by
  obtain ⟨p, hp⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {p}).Infinite := infinite_coe_iff.mp hp
  obtain ⟨s, hs, heq⟩ := Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨k, hk, hNk⟩ := hinf.exists_gt N
    exact ⟨k, hNk, hk⟩)
  exact ⟨p, s, hs, heq⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AnchorTruncation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Truncation at a domain point of an anchor preserves the interior cost
budget, so an omitted dust endpoint is never charged during attachment. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

private theorem exists_domain_time_inside_anchor
    (γ : C(PathTime, X)) {U A : Set X} (hU : IsOpen U)
    (hfront : frontier A ⊆ U) (hstart : γ ⊥ ∈ interior A)
    (hend : γ ⊤ ∉ interior A) :
    ∃t : PathTime, t < ⊤ ∧ γ t ∈ interior A ∩ U := by
  let s := firstExitTime γ (interior A)
  have hspos : ⊥ < s := firstExit_pos γ isOpen_interior hstart hend
  have hsU : γ s ∈ U :=
    hfront (frontier_interior_subset (firstExit_frontier γ isOpen_interior hstart hend))
  have hscl : s ∈ closure (Iio s) := by
    rw [closure_Iio' ⟨⊥, hspos⟩]
    exact (le_rfl : s ≤ s)
  obtain ⟨t, htU, hts⟩ := mem_closure_iff.mp hscl (γ ⁻¹' U)
    (hU.preimage γ.continuous) hsU
  exact ⟨t, hts.trans_le le_top, mem_before_firstExit γ (interior A) hts, htU⟩

variable {Y : Type*} [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem interiorPhysicalTollCost_affine_le
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞) :
    interiorPhysicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hab) ≤
      interiorPhysicalTollCost d g m γ := by
  unfold interiorPhysicalTollCost
  rw [physicalCost_affine d.domainEquiv hU d.basePoint γ hab g hg,
    physicalOccupation_integral d.domainEquiv hU d.basePoint γ g hg]
  change _ + timeToll (affineRestrictedPath a b γ.val) (Ioo ⊥ ⊤) m ≤ _
  rw [interiorToll_affine γ.val m hab]
  apply add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl)
  apply timeToll_mono
  intro t ht
  exact ⟨bot_le.trans_lt ht.1, ht.2.trans_le le_top⟩

theorem exists_allowed_suffix_from_anchor
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    {A : Set X} (hfront : frontier A ⊆ d.quotientDomain)
    (hstart : Γ.1.val ⊥ ∈ interior A) (hend : Γ.1.val ⊤ ∉ interior A)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ ∈ interior A ∩ d.quotientDomain ∧ ρ.1.val ⊤ = Γ.1.val ⊤ ∧
      interiorPhysicalTollCost d g m ρ.1 ≤ interiorPhysicalTollCost d g m Γ.1 := by
  obtain ⟨t, ht, htm⟩ := exists_domain_time_inside_anchor Γ.1.val hU hfront hstart hend
  let ρ := restrictTaggedPhysicalPath d hU Γ ht
  refine ⟨ρ, restrictTaggedPhysicalPath_allowed d hU ν N Γ hΓ hpoint ht, ?_, ?_, ?_⟩
  · exact (restrictTaggedPhysicalPath_zero d hU Γ ht).symm ▸ htm
  · exact restrictTaggedPhysicalPath_one d hU Γ ht
  · exact interiorPhysicalTollCost_affine_le d hU Γ.1 ht g hg m

theorem exists_allowed_prefix_to_anchor
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    {A : Set X} (hfront : frontier A ⊆ d.quotientDomain)
    (hstart : Γ.1.val ⊥ ∉ interior A) (hend : Γ.1.val ⊤ ∈ interior A)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ = Γ.1.val ⊥ ∧ ρ.1.val ⊤ ∈ interior A ∩ d.quotientDomain ∧
      interiorPhysicalTollCost d g m ρ.1 ≤ interiorPhysicalTollCost d g m Γ.1 := by
  obtain ⟨t, ht, htm⟩ := exists_domain_time_inside_anchor (reversedPath Γ.1.val) hU hfront
    (by simpa only [reversedPath_zero] using hend)
    (by simpa only [reversedPath_one] using hstart)
  have hcut : (⊥ : PathTime) < unitInterval.symm t := by
    have h : unitInterval.symm (1 : PathTime) < unitInterval.symm t :=
      unitInterval.symm_lt_symm.mpr ht
    rw [unitInterval.symm_one] at h
    exact h
  let ρ := restrictTaggedPhysicalPath d hU Γ hcut
  refine ⟨ρ, restrictTaggedPhysicalPath_allowed d hU ν N Γ hΓ hpoint hcut, ?_, ?_, ?_⟩
  · exact restrictTaggedPhysicalPath_zero d hU Γ hcut
  · exact (restrictTaggedPhysicalPath_one d hU Γ hcut).symm ▸ htm
  · exact interiorPhysicalTollCost_affine_le d hU Γ.1 hcut g hg m

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_SmallWeightedArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute continuity of finite weighted arclength gives arbitrarily
cheap short parameter arcs through every point, including density singularities. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_small_time_interval (μ : Measure PathTime) [IsFiniteMeasure μ]
    [NullSingletonClass μ] (r : PathTime) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s t : PathTime, dist s r < δ → dist t r < δ →
      μ (Icc (min s t) (max s t)) < ε := by
  obtain ⟨V, hrV, hV, hμV⟩ := Set.exists_isOpen_lt_of_lt (μ := μ) {r} ε (by simpa using hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hrV (mem_singleton r)))
  refine ⟨δ, hδ, fun s t hs ht => (measure_mono ?_).trans_lt hμV⟩
  intro u hu
  apply hball
  change |(u : ℝ) - r| < δ
  change |(s : ℝ) - r| < δ at hs
  change |(t : ℝ) - r| < δ at ht
  rw [abs_lt] at hs ht ⊢
  have hlo : (r : ℝ) - δ < min (s : ℝ) t := lt_min (by linarith [hs.1]) (by linarith [ht.1])
  have hhi : max (s : ℝ) t < (r : ℝ) + δ := max_lt (by linarith [hs.2]) (by linarith [ht.2])
  change min (s : ℝ) t ≤ (u : ℝ) ∧ (u : ℝ) ≤ max (s : ℝ) t at hu
  constructor <;> linarith

variable {X : Type*} [MetricSpace X]

theorem exists_small_weighted_arcs (γ : RectifiablePath X) (g : X → ℝ≥0∞)
    (hfinite : (∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ) < ∞)
    (r : PathTime) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s t : PathTime, dist s r < δ → dist t r < δ →
      (∫⁻ v in Icc (min s t) (max s t), g (γ.val v) ∂pathLengthMeasure γ) < ε := by
  let μ := (pathLengthMeasure γ).withDensity (fun t => g (γ.val t))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity hfinite.ne
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_time_interval μ r hε
  refine ⟨δ, hδ, fun s t hs ht => ?_⟩
  simpa only [μ, withDensity_apply _ measurableSet_Icc] using hsmall s t hs ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RectifiableSubarcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual short rectifiable arcs between nearby parameters of a
finite-cost curve, with either orientation. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem pathOccupation_affine (γ : RectifiablePath X) {a b : PathTime} (hab : a < b) :
    pathOccupation (affineRectifiablePath γ hab) =
      ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val := by
  rw [pathOccupation, pathLengthMeasure_affine]
  change (((pathLengthMeasure γ).restrict (Icc a b)).map (rescalePathTime a b)).map
    (affineRestrictedPath a b γ.val) = _
  rw [Measure.map_map (affineRestrictedPath a b γ.val).continuous.measurable
    (rescalePathTime a b).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change γ.val (affinePathTime a b (rescalePathTime a b t)) = γ.val t
  rw [affine_rescalePathTime hab ht]

theorem pathCost_affine (γ : RectifiablePath X) {a b : PathTime} (hab : a < b)
    (g : X → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂pathOccupation (affineRectifiablePath γ hab)) =
      ∫⁻ t in Icc a b, g (γ.val t) ∂pathLengthMeasure γ := by
  rw [pathOccupation_affine γ hab]
  exact lintegral_map hg γ.val.continuous.measurable

theorem pathOccupation_constant (x : X) : pathOccupation (constantRectifiablePath x) = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [pathOccupation_univ]
  exact (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _

theorem exists_rectifiable_subarc (γ : RectifiablePath X) (a b : PathTime)
    (g : X → ℝ≥0∞) (hg : Measurable g) :
    ∃ ρ : RectifiablePath X, ρ.val ⊥ = γ.val a ∧ ρ.val ⊤ = γ.val b ∧
      range ρ.val ⊆ γ.val '' Icc (min a b) (max a b) ∧
      (∫⁻ x, g x ∂pathOccupation ρ) =
        ∫⁻ t in Icc (min a b) (max a b), g (γ.val t) ∂pathLengthMeasure γ := by
  have hforward {s t : PathTime} (hst : s < t) :
      ∃ ρ : RectifiablePath X, ρ.val ⊥ = γ.val s ∧ ρ.val ⊤ = γ.val t ∧
        range ρ.val ⊆ γ.val '' Icc s t ∧
        (∫⁻ x, g x ∂pathOccupation ρ) =
          ∫⁻ u in Icc s t, g (γ.val u) ∂pathLengthMeasure γ := by
    refine ⟨affineRectifiablePath γ hst, ?_, ?_, ?_, pathCost_affine γ hst g hg⟩
    · exact congrArg γ.val (affinePathTime_zero s t)
    · exact congrArg γ.val (affinePathTime_one s t)
    · rintro x ⟨u, rfl⟩
      exact ⟨affinePathTime s t u, affinePathTime_mem_Icc hst.le u, rfl⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · simpa only [min_eq_left hab.le, max_eq_right hab.le] using hforward hab
  · refine ⟨constantRectifiablePath (γ.val a), rfl, rfl, ?_, ?_⟩
    · rintro x ⟨u, rfl⟩
      exact ⟨a, by simp, rfl⟩
    · simp only [pathOccupation_constant, lintegral_zero_measure, min_self, max_self, Icc_self,
        Measure.restrict_singleton, measure_singleton, zero_smul]
  · obtain ⟨ρ, hρ0, hρ1, hρrange, hρcost⟩ := hforward hba
    refine ⟨reversedRectifiablePath ρ, ?_, ?_, ?_, ?_⟩
    · exact (reversedPath_zero ρ.val).trans hρ1
    · exact (reversedPath_one ρ.val).trans hρ0
    · rintro x ⟨u, rfl⟩
      change ρ.val (unitInterval.symm u) ∈ γ.val '' Icc (min a b) (max a b)
      simpa only [min_eq_right hba.le, max_eq_left hba.le] using
        hρrange (mem_range_self (unitInterval.symm u))
    · simpa only [pathOccupation_reversed, min_eq_right hba.le, max_eq_left hba.le] using hρcost

theorem exists_small_rectifiable_subarcs (γ : RectifiablePath X) (g : X → ℝ≥0∞)
    (hg : Measurable g) (hfinite : (∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ) < ∞)
    (r : PathTime) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : PathTime, dist a r < δ → dist b r < δ →
      ∃ ρ : RectifiablePath X, ρ.val ⊥ = γ.val a ∧ ρ.val ⊤ = γ.val b ∧
        range ρ.val ⊆ range γ.val ∧ (∫⁻ x, g x ∂pathOccupation ρ) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_weighted_arcs γ g hfinite r hε
  refine ⟨δ, hδ, fun a b ha hb => ?_⟩
  obtain ⟨ρ, hρa, hρb, hρrange, hρcost⟩ := exists_rectifiable_subarc γ a b g hg
  refine ⟨ρ, hρa, hρb, hρrange.trans (image_subset_range _ _), ?_⟩
  rw [hρcost]
  exact hsmall a b ha hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConstantPhysicalPath
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A constant path at a domain point is allowed and has zero cost. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_constant_physical_path
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    {x : X} (hx : x ∈ d.quotientDomain) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hm : m x = 0) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ (∀t, ρ.val t = x) ∧
      physicalTollCost d g m ρ = 0 := by
  let y := d.domainEquiv.symm ⟨x, hx⟩
  let β := constantRectifiablePath y.val
  have hβ (t : PathTime) : β.val t ∈ d.physicalDomain := y.property
  let γ := projectDomainPath d.domainEquiv β.val hβ
  have hγ (t : PathTime) : γ t = x := by
    change (d.domainEquiv y).val = x
    exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨x, hx⟩)
  have hlen : physicalDomainLength d.domainEquiv d.basePoint γ = 0 := by
    rw [physicalDomainLength_project d.domainEquiv d.basePoint β hβ]
    exact (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _
  let ρ : FinitePhysicalPath d.domainEquiv d.basePoint := ⟨γ, by rw [hlen]; exact ENNReal.zero_lt_top⟩
  have hocc : dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    rw [dyadicPhysicalOccupation_univ]
    exact hlen
  refine ⟨ρ, fun _ => inactiveTag,
    projected_physical_path_allowed d hdisj ν N β hβ, hγ, ?_⟩
  unfold physicalTollCost
  rw [hocc, lintegral_zero_measure, zero_add]
  change (∑'t : PathTime, m (γ t)) = 0
  simp only [hγ, hm, tsum_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AnchorTailAttachment
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attach the two outer ends of a limiting block. An anchor containing
the limiting junction is handled by truncation or a common domain point. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_anchor_tail_attachment
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust) (hdense : Dense d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (F H : Set X) (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (p : X) (L R J : ℝ≥0∞) (hpaid : m p ≤ J)
    (hleft : p ∈ interior F ∨
      ∃ (α : FinitePhysicalPath d.domainEquiv d.basePoint) (θα : ℕ → TagSlot),
        AllowedTaggedPath d ν N (α.val, θα) ∧ α.val ⊥ ∈ F ∩ d.quotientDomain ∧
        α.val ⊤ = p ∧ interiorPhysicalTollCost d g m α ≤ L)
    (hright : p ∈ interior H ∨
      ∃ (β : FinitePhysicalPath d.domainEquiv d.basePoint) (θβ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (β.val, θβ) ∧ β.val ⊥ ∈ H ∩ d.quotientDomain ∧
        β.val ⊤ = p ∧ interiorPhysicalTollCost d g m β ≤ R) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧
      ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧
      physicalTollCost d g m ρ ≤ L + R + J := by
  classical
  have hL : L ≤ L + R + J := le_add_right (le_add_right le_rfl)
  have hR : R ≤ L + R + J := le_add_right (le_add_left le_rfl)
  have finish (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot)
      (hρ : AllowedTaggedPath d ν N (ρ.val, θ))
      (hρ0 : ρ.val ⊥ ∈ F ∩ d.quotientDomain) (hρ1 : ρ.val ⊤ ∈ H ∩ d.quotientDomain)
      (hc : interiorPhysicalTollCost d g m ρ ≤ L + R + J) :
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧
        ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧ physicalTollCost d g m ρ ≤ L + R + J := by
    refine ⟨ρ, θ, hρ, hρ0, hρ1, ?_⟩
    rw [← interiorPhysicalTollCost_eq_full d g m ρ (hm _ hρ0.2) (hm _ hρ1.2)]
    exact hc
  have constant (x : X) (hxF : x ∈ F ∩ d.quotientDomain) (hxH : x ∈ H) :
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧
        ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧ physicalTollCost d g m ρ ≤ L + R + J := by
    obtain ⟨ρ, θ, hρ, heq, hc⟩ := exists_allowed_constant_physical_path d hdisj ν N hxF.2
      g m (hm _ hxF.2)
    exact ⟨ρ, θ, hρ, (heq ⊥).symm ▸ hxF, (heq ⊤).symm ▸ ⟨hxH, hxF.2⟩,
      hc.le.trans bot_le⟩
  rcases hleft with hpF | ⟨α, θα, hα, hα0, hα1, hαc⟩
  · rcases hright with hpH | ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩
    · obtain ⟨x, hxU, hxF, hxH⟩ := hdense.exists_mem_open (isOpen_interior.inter isOpen_interior)
        ⟨p, hpF, hpH⟩
      exact constant x ⟨interior_subset hxF, hxU⟩ (interior_subset hxH)
    · by_cases hstart : β.val ⊥ ∈ interior F
      · exact constant (β.val ⊥) ⟨interior_subset hstart, hβ0.2⟩ hβ0.1
      · obtain ⟨σ, hσ, hσ0, hσ1, hσc⟩ := exists_allowed_prefix_to_anchor
          d hU ν N (β, θβ) hβ hF hstart (hβ1.symm ▸ hpF) g hg m hpoint
        obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ :=
          exists_allowed_reversed_interior_cost d ν N σ hσ g m hpoint
        exact finish ρ θ hρ (hρ0.symm ▸ ⟨interior_subset hσ1.1, hσ1.2⟩)
          (hρ1.symm ▸ hσ0.symm ▸ hβ0) (hc.le.trans (hσc.trans (hβc.trans hR)))
  · rcases hright with hpH | ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩
    · by_cases hstart : α.val ⊥ ∈ interior H
      · exact constant (α.val ⊥) hα0 (interior_subset hstart)
      · obtain ⟨ρ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_prefix_to_anchor
          d hU ν N (α, θα) hα hH hstart (hα1.symm ▸ hpH) g hg m hpoint
        exact finish ρ.1 ρ.2 hρ (hρ0.symm ▸ hα0) ⟨interior_subset hρ1.1, hρ1.2⟩
          (hc.trans (hαc.trans hL))
    · obtain ⟨βr, θr, hβr, hβr0, hβr1, hβrc⟩ :=
        exists_allowed_reversed_interior_cost d ν N (β, θβ) hβ g m hpoint
      obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_joined_junction_cost
        d hU ν N (α, θα) (βr, θr) hα hβr (hα1.trans (hβ1.symm.trans hβr0.symm))
        g hg m hpoint
      apply finish ρ θ hρ (hρ0.symm ▸ hα0) (hρ1.symm ▸ hβr1.symm ▸ hβ0)
      rw [hc, hβrc, hα1]
      exact add_le_add (add_le_add hαc hβc) hpaid

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AnchoredJunctionChain
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In a chain of limiting junctions an equal consecutive pair requires
no extra path or pause. Only distinct pairs are connected, and every
actually used junction is paid once. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_anchored_junction_prefix
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (F : Set X) (hfront : frontier F ⊆ d.quotientDomain) (n : ℕ) (p : Fin (n+1) → X)
    (A : Fin (n+1) → ℝ≥0∞) (J : Fin n → ℝ≥0∞)
    (hpaid : ∀i : Fin n, m (p i.castSucc) ≤ J i)
    (hfirst : p 0 ∈ interior F ∨ ∀ε : ℝ, 0 < ε →
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ = p 0 ∧
        interiorPhysicalTollCost d g m ρ ≤ A 0 + ENNReal.ofReal ε)
    (hstep : ∀i : Fin n, p i.castSucc ≠ p i.succ → ∀ε : ℝ, 0 < ε →
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧
        ρ.val ⊥ = p i.castSucc ∧ ρ.val ⊤ = p i.succ ∧
        interiorPhysicalTollCost d g m ρ ≤ A i.succ + ENNReal.ofReal ε)
    {η : ℝ} (hη : 0 < η) :
    p (Fin.last n) ∈ interior F ∨
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ = p (Fin.last n) ∧
      interiorPhysicalTollCost d g m ρ ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  classical
  induction n generalizing η with
  | zero =>
      rcases hfirst with hin | hfirst
      · exact Or.inl hin
      · obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := hfirst η hη
        exact Or.inr ⟨ρ, θ, hρ, hρ0, hρ1, by simpa using hc⟩
  | succ n ih =>
      have hh : 0 < η/2 := by positivity
      let p' : Fin (n+1) → X := fun i => p i.castSucc
      let A' : Fin (n+1) → ℝ≥0∞ := fun i => A i.castSucc
      let J' : Fin n → ℝ≥0∞ := fun i => J i.castSucc
      have hp' (i : Fin n) : m (p' i.castSucc) ≤ J' i := hpaid i.castSucc
      have hf' : p' 0 ∈ interior F ∨ ∀ε : ℝ, 0 < ε →
          ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
            AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ = p' 0 ∧
            interiorPhysicalTollCost d g m ρ ≤ A' 0 + ENNReal.ofReal ε := hfirst
      have hs' (i : Fin n) (hne : p' i.castSucc ≠ p' i.succ) (ε : ℝ) (hε : 0 < ε) :
          ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
            AllowedTaggedPath d ν N (ρ.val, θ) ∧
            ρ.val ⊥ = p' i.castSucc ∧ ρ.val ⊤ = p' i.succ ∧
            interiorPhysicalTollCost d g m ρ ≤ A' i.succ + ENNReal.ofReal ε :=
        hstep i.castSucc hne ε hε
      rcases ih p' A' J' hp' hf' hs' hh with hin | ⟨α, θα, hα, hα0, hα1, hαc⟩
      · by_cases hn : p (Fin.last (n+1)) ∈ interior F
        · exact Or.inl hn
        · right
          have hne : p (Fin.last n).castSucc ≠ p (Fin.last (n+1)) := by
            intro heq
            exact hn (heq ▸ hin)
          obtain ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩ := hstep (Fin.last n) hne η hη
          obtain ⟨ρ, hρ, hρ0, hρ1, hρc⟩ := exists_allowed_suffix_from_anchor
            d hU ν N (β, θβ) hβ hfront (hβ0.symm ▸ hin) (hβ1.symm ▸ hn)
            g hg m hpoint
          refine ⟨ρ.1, ρ.2, hρ, ⟨interior_subset hρ0.1, hρ0.2⟩, hρ1.trans hβ1, ?_⟩
          have hA : A (Fin.last (n+1)) ≤ ∑i, A i :=
            Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ _)
          exact (hρc.trans hβc).trans (add_le_add (le_add_right hA) le_rfl)
      · right
        have hsA := Fin.sum_univ_castSucc A
        have hsJ := Fin.sum_univ_castSucc J
        by_cases heq : p (Fin.last n).castSucc = p (Fin.last (n+1))
        · refine ⟨α, θα, hα, hα0, hα1.trans heq, ?_⟩
          have he : ENNReal.ofReal (η/2) ≤ ENNReal.ofReal η :=
            ENNReal.ofReal_le_ofReal (by linarith)
          calc
            interiorPhysicalTollCost d g m α ≤ (∑i, A' i) + (∑i, J' i) + ENNReal.ofReal η :=
              hαc.trans (add_le_add le_rfl he)
            _ ≤ ((∑i, A' i) + A (Fin.last (n+1))) +
                ((∑i, J' i) + J (Fin.last n)) + ENNReal.ofReal η :=
              add_le_add (add_le_add (le_add_right le_rfl) (le_add_right le_rfl)) le_rfl
            _ = (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
              rw [hsA, hsJ]
        · obtain ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩ := hstep (Fin.last n) heq (η/2) hh
          obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_joined_junction_cost
            d hU ν N (α, θα) (β, θβ) hα hβ (hα1.trans hβ0.symm) g hg m hpoint
          refine ⟨ρ, θ, hρ, hρ0.symm ▸ hα0, hρ1.trans hβ1, ?_⟩
          have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
            rw [← ENNReal.ofReal_add hh.le hh.le]
            congr 1
            ring
          calc
            interiorPhysicalTollCost d g m ρ =
                interiorPhysicalTollCost d g m α + interiorPhysicalTollCost d g m β + m (p' (Fin.last n)) := by
              rw [hc, hα1]
            _ ≤ ((∑i, A' i) + (∑i, J' i) + ENNReal.ofReal (η/2)) +
                (A (Fin.last (n+1)) + ENNReal.ofReal (η/2)) + J (Fin.last n) :=
              add_le_add (add_le_add hαc hβc) (hpaid (Fin.last n))
            _ = (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
              rw [hsA, hsJ, ← herr]
              dsimp [A', J']
              ac_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ExclusionTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Infinite auxiliary tolls enforce avoidance without changing the cost
of the original paths. They are used only inside the collar construction. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {T X Y : Type*}

theorem le_exclusionToll (S : Set X) (m : X → ℝ≥0∞) : m ≤ exclusionToll S m := by
  intro x
  by_cases hx : x ∈ S <;> simp [exclusionToll, hx]

theorem exclusionToll_eq (S : Set X) (m : X → ℝ≥0∞) {x : X} (hx : x ∉ S) :
    exclusionToll S m x = m x := by
  simp [exclusionToll, hx]

theorem timeToll_mono_weight (γ : T → X) (A : Set T) {m n : X → ℝ≥0∞} (h : m ≤ n) :
    timeToll γ A m ≤ timeToll γ A n :=
  ENNReal.tsum_le_tsum (fun t => h (γ t))

theorem avoids_of_finite_exclusionToll (γ : T → X) (A : Set T)
    (S : Set X) (m : X → ℝ≥0∞) (h : timeToll γ A (exclusionToll S m) < ∞) :
    ∀t ∈ A, γ t ∉ S := by
  intro t ht hs
  have hb : exclusionToll S m (γ t) ≤ timeToll γ A (exclusionToll S m) :=
    ENNReal.le_tsum (f := fun u : A => exclusionToll S m (γ u)) ⟨t, ht⟩
  simpa [exclusionToll, hs] using hb.trans_lt h

variable [MetricSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem physicalTollCost_exclusion (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (S : Set X)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (h : ∀t, γ.val t ∉ S) :
    physicalTollCost d g (exclusionToll S m) γ = physicalTollCost d g m γ := by
  unfold physicalTollCost boundaryToll
  congr 1
  exact tsum_congr (fun t => exclusionToll_eq S m (h t))

theorem interiorPhysicalTollCost_mono_weight (d : PathCodeData X Y)
    (g : Y → ℝ≥0∞) {m n : X → ℝ≥0∞} (h : m ≤ n)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) :
    interiorPhysicalTollCost d g m γ ≤ interiorPhysicalTollCost d g n γ :=
  add_le_add le_rfl (timeToll_mono_weight γ.val _ h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarLevels
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted regular levels for collar construction, using
Federer's coarea theorem and Sard's theorem. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem ennreal_mul_le_add_squares (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc
      a * b ≤ b * b := mul_le_mul' h le_rfl
      _ ≤ a ^ 2 + b ^ 2 := by rw [← pow_two]; exact le_add_self
  · calc
      a * b ≤ a * a := mul_le_mul' le_rfl h
      _ ≤ a ^ 2 + b ^ 2 := by rw [← pow_two]; exact le_self_add

theorem weighted_scalar_coarea_integral_lt_top
    {D : Set ℂ} {f : ℂ → ℝ} {q : ℂ → ℝ≥0∞}
    (hcoarea : WeightedScalarCoareaIdentity D f q) (hq : Measurable q)
    (hq2 : (∫⁻ z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞) :
    (∫⁻ t, weightedScalarLevelLength D f q t) < ∞ := by
  rw [hcoarea.2]
  have hb : (∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) ≤
      (∫⁻ z in D, q z ^ 2) + ∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2 := by
    calc
      _ ≤ ∫⁻ z in D, (q z ^ 2 + (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) :=
        lintegral_mono fun z => ennreal_mul_le_add_squares _ _
      _ = _ := lintegral_add_left (hq.pow_const 2) _
  exact hb.trans_lt (ENNReal.add_lt_top.mpr ⟨hq2, hf2⟩)

theorem exists_weighted_regular_level
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hcompact : HasCompactSupport f) (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    (hq2 : (∫⁻ z in D, q z ^ 2) < ∞)
    (hf2 : (∫⁻ z in D, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, IsPlanarRegularValue f t ∧ weightedScalarLevelLength D f q t < ∞ := by
  have hc := hcoarea D hD f (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn q hq
  have hfin := weighted_scalar_coarea_integral_lt_top hc hq hq2 hf2
  have hbad : volume {t | weightedScalarLevelLength D f q t = ∞} = 0 := by
    have ha := ae_lt_top' hc.1 hfin.ne
    rw [ae_iff] at ha
    simpa only [not_lt, top_le_iff] using ha
  have hcrit := hsard f hf hcompact
  have hnull : volume ((f '' {z | fderiv ℝ f z = 0}) ∪
      {t | weightedScalarLevelLength D f q t = ∞}) = 0 := measure_union_null hcrit hbad
  have hpositive : 0 < volume (Ioo a b \ ((f '' {z | fderiv ℝ f z = 0}) ∪
      {t | weightedScalarLevelLength D f q t = ∞})) := by
    rw [measure_sdiff_null hnull, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  obtain ⟨t, ht, hgood⟩ := nonempty_of_measure_ne_zero hpositive.ne'
  refine ⟨t, ht, ?_, ?_⟩
  · intro z hz hzero
    exact hgood (Or.inl ⟨z, hzero, hz⟩)
  · exact lt_top_iff_ne_top.mpr (fun ht => hgood (Or.inr ht))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteWeightedCutoffs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth compact cutoffs have finite differential energy, so weighted
coarea and Sard choose finite-cost regular contours without an added
energy hypothesis on the cutoff. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem smooth_compact_differential_energy {f : ℂ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hcompact : HasCompactSupport f) :
    (∫⁻ z, (ENNReal.ofReal ‖fderiv ℝ f z‖) ^ 2) < ∞ := by
  have hd : Continuous (fderiv ℝ f) := (hf.fderiv_right (m := (↑(⊤ : ℕ∞))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  have hcont : Continuous (fun z => ‖fderiv ℝ f z‖ ^ 2) := hd.norm.pow 2
  have hsupp : HasCompactSupport (fun z => ‖fderiv ℝ f z‖ ^ 2) := by
    apply hcompact.mono'
    intro z hz
    by_contra hzf
    have hd := fderiv_of_notMem_tsupport ℝ hzf
    apply hz
    change ‖fderiv ℝ f z‖ ^ 2 = 0
    rw [hd]
    simp
  have hint : Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2) :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hfin := (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun z => sq_nonneg ‖fderiv ℝ f z‖))).mp hint.hasFiniteIntegral
  simpa only [ENNReal.ofReal_pow (norm_nonneg _)] using hfin

theorem exists_finite_weighted_regular_superlevel
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {A O : Set ℂ} (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻ z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ O ∧
      IsCompact {z | f z = t} ∧ IsPlanarRegularValue f t ∧
      frontier {z | t < f z} ⊆ {z | f z = t} ∧
      weightedScalarLevelLength univ f q t < ∞ := by
  obtain ⟨f, hf, hcompact, hsupp, hrange, hone⟩ := exists_smooth_planar_cutoff hA hO hAO
  obtain ⟨t, ht, hregular, hfinite⟩ := exists_weighted_regular_level hcoarea hsard isOpen_univ
    hf hcompact q hq (by simpa only [Measure.restrict_univ] using hq2)
    (by simpa only [Measure.restrict_univ] using smooth_compact_differential_energy hf hcompact)
    zero_lt_one
  have hclosure := closure_superlevel_subset_tsupport (f := f) ht.1
  refine ⟨f, t, hf, hcompact, hsupp, hrange, ht, isOpen_lt continuous_const hf.continuous,
    ?_, hcompact.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hsupp,
    isCompact_nonzero_level hf.continuous hcompact ht.1.ne', hregular, ?_, hfinite⟩
  · intro z hz
    change t < f z
    rw [hone.self_of_nhdsSet z hz]
    exact ht.2
  · intro z hz
    exact (frontier_lt_subset_eq continuous_const hf.continuous hz).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedSmoothContours
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth obstacle-isolating contours whose actual Hausdorff arclength
integral against the prescribed density is finite. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Manifold

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_regular_isolating_obstacle
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻ z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ V ∧
      closure {z | t < f z} ∩ F = A ∧ IsCompact {z | f z = t} ∧
      IsPlanarRegularValue f t ∧ Disjoint {z | f z = t} F ∧
      weightedScalarLevelLength univ f q t < ∞ := by
  let O := V ∩ (F \ A)ᶜ
  have hO : IsOpen O := hV.inter hFA.isOpen_compl
  have hAO : A ⊆ O := fun z hz => ⟨hAV hz, fun hbad => hbad.2 hz⟩
  obtain ⟨f, t, hf, _, hsupp, _, ht, hopen, hAU, hcompact, hclO,
    hlevel, hregular, _, hfinite⟩ :=
    exists_finite_weighted_regular_superlevel hcoarea hsard hA hO hAO q hq hq2
  have hclF : closure {z | t < f z} ∩ F = A := by
    apply Subset.antisymm
    · intro z hz
      by_contra hzA
      exact (hclO hz.1).2 ⟨hz.2, hzA⟩
    · intro z hz
      exact ⟨subset_closure (hAU hz), hAF hz⟩
  have hdisj : Disjoint {z | f z = t} F := by
    apply disjoint_left.mpr
    intro z hz hzF
    have hzSupp : z ∈ tsupport f := subset_tsupport f (by
      change f z ≠ 0
      rw [hz]
      exact ht.1.ne')
    have hzA : z ∈ A := by
      by_contra hnot
      exact (hsupp hzSupp).2 ⟨hzF, hnot⟩
    have hh := hAU hzA
    change t < f z at hh
    rw [hz] at hh
    exact hh.false
  exact ⟨f, t, hf, ht, hopen, hAU, hcompact, fun z hz => (hclO hz).1,
    hclF, hlevel, hregular, hdisj, hfinite⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedJordanCovers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Jordan fillings of finite-weight regular levels. The selected
frontiers retain the original regular-level equation and weighted bound. -/

open Set Filter Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_finite_weighted_jordan_cover
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hAF : A ⊆ F)
    (hFA : IsClosed (F \ A)) (hV : IsOpen V) (hAV : A ⊆ V)
    (hVconn : IsPreconnected Vᶜ) (hVunbounded : ¬ Bornology.IsBounded Vᶜ)
    (q : ℂ → ℝ≥0∞) (hq : Measurable q) (hq2 : (∫⁻z, q z ^ 2) < ∞) :
    ∃ (f : ℂ → ℝ) (t : ℝ)
      (γ : ConnectedComponents {z // f z = t} → Circle → ℂ)
      (H : ConnectedComponents {z // f z = t} → ℂ ≃ₜ ℂ)
      (s : Set (ConnectedComponents {z // f z = t})),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ V ∧ Disjoint {z | f z = t} F ∧
      (∫⁻z in {z | f z = t}, q z ∂(μH[1] : Measure ℂ)) < ∞ ∧
      s.Finite ∧ A ⊆ ⋃ i ∈ s, jordanInterior (H i) ∧
      s.Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      (∀ i ∈ s, closure (jordanInterior (H i)) ⊆ V) ∧
      ∀ i ∈ s, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) (γ i) ∧
        Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (H i)) = range (γ i) ∧
        Disjoint (frontier (jordanInterior (H i))) F ∧
        frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
  classical
  obtain ⟨f, t, hf, ht, hU, hAU, hUc, hUV, _, hlevel, hregular, havoid, hcost⟩ :=
    exists_weighted_regular_isolating_obstacle hcoarea hsard hA hAF hFA hV hAV q hq hq2
  obtain ⟨hfinite, γ, hγ, hγdisj, hγcover⟩ :=
    compact_regular_level_circle_contours hf hregular hlevel
  let : Finite (ConnectedComponents {z // f z = t}) := hfinite
  choose H hH using fun i => hschoenflies (γ i) (hγ i).2.continuous (hγ i).2.injective
  have hfront (i) : frontier (jordanInterior (H i)) = range (γ i) :=
    frontier_jordanInterior_eq_circle_range (H i) (γ i) (hH i)
  have hUd : frontier {z | t < f z} = {z | f z = t} :=
    frontier_superlevel_eq_regular_level hf.continuous hregular
  have hfrontlevel (i) : frontier (jordanInterior (H i)) ⊆ {z | f z = t} := by
    rw [hfront, ← hγcover]
    exact subset_iUnion (fun i => range (γ i)) i
  have hpair : Pairwise (fun i j => Disjoint (frontier (jordanInterior (H i)))
      (frontier (jordanInterior (H j)))) := by
    intro i j hij
    simpa only [hfront] using hγdisj hij
  obtain ⟨s, hs, hsd, hdom, _⟩ := exists_outer_jordanInteriors H hpair
  let : Finite s := hs.to_subtype
  have hsd' : Pairwise (Disjoint on fun i : s => closure (jordanInterior (H i))) := by
    intro i j hij
    exact hsd i.property j.property (fun h => hij (Subtype.ext h))
  have hcover : frontier {z | t < f z} ⊆ ⋃ i : s, closure (jordanInterior (H i)) := by
    intro z hz
    rw [hUd, ← hγcover] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    have hi' : z ∈ closure (jordanInterior (H i)) := by
      apply frontier_subset_closure
      simpa only [hfront] using hi
    obtain ⟨j, hj, hij⟩ := hdom i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi'⟩
  have hUcover : {z | t < f z} ⊆ ⋃ i : s, jordanInterior (H i) :=
    open_subset_finite_jordanInteriors_of_frontier_subset (fun i : s => H i) hsd'
      hU (hUc.isBounded.subset subset_closure) hcover
      (fun i => hUd.symm ▸ hfrontlevel i)
  have hlevelV : {z | f z = t} ⊆ V := fun z hz =>
    hUV (frontier_subset_closure (hUd.symm ▸ hz))
  have hfiniteCost : (∫⁻z in {z | f z = t}, q z ∂(μH[1] : Measure ℂ)) < ∞ := by
    simpa only [weightedScalarLevelLength, univ_inter] using hcost
  refine ⟨f, t, γ, H, s, hf, hregular, hlevelV, havoid, hfiniteCost, hs, ?_, hsd, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hUcover (hAU hz))
    exact mem_iUnion₂.mpr ⟨i, i.property, hi⟩
  · intro i _
    apply closed_jordanInterior_subset_of_unbounded_connected_compl (H i) hVconn hVunbounded
    intro z hz
    apply hUV
    apply frontier_subset_closure
    rw [hUd]
    exact hfrontlevel i hz
  · intro i _
    exact ⟨(hγ i).1, (hγ i).2, hfront i, havoid.mono_left (hfrontlevel i), hfrontlevel i⟩


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SinglePhysicalDisk
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single smooth physical disk about a quotient singleton

Connectedness of the fiber upgrades the finite disjoint cover to a single
disk. The general open-family lemma does not need finiteness.
-/

open Set Function
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

theorem exists_member_containing_connected_set
    {X I : Type*} [TopologicalSpace X] {S : Set X} (hS : IsConnected S)
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (Disjoint on U)) (hcover : S ⊆ ⋃ i, U i) :
    ∃ i, S ⊆ U i := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  let V : Set X := ⋃ j ∈ ({i}ᶜ : Set I), U j
  have hV : IsOpen V := isOpen_biUnion (fun j _ => hU j)
  have hUV : Disjoint (U i) V := by
    apply Set.disjoint_left.mpr
    intro z hz hzV
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzV
    exact Set.disjoint_left.mp (hd (fun h => hj (mem_singleton_iff.mpr h.symm))) hz hzj
  have hSC : S ⊆ U i ∪ V := by
    intro z hz
    obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover hz)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hzj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, by simpa using hji, hzj⟩)
  rcases hS.isPreconnected.subset_or_subset (hU i) hV hUV hSC with h | h
  · exact ⟨i, h⟩
  · exact (Set.disjoint_left.mp hUV hxi (h hx)).elim

theorem isConnected_finite_fiber
    {X : Type*} (π : Sphere → X) (hfibers : ∀ x, IsConnected (π ⁻¹' {x}))
    {x : X} (hne : π OnePoint.infty ≠ x) :
    IsConnected {z : ℂ | π (z : Sphere) = x} := by
  have heq : ((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x} = π ⁻¹' {x} := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [hne]
    | coe z => simp [OnePoint.coe_injective.mem_set_image]
  have hconn : IsConnected (((↑) : ℂ → Sphere) '' {z : ℂ | π (z : Sphere) = x}) :=
    heq.symm ▸ hfibers x
  refine ⟨?_, OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    hconn.isPreconnected⟩
  obtain ⟨p, hp⟩ := hconn.nonempty
  obtain ⟨z, hz, _⟩ := hp
  exact ⟨z, hz⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedPhysicalCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-cost smooth physical collars of an actual collapsed component.
The regular level containing the chosen boundary is retained explicitly. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_small_physical_disk
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hschoenflies : PlanarSchoenflies)
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (G : Set Sphere) (π : Sphere → X) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {F V : Set X} (hF : IsClosed F) {x : X} (hx : x ∈ F)
    (hcomponent : connectedComponentIn F x = {x})
    (hV : IsOpen V) (hxV : x ∈ V) (hVconn : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ F)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (f : ℂ → ℝ) (t : ℝ),
      {z : ℂ | π (z : Sphere) = x} ⊆ jordanInterior H ∧
      closure (jordanInterior H) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      frontier (jordanInterior H) ⊆ {z | f z = t} ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V ∧
      (∀ z, f z = t → (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ F) ∧
      (∫⁻z in {z | f z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
  classical
  obtain ⟨hphysical, hunbounded⟩ :=
    physical_exterior_connected_unbounded_of_component_collapse G π hπ hclosed hsurj hr
      hV hVconn hinfty
  obtain ⟨A, hAc, hxA, hAF, hAV, hFA⟩ :=
    exists_compact_piece_of_singleton_component hF hx hcomponent hV hxV
  let q : ℂ → X := fun z => π (z : Sphere)
  have hq : Continuous q := hπ.comp OnePoint.continuous_coe
  have hAp : IsCompact (q ⁻¹' A) := by
    apply isCompact_finite_preimage (hAc.isClosed.preimage hπ)
    exact fun h => hinfty (subset_closure (hAV h))
  have hFp : IsClosed ((q ⁻¹' F) \ (q ⁻¹' A)) := by
    simpa only [preimage_sdiff] using hFA.preimage hq
  obtain ⟨f, t, γ, H, s, hf, hreg, hlevelV, havoid, hcost,
    _, hcov, hd, hinside, hcurves⟩ :=
    exists_finite_weighted_jordan_cover hcoarea hsard hschoenflies hAp
      (preimage_mono hAF) hFp (hV.preimage hq) (preimage_mono hAV)
      hphysical hunbounded g hg hg2
  have hfiber : IsConnected {z : ℂ | π (z : Sphere) = x} := by
    apply isConnected_finite_fiber π (connected_fibers_of_component_collapse G π hsurj hr)
    intro heq
    exact hinfty (subset_closure (heq.symm ▸ hxV))
  have hpair : Pairwise (Disjoint on fun i : s => jordanInterior (H i)) := by
    intro i j hij
    exact (hd i.property j.property (fun h => hij (Subtype.ext h))).mono
      subset_closure subset_closure
  have hcover : {z : ℂ | π (z : Sphere) = x} ⊆ ⋃ i : s, jordanInterior (H i) := by
    intro z hz
    have hzA : z ∈ q ⁻¹' A := by
      change π (z : Sphere) ∈ A
      rwa [hz]
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcov hzA)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨i, hi⟩ := exists_member_containing_connected_set hfiber
    (fun i : s => jordanInterior (H i)) (fun i => jordanInterior_isOpen (H i)) hpair hcover
  obtain ⟨hγ, hemb, hfront, _, hfrontlevel⟩ := hcurves i i.property
  refine ⟨H i, γ i, f, t, hi, hinside i i.property, hγ, hemb, hfront,
    hfrontlevel, hf, hreg, hlevelV, ?_, hcost⟩
  intro z hz
  have hnot : π (z : Sphere) ∉ F := fun h => disjoint_left.mp havoid hz h
  refine ⟨?_, hnot⟩
  by_contra h
  exact hnot (hbad _ h)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzIntervalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.pathLengthKernel_apply _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete paths obtained by traversing a real interval in a Lipschitz chart. -/

open Set Function Metric
open scoped NNReal ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem realIntervalPath_antilipschitz {a b : ℝ} (hab : a ≠ b) :
    AntilipschitzWith (nndist a b)⁻¹ (realIntervalPath a b) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro s t
  change dist s t ≤ _ * dist (AffineMap.lineMap a b (s : ℝ))
    (AffineMap.lineMap a b (t : ℝ))
  rw [dist_lineMap_lineMap, Subtype.dist_eq, NNReal.coe_inv, coe_nndist,
    mul_left_comm, inv_mul_cancel₀ (dist_ne_zero.mpr hab), mul_one]

theorem range_realIntervalPath {a b : ℝ} (hab : a < b) :
    range (realIntervalPath a b) = Icc a b := by
  apply Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    exact realIntervalPath_mem hab.le s
  · intro y hy
    have hd : 0 < b - a := sub_pos.mpr hab
    let s : PathTime := ⟨(y-a)/(b-a), div_nonneg (sub_nonneg.mpr hy.1) hd.le,
      (div_le_one hd).mpr (sub_le_sub_right hy.2 a)⟩
    refine ⟨s, ?_⟩
    change AffineMap.lineMap a b ((y-a)/(b-a)) = y
    rw [AffineMap.lineMap_apply_module]
    dsimp
    field_simp
    ring

variable {X : Type*} [MetricSpace X]

theorem intervalChartPath_lipschitz (φ : ℝ → X) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) :
    LipschitzWith (L * nndist a b) (intervalChartPath φ hab hL).val := by
  exact intervalChart_lipschitz φ hab hL

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FiniteCostChartPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual interval in a chart with a Lipschitz inverse coordinate has
finite weighted path cost whenever its image has finite weighted Hausdorff length. -/

open Set Function MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem intervalChartPath_antilipschitz (φ : ℝ → X) (ψ : X → ℝ)
    {a b : ℝ} (hab : a < b) {L K : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) {U : Set X}
    (hK : LipschitzOnWith K ψ U) (hU : MapsTo φ (Icc a b) U)
    (hinv : ∀u ∈ Icc a b, ψ (φ u) = u) :
    AntilipschitzWith ((nndist a b)⁻¹ * K) (intervalChartPath φ hab.le hL).val := by
  apply AntilipschitzWith.of_le_mul_dist
  intro s t
  have hs := realIntervalPath_mem hab.le s
  have ht := realIntervalPath_mem hab.le t
  change dist s t ≤ _ * dist (φ (realIntervalPath a b s)) (φ (realIntervalPath a b t))
  calc
    dist s t ≤ ((nndist a b)⁻¹ : ℝ≥0) *
        dist (realIntervalPath a b s) (realIntervalPath a b t) :=
      (realIntervalPath_antilipschitz hab.ne).le_mul_dist s t
    _ = ((nndist a b)⁻¹ : ℝ≥0) *
        dist (ψ (φ (realIntervalPath a b s))) (ψ (φ (realIntervalPath a b t))) := by
      rw [hinv _ hs, hinv _ ht]
    _ ≤ ((nndist a b)⁻¹ : ℝ≥0) *
        (K * dist (φ (realIntervalPath a b s)) (φ (realIntervalPath a b t))) := by
      exact mul_le_mul_of_nonneg_left (hK.dist_le_mul _ (hU hs) _ (hU ht)) (by positivity)
    _ = _ := by simp only [NNReal.coe_mul, mul_assoc]

theorem intervalChartPath_range (φ : ℝ → X) {a b : ℝ} (hab : a < b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) :
    range (intervalChartPath φ hab.le hL).val = φ '' Icc a b := by
  change range (φ ∘ realIntervalPath a b) = _
  rw [range_comp, range_realIntervalPath hab]

variable [MeasurableSpace X] [BorelSpace X]

theorem intervalChartPath_cost_lt_top (φ : ℝ → X) (ψ : X → ℝ)
    {a b : ℝ} (hab : a < b) {L K : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hL0 : L ≠ 0) {U : Set X}
    (hK : LipschitzOnWith K ψ U) (hU : MapsTo φ (Icc a b) U)
    (hinv : ∀u ∈ Icc a b, ψ (φ u) = u)
    {S : Set X} (hS : φ '' Icc a b ⊆ S) (g : X → ℝ≥0∞)
    (hfinite : (∫⁻x in S, g x ∂(μH[1] : Measure X)) < ∞) :
    (∫⁻x, g x ∂pathOccupation (intervalChartPath φ hab.le hL)) < ∞ := by
  apply bilipschitz_pathCost_lt_top _ (intervalChartPath_lipschitz φ hab.le hL)
    (mul_ne_zero hL0 (by simpa only [ne_eq, nndist_eq_zero] using hab.ne))
    (intervalChartPath_antilipschitz φ ψ hab hL hK hU hinv)
  apply lt_of_le_of_lt (lintegral_mono_set (μ := (μH[1] : Measure X)) ?_) hfinite
  rw [intervalChartPath_range φ hab hL]
  exact hS

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularLevelArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local regular-level arcs with finite weighted path cost, obtained from
actual smooth implicit-function coordinates and Hausdorff length. -/

open Set Function MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_finite_cost_regular_level_arc {f : ℂ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {t : ℝ} {z : ℂ}
    (hz : f z = t) (hregular : fderiv ℝ f z ≠ 0)
    (g : ℂ → ℝ≥0∞)
    (hfinite : (∫⁻w in {w | f w = t}, g w ∂(μH[1] : Measure ℂ)) < ∞) :
    ∃ (γ : RectifiablePath ℂ) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      V ∩ {w | f w = t} ⊆ range γ.val ∧ range γ.val ⊆ {w | f w = t} ∧
      Injective γ.val ∧ (∫⁻w, g w ∂pathOccupation γ) < ∞ := by
  obtain ⟨e, hze, he, heSmooth, heInv⟩ := exists_smooth_planar_level_chart hf hregular
  let y0 : ℝ := (e z).2
  let φ : ℝ → ℂ := fun y => e.symm (t, y)
  let ψ : ℂ → ℝ := fun w => (e w).2
  have hez : (t, y0) = e z := Prod.ext ((he z).trans hz).symm rfl
  have htarget : (t, y0) ∈ e.target := hez ▸ e.map_source hze
  have hφz : φ y0 = z := by
    change e.symm (t, y0) = z
    rw [hez, e.left_inv hze]
  have hφsmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞)) φ y0 :=
    (heInv.contDiffAt (e.open_target.mem_nhds htarget)).comp y0
      (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨L0, T, hT, hL0⟩ := (hφsmooth.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).exists_lipschitzOnWith
  obtain ⟨K, U, hU, hK⟩ :=
    (show ContDiffAt ℝ 1 ψ z from
      (contDiff_snd.comp heSmooth).contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).exists_lipschitzOnWith
  have hφU : φ ⁻¹' U ∈ 𝓝 y0 := by
    apply hφsmooth.continuousAt.preimage_mem_nhds
    rwa [hφz]
  have htargetN : (fun y : ℝ => (t, y)) ⁻¹' e.target ∈ 𝓝 y0 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds htarget)
  obtain ⟨δ, hδ, hδR⟩ := Metric.mem_nhds_iff.mp (inter_mem (inter_mem hT hφU) htargetN)
  let a : ℝ := y0 - δ / 2
  let b : ℝ := y0 + δ / 2
  have hab : a < b := by dsimp [a, b] <;> linarith
  have hI : Icc a b ⊆ ball y0 δ := by
    intro y hy
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [a, b] at hy
    constructor <;> linarith [hy.1, hy.2]
  have hφLip : LipschitzOnWith (L0 + 1) φ (Icc a b) :=
    (hL0.mono (fun y hy => (hδR (hI hy)).1.1)).weaken (le_add_of_nonneg_right zero_le_one)
  have hφU' : MapsTo φ (Icc a b) U := fun y hy => (hδR (hI hy)).1.2
  have hφtarget : ∀ y ∈ Icc a b, (t, y) ∈ e.target := fun y hy => (hδR (hI hy)).2
  have hinv : ∀ y ∈ Icc a b, ψ (φ y) = y := by
    intro y hy
    exact congrArg Prod.snd (e.right_inv (hφtarget y hy))
  have hlevel : φ '' Icc a b ⊆ {w | f w = t} := by
    rintro w ⟨y, hy, rfl⟩
    change f (e.symm (t, y)) = t
    rw [← he, e.right_inv (hφtarget y hy)]
  let γ := intervalChartPath φ hab.le hφLip
  let V := e.source ∩ ψ ⁻¹' Ioo a b
  have hV : IsOpen V := e.open_source.inter (isOpen_Ioo.preimage (continuous_snd.comp heSmooth.continuous))
  have hzV : z ∈ V := by
    refine ⟨hze, ?_⟩
    change a < y0 ∧ y0 < b
    dsimp [a, b]
    constructor <;> linarith
  have hrange : range γ.val = φ '' Icc a b := intervalChartPath_range φ hab hφLip
  refine ⟨γ, V, hV, hzV, ?_, hrange ▸ hlevel, ?_, ?_⟩
  · intro w hw
    rw [hrange]
    refine ⟨ψ w, ⟨hw.1.2.1.le, hw.1.2.2.le⟩, ?_⟩
    change e.symm (t, (e w).2) = w
    have hwcoord : (t, (e w).2) = e w := Prod.ext ((he w).trans hw.2).symm rfl
    rw [hwcoord, e.left_inv hw.1.1]
  · exact (intervalChartPath_antilipschitz φ ψ hab hφLip hK hφU' hinv).injective
  · exact intervalChartPath_cost_lt_top φ ψ hab hφLip (by positivity) hK hφU' hinv hlevel g hfinite

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallCollarArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small image neighborhoods on a finite-cost simple collar admit
actual joining arcs of arbitrarily small cost. Compactness converts
parameter neighborhoods into neighborhoods in the ambient space. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_small_collar_arcs (γ : RectifiablePath X) (g : X → ℝ≥0∞)
    (hg : Measurable g) (hfinite : (∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ) < ∞)
    (r : PathTime) (hsingle : ∀ s, γ.val s = γ.val r → s = r)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ V : Set X, IsOpen V ∧ γ.val r ∈ V ∧
      ∀ x ∈ V ∩ range γ.val, ∀ y ∈ V ∩ range γ.val,
        ∃ ρ : RectifiablePath X, ρ.val ⊥ = x ∧ ρ.val ⊤ = y ∧
          range ρ.val ⊆ range γ.val ∧ (∫⁻ z, g z ∂pathOccupation ρ) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_rectifiable_subarcs γ g hg hfinite r hε
  let K : Set PathTime := {s | δ ≤ dist s r}
  have hK : IsCompact K := (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  let V := (γ.val '' K)ᶜ
  have hr : γ.val r ∈ V := by
    rintro ⟨s, hs, he⟩
    have hsr := hsingle s he
    subst s
    change δ ≤ dist r r at hs
    exact hδ.not_ge (by simpa only [dist_self] using hs)
  refine ⟨V, (hK.image γ.val.continuous).isClosed.isOpen_compl, hr, ?_⟩
  intro x hx y hy
  obtain ⟨a, ha⟩ := hx.2
  obtain ⟨b, hb⟩ := hy.2
  have had : dist a r < δ := by
    by_contra h
    exact hx.1 ⟨a, le_of_not_gt h, ha⟩
  have hbd : dist b r < δ := by
    by_contra h
    exact hy.1 ⟨b, le_of_not_gt h, hb⟩
  obtain ⟨ρ, hρa, hρb, hρrange, hρcost⟩ := hsmall a b had hbd
  exact ⟨ρ, hρa.trans ha, hρb.trans hb, hρrange, hρcost⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SaturatedDisks
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Saturation of physical Jordan interiors

A connected quotient fiber cannot cross a boundary consisting of singleton
fibers. Thus physical Jordan interiors whose boundaries lie in the original
domain are saturated, and project to open quotient neighborhoods. This is
the saturation assertion preceding the small-disks lemma in Section 1.
-/

open Set Function
open scoped Topology

namespace CircleDomainRigidity

theorem preimage_image_open_of_singleton_boundary_fibers
    {X Y : Type*} [TopologicalSpace X]
    (π : X → Y) (hfibers : ∀ y, IsPreconnected (π ⁻¹' {y}))
    {U : Set X} (hU : IsOpen U)
    (hsing : ∀ p ∈ frontier U, ∀ q, π q = π p → q = p) :
    π ⁻¹' (π '' U) = U := by
  apply Set.Subset.antisymm
  · rintro q ⟨p, hp, hpq⟩
    let K : Set X := π ⁻¹' {π p}
    have hpK : p ∈ K := rfl
    have hmiss : Disjoint K (frontier U) := by
      apply Set.disjoint_left.mpr
      intro z hz hzfront
      have hpz : p = z := hsing z hzfront p hz.symm
      have hpfront : p ∈ frontier U := hpz.symm ▸ hzfront
      rw [hU.frontier_eq] at hpfront
      exact hpfront.2 hp
    have hsplit : K ⊆ U ∨ K ⊆ (closure U)ᶜ := by
      apply (hfibers (π p)).subset_or_subset hU isClosed_closure.isOpen_compl
      · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
      · intro z hz
        by_cases hzU : z ∈ U
        · exact Or.inl hzU
        · right
          intro hzcl
          apply Set.disjoint_left.mp hmiss hz
          rw [hU.frontier_eq]
          exact ⟨hzcl, hzU⟩
    rcases hsplit with hin | hout
    · exact hin hpq.symm
    · exact (hout hpK (subset_closure hp)).elim
  · exact subset_preimage_image π U

/-- Physical Jordan disks with boundary in the domain are saturated for
the actual component-collapse quotient. -/
theorem preimage_image_jordanInterior_of_component_collapse
    {Y : Type*} (G : Set Sphere) (π : Sphere → Y) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
  apply preimage_image_open_of_singleton_boundary_fibers π
    (fun y => (connected_fibers_of_component_collapse G π hsurj hr y).isPreconnected)
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
  intro p hp q hqp
  rw [frontier_sphere_image_jordanInterior] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  rcases (hr (z : Sphere) q).mp hqp.symm with heq | ⟨hznot, _⟩
  · exact heq.symm
  · exact (hznot (hboundary z hz)).elim

/-- The saturated physical disk projects to an open quotient neighborhood. -/
theorem isOpen_image_jordanInterior_of_component_collapse
    {Y : Type*} [TopologicalSpace Y]
    (G : Set Sphere) (π : Sphere → Y) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (H : ℂ ≃ₜ ℂ) (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G) :
    IsOpen (π '' (((↑) : ℂ → Sphere) '' jordanInterior H)) := by
  apply (hclosed.isQuotientMap hπ hsurj).isOpen_preimage.mp
  rw [preimage_image_jordanInterior_of_component_collapse G π hsurj hr H hboundary]
  exact OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarNeighborhoods
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted collars in the physical plane and their actual open quotient
neighborhoods. Compact containment survives projection. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

namespace WeightedCollar

variable {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere}
  {p : Sphere} {g : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g)

theorem isOpen_region (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsOpen D.region :=
  isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed hsurj hr D.disk
    (fun z hz => (D.level_good z (D.frontier_level hz)).1)

theorem point_mem_region (hsurj : Surjective π) (hp : p ≠ π OnePoint.infty) :
    p ∈ D.region := by
  obtain ⟨x, hx⟩ := hsurj p
  cases x using OnePoint.rec with
  | infty => exact (hp hx.symm).elim
  | coe z => exact ⟨z, ⟨z, D.fiber_inside hx, rfl⟩, hx⟩

theorem closure_region_subset_image (hπ : Continuous π) :
    closure D.region ⊆ π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior D.disk)) := by
  apply closure_minimal (image_mono (image_mono subset_closure))
  exact (((isCompact_closure_jordanInterior D.disk).image OnePoint.continuous_coe).image hπ).isClosed

theorem closure_region_subset {V : Set Sphere} (hπ : Continuous π)
    (hV : closure (jordanInterior D.disk) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V) :
    closure D.region ⊆ V := by
  intro x hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := D.closure_region_subset_image hπ hx
  exact hV hz

theorem frontier_region_subset (hπ : Continuous π) (hregion : IsOpen D.region) :
    frontier D.region ⊆ π '' (((↑) : ℂ → Sphere) '' {z | D.function z = D.level}) := by
  intro x hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := D.closure_region_subset_image hπ (frontier_subset_closure hx)
  have hznot : z ∉ jordanInterior D.disk := by
    intro h
    rw [hregion.frontier_eq] at hx
    exact hx.2 ⟨z, ⟨z, h, rfl⟩, rfl⟩
  have hzfront : z ∈ frontier (jordanInterior D.disk) := by
    rw [(jordanInterior_isOpen D.disk).frontier_eq]
    exact ⟨hz, hznot⟩
  exact ⟨z, ⟨z, D.frontier_level hzfront, rfl⟩, rfl⟩

end WeightedCollar

theorem exists_weighted_collar_in_neighborhood
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {O : Set Sphere} (hO : IsOpen O) (hpO : p ∈ O)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : WeightedCollar G π B p g,
      closure D.region ⊆ O ∧ {z | D.function z = D.level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' O := by
  obtain ⟨V, hV, hpV, hVO, hVc⟩ := exists_sphere_neighborhood_connected_compl
    (hO.inter isClosed_singleton.isOpen_compl) ⟨hpO, hp⟩
  have hcomponent : connectedComponentIn B p = {p} :=
    (hTD _ (connectedComponentIn_subset B p) isPreconnected_connectedComponentIn).eq_singleton_of_mem
      (mem_connectedComponentIn hpB)
  obtain ⟨H, γ, f, t, hfiber, hinside, hsmooth, hemb, hfront, hfrontlevel,
    hf, hreg, hlevelV, hgood, hcost⟩ :=
    exists_weighted_small_physical_disk hcoarea hsard hsch G π hπ hclosed hsurj hr
      hB hpB hcomponent hV hpV hVc (fun h => (hVO h).2 rfl) hbad g hg hg2
  let D : WeightedCollar G π B p g :=
    ⟨H, γ, f, t, hfiber, hsmooth, hemb, hfront, hfrontlevel, hf, hreg, hgood, hcost⟩
  refine ⟨D, ?_, ?_⟩
  · exact (D.closure_region_subset hπ hinside).trans (fun _ h => (hVO (subset_closure h)).1)
  · exact hlevelV.trans (fun _ h => (hVO (subset_closure h)).1)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NestedWeightedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strictly nested actual weighted collars, chosen inside any prescribed
sequence of quotient neighborhoods. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_nested_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (O : ℕ → Set Sphere) (hO : ∀n, IsOpen (O n)) (hpO : ∀n, p ∈ O n)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      (∀n, closure (D n).region ⊆ O n) ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D n).function z = (D n).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' O n) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) := by
  classical
  obtain ⟨D0, hD0, hL0⟩ := exists_weighted_collar_in_neighborhood hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hpB hp (hO 0) (hpO 0) g hg hg2
  have hstep : ∀ (n : ℕ) (D : WeightedCollar G π B p g),
      ∃ E : WeightedCollar G π B p g,
        closure E.region ⊆ D.region ∩ O (n+1) ∧
        {z | E.function z = E.level} ⊆
          (fun z : ℂ => π (z : Sphere)) ⁻¹' (D.region ∩ O (n+1)) := by
    intro n D
    exact exists_weighted_collar_in_neighborhood hcoarea hsard hsch
      G π hπ hclosed hsurj hr hB hTD hbad hpB hp
      ((D.isOpen_region hπ hclosed hsurj hr).inter (hO (n+1)))
      ⟨D.point_mem_region hsurj hp, hpO (n+1)⟩ g hg hg2
  choose step hstep using hstep
  let D : ℕ → WeightedCollar G π B p g := Nat.rec D0 step
  have hs (n : ℕ) : D (n+1) = step n (D n) := rfl
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hD0
    | succ n => exact fun z hz => ((hstep n (D n)).1 hz).2
  · intro n z hz
    exact ((hstep n (D n)).1 hz).1
  · intro n
    cases n with
    | zero => exact hL0
    | succ n => exact fun z hz => ((hstep n (D n)).2 hz).2
  · intro n z hz
    exact ((hstep n (D n)).2 hz).1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ShrinkingLocalWeightedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shrinking weighted collars require square integrability only in the
chosen outer neighborhood. This allows densities positive near infinity. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem exists_shrinking_local_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    {W : Set Sphere} (hW : IsOpen W) (hpW : p ∈ W)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (hg2 : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' W, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      closure (D 0).region ⊆ W ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) ∧
      (∀V ∈ 𝓝 p, ∃N : ℕ, ∀n ≥ N, closure (D n).region ⊆ V) := by
  let P : Set ℂ := (fun z : ℂ => π (z : Sphere)) ⁻¹' W
  have hP : MeasurableSet P := (hW.preimage (hπ.comp OnePoint.continuous_coe)).measurableSet
  let q := P.indicator g
  have hq : Measurable q := hg.indicator hP
  have hq2 : (∫⁻z, q z ^ 2) < ∞ := by
    have heq : (fun z => q z ^ 2) = P.indicator (fun z => g z ^ 2) := by
      funext z
      by_cases hz : z ∈ P <;> simp [q, hz]
    rw [heq, lintegral_indicator hP]
    exact hg2
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r] <;> positivity
  let O : ℕ → Set Sphere := fun n => W ∩ ball p (r n)
  obtain ⟨D, hD, hnest, hlevel, hlevelNest⟩ := exists_nested_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hTD hbad hpB hp O
    (fun _ => hW.inter isOpen_ball) (fun n => ⟨hpW, mem_ball_self (hrpos n)⟩) q hq hq2
  have hcost (n : ℕ) : (∫⁻z in {z | (D n).function z = (D n).level}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
    have hm : MeasurableSet {z | (D n).function z = (D n).level} :=
      (isClosed_eq (D n).smooth.continuous continuous_const).measurableSet
    have heq : (∫⁻z in {z | (D n).function z = (D n).level}, g z ∂(μH[1] : Measure ℂ)) =
        ∫⁻z in {z | (D n).function z = (D n).level}, q z ∂(μH[1] : Measure ℂ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hm] with z hz
      exact (indicator_of_mem (show z ∈ P from (hlevel n hz).1) g).symm
    rw [heq]
    exact (D n).cost_finite
  let E : ℕ → WeightedCollar G π B p g := fun n =>
    ⟨(D n).disk, (D n).curve, (D n).function, (D n).level, (D n).fiber_inside,
      (D n).curve_smooth, (D n).curve_embedding, (D n).frontier_eq, (D n).frontier_level,
      (D n).smooth, (D n).regular, (D n).level_good, hcost n⟩
  refine ⟨E, (hD 0).trans inter_subset_left, hnest, hlevelNest, ?_⟩
  intro V hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrzero.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => (hD n).trans ?_⟩
  exact inter_subset_right.trans ((ball_subset_ball (hN n hn).le).trans hball)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzMappedArclength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Lipschitz map multiplies actual path arclength by at most its
Lipschitz constant. The proof constructs the nonnegative Stieltjes difference. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pathLengthMeasure_le_of_interval_bounds
    (α : RectifiablePath X) (β : RectifiablePath Y) (L : ℝ≥0)
    (hI : ∀a b : PathTime, a ≤ b → pathLengthMeasure β (Icc a b) ≤
      (L : ℝ≥0∞) * pathLengthMeasure α (Icc a b)) :
    pathLengthMeasure β ≤ L • pathLengthMeasure α := by
  have hdiff (γ : RectifiablePath X) (a b : PathTime) (hab : a ≤ b) :
      pathLengthMeasure γ (Icc a b) =
        ENNReal.ofReal (pathLengthFunction γ b - pathLengthFunction γ a) := by
    rw [← measure_congr (Ioc_ae_eq_Icc (μ := pathLengthMeasure γ)),
      pathLengthMeasure, StieltjesFunction.measure_Ioc]
  have hdiffβ (a b : PathTime) (hab : a ≤ b) :
      pathLengthMeasure β (Icc a b) =
        ENNReal.ofReal (pathLengthFunction β b - pathLengthFunction β a) := by
    rw [← measure_congr (Ioc_ae_eq_Icc (μ := pathLengthMeasure β)),
      pathLengthMeasure, StieltjesFunction.measure_Ioc]
  have hbound (a b : PathTime) (hab : a ≤ b) :
      pathLengthFunction β b - pathLengthFunction β a ≤
        L * (pathLengthFunction α b - pathLengthFunction α a) := by
    have h := hI a b hab
    rw [hdiff α a b hab, hdiffβ a b hab] at h
    have hnonneg : 0 ≤ (L : ℝ) * (pathLengthFunction α b - pathLengthFunction α a) :=
      mul_nonneg L.property (sub_nonneg.mpr ((pathLengthFunction α).mono hab))
    apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
    rw [ENNReal.ofReal_mul (p := (L : ℝ))
      (q := pathLengthFunction α b - pathLengthFunction α a) L.property,
      ENNReal.ofReal_coe_nnreal]
    exact h
  let F : StieltjesFunction PathTime := {
    toFun := fun t => L * pathLengthFunction α t - pathLengthFunction β t
    mono' := by
      intro a b hab
      have h := hbound a b hab
      dsimp
      linarith
    right_continuous' := fun t =>
      (((continuous_pathLengthFunction α).const_mul (L : ℝ)).sub
        (continuous_pathLengthFunction β)).continuousAt.continuousWithinAt }
  have he : F + pathLengthFunction β = L • pathLengthFunction α := by
    apply StieltjesFunction.ext
    intro t
    change (L : ℝ) * pathLengthFunction α t - pathLengthFunction β t +
      pathLengthFunction β t = (L : ℝ) * pathLengthFunction α t
    ring
  have hmeasure := congrArg (fun f : StieltjesFunction PathTime => f.measure) he
  rw [StieltjesFunction.measure_add, StieltjesFunction.measure_smul] at hmeasure
  change F.measure + pathLengthMeasure β = L • pathLengthMeasure α at hmeasure
  rw [← hmeasure]
  exact le_add_of_nonneg_left bot_le

theorem lipschitzMappedPath_length_le (α : RectifiablePath X) (f : X → Y)
    {S : Set X} {L : ℝ≥0} (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S) :
    pathLengthMeasure (lipschitzMappedPath α f hL hα) ≤ L • pathLengthMeasure α := by
  apply pathLengthMeasure_le_of_interval_bounds
  intro a b hab
  rw [pathLengthMeasure_Icc _ hab, pathLengthMeasure_Icc _ hab]
  exact hL.comp_eVariationOn_le (fun t _ => hα t)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzMappedCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted physical cost under a Lipschitz change of ambient metric. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem lipschitzMappedPath_cost_le (α : RectifiablePath X) (f : X → Y)
    {S : Set X} {L : ℝ≥0} (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y, g y ∂pathOccupation (lipschitzMappedPath α f hL hα)) ≤
      (L : ℝ≥0∞) * ∫⁻t, g (f (α.val t)) ∂pathLengthMeasure α := by
  rw [lintegral_pathOccupation _ hg]
  calc
    _ ≤ ∫⁻t, g (f (α.val t)) ∂(L • pathLengthMeasure α) :=
      lintegral_mono' (lipschitzMappedPath_length_le α f hL hα) (fun _ => le_rfl)
    _ = _ := by rw [lintegral_smul_measure]; rfl

theorem lipschitzMappedPath_cost_lt_top (α : RectifiablePath X) (f : X → Y)
    {S : Set X} {L : ℝ≥0} (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S)
    (g : Y → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻t, g (f (α.val t)) ∂pathLengthMeasure α) < ∞) :
    (∫⁻y, g y ∂pathOccupation (lipschitzMappedPath α f hL hα)) < ∞ :=
  (lipschitzMappedPath_cost_le α f hL hα g hg).trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hfinite)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SphereChartLipschitz
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed physical sphere metric has locally Lipschitz finite charts.
This follows from the explicit smooth inverse stereographic formula in
Mathlib, including the linear coordinates chosen by the sphere homeomorphism. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section

namespace CircleDomainRigidity

theorem contDiff_roundSphere_finite_chart :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) := by
  classical
  have hlin (W : Submodule ℝ RoundAmbient) (e : ℂ ≃L[ℝ] W) :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z => (e z : RoundAmbient)) :=
    W.subtypeL.contDiff.comp e.contDiff
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (stereoInvFunAux _ ∘ _)
  apply contDiff_stereoInvFunAux.comp
  exact hlin _ _

attribute [local instance] sphereMetric


theorem finite_sphere_chart_lipschitz_on_compact {K : Set ℂ} (hK : IsCompact K) :
    ∃ L : ℝ≥0, LipschitzOnWith L ((↑) : ℂ → Sphere) K := by
  obtain ⟨R, _, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  let F : ℂ → RoundAmbient := fun z => roundSphereEquiv (z : Sphere)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F := contDiff_roundSphere_finite_chart
  have hd : Continuous (fun z => ‖fderiv ℝ F z‖₊) :=
    (hF.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).nnnorm
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hd.continuousOn
  have hLip : LipschitzOnWith L F (closedBall (0 : ℂ) R) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun _ _ => (hF.differentiable (by simp)).differentiableAt)
      (fun z hz => hL ⟨z, hz, rfl⟩) (convex_closedBall _ _)
  refine ⟨L, ?_⟩
  intro z hz w hw
  apply hLip
  · simpa only [mem_closedBall, dist_zero_right] using (hKR z hz).le
  · simpa only [mem_closedBall, dist_zero_right] using (hKR w hw).le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphereRegularLevelArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily short weighted arcs on a compact regular level, measured
in the fixed physical sphere metric. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

local instance localInst_rbc6963_4 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_small_sphere_regular_level_arcs {f : ℂ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {t : ℝ} (hreg : IsPlanarRegularValue f t)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻z in {z | f z = t}, g (z : Sphere) ∂(μH[1] : Measure ℂ)) < ∞)
    {z : ℂ} (hz : f z = t) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ V : Set Sphere, IsOpen V ∧ (z : Sphere) ∈ V ∧
      ∀x ∈ V ∩ (((↑) : ℂ → Sphere) '' {z | f z = t}),
      ∀y ∈ V ∩ (((↑) : ℂ → Sphere) '' {z | f z = t}),
        ∃ρ : RectifiablePath Sphere, ρ.val ⊥ = x ∧ ρ.val ⊤ = y ∧
          range ρ.val ⊆ ((↑) : ℂ → Sphere) '' {z | f z = t} ∧
          (∫⁻p, g p ∂pathOccupation ρ) < ε := by
  have hgc : Measurable (fun z : ℂ => g (z : Sphere)) :=
    hg.comp OnePoint.continuous_coe.measurable
  obtain ⟨γ, U, hU, hzU, hcover, hrange, hinj, hcost⟩ :=
    exists_finite_cost_regular_level_arc hf hz (hreg z hz)
      (fun z : ℂ => g (z : Sphere)) hfinite
  obtain ⟨L, hL⟩ := finite_sphere_chart_lipschitz_on_compact
    (isCompact_range γ.val.continuous)
  have hγ : ∀s, γ.val s ∈ range γ.val := fun s => mem_range_self s
  let β := lipschitzMappedPath γ ((↑) : ℂ → Sphere) hL hγ
  have hβcost : (∫⁻s, g (β.val s) ∂pathLengthMeasure β) < ∞ := by
    rw [← lintegral_pathOccupation β hg]
    apply lipschitzMappedPath_cost_lt_top γ ((↑) : ℂ → Sphere) hL hγ g hg
    rwa [← lintegral_pathOccupation γ hgc]
  obtain ⟨r, hr⟩ := hcover ⟨hzU, hz⟩
  have hβr : β.val r = (z : Sphere) := congrArg ((↑) : ℂ → Sphere) hr
  have hβinj : Injective β.val := OnePoint.coe_injective.comp hinj
  obtain ⟨W, hW, hrW, hsmall⟩ := exists_small_collar_arcs β g hg hβcost r
    (fun s h => hβinj h) hε
  refine ⟨W ∩ (((↑) : ℂ → Sphere) '' U),
    hW.inter (OnePoint.isOpen_image_coe.mpr hU),
    ⟨hβr ▸ hrW, mem_image_of_mem _ hzU⟩, ?_⟩
  intro x hx y hy
  have hmem : ∀v : Sphere, v ∈ ((↑) : ℂ → Sphere) '' U →
      v ∈ ((↑) : ℂ → Sphere) '' {z | f z = t} → v ∈ range β.val := by
    intro v hvU hv
    obtain ⟨a, ha, rfl⟩ := hv
    have haU : a ∈ U := by
      obtain ⟨b, hb, he⟩ := hvU
      exact (OnePoint.coe_injective he) ▸ hb
    obtain ⟨s, hs⟩ := hcover ⟨haU, ha⟩
    exact ⟨s, congrArg ((↑) : ℂ → Sphere) hs⟩
  obtain ⟨ρ, hρ0, hρ1, hρrange, hρcost⟩ :=
    hsmall x ⟨hx.1.1, hmem x hx.1.2 hx.2⟩ y ⟨hy.1.1, hmem y hy.1.2 hy.2⟩
  refine ⟨ρ, hρ0, hρ1, hρrange.trans ?_, hρcost⟩
  rintro p ⟨s, rfl⟩
  exact ⟨γ.val s, hrange (mem_range_self s), rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ProjectedRegularLevelArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short physical regular-level arcs descend through the actual domain
homeomorphism. Their cost is unchanged and their dust toll vanishes. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_5 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_small_projected_regular_level_arcs
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    {f : ℂ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {t : ℝ}
    (hreg : IsPlanarRegularValue f t)
    (hgood : ∀z, f z = t → (z : Sphere) ∈ d.physicalDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻z in {z | f z = t}, g (z : Sphere) ∂(μH[1] : Measure ℂ)) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    {z : ℂ} (hz : f z = t) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Set Sphere, IsOpen W ∧ π (z : Sphere) ∈ W ∧
      ∀a ∈ W ∩ (π '' (((↑) : ℂ → Sphere) '' {z | f z = t})),
      ∀b ∈ W ∩ (π '' (((↑) : ℂ → Sphere) '' {z | f z = t})),
        ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧
          range ρ.1.val ⊆ π '' (((↑) : ℂ → Sphere) '' {z | f z = t}) ∧
          physicalTollCost d g m ρ.1 < ε := by
  obtain ⟨V, hV, hzV, hsmall⟩ := exists_small_sphere_regular_level_arcs
    hf hreg g hg hfinite hz hε
  let W : Set Sphere := Subtype.val '' (d.domainEquiv '' (Subtype.val ⁻¹' V))
  have hW : IsOpen W := hU.isOpenMap_subtype_val _
    (d.domainEquiv.isOpenMap _ (hV.preimage continuous_subtype_val))
  have hzW : π (z : Sphere) ∈ W := by
    refine ⟨d.domainEquiv ⟨(z : Sphere), hgood z hz⟩, ?_, he _⟩
    exact ⟨⟨(z : Sphere), hgood z hz⟩, hzV, rfl⟩
  refine ⟨W, hW, hzW, ?_⟩
  intro a ha b hb
  obtain ⟨_, ⟨za, hza, rfl⟩, rfl⟩ := ha.2
  obtain ⟨_, ⟨zb, hzb, rfl⟩, rfl⟩ := hb.2
  have hpre : ∀w : ℂ, f w = t → π (w : Sphere) ∈ W → (w : Sphere) ∈ V := by
    intro w hw hWw
    obtain ⟨u, ⟨v, hv, rfl⟩, hval⟩ := hWw
    have heq : d.domainEquiv v = d.domainEquiv ⟨(w : Sphere), hgood w hw⟩ :=
      Subtype.ext (hval.trans (he ⟨(w : Sphere), hgood w hw⟩).symm)
    have hvw := congrArg Subtype.val (d.domainEquiv.injective heq)
    change (v : Sphere) = (w : Sphere) at hvw
    change (w : Sphere) ∈ V
    rw [← hvw]
    exact hv
  obtain ⟨α, hα0, hα1, hαrange, hαcost⟩ := hsmall (za : Sphere)
    ⟨hpre za hza ha.1, ⟨za, hza, rfl⟩⟩ (zb : Sphere)
    ⟨hpre zb hzb hb.1, ⟨zb, hzb, rfl⟩⟩
  have hα : ∀s, α.val s ∈ d.physicalDomain := by
    intro s
    obtain ⟨w, hw, heq⟩ := hαrange (mem_range_self s)
    exact heq ▸ hgood w hw
  let ρ := finiteProjectedPhysicalPath d.domainEquiv d.basePoint α hα
  have hρval (s : PathTime) : ρ.val s = π (α.val s) := he ⟨α.val s, hα s⟩
  have hzero : boundaryToll ρ.val m = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro s
    exact hm _ (projectDomainPath_mem d.domainEquiv α.val hα s)
  refine ⟨(ρ, fun _ => inactiveTag), projected_physical_path_allowed d hdisj ν N α hα,
    ?_, ?_, ?_, ?_⟩
  · exact (hρval ⊥).trans (congrArg π hα0)
  · exact (hρval ⊤).trans (congrArg π hα1)
  · rintro q ⟨s, rfl⟩
    exact ⟨α.val s, hαrange (mem_range_self s), (hρval s).symm⟩
  · change (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      boundaryToll ρ.val m < ε
    rw [hzero, add_zero]
    change (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint
      (finiteProjectedPhysicalPath d.domainEquiv d.basePoint α hα)) < ε
    rwa [dyadicPhysicalOccupation_project]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarArcs
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual weighted collars supply the local short joining arcs
required for splicing. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_6 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_small_weighted_collar_arcs
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    {B : Set Sphere} {p : Sphere}
    (D : WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hD : IsOpen D.region) {T : Set Sphere}
    (hlevel : {z | D.function z = D.level} ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' T)
    {x : Sphere} (hx : x ∈ frontier D.region) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Set Sphere, W ∈ 𝓝 x ∧
      ∀a ∈ W ∩ frontier D.region, ∀b ∈ W ∩ frontier D.region,
        ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ T ∧
          physicalTollCost d g m ρ.1 ≤ ε := by
  have hfront := D.frontier_region_subset hπ hD
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hfront hx
  obtain ⟨W, hW, hzW, hsmall⟩ := exists_small_projected_regular_level_arcs
    d hU hdisj π he ν N D.smooth D.regular
    (fun z hz => (D.level_good z hz).1) g hg D.cost_finite m hm hz hε
  refine ⟨W, hW.mem_nhds hzW, ?_⟩
  intro a ha b hb
  obtain ⟨ρ, hρ, hρ0, hρ1, hρrange, hρcost⟩ :=
    hsmall a ⟨ha.1, hfront ha.2⟩ b ⟨hb.1, hfront hb.2⟩
  refine ⟨ρ, hρ, hρ0, hρ1, hρrange.trans ?_, hρcost.le⟩
  rintro y ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact hlevel hw

namespace WeightedCollar

theorem frontier_region_subset_quotient
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar d.physicalDomain π B p g) (hD : IsOpen D.region) :
    frontier D.region ⊆ d.quotientDomain := by
  intro x hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := D.frontier_region_subset hπ hD hx
  rw [← he ⟨(z : Sphere), (D.level_good z hz).1⟩]
  exact (d.domainEquiv _).property

end WeightedCollar
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FragmentReindexing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cofinal reindexing preserves each fixed actual fragment eventually;
only the deliberately unused early triangular entries can differ. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem firstExitFragmentArray_reindex_eventually
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X) (s : ℕ → ℕ) (hs : ∀n, n ≤ s n)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) < firstExitTime (Γ n).1.val (V j))
    (hcutS : ∀n j, j ≤ n → firstExitTime (Γ (s n)).1.val (V (j+1)) < firstExitTime (Γ (s n)).1.val (V j))
    (j : ℕ) : ∀ᶠn in atTop,
    firstExitFragmentArray d hU (fun n => Γ (s n)) V hcutS n j =
      firstExitFragmentArray d hU Γ V hcut (s n) j := by
  filter_upwards [eventually_ge_atTop j] with n hn
  rw [firstExitFragmentArray_eq d hU _ _ hcutS hn,
    firstExitFragmentArray_eq d hU _ _ hcut (hn.trans (hs n))]

theorem lastEntryFragmentArray_reindex_eventually
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X) (s : ℕ → ℕ) (hs : ∀n, n ≤ s n)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hcutS : ∀n j, j ≤ n → lastEntryTime (Γ (s n)).1.val (W j) < lastEntryTime (Γ (s n)).1.val (W (j+1)))
    (j : ℕ) : ∀ᶠn in atTop,
    lastEntryFragmentArray d hU (fun n => Γ (s n)) W hcutS n j =
      lastEntryFragmentArray d hU Γ W hcut (s n) j := by
  filter_upwards [eventually_ge_atTop j] with n hn
  rw [lastEntryFragmentArray_eq d hU _ _ hcutS hn,
    lastEntryFragmentArray_eq d hU _ _ hcut (hn.trans (hs n))]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FivePieceSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact five-piece attachment used by collar splicing: initial tail,
short arc, retained middle, short arc, final tail. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_five_piece_splicing (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (a b c e f : TaggedPhysicalPath d)
    (ha : AllowedTaggedPath d ν N (a.1.val, a.2))
    (hb : AllowedTaggedPath d ν N (b.1.val, b.2))
    (hc : AllowedTaggedPath d ν N (c.1.val, c.2))
    (he : AllowedTaggedPath d ν N (e.1.val, e.2))
    (hf : AllowedTaggedPath d ν N (f.1.val, f.2))
    (hab : a.1.val ⊤ = b.1.val ⊥) (hbc : b.1.val ⊤ = c.1.val ⊥)
    (hce : c.1.val ⊤ = e.1.val ⊥) (hef : e.1.val ⊤ = f.1.val ⊥)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hma : m (a.1.val ⊤) = 0) (hmb : m (b.1.val ⊤) = 0)
    (hmc : m (c.1.val ⊤) = 0) (hme : m (e.1.val ⊤) = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = a.1.val ⊥ ∧ ρ.val ⊤ = f.1.val ⊤ ∧
      interiorPhysicalTollCost d g m ρ = interiorPhysicalTollCost d g m a.1 +
        interiorPhysicalTollCost d g m b.1 + interiorPhysicalTollCost d g m c.1 +
        interiorPhysicalTollCost d g m e.1 + interiorPhysicalTollCost d g m f.1 := by
  obtain ⟨ab, tab, habA, hab0, hab1, habcost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N a b ha hb hab g hg m hma hpoint
  obtain ⟨abc, tabc, habcA, habc0, habc1, habccost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N (ab, tab) c habA hc
      (hab1.trans hbc) g hg m (by rw [hab1]; exact hmb) hpoint
  obtain ⟨abce, tabce, habceA, habce0, habce1, habcecost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N (abc, tabc) e habcA he
      (habc1.trans hce) g hg m (by rw [habc1]; exact hmc) hpoint
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hρcost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N (abce, tabce) f habceA hf
      (habce1.trans hef) g hg m (by rw [habce1]; exact hme) hpoint
  refine ⟨ρ, θ, hρ, hρ0.trans (habce0.trans (habc0.trans hab0)), hρ1, ?_⟩
  rw [hρcost, habcecost, habccost, habcost]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstExitFragmentProperties
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frontier endpoints and vanishing endpoint tolls for actual first-exit
fragments. These discharge the geometric premises of fragment splicing. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] in
theorem firstExitFragmentArray_frontiers
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    {n j : ℕ} (hj : j ≤ n) :
    (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊥ ∈ frontier (V (j+1)) ∧
    (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊤ ∈ frontier (V j) := by
  rw [(firstExitFragmentArray_endpoints d hU Γ V hcut hj).1,
    (firstExitFragmentArray_endpoints d hU Γ V hcut hj).2]
  constructor
  · exact firstExit_frontier (Γ n).1.val (hV (j+1))
      (hanti (Nat.add_le_add_right hj 1) (hstart n))
      (fun h => hend n (hanti (Nat.zero_le (j+1)) h))
  · exact firstExit_frontier (Γ n).1.val (hV j)
      (hanti (hj.trans (Nat.le_succ n)) (hstart n))
      (fun h => hend n (hanti (Nat.zero_le j) h))

omit [MeasurableSpace X] in
theorem firstExit_toll_zero
    (d : PathCodeData X Y) (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (m : X → ℝ≥0∞) (hm : ∀j x, x ∈ frontier (V j) → m x = 0)
    (n j : ℕ) (hj : j ≤ n+1) :
    m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0 := by
  apply hm j
  exact firstExit_frontier (Γ n).1.val (hV j) (hanti hj (hstart n))
    (fun h => hend n (hanti (Nat.zero_le j) h))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_LinkedFragmentSelection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous selection of actual fragments and joining arcs. Both ends
of each chosen fragment lie in the neighborhoods needed by its two neighbors. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_linked_fragment_selection
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : ℕ → ℕ → TaggedPhysicalPath d) (x : ℕ → X) (C T : ℕ → Set X)
    (hΓ : ∀n j, j ≤ n → AllowedTaggedPath d ν N ((γ n j).1.val, (γ n j).2))
    (hstart : ∀n j, j ≤ n → (γ n j).1.val ⊥ ∈ C (j+1))
    (hstop : ∀n j, j ≤ n → (γ n j).1.val ⊤ ∈ C j)
    (hstartlim : ∀j, Tendsto (fun n => (γ n j).1.val ⊥) atTop (𝓝 (x (j+1))))
    (hstoplim : ∀j, Tendsto (fun n => (γ n j).1.val ⊤) atTop (𝓝 (x j)))
    (c ε δ : ℕ → ℝ≥0∞) (A E : ℝ≥0∞) (hA : A < ∞)
    (hcostlim : ∀j, Tendsto (fun n => physicalTollCost d g m (γ n j).1) atTop (𝓝 (c j)))
    (hc : (∑'j, c j) ≤ A) (hε : ∀j, 0 < ε j) (hεsum : (∑'j, ε j) ≤ E)
    (hbridge : ∀j, ∃ U : Set X, U ∈ 𝓝 (x (j+1)) ∧
      ∀a ∈ U ∩ C (j+1), ∀b ∈ U ∩ C (j+1),
        ∃ ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ T j ∧
          physicalTollCost d g m ρ.1 ≤ δ j) :
    ∃ (M : ℕ → ℕ) (b : ℕ → TaggedPhysicalPath d),
      (∀j, j ≤ M j) ∧
      (∀j, AllowedTaggedPath d ν N ((γ (M j) j).1.val, (γ (M j) j).2)) ∧
      (∀j, AllowedTaggedPath d ν N ((b j).1.val, (b j).2)) ∧
      (∀j, (b j).1.val ⊥ = (γ (M (j+1)) (j+1)).1.val ⊤) ∧
      (∀j, (b j).1.val ⊤ = (γ (M j) j).1.val ⊥) ∧
      (∀j, range (b j).1.val ⊆ T j) ∧
      ((∑'j, physicalTollCost d g m (γ (M j) j).1) ≤ A + E) ∧
      ((∑'j, physicalTollCost d g m (b j).1) ≤ ∑'j, δ j) := by
  classical
  choose U hU hlink using hbridge
  let V : ℕ → Set X := fun j => match j with
    | 0 => univ
    | j+1 => U j
  have hV (j : ℕ) : V j ∈ 𝓝 (x j) := by
    cases j with
    | zero => exact univ_mem
    | succ j => exact hU j
  have hfinite (j : ℕ) : c j ≠ ∞ := ne_top_of_le_ne_top hA.ne
    ((ENNReal.le_tsum j).trans hc)
  obtain ⟨M, hM⟩ := exists_close_fragment_selection
    (fun n j => (γ n j).1.val ⊥) (fun n j => (γ n j).1.val ⊤)
    (fun n j => physicalTollCost d g m (γ n j).1)
    (fun j => x (j+1)) x c ε hstartlim hstoplim hcostlim hfinite
    (fun j => (hε j).ne') U V hU hV
  have hlinks (j : ℕ) : ∃ ρ : TaggedPhysicalPath d,
      AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ = (γ (M (j+1)) (j+1)).1.val ⊤ ∧
      ρ.1.val ⊤ = (γ (M j) j).1.val ⊥ ∧ range ρ.1.val ⊆ T j ∧
      physicalTollCost d g m ρ.1 ≤ δ j := by
    apply hlink j _ ⟨(hM (j+1)).2.2.1, hstop _ _ (hM (j+1)).1⟩
      _ ⟨(hM j).2.1, hstart _ _ (hM j).1⟩
  choose b hb using hlinks
  refine ⟨M, b, fun j => (hM j).1, fun j => hΓ _ _ (hM j).1,
    fun j => (hb j).1, fun j => (hb j).2.1, fun j => (hb j).2.2.1,
    fun j => (hb j).2.2.2.1, ?_, ?_⟩
  · exact selected_fragment_total_cost (fun n j => physicalTollCost d g m (γ n j).1)
      M c ε A E (fun j => (hM j).2.2.2) hc hεsum
  · exact ENNReal.tsum_le_tsum (fun j => (hb j).2.2.2.2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CollarSplicingFromFragments
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-ended collar assembled from convergent actual fragments and
short joining arcs. This is the constructive gluing step of Section 3. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_collar_path_from_fragment_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (p : X) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (γ : ℕ → ℕ → TaggedPhysicalPath d) (x : ℕ → X) (C T : ℕ → Set X)
    (hΓ : ∀n j, j ≤ n → AllowedTaggedPath d ν N ((γ n j).1.val, (γ n j).2))
    (hstart : ∀n j, j ≤ n → (γ n j).1.val ⊥ ∈ C (j+1))
    (hstop : ∀n j, j ≤ n → (γ n j).1.val ⊤ ∈ C j)
    (hstartlim : ∀j, Tendsto (fun n => (γ n j).1.val ⊥) atTop (𝓝 (x (j+1))))
    (hstoplim : ∀j, Tendsto (fun n => (γ n j).1.val ⊤) atTop (𝓝 (x j)))
    (c ε δ : ℕ → ℝ≥0∞) (A E F : ℝ≥0∞)
    (hA : A < ∞) (hE : E < ∞) (hF : F < ∞)
    (hcostlim : ∀j, Tendsto (fun n => physicalTollCost d g m (γ n j).1) atTop (𝓝 (c j)))
    (hc : (∑'j, c j) ≤ A) (hε : ∀j, 0 < ε j) (hεsum : (∑'j, ε j) ≤ E)
    (hδsum : (∑'j, δ j) ≤ F)
    (hbridge : ∀j, ∃ U : Set X, U ∈ 𝓝 (x (j+1)) ∧
      ∀a ∈ U ∩ C (j+1), ∀b ∈ U ∩ C (j+1),
        ∃ ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ T j ∧
          physicalTollCost d g m ρ.1 ≤ δ j)
    (hm : ∀n j, j ≤ n → m ((γ n j).1.val ⊥) = 0 ∧ m ((γ n j).1.val ⊤) = 0)
    (hγtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀n ≥ j, ∀s, (γ n j).1.val s ∈ V)
    (hTtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, T j ⊆ V)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀y ∈ d.physicalDomain, w ≤ g y)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (k : ℕ) (η : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (η.val, θ) ∧ η.val ⊥ = p ∧ η.val ⊤ = (γ k 0).1.val ⊤ ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint η) +
        timeToll η.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + E + F := by
  obtain ⟨M, b, hM, ha, hb, hleft, hright, hbT, hacost, hbcost⟩ :=
    exists_linked_fragment_selection d ν N g m γ x C T hΓ hstart hstop hstartlim hstoplim
      c ε δ A E hA hcostlim hc hε hεsum hbridge
  let a : ℕ → TaggedPhysicalPath d := fun j => γ (M j) j
  have hatail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀s, (a j).1.val s ∈ V := by
    intro V hV
    obtain ⟨k, hk⟩ := hγtail V hV
    exact ⟨k, fun j hj s => hk j hj (M j) (hM j) s⟩
  have hbtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀s, (b j).1.val s ∈ V := by
    intro V hV
    obtain ⟨k, hk⟩ := hTtail V hV
    exact ⟨k, fun j hj s => hk j hj (hbT j (mem_range_self s))⟩
  have hb0 (j : ℕ) : m ((b j).1.val ⊥) = 0 := by
    rw [hleft j]
    exact (hm _ _ (hM (j+1))).2
  have hb1 (j : ℕ) : m ((b j).1.val ⊤) = 0 := by
    rw [hright j]
    exact (hm _ _ (hM j)).1
  obtain ⟨η, θ, hη, hη0, hη1, hcost⟩ := exists_allowed_interleaved_collar d hU hG ν N
    p a b ha hb hleft hright hatail hbtail g hg m w hw hpos
    (fun j => (hm _ _ (hM j)).1) (fun j => (hm _ _ (hM j)).2) hb0 hb1
    (A+E) F (ENNReal.add_lt_top.mpr ⟨hA, hE⟩) hF hacost (hbcost.trans hδsum) hpoint
  exact ⟨M 0, η, θ, hη, hη0, hη1, hcost⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LocalizedCollarSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The collar endpoint may be selected in any prescribed neighborhood of
its limiting outer hit point, for attaching a common middle fragment. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_collar_path_from_fragment_limits_near
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (p : X) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (γ : ℕ → ℕ → TaggedPhysicalPath d) (x : ℕ → X) (C T : ℕ → Set X)
    (hΓ : ∀n j, j ≤ n → AllowedTaggedPath d ν N ((γ n j).1.val, (γ n j).2))
    (hstart : ∀n j, j ≤ n → (γ n j).1.val ⊥ ∈ C (j+1))
    (hstop : ∀n j, j ≤ n → (γ n j).1.val ⊤ ∈ C j)
    (hstartlim : ∀j, Tendsto (fun n => (γ n j).1.val ⊥) atTop (𝓝 (x (j+1))))
    (hstoplim : ∀j, Tendsto (fun n => (γ n j).1.val ⊤) atTop (𝓝 (x j)))
    (c ε δ : ℕ → ℝ≥0∞) (A E F : ℝ≥0∞)
    (hA : A < ∞) (hE : E < ∞) (hF : F < ∞)
    (hcostlim : ∀j, Tendsto (fun n => physicalTollCost d g m (γ n j).1) atTop (𝓝 (c j)))
    (hc : (∑'j, c j) ≤ A) (hε : ∀j, 0 < ε j) (hεsum : (∑'j, ε j) ≤ E)
    (hδsum : (∑'j, δ j) ≤ F)
    (hbridge : ∀j, ∃ U : Set X, U ∈ 𝓝 (x (j+1)) ∧
      ∀a ∈ U ∩ C (j+1), ∀b ∈ U ∩ C (j+1),
        ∃ ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ T j ∧
          physicalTollCost d g m ρ.1 ≤ δ j)
    (hm : ∀n j, j ≤ n → m ((γ n j).1.val ⊥) = 0 ∧ m ((γ n j).1.val ⊤) = 0)
    (hγtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀n ≥ j, ∀s, (γ n j).1.val s ∈ V)
    (hTtail : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, T j ⊆ V)
    (O : Set X) (hO : O ∈ 𝓝 (x 0))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀y ∈ d.physicalDomain, w ≤ g y)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (k : ℕ) (η : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (η.val, θ) ∧ η.val ⊥ = p ∧ η.val ⊤ = (γ k 0).1.val ⊤ ∧ η.val ⊤ ∈ O ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint η) +
        timeToll η.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + E + F := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((hstoplim 0).eventually hO)
  let σ : ℕ → ℕ := fun n => n + K
  have hσ : Tendsto σ atTop atTop := tendsto_add_atTop_nat K
  have hle (n : ℕ) : n ≤ σ n := Nat.le_add_right n K
  obtain ⟨k, η, θ, hη, hη0, hη1, hcost⟩ := exists_collar_path_from_fragment_limits
    d hU hG ν N p g hg m (fun n j => γ (σ n) j) x C T
    (fun n j hj => hΓ _ _ (hj.trans (hle n)))
    (fun n j hj => hstart _ _ (hj.trans (hle n)))
    (fun n j hj => hstop _ _ (hj.trans (hle n)))
    (fun j => (hstartlim j).comp hσ) (fun j => (hstoplim j).comp hσ)
    c ε δ A E F hA hE hF (fun j => (hcostlim j).comp hσ) hc hε hεsum hδsum hbridge
    (fun n j hj => hm _ _ (hj.trans (hle n)))
    (by
      intro V hV
      obtain ⟨l, hl⟩ := hγtail V hV
      exact ⟨l, fun j hj n hn s => hl j hj (σ n) (hn.trans (hle n)) s⟩)
    hTtail w hw hpos hpoint
  exact ⟨σ k, η, θ, hη, hη0, hη1, hη1 ▸ hK (σ k) (Nat.le_add_left K k), hcost⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FinalCollarPrescribedLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final collar, oriented from the limiting endpoint inward, uses the
prescribed common limits of actual last-entry fragments. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_final_collar_path_of_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p : X) (V : ℕ → Set X) (hV : ∀j, IsOpen (V j))
    (hnest : ∀j, closure (V (j+1)) ⊆ V j)
    (hshrink : ∀W ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (V j) ⊆ W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ V 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ V (n+1))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀j x, x ∈ frontier (V j) → m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (x : ℕ → X) (c : ℕ → ℝ≥0∞)
    (hhitlim : ∀j, Tendsto (fun n => (Γ n).1.val (lastEntryTime (Γ n).1.val (V j)))
      atTop (𝓝 (x j)))
    (hclim : ∀hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (V j) <
        lastEntryTime (Γ n).1.val (V (j+1)),
      ∀j, Tendsto (fun n => physicalTollCost d g m
        (lastEntryFragmentArray d hU Γ V hcut n j).1) atTop (𝓝 (c j)))
    (hcsum : (∑'j, c j) ≤ A) (O : Set X) (hO : O ∈ 𝓝 (x 0))
    (hsmall : ∀j z, z ∈ frontier (V (j+1)) → ∀ε : ℝ≥0∞, 0 < ε →
      ∃ W : Set X, W ∈ 𝓝 z ∧
        ∀a ∈ W ∩ frontier (V (j+1)), ∀b ∈ W ∩ frontier (V (j+1)),
          ∃ ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
            ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ closure (V j) ∧
            physicalTollCost d g m ρ.1 ≤ ε)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀y ∈ d.physicalDomain, w ≤ g y)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {η : ℝ} (hη : 0 < η) :
    ∃ (k : ℕ) (α : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (α.val, θ) ∧ α.val ⊥ = p ∧
      α.val ⊤ = (Γ k).1.val (lastEntryTime (Γ k).1.val (V 0)) ∧ α.val ⊤ ∈ O ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint α) +
        timeToll α.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + ENNReal.ofReal η := by
  have hanti : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (V j) <
      lastEntryTime (Γ n).1.val (V (j+1)) := fun n j hj =>
    lastEntryFragments_strict (Γ n).1.val V hV hnest (hstart n) (hend n) hj
  let γ : ℕ → ℕ → TaggedPhysicalPath d := fun n j =>
    reversedTaggedPhysicalPath d (lastEntryFragmentArray d hU Γ V hcut n j)
  have hzero {n j : ℕ} (hj : j ≤ n) : (γ n j).1.val ⊥ =
      (Γ n).1.val (lastEntryTime (Γ n).1.val (V (j+1))) := by
    change reversedPath (lastEntryFragmentArray d hU Γ V hcut n j).1.val ⊥ = _
    rw [reversedPath_zero]
    exact (lastEntryFragmentArray_endpoints d hU Γ V hcut hj).2
  have hone {n j : ℕ} (hj : j ≤ n) : (γ n j).1.val ⊤ =
      (Γ n).1.val (lastEntryTime (Γ n).1.val (V j)) := by
    change reversedPath (lastEntryFragmentArray d hU Γ V hcut n j).1.val ⊤ = _
    rw [reversedPath_one]
    exact (lastEntryFragmentArray_endpoints d hU Γ V hcut hj).1
  have hfront {n j : ℕ} (hj : j ≤ n) : (γ n j).1.val ⊥ ∈ frontier (V (j+1)) ∧
      (γ n j).1.val ⊤ ∈ frontier (V j) := by
    change reversedPath (lastEntryFragmentArray d hU Γ V hcut n j).1.val ⊥ ∈ _ ∧
      reversedPath (lastEntryFragmentArray d hU Γ V hcut n j).1.val ⊤ ∈ _
    rw [reversedPath_zero, reversedPath_one]
    exact (lastEntryFragmentArray_frontiers d hU Γ V hcut hV hanti hstart hend hj).symm
  have hx (j : ℕ) : x j ∈ frontier (V j) := by
    apply isClosed_frontier.mem_of_tendsto (hhitlim j)
    filter_upwards [eventually_ge_atTop j] with n hn
    exact lastEntry_frontier (Γ n).1.val (hV j)
      (fun h => hstart n (hanti (Nat.zero_le j) h))
      (hanti (hn.trans (Nat.le_succ _)) (hend n))
  have hstartlim (j : ℕ) : Tendsto (fun n => (γ n j).1.val ⊥) atTop (𝓝 (x (j+1))) := by
    apply (hhitlim (j+1)).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    exact (hzero hn).symm
  have hstoplim (j : ℕ) : Tendsto (fun n => (γ n j).1.val ⊤) atTop (𝓝 (x j)) := by
    apply (hhitlim j).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    exact (hone hn).symm
  have hcostlim (j : ℕ) : Tendsto (fun n => physicalTollCost d g m (γ n j).1) atTop (𝓝 (c j)) := by
    convert hclim hcut j using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact physicalTollCost_reversed d g m (lastEntryFragmentArray d hU Γ V hcut n j).1
  have hallowed (n j : ℕ) (hj : j ≤ n) : AllowedTaggedPath d ν N ((γ n j).1.val, (γ n j).2) := by
    change AllowedTaggedPath d ν N (reversedTaggedPath
      ((lastEntryFragmentArray d hU Γ V hcut n j).1.val,
        (lastEntryFragmentArray d hU Γ V hcut n j).2))
    exact allowedTaggedPath_reversed d ν N
      ((lastEntryFragmentArray d hU Γ V hcut n j).1.val,
        (lastEntryFragmentArray d hU Γ V hcut n j).2)
      (lastEntryFragmentArray_allowed d hU Γ V hcut ν N hΓ hpoint hj) hpoint
  obtain ⟨weights, hweights, hsum⟩ := exists_positive_summable_weights ℕ
  let e : ℝ≥0∞ := ENNReal.ofReal (η/2)
  let ε : ℕ → ℝ≥0∞ := fun j => e * weights j
  have hepos : 0 < e := ENNReal.ofReal_pos.mpr (by linarith)
  have hefinite : e < ∞ := ENNReal.ofReal_lt_top
  have hεpos (j : ℕ) : 0 < ε j := ENNReal.mul_pos hepos.ne' (hweights j).ne'
  have hεsum : (∑'j, ε j) ≤ e := by
    change (∑'j, e * weights j) ≤ e
    rw [ENNReal.tsum_mul_left]
    simpa only [mul_one] using mul_le_mul' (le_refl e) hsum
  have htail : ∀W ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀n ≥ j, ∀t, (γ n j).1.val t ∈ W := by
    intro W hW
    obtain ⟨k, hk⟩ := hshrink W hW
    refine ⟨k, fun j hj n hn t => hk j hj ?_⟩
    exact lastEntryFragmentArray_support d hU Γ V hcut hV hanti hstart hend
      hn (mem_range_self (unitInterval.symm t))
  obtain ⟨k, α, θ, hα, hα0, hα1, hαO, hbound⟩ := exists_collar_path_from_fragment_limits_near
    d hU hG ν N p g hg m γ x (fun j => frontier (V j)) (fun j => closure (V j))
    hallowed
    (fun _ _ hj => (hfront hj).1) (fun _ _ hj => (hfront hj).2)
    hstartlim hstoplim c ε ε A e e hA hefinite hefinite hcostlim hcsum hεpos hεsum hεsum
    (fun j => hsmall j (x (j+1)) (hx (j+1)) (ε j) (hεpos j))
    (fun _ j hj => ⟨hm (j+1) _ (hfront hj).1, hm j _ (hfront hj).2⟩)
    htail hshrink O hO w hw hpos hpoint
  refine ⟨k, α, θ, hα, hα0, ?_, hαO, ?_⟩
  · exact hα1.trans (hone (Nat.zero_le k))
  · have he : e + e = ENNReal.ofReal η := by
      dsimp [e]
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ η/2) (by linarith : 0 ≤ η/2)]
      congr 1
      ring
    simpa only [add_assoc, he] using hbound

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_InitialCollarPrescribedLimits
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial collar splicing on a prescribed common subsequence and budget.
This retains the shared budget with the final tail and middle fragment. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_initial_collar_path_of_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p : X) (V : ℕ → Set X) (hV : ∀j, IsOpen (V j))
    (hnest : ∀j, closure (V (j+1)) ⊆ V j)
    (hshrink : ∀W ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (V j) ⊆ W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀j x, x ∈ frontier (V j) → m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (x : ℕ → X) (c : ℕ → ℝ≥0∞)
    (hhitlim : ∀j, Tendsto (fun n => (Γ n).1.val (firstExitTime (Γ n).1.val (V j)))
      atTop (𝓝 (x j)))
    (hclim : ∀hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
        firstExitTime (Γ n).1.val (V j),
      ∀j, Tendsto (fun n => physicalTollCost d g m
        (firstExitFragmentArray d hU Γ V hcut n j).1) atTop (𝓝 (c j)))
    (hcsum : (∑'j, c j) ≤ A) (O : Set X) (hO : O ∈ 𝓝 (x 0))
    (hsmall : ∀j z, z ∈ frontier (V (j+1)) → ∀ε : ℝ≥0∞, 0 < ε →
      ∃ W : Set X, W ∈ 𝓝 z ∧
        ∀a ∈ W ∩ frontier (V (j+1)), ∀b ∈ W ∩ frontier (V (j+1)),
          ∃ ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
            ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ closure (V j) ∧
            physicalTollCost d g m ρ.1 ≤ ε)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀y ∈ d.physicalDomain, w ≤ g y)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {η : ℝ} (hη : 0 < η) :
    ∃ (k : ℕ) (α : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (α.val, θ) ∧ α.val ⊥ = p ∧
      α.val ⊤ = (Γ k).1.val (firstExitTime (Γ k).1.val (V 0)) ∧ α.val ⊤ ∈ O ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint α) +
        timeToll α.val (Ioo (⊥ : PathTime) ⊤) m ≤ A + ENNReal.ofReal η := by
  have hanti : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j) := fun n j hj =>
    firstExitFragments_strict (Γ n).1.val V hV hnest (hstart n) (hend n) hj
  let γ : ℕ → ℕ → TaggedPhysicalPath d := fun n j => firstExitFragmentArray d hU Γ V hcut n j
  have hfront {n j : ℕ} (hj : j ≤ n) : (γ n j).1.val ⊥ ∈ frontier (V (j+1)) ∧
      (γ n j).1.val ⊤ ∈ frontier (V j) :=
    firstExitFragmentArray_frontiers d hU Γ V hcut hV hanti hstart hend hj
  have hx (j : ℕ) : x j ∈ frontier (V j) := by
    apply isClosed_frontier.mem_of_tendsto (hhitlim j)
    filter_upwards [eventually_ge_atTop j] with n hn
    exact firstExit_frontier (Γ n).1.val (hV j)
      (hanti (hn.trans (Nat.le_succ _)) (hstart n))
      (fun h => hend n (hanti (Nat.zero_le j) h))
  have hstartlim (j : ℕ) : Tendsto (fun n => (γ n j).1.val ⊥) atTop (𝓝 (x (j+1))) := by
    apply (hhitlim (j+1)).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    exact (firstExitFragmentArray_endpoints d hU Γ V hcut hn).1.symm
  have hstoplim (j : ℕ) : Tendsto (fun n => (γ n j).1.val ⊤) atTop (𝓝 (x j)) := by
    apply (hhitlim j).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    exact (firstExitFragmentArray_endpoints d hU Γ V hcut hn).2.symm
  obtain ⟨weights, hweights, hsum⟩ := exists_positive_summable_weights ℕ
  let e : ℝ≥0∞ := ENNReal.ofReal (η/2)
  let ε : ℕ → ℝ≥0∞ := fun j => e * weights j
  have hepos : 0 < e := ENNReal.ofReal_pos.mpr (by linarith)
  have hefinite : e < ∞ := ENNReal.ofReal_lt_top
  have hεpos (j : ℕ) : 0 < ε j := ENNReal.mul_pos hepos.ne' (hweights j).ne'
  have hεsum : (∑'j, ε j) ≤ e := by
    change (∑'j, e * weights j) ≤ e
    rw [ENNReal.tsum_mul_left]
    simpa only [mul_one] using mul_le_mul' (le_refl e) hsum
  have htail : ∀W ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, ∀n ≥ j, ∀t, (γ n j).1.val t ∈ W := by
    intro W hW
    obtain ⟨k, hk⟩ := hshrink W hW
    refine ⟨k, fun j hj n hn t => hk j hj ?_⟩
    exact firstExitFragmentArray_support d hU Γ V hcut hV hanti hstart hend
      hn (mem_range_self t)
  obtain ⟨k, α, θ, hα, hα0, hα1, hαO, hbound⟩ := exists_collar_path_from_fragment_limits_near
    d hU hG ν N p g hg m γ x (fun j => frontier (V j)) (fun j => closure (V j))
    (fun n j hj => firstExitFragmentArray_allowed d hU Γ V hcut ν N hΓ hpoint hj)
    (fun _ _ hj => (hfront hj).1) (fun _ _ hj => (hfront hj).2)
    hstartlim hstoplim c ε ε A e e hA hefinite hefinite (hclim hcut) hcsum hεpos hεsum hεsum
    (fun j => hsmall j (x (j+1)) (hx (j+1)) (ε j) (hεpos j))
    (fun _ j hj => ⟨hm (j+1) _ (hfront hj).1, hm j _ (hfront hj).2⟩)
    htail hshrink O hO w hw hpos hpoint
  refine ⟨k, α, θ, hα, hα0, ?_, hαO, ?_⟩
  · exact hα1.trans (firstExitFragmentArray_endpoints d hU Γ V hcut (Nat.zero_le k)).2
  · have he : e + e = ENNReal.ofReal η := by
      dsimp [e]
      rw [← ENNReal.ofReal_add (by linarith : 0 ≤ η/2) (by linarith : 0 ≤ η/2)]
      congr 1
      ring
    simpa only [add_assoc, he] using hbound

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TwoEndedCollarSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the two actual collar tails and a selected actual middle
fragment using the common limiting budget. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_twoEnded_collar_splicing_of_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : X) (V W : ℕ → Set X) (hV : ∀j, IsOpen (V j)) (hW : ∀j, IsOpen (W j))
    (hnestV : ∀j, closure (V (j+1)) ⊆ V j) (hnestW : ∀j, closure (W (j+1)) ⊆ W j)
    (hshrinkV : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (V j) ⊆ O)
    (hshrinkW : ∀O ∈ 𝓝 q, ∃k : ℕ, ∀j ≥ k, closure (W j) ⊆ O)
    (hstartV : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hendV : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (hstartW : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hendW : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (hmid : ∀n, firstExitTime (Γ n).1.val (V 0) < lastEntryTime (Γ n).1.val (W 0))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmV : ∀j z, z ∈ frontier (V j) → m z = 0)
    (hmW : ∀j z, z ∈ frontier (W j) → m z = 0)
    (x y : ℕ → X) (c e : ℕ → ℝ≥0∞) (M A : ℝ≥0∞) (hA : A < ∞)
    (hx : ∀j, Tendsto (fun n => (Γ n).1.val (firstExitTime (Γ n).1.val (V j))) atTop (𝓝 (x j)))
    (hy : ∀j, Tendsto (fun n => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) atTop (𝓝 (y j)))
    (hc : ∀hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) < firstExitTime (Γ n).1.val (V j),
      ∀j, Tendsto (fun n => physicalTollCost d g m (firstExitFragmentArray d hU Γ V hcut n j).1) atTop (𝓝 (c j)))
    (he : ∀hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)),
      ∀j, Tendsto (fun n => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1) atTop (𝓝 (e j)))
    (hM : Tendsto (fun n => physicalTollCost d g m (restrictTaggedPhysicalPath d hU (Γ n) (hmid n)).1) atTop (𝓝 M))
    (hbudget : M + (∑'j, c j) + (∑'j, e j) ≤ A)
    (hsmallV : ∀j, HasShortCollarJoining d ν N g m (frontier (V (j+1))) (closure (V j)))
    (hsmallW : ∀j, HasShortCollarJoining d ν N g m (frontier (W (j+1))) (closure (W j)))
    (houterV : HasShortCollarJoining d ν N g m (frontier (V 0)) univ)
    (houterW : HasShortCollarJoining d ν N g m (frontier (W 0)) univ)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η := by
  have haV : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnestV j))
  have haW : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnestW j))
  have hfrontV (n : ℕ) : (Γ n).1.val (firstExitTime (Γ n).1.val (V 0)) ∈ frontier (V 0) :=
    firstExit_frontier (Γ n).1.val (hV 0) (haV (Nat.zero_le _) (hstartV n)) (hendV n)
  have hfrontW (n : ℕ) : (Γ n).1.val (lastEntryTime (Γ n).1.val (W 0)) ∈ frontier (W 0) :=
    lastEntry_frontier (Γ n).1.val (hW 0) (hstartW n) (haW (Nat.zero_le _) (hendW n))
  have hx0 : x 0 ∈ frontier (V 0) :=
    isClosed_frontier.mem_of_tendsto (hx 0) (Eventually.of_forall hfrontV)
  have hy0 : y 0 ∈ frontier (W 0) :=
    isClosed_frontier.mem_of_tendsto (hy 0) (Eventually.of_forall hfrontW)
  have hfinite := hbudget.trans_lt hA
  have hMfin : M < ∞ := (ENNReal.add_lt_top.mp (ENNReal.add_lt_top.mp hfinite).1).1
  have hCfin : (∑'j, c j) < ∞ := (ENNReal.add_lt_top.mp (ENNReal.add_lt_top.mp hfinite).1).2
  have hEfin : (∑'j, e j) < ∞ := (ENNReal.add_lt_top.mp hfinite).2
  let ε : ℝ≥0∞ := ENNReal.ofReal (η/5)
  have hδ : 0 < η/5 := by positivity
  have hε : 0 < ε := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨O, hO, hjoinV⟩ := houterV (x 0) hx0 ε hε
  obtain ⟨P, hP, hjoinW⟩ := houterW (y 0) hy0 ε hε
  obtain ⟨i, α, θα, hα, hα0, hα1, hαO, hαcost⟩ := exists_initial_collar_path_of_limits
    d hU hG ν N Γ hΓ p V hV hnestV hshrinkV hstartV hendV g hg m hmV
    (∑'j, c j) hCfin x c hx hc le_rfl O hO hsmallV w hw hpos hpoint hδ
  obtain ⟨j, β, θβ, hβ, hβ0, hβ1, hβP, hβcost⟩ := exists_final_collar_path_of_limits
    d hU hG ν N Γ hΓ q W hW hnestW hshrinkW hstartW hendW g hg m hmW
    (∑'j, e j) hEfin y e hy he le_rfl P hP hsmallW w hw hpos hpoint hδ
  have hMc : ∀ᶠn in atTop, physicalTollCost d g m (restrictTaggedPhysicalPath d hU (Γ n) (hmid n)).1 < M + ε :=
    (tendsto_order.mp hM).2 _ (ENNReal.lt_add_right hMfin.ne hε.ne')
  obtain ⟨k, hkO, hkP, hkcost⟩ :=
    (((hx 0).eventually hO).and (((hy 0).eventually hP).and hMc)).exists
  let μ := restrictTaggedPhysicalPath d hU (Γ k) (hmid k)
  have hμ : AllowedTaggedPath d ν N (μ.1.val, μ.2) :=
    restrictTaggedPhysicalPath_allowed d hU ν N (Γ k) (hΓ k) hpoint (hmid k)
  have hμ0 : μ.1.val ⊥ = (Γ k).1.val (firstExitTime (Γ k).1.val (V 0)) :=
    restrictTaggedPhysicalPath_zero d hU (Γ k) (hmid k)
  have hμ1 : μ.1.val ⊤ = (Γ k).1.val (lastEntryTime (Γ k).1.val (W 0)) :=
    restrictTaggedPhysicalPath_one d hU (Γ k) (hmid k)
  obtain ⟨a, ha, ha0, ha1, _, hacost⟩ := hjoinV (α.val ⊤)
    ⟨hαO, hα1.symm ▸ hfrontV i⟩ (μ.1.val ⊥) ⟨hμ0.symm ▸ hkO, hμ0.symm ▸ hfrontV k⟩
  obtain ⟨b, hb, hb0, hb1, _, hbcost⟩ := hjoinW (μ.1.val ⊤)
    ⟨hμ1.symm ▸ hkP, hμ1.symm ▸ hfrontW k⟩ (β.val ⊤) ⟨hβP, hβ1.symm ▸ hfrontW j⟩
  obtain ⟨βr, θr, hβr, hβr0, hβr1, hβrcost⟩ :=
    exists_allowed_reversed_interior_cost d ν N (β, θβ) hβ g m hpoint
  have hαm : m (α.val ⊤) = 0 := by rw [hα1]; exact hmV 0 _ (hfrontV i)
  have hμm0 : m (μ.1.val ⊥) = 0 := by rw [hμ0]; exact hmV 0 _ (hfrontV k)
  have hμm1 : m (μ.1.val ⊤) = 0 := by rw [hμ1]; exact hmW 0 _ (hfrontW k)
  have hβm : m (β.val ⊤) = 0 := by rw [hβ1]; exact hmW 0 _ (hfrontW j)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hρcost⟩ := exists_allowed_five_piece_splicing d hU ν N
    (α, θα) a μ b (βr, θr) hα ha hμ hb hβr ha0.symm ha1 hb0.symm
    (hb1.trans hβr0.symm) g hg m hαm (by rw [ha1]; exact hμm0) hμm1
    (by rw [hb1]; exact hβm) hpoint
  refine ⟨ρ, θ, hρ, hρ0.trans hα0, hρ1.trans (hβr1.trans hβ0), ?_⟩
  have hεsum : ε + ε + ε + ε + ε = ENNReal.ofReal η := by
    dsimp [ε]
    rw [← ENNReal.ofReal_add hδ.le hδ.le,
      ← ENNReal.ofReal_add (by positivity) hδ.le,
      ← ENNReal.ofReal_add (by positivity) hδ.le,
      ← ENNReal.ofReal_add (by positivity) hδ.le]
    congr 1
    ring
  calc
    interiorPhysicalTollCost d g m ρ = _ := hρcost
    _ ≤ (((∑'j, c j) + ε) + ε + (M + ε) + ε + ((∑'j, e j) + ε)) := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact add_le_add hαcost ((interiorPhysicalTollCost_le_full d g m a.1).trans hacost)
          · exact (interiorPhysicalTollCost_le_full d g m μ.1).trans hkcost.le
        · exact (interiorPhysicalTollCost_le_full d g m b.1).trans hbcost
      · rw [hβrcost]
        exact hβcost
    _ = (M + (∑'j, c j) + (∑'j, e j)) + (ε + ε + ε + ε + ε) := by ac_rfl
    _ ≤ A + ENNReal.ofReal η := by rw [hεsum]; exact add_le_add hbudget le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_OneEndedCollarSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attach one actual retained prefix to the final collar tail, keeping
its original initial point and using the joint prefix/tail budget. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_oneEnded_collar_splicing_of_limits
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set X) (hF : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : X) (W : ℕ → Set X) (hW : ∀j, IsOpen (W j))
    (hnest : ∀j, closure (W (j+1)) ⊆ W j)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (W j) ⊆ O)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (hprefix : ∀n, ⊥ < lastEntryTime (Γ n).1.val (W 0))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀j z, z ∈ frontier (W j) → m z = 0) (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    (x : ℕ → X) (c : ℕ → ℝ≥0∞) (M A : ℝ≥0∞) (hA : A < ∞)
    (hx : ∀j, Tendsto (fun n => (Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) atTop (𝓝 (x j)))
    (hc : ∀hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)),
      ∀j, Tendsto (fun n => physicalTollCost d g m (lastEntryFragmentArray d hU Γ W hcut n j).1) atTop (𝓝 (c j)))
    (hM : Tendsto (fun n => physicalTollCost d g m (prefixFragment d hU Γ W hprefix n).1) atTop (𝓝 M))
    (hbudget : M + (∑'j, c j) ≤ A)
    (hsmall : ∀j, HasShortCollarJoining d ν N g m (frontier (W (j+1))) (closure (W j)))
    (houter : HasShortCollarJoining d ν N g m (frontier (W 0)) univ)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have ha : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hfront (n : ℕ) : (Γ n).1.val (lastEntryTime (Γ n).1.val (W 0)) ∈ frontier (W 0) :=
    lastEntry_frontier (Γ n).1.val (hW 0) (hstart n) (ha (Nat.zero_le _) (hend n))
  have hx0 : x 0 ∈ frontier (W 0) :=
    isClosed_frontier.mem_of_tendsto (hx 0) (Eventually.of_forall hfront)
  have hfinite := hbudget.trans_lt hA
  have hMfin : M < ∞ := (ENNReal.add_lt_top.mp hfinite).1
  have hCfin : (∑'j, c j) < ∞ := (ENNReal.add_lt_top.mp hfinite).2
  let ε : ℝ≥0∞ := ENNReal.ofReal (η/3)
  have hδ : 0 < η/3 := by positivity
  have hε : 0 < ε := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨O, hO, hjoin⟩ := houter (x 0) hx0 ε hε
  obtain ⟨i, β, θβ, hβ, hβ0, hβ1, hβO, hβcost⟩ := exists_final_collar_path_of_limits
    d hU hG ν N Γ hΓ p W hW hnest hshrink hstart hend g hg m hm
    (∑'j, c j) hCfin x c hx hc le_rfl O hO hsmall w hw hpos hpoint hδ
  have hMc : ∀ᶠn in atTop, physicalTollCost d g m (prefixFragment d hU Γ W hprefix n).1 < M + ε :=
    (tendsto_order.mp hM).2 _ (ENNReal.lt_add_right hMfin.ne hε.ne')
  obtain ⟨k, hkO, hkcost⟩ := (((hx 0).eventually hO).and hMc).exists
  let α := prefixFragment d hU Γ W hprefix k
  have hα : AllowedTaggedPath d ν N (α.1.val, α.2) :=
    restrictTaggedPhysicalPath_allowed d hU ν N (Γ k) (hΓ k) hpoint (hprefix k)
  have hα0 : α.1.val ⊥ = (Γ k).1.val ⊥ := restrictTaggedPhysicalPath_zero d hU (Γ k) (hprefix k)
  have hα1 : α.1.val ⊤ = (Γ k).1.val (lastEntryTime (Γ k).1.val (W 0)) :=
    restrictTaggedPhysicalPath_one d hU (Γ k) (hprefix k)
  obtain ⟨a, haA, ha0, ha1, _, hacost⟩ := hjoin (α.1.val ⊤)
    ⟨hα1.symm ▸ hkO, hα1.symm ▸ hfront k⟩ (β.val ⊤) ⟨hβO, hβ1.symm ▸ hfront i⟩
  obtain ⟨βr, θr, hβr, hβr0, hβr1, hβrcost⟩ :=
    exists_allowed_reversed_interior_cost d ν N (β, θβ) hβ g m hpoint
  have hαm : m (α.1.val ⊤) = 0 := by rw [hα1]; exact hm 0 _ (hfront k)
  have ham : m (a.1.val ⊤) = 0 := by rw [ha1, hβ1]; exact hm 0 _ (hfront i)
  obtain ⟨αa, θαa, hαa, hαa0, hαa1, hαacost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N α a hα haA ha0.symm g hg m hαm hpoint
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hρcost⟩ :=
    exists_allowed_joined_interior_cost d hU ν N (αa, θαa) (βr, θr) hαa hβr
      (hαa1.trans (ha1.trans hβr0.symm)) g hg m (by rw [hαa1]; exact ham) hpoint
  have hstartρ : ρ.val ⊥ = (Γ k).1.val ⊥ := hρ0.trans (hαa0.trans hα0)
  refine ⟨ρ, θ, hρ, hstartρ.symm ▸ hF k, hρ1.trans (hβr1.trans hβ0), ?_⟩
  rw [preterminalToll_eq_interior_of_initial_zero ρ.val m (by rw [hstartρ]; exact hzero k)]
  change interiorPhysicalTollCost d g m ρ ≤ _
  have hεsum : ε + ε + ε = ENNReal.ofReal η := by
    dsimp [ε]
    rw [← ENNReal.ofReal_add hδ.le hδ.le, ← ENNReal.ofReal_add (by positivity) hδ.le]
    congr 1
    ring
  calc
    interiorPhysicalTollCost d g m ρ =
        interiorPhysicalTollCost d g m α.1 + interiorPhysicalTollCost d g m a.1 +
          interiorPhysicalTollCost d g m β := by rw [hρcost, hαacost, hβrcost]
    _ ≤ (M + ε) + ε + ((∑'j, c j) + ε) :=
      add_le_add (add_le_add ((interiorPhysicalTollCost_le_full d g m α.1).trans hkcost.le)
        ((interiorPhysicalTollCost_le_full d g m a.1).trans hacost)) hβcost
    _ = (M + (∑'j, c j)) + (ε + ε + ε) := by ac_rfl
    _ ≤ A + ENNReal.ofReal η := by rw [hεsum]; exact add_le_add hbudget le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ActualOneEndedSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-ended construction retains an original prefix. Its common
prefix and tail budget and compact limits are derived from the input paths. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_actual_oneEnded_collar_splicing
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set X) (hF : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : X) (W : ℕ → Set X) (hW : ∀j, IsOpen (W j))
    (hnest : ∀j, closure (W (j+1)) ⊆ W j)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (W j) ⊆ O)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ closure (W 0)) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀j z, z ∈ frontier (W j) → m z = 0) (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (hsmall : ∀j, HasShortCollarJoining d ν N g m (frontier (W (j+1))) (closure (W j)))
    (houter : HasShortCollarJoining d ν N g m (frontier (W 0)) univ)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have ha : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hstart' (n : ℕ) : (Γ n).1.val ⊥ ∉ W 0 := fun h => hstart n (subset_closure h)
  have hfront (n : ℕ) := lastEntry_frontier (Γ n).1.val (hW 0) (hstart' n)
    (ha (Nat.zero_le _) (hend n))
  have hprefix (n : ℕ) : ⊥ < lastEntryTime (Γ n).1.val (W 0) := by
    apply bot_lt_iff_ne_bot.mpr
    intro h
    have hf := frontier_subset_closure (hfront n)
    rw [h] at hf
    exact hstart n hf
  have hcut (n j : ℕ) (hj : j ≤ n) :=
    lastEntryFragments_strict (Γ n).1.val W hW hnest (hstart' n) (hend n) hj
  obtain ⟨s, x, c, M, hs, hx, hc, hM, hbudget⟩ := exists_actual_oneEnded_limits
    d hU Γ W hcut hprefix hW ha hstart' g hg m hzero
    (lastEntry_toll_zero d Γ W hW ha hstart' hend m hm) A hcost
  let Γs : ℕ → TaggedPhysicalPath d := fun n => Γ (s n)
  apply exists_oneEnded_collar_splicing_of_limits d hU hG ν N Γs (fun n => hΓ (s n))
    F (fun n => hF (s n)) p W hW hnest hshrink (fun n => hstart' (s n))
    (fun n => ha (Nat.add_le_add_right (hs.id_le n) 1) (hend (s n)))
    (fun n => hprefix (s n)) g hg m hm (fun n => hzero (s n)) x c M A hA hx
  · intro hcutS j
    apply (hc j).congr'
    filter_upwards [lastEntryFragmentArray_reindex_eventually d hU Γ W s hs.id_le hcut hcutS j] with n hn
    exact congrArg (fun P : TaggedPhysicalPath d => physicalTollCost d g m P.1) hn.symm
  · exact hM
  · exact hbudget
  · exact hsmall
  · exact houter
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CollarEndpointSubsequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergent endpoints may be placed in the successive chosen collars
without losing a cofinal, strictly increasing original-path subsequence. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_subsequence_in_nested_endpoint_neighborhoods
    {X : Type*} [TopologicalSpace X] (x y : ℕ → X) {p q : X}
    (hx : Tendsto x atTop (𝓝 p)) (hy : Tendsto y atTop (𝓝 q))
    (V W : ℕ → Set X) (hV : ∀j, V j ∈ 𝓝 p) (hW : ∀j, W j ∈ 𝓝 q) :
    ∃s : ℕ → ℕ, StrictMono s ∧ ∀n, x (s n) ∈ V (n+1) ∧ y (s n) ∈ W (n+1) := by
  have hchoose : ∀n N : ℕ, ∃k, N < k ∧ x k ∈ V (n+1) ∧ y k ∈ W (n+1) := by
    intro n N
    exact ((eventually_gt_atTop N).and
      ((hx.eventually (hV (n+1))).and (hy.eventually (hW (n+1))))).exists
  choose f hf using hchoose
  let s : ℕ → ℕ := Nat.rec (f 0 0) (fun n k => f (n+1) k)
  have hsucc (n : ℕ) : s (n+1) = f (n+1) (s n) := rfl
  refine ⟨s, strictMono_nat_of_lt_succ (fun n => ?_), ?_⟩
  · rw [hsucc]
    exact (hf (n+1) (s n)).1
  · intro n
    cases n with
    | zero => exact (hf 0 0).2
    | succ n => exact (hf (n+1) (s n)).2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedOneEndedSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-ended splicing using actual weighted smooth collars, retaining
an original initial point in the prescribed set. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_7 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_weighted_oneEnded_splicing
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hnest : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hlevel : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hDF : Disjoint F (closure (D 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have hD (j : ℕ) : IsOpen (D j).region := (D j).isOpen_region hπ hclosed hsurj hr
  have hDn (j : ℕ) : (D j).region ∈ 𝓝 p :=
    (hD j).mem_nhds ((D j).point_mem_region hsurj hp)
  obtain ⟨s, hs, hsends⟩ := exists_subsequence_in_nested_endpoint_neighborhoods
    (fun n => (Γ n).1.val ⊤) (fun n => (Γ n).1.val ⊤) hend hend
    (fun j => (D j).region) (fun j => (D j).region) hDn hDn
  apply exists_actual_oneEnded_collar_splicing d hU hG ν N (fun n => Γ (s n))
    (fun n => hΓ (s n)) F (fun n => hstart (s n)) p (fun j => (D j).region)
    hD hnest hshrink
    (fun n hx => Set.disjoint_left.mp hDF (hstart (s n)) hx)
    (fun n => (hsends n).1) g hg m
    (fun j z hz => hm z ((D j).frontier_region_subset_quotient d π hπ he (hD j) hz))
    (fun n => hm _ (hF (hstart (s n)))) A hA (hcost.comp hs.tendsto_atTop)
  · intro j z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (D (j+1)) (hD (j+1)) (T := closure (D j).region)
      (fun z hz => (show π (z : Sphere) ∈ closure (D j).region from subset_closure (hlevel j hz))) hz hε
  · intro z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (D 0) (hD 0) (T := univ) (fun _ _ => mem_univ _) hz hε
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalEnergyOneEndedSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-ended collar lemma with its collars constructed from the
published coarea, regular-value, one-manifold, and Schoenflies inputs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_8 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_oneEnded_splicing_of_local_energy
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (O : Set Sphere) (hO : IsOpen O) (hpO : p ∈ O) (hFO : Disjoint F O)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hgO : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g (z : Sphere) ^ 2) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have hgc : Measurable (fun z : ℂ => g (z : Sphere)) :=
    hg.comp OnePoint.continuous_coe.measurable
  obtain ⟨D, hD0, hDn, hDl, hDs⟩ := exists_shrinking_local_weighted_collars
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr hB hTD hbad
    hpB hp hO hpO (fun z : ℂ => g (z : Sphere)) hgc hgO
  exact exists_weighted_oneEnded_splicing d hU hG hdisj π hπ hclosed hsurj hr he ν N
    Γ hΓ F hF hstart p hp hend g hg m hm D hDn hDs hDl
    (hFO.mono_right hD0) A hA hcost w hw hpos hpoint hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ActualTwoEndedSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-ended collar construction on restrictions of the original paths,
with joint limits and finite budgets. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_actual_twoEnded_collar_splicing
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : X) (V W : ℕ → Set X) (hV : ∀j, IsOpen (V j)) (hW : ∀j, IsOpen (W j))
    (hnestV : ∀j, closure (V (j+1)) ⊆ V j) (hnestW : ∀j, closure (W (j+1)) ⊆ W j)
    (hshrinkV : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (V j) ⊆ O)
    (hshrinkW : ∀O ∈ 𝓝 q, ∃k : ℕ, ∀j ≥ k, closure (W j) ⊆ O)
    (hstartV : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hendW : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (hdis : Disjoint (closure (V 0)) (closure (W 0)))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmV : ∀j z, z ∈ frontier (V j) → m z = 0)
    (hmW : ∀j z, z ∈ frontier (W j) → m z = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (hsmallV : ∀j, HasShortCollarJoining d ν N g m (frontier (V (j+1))) (closure (V j)))
    (hsmallW : ∀j, HasShortCollarJoining d ν N g m (frontier (W (j+1))) (closure (W j)))
    (houterV : HasShortCollarJoining d ν N g m (frontier (V 0)) univ)
    (houterW : HasShortCollarJoining d ν N g m (frontier (W 0)) univ)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η := by
  have haV : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnestV j))
  have haW : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnestW j))
  have hstart (n : ℕ) : (Γ n).1.val ⊥ ∈ V 0 := haV (Nat.zero_le _) (hstartV n)
  have hend (n : ℕ) : (Γ n).1.val ⊤ ∈ W 0 := haW (Nat.zero_le _) (hendW n)
  have hendV (n : ℕ) : (Γ n).1.val ⊤ ∉ V 0 := fun h =>
    disjoint_left.mp hdis (subset_closure h) (subset_closure (hend n))
  have hstartW (n : ℕ) : (Γ n).1.val ⊥ ∉ W 0 := fun h =>
    disjoint_left.mp hdis (subset_closure (hstart n)) (subset_closure h)
  have hleft (n j : ℕ) (hj : j ≤ n) :=
    firstExitFragments_strict (Γ n).1.val V hV hnestV (hstartV n) (hendV n) hj
  have hright (n j : ℕ) (hj : j ≤ n) :=
    lastEntryFragments_strict (Γ n).1.val W hW hnestW (hstartW n) (hendW n) hj
  have hmid (n : ℕ) := firstExit_lt_lastEntry (Γ n).1.val (hV 0) (hW 0) hdis (hstart n) (hend n)
  obtain ⟨s, x, y, c, e, M, hs, hx, hy, hc, he, hM, hbudget⟩ := exists_actual_twoEnded_limits
    d hU Γ V W hleft hright hmid hV hW haV haW hendV hstartW g hg m
    (firstExit_toll_zero d Γ V hV haV hstartV hendV m hmV)
    (lastEntry_toll_zero d Γ W hW haW hstartW hendW m hmW) A hcost
  let Γs : ℕ → TaggedPhysicalPath d := fun n => Γ (s n)
  apply exists_twoEnded_collar_splicing_of_limits d hU hG ν N Γs (fun n => hΓ (s n))
    p q V W hV hW hnestV hnestW hshrinkV hshrinkW
    (fun n => haV (Nat.add_le_add_right (hs.id_le n) 1) (hstartV (s n)))
    (fun n => hendV (s n)) (fun n => hstartW (s n))
    (fun n => haW (Nat.add_le_add_right (hs.id_le n) 1) (hendW (s n)))
    (fun n => hmid (s n)) g hg m hmV hmW x y c e M A hA hx hy
  · intro hcutS j
    apply (hc j).congr'
    filter_upwards [firstExitFragmentArray_reindex_eventually d hU Γ V s hs.id_le hleft hcutS j] with n hn
    exact congrArg (fun P : TaggedPhysicalPath d => physicalTollCost d g m P.1) hn.symm
  · intro hcutS j
    apply (he j).congr'
    filter_upwards [lastEntryFragmentArray_reindex_eventually d hU Γ W s hs.id_le hright hcutS j] with n hn
    exact congrArg (fun P : TaggedPhysicalPath d => physicalTollCost d g m P.1) hn.symm
  · exact hM
  · exact hbudget
  · exact hsmallV
  · exact hsmallW
  · exact houterV
  · exact houterW
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedTwoEndedSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-ended splicing for the actual weighted smooth collars. All short
joining arcs, path restrictions, and limiting budgets are constructed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_9 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_weighted_twoEnded_splicing
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : Sphere) (hp : p ≠ π OnePoint.infty) (hq : q ≠ π OnePoint.infty)
    (hstart : Tendsto (fun n => (Γ n).1.val ⊥) atTop (𝓝 p))
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 q))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (E : ℕ → WeightedCollar d.physicalDomain π B q (fun z => g (z : Sphere)))
    (hnestD : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hnestE : ∀j, closure (E (j+1)).region ⊆ (E j).region)
    (hshrinkD : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hshrinkE : ∀O ∈ 𝓝 q, ∃k : ℕ, ∀j ≥ k, closure (E j).region ⊆ O)
    (hlevelD : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hlevelE : ∀j, {z | (E (j+1)).function z = (E (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (E j).region)
    (hDE : Disjoint (closure (D 0).region) (closure (E 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η := by
  have hD (j : ℕ) : IsOpen (D j).region := (D j).isOpen_region hπ hclosed hsurj hr
  have hE (j : ℕ) : IsOpen (E j).region := (E j).isOpen_region hπ hclosed hsurj hr
  obtain ⟨s, hs, hsends⟩ := exists_subsequence_in_nested_endpoint_neighborhoods
    (fun n => (Γ n).1.val ⊥) (fun n => (Γ n).1.val ⊤) hstart hend
    (fun j => (D j).region) (fun j => (E j).region)
    (fun j => (hD j).mem_nhds ((D j).point_mem_region hsurj hp))
    (fun j => (hE j).mem_nhds ((E j).point_mem_region hsurj hq))
  apply exists_actual_twoEnded_collar_splicing d hU hG ν N (fun n => Γ (s n))
    (fun n => hΓ (s n)) p q (fun j => (D j).region) (fun j => (E j).region)
    hD hE hnestD hnestE hshrinkD hshrinkE (fun n => (hsends n).1) (fun n => (hsends n).2)
    hDE g hg m
    (fun j z hz => hm z ((D j).frontier_region_subset_quotient d π hπ he (hD j) hz))
    (fun j z hz => hm z ((E j).frontier_region_subset_quotient d π hπ he (hE j) hz))
    A hA (hcost.comp hs.tendsto_atTop)
  · intro j z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (D (j+1)) (hD (j+1)) (T := closure (D j).region)
      (fun z hz => (show π (z : Sphere) ∈ closure (D j).region from subset_closure (hlevelD j hz))) hz hε
  · intro j z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (E (j+1)) (hE (j+1)) (T := closure (E j).region)
      (fun z hz => (show π (z : Sphere) ∈ closure (E j).region from subset_closure (hlevelE j hz))) hz hε
  · intro z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (D 0) (hD 0) (T := univ) (fun _ _ => mem_univ _) hz hε
  · intro z hz ε hε
    exact exists_small_weighted_collar_arcs d hU hdisj π hπ he ν N g hg m hm
      (E 0) (hE 0) (T := univ) (fun _ _ => mem_univ _) hz hε
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalEnergyTwoEndedSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-ended collar lemma with its collars constructed from the
published coarea, regular-value, one-manifold, and Schoenflies inputs. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_10 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_twoEnded_splicing_of_local_energy
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : Sphere) (hpB : p ∈ B) (hqB : q ∈ B)
    (hp : p ≠ π OnePoint.infty) (hq : q ≠ π OnePoint.infty)
    (hstart : Tendsto (fun n => (Γ n).1.val ⊥) atTop (𝓝 p))
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 q))
    (O P : Set Sphere) (hO : IsOpen O) (hP : IsOpen P) (hpO : p ∈ O) (hqP : q ∈ P)
    (hOP : Disjoint O P)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hgO : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g (z : Sphere) ^ 2) < ∞)
    (hgP : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' P, g (z : Sphere) ^ 2) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η := by
  have hgc : Measurable (fun z : ℂ => g (z : Sphere)) :=
    hg.comp OnePoint.continuous_coe.measurable
  obtain ⟨D, hD0, hDn, hDl, hDs⟩ := exists_shrinking_local_weighted_collars
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr hB hTD hbad
    hpB hp hO hpO (fun z : ℂ => g (z : Sphere)) hgc hgO
  obtain ⟨E, hE0, hEn, hEl, hEs⟩ := exists_shrinking_local_weighted_collars
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr hB hTD hbad
    hqB hq hP hqP (fun z : ℂ => g (z : Sphere)) hgc hgP
  exact exists_weighted_twoEnded_splicing d hU hG hdisj π hπ hclosed hsurj hr he ν N
    Γ hΓ p q hp hq hstart hend g hg m hm D E hDn hEn hDs hEs hDl hEl
    (hOP.mono hD0 hE0) A hA hcost w hw hpos hpoint hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CollarDustAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The collar constructions preserve avoidance of arbitrary dust sets.
Auxiliary infinite tolls enforce the condition only at non-omitted times. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_11 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_twoEnded_splicing_avoiding_dust
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : Sphere) (hpB : p ∈ B) (hqB : q ∈ B)
    (hp : p ≠ π OnePoint.infty) (hq : q ≠ π OnePoint.infty)
    (hstart : Tendsto (fun n => (Γ n).1.val ⊥) atTop (𝓝 p))
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 q))
    (O P : Set Sphere) (hO : IsOpen O) (hP : IsOpen P) (hpO : p ∈ O) (hqP : q ∈ P)
    (hOP : Disjoint O P)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hgO : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g (z : Sphere) ^ 2) < ∞)
    (hgP : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' P, g (z : Sphere) ^ 2) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (hS : Disjoint S d.quotientDomain)
    (havoid : ∀n t, (Γ n).1.val t ∉ S)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η ∧
      ∀t ∈ Ioo (⊥ : PathTime) ⊤, ρ.val t ∉ S := by
  have hmS (x : Sphere) (hx : x ∈ d.quotientDomain) : exclusionToll S m x = 0 := by
    rw [exclusionToll_eq S m (fun hs => Set.disjoint_left.mp hS hs hx)]
    exact hm x hx
  have hcostS : Tendsto (fun n => physicalTollCost d g (exclusionToll S m) (Γ n).1)
      atTop (𝓝 A) := by
    convert hcost using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact physicalTollCost_exclusion d g m S (Γ n).1 (havoid n)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC⟩ := exists_twoEnded_splicing_of_local_energy
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ p q hpB hqB hp hq hstart hend O P hO hP hpO hqP hOP
    g hg hgO hgP (exclusionToll S m) hmS A hA hcostS w hw hpos hpoint hη
  have hfinite : interiorPhysicalTollCost d g (exclusionToll S m) ρ < ∞ :=
    hC.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, ENNReal.ofReal_lt_top⟩)
  refine ⟨ρ, θ, hρ, hρ0, hρ1,
    (interiorPhysicalTollCost_mono_weight d g (le_exclusionToll S m) ρ).trans hC, ?_⟩
  apply avoids_of_finite_exclusionToll ρ.val _ S m
  exact (show timeToll ρ.val (Ioo (⊥ : PathTime) ⊤) (exclusionToll S m) ≤
    interiorPhysicalTollCost d g (exclusionToll S m) ρ from le_add_self).trans_lt hfinite

theorem exists_oneEnded_splicing_avoiding_dust
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (O : Set Sphere) (hO : IsOpen O) (hpO : p ∈ O) (hFO : Disjoint F O)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hgO : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' O, g (z : Sphere) ^ 2) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (hS : Disjoint S d.quotientDomain)
    (havoid : ∀n t, (Γ n).1.val t ∉ S)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η ∧
      ∀t < (⊤ : PathTime), ρ.val t ∉ S := by
  have hmS (x : Sphere) (hx : x ∈ d.quotientDomain) : exclusionToll S m x = 0 := by
    rw [exclusionToll_eq S m (fun hs => Set.disjoint_left.mp hS hs hx)]
    exact hm x hx
  have hcostS : Tendsto (fun n => physicalTollCost d g (exclusionToll S m) (Γ n).1)
      atTop (𝓝 A) := by
    convert hcost using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact physicalTollCost_exclusion d g m S (Γ n).1 (havoid n)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC⟩ := exists_oneEnded_splicing_of_local_energy
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ F hF hstart p hpB hp hend O hO hpO hFO
    g hg hgO (exclusionToll S m) hmS A hA hcostS w hw hpos hpoint hη
  have hfinite : preterminalToll ρ.val (exclusionToll S m) < ∞ :=
    (show preterminalToll ρ.val (exclusionToll S m) ≤
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      preterminalToll ρ.val (exclusionToll S m) from le_add_self).trans_lt
      (hC.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, ENNReal.ofReal_lt_top⟩))
  refine ⟨ρ, θ, hρ, hρ0, hρ1,
    (add_le_add le_rfl (preterminalToll_mono ρ.val (le_exclusionToll S m))).trans hC, ?_⟩
  rw [preterminalToll_eq_timeToll] at hfinite
  exact avoids_of_finite_exclusionToll ρ.val _ S m hfinite

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SphericalCollarSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spherical-energy forms of the two collar constructions. The outer
neighborhoods and local energy bounds are derived, and all new interior
dust contacts belong to one of the original paths. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

omit [MeasurableSpace C(PathTime, Sphere)] in
private theorem exists_sphere_open_closure_inside {p : Sphere} {U : Set Sphere}
    (hU : U ∈ 𝓝 p) : ∃V : Set Sphere, IsOpen V ∧ p ∈ V ∧ closure V ⊆ U := by
  obtain ⟨C, hC, hCc, hCU⟩ := exists_mem_nhds_isClosed_subset hU
  exact ⟨interior C, isOpen_interior, mem_interior_iff_mem_nhds.mpr hC,
    (closure_minimal interior_subset hCc).trans hCU⟩

local instance localInst_rbc6963_12 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_spherical_twoEnded_collar
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (p q : Sphere) (hpB : p ∈ B) (hqB : q ∈ B)
    (hpq : p ≠ q)
    (hp : p ≠ π OnePoint.infty) (hq : q ≠ π OnePoint.infty)
    (hstart : Tendsto (fun n => (Γ n).1.val ⊥) atTop (𝓝 p))
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 q))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = p ∧ ρ.val ⊤ = q ∧
      interiorPhysicalTollCost d g m ρ ≤ A + ENNReal.ofReal η ∧
      ρ.val '' Ioo (⊥ : PathTime) ⊤ ∩ d.dust ⊆ ⋃n, range (Γ n).1.val := by
  obtain ⟨U, hpU, hUo, V, hqV, hVo, hUV⟩ := exists_open_nhds_disjoint_closure hpq
  obtain ⟨W, hWo, hpW, hW⟩ := exists_sphere_open_closure_inside
    (isClosed_singleton.isOpen_compl.mem_nhds hp)
  obtain ⟨Z, hZo, hqZ, hZ⟩ := exists_sphere_open_closure_inside
    (isClosed_singleton.isOpen_compl.mem_nhds hq)
  let O := U ∩ W
  let P := V ∩ Z
  have hOi : π OnePoint.infty ∉ closure O := fun h =>
    (hW (closure_mono inter_subset_right h)) rfl
  have hPi : π OnePoint.infty ∉ closure P := fun h =>
    (hZ (closure_mono inter_subset_right h)) rfl
  let S := d.dust \ ⋃n, range (Γ n).1.val
  have hS : Disjoint S d.quotientDomain := by
    apply Set.disjoint_left.mpr
    intro x hx hxu
    exact Set.disjoint_left.mp hdisj hxu hx.1
  have hav (n : ℕ) (t : PathTime) : (Γ n).1.val t ∉ S := by
    intro h
    exact h.2 (mem_iUnion.mpr ⟨n, mem_range_self t⟩)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, havoid⟩ := exists_twoEnded_splicing_avoiding_dust
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ p q hpB hqB hp hq hstart hend O P (hUo.inter hWo) (hVo.inter hZo)
    ⟨hpU, hpW⟩ ⟨hqV, hqZ⟩
    (hUV.mono (inter_subset_left.trans subset_closure) (inter_subset_left.trans subset_closure))
    g hg (planar_energy_quotient_neighborhood_finite π hπ hOi g hg henergy)
    (planar_energy_quotient_neighborhood_finite π hπ hPi g hg henergy)
    m hm S hS hav A hA hcost w hw hpos hpoint hη
  refine ⟨ρ, θ, hρ, hρ0, hρ1, hC, ?_⟩
  rintro x ⟨⟨t, ht, rfl⟩, hx⟩
  by_contra h
  exact havoid t ht ⟨hx, h⟩

theorem exists_spherical_oneEnded_collar
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (hpF : p ∉ closure F)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η ∧
      ρ.val '' Iio (⊤ : PathTime) ∩ d.dust ⊆ ⋃n, range (Γ n).1.val := by
  obtain ⟨O, hOo, hpO, hO⟩ := exists_sphere_open_closure_inside
    ((isClosed_closure.union isClosed_singleton).isOpen_compl.mem_nhds
      (show p ∉ closure F ∪ {π OnePoint.infty} from fun h => h.elim hpF hp))
  have hOi : π OnePoint.infty ∉ closure O := fun h =>
    hO h (Or.inr rfl)
  have hFO : Disjoint F O := by
    apply Set.disjoint_left.mpr
    intro x hx hxO
    exact hO (subset_closure hxO) (Or.inl (subset_closure hx))
  let S := d.dust \ ⋃n, range (Γ n).1.val
  have hS : Disjoint S d.quotientDomain := by
    apply Set.disjoint_left.mpr
    intro x hx hxu
    exact Set.disjoint_left.mp hdisj hxu hx.1
  have hav (n : ℕ) (t : PathTime) : (Γ n).1.val t ∉ S := by
    intro h
    exact h.2 (mem_iUnion.mpr ⟨n, mem_range_self t⟩)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, havoid⟩ := exists_oneEnded_splicing_avoiding_dust
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
    ν N Γ hΓ F hF hstart p hpB hp hend O hOo hpO hFO
    g hg (planar_energy_quotient_neighborhood_finite π hπ hOi g hg henergy)
    m hm S hS hav A hA hcost w hw hpos hpoint hη
  refine ⟨ρ, θ, hρ, hρ0, hρ1, hC, ?_⟩
  rintro x ⟨⟨t, ht, rfl⟩, hx⟩
  by_contra h
  exact havoid t ht ⟨hx, h⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AnchoredDustBlock
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite block of possibly repeated limiting dust junctions can be
replaced by one allowed true path. The original true-piece limits and one
paid toll per junction cover the replacement, up to any positive error. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_13 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_path_replacing_anchored_dust_block
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (hF : frontier F ⊆ d.quotientDomain)
    (hH : frontier H ⊆ d.quotientDomain)
    (n : ℕ) (p : Fin (n+1) → Sphere)
    (hpB : ∀i, p i ∈ B) (hp : ∀i, p i ≠ π OnePoint.infty)
    (Γ : Fin (n+2) → ℕ → TaggedPhysicalPath d)
    (hΓ : ∀i k, AllowedTaggedPath d ν N ((Γ i k).1.val, (Γ i k).2))
    (hΓF : ∀k, (Γ 0 k).1.val ⊥ ∈ F ∩ d.quotientDomain)
    (hΓH : ∀k, (Γ (Fin.last (n+1)) k).1.val ⊤ ∈ H ∩ d.quotientDomain)
    (hstart : ∀i : Fin (n+1), Tendsto (fun k => (Γ i.succ k).1.val ⊥) atTop (𝓝 (p i)))
    (hend : ∀i : Fin (n+1), Tendsto (fun k => (Γ i.castSucc k).1.val ⊤) atTop (𝓝 (p i)))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : Fin (n+2) → ℝ≥0∞) (hA : ∀i, A i < ∞)
    (hcost : ∀i, Tendsto (fun k => physicalTollCost d g m (Γ i k).1) atTop (𝓝 (A i)))
    (J : Fin (n+1) → ℝ≥0∞) (hpaid : ∀i, m (p i) ≤ J i)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧
      physicalTollCost d g m ρ ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  have hh : 0 < η/2 := by positivity
  let A' : Fin (n+1) → ℝ≥0∞ := fun i => A i.castSucc
  let J' : Fin n → ℝ≥0∞ := fun i => J i.castSucc
  have inside (S : Set Sphere) (hS : frontier S ⊆ d.quotientDomain)
      (i : Fin (n+1)) (hin : p i ∈ closure S) : p i ∈ interior S := by
    by_contra hn
    exact Set.disjoint_left.mp hUB (hS ⟨hin, hn⟩) (hpB i)
  have hj (i : Fin n) : m (p i.castSucc) ≤ J' i := hpaid i.castSucc
  have hf : p 0 ∈ interior F ∨ ∀ε : ℝ, 0 < ε →
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ = p 0 ∧
        interiorPhysicalTollCost d g m ρ ≤ A' 0 + ENNReal.ofReal ε := by
    by_cases hin : p 0 ∈ closure F
    · exact Or.inl (inside F hF 0 hin)
    · right
      intro ε hε
      have hout : p 0 ∉ closure (F ∩ d.quotientDomain) :=
        fun h => hin (closure_mono inter_subset_left h)
      obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc, _⟩ := exists_spherical_oneEnded_collar
        hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
        ν N (Γ 0) (hΓ 0) (F ∩ d.quotientDomain) inter_subset_right hΓF
        (p 0) (hpB 0) (hp 0) (hend 0) hout
        g hg henergy m hm (A 0) (hA 0) (hcost 0) w hw hpos hpoint hε
      rw [preterminalToll_eq_interior_of_initial_zero ρ.val m (hm _ hρ0.2)] at hc
      exact ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩
  have hs (i : Fin n) (hne : p i.castSucc ≠ p i.succ) (ε : ℝ) (hε : 0 < ε) :
      ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (ρ.val, θ) ∧
        ρ.val ⊥ = p i.castSucc ∧ ρ.val ⊤ = p i.succ ∧
        interiorPhysicalTollCost d g m ρ ≤ A' i.succ + ENNReal.ofReal ε := by
    obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc, _⟩ := exists_spherical_twoEnded_collar
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
      ν N (Γ i.castSucc.succ) (hΓ _) (p i.castSucc) (p i.succ)
      (hpB _) (hpB _) hne (hp _) (hp _)
      (hstart i.castSucc) (hend i.succ) g hg henergy m hm
      (A i.castSucc.succ) (hA _) (hcost _) w hw hpos hpoint hε
    exact ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩
  have hleft := exists_allowed_anchored_junction_prefix
    d hU ν N g hg m hpoint F hF n p A' J' hj hf hs hh
  have hright : p (Fin.last n) ∈ interior H ∨
      ∃ (β : FinitePhysicalPath d.domainEquiv d.basePoint) (θβ : ℕ → TagSlot),
        AllowedTaggedPath d ν N (β.val, θβ) ∧ β.val ⊥ ∈ H ∩ d.quotientDomain ∧
        β.val ⊤ = p (Fin.last n) ∧
        interiorPhysicalTollCost d g m β ≤ A (Fin.last (n+1)) + ENNReal.ofReal (η/2) := by
    by_cases hin : p (Fin.last n) ∈ closure H
    · exact Or.inl (inside H hH _ hin)
    · right
      let Δ := fun k => reversedTaggedPhysicalPath d (Γ (Fin.last (n+1)) k)
      have hΔ (k : ℕ) : AllowedTaggedPath d ν N ((Δ k).1.val, (Δ k).2) :=
        allowedTaggedPath_reversed d ν N
          ((Γ (Fin.last (n+1)) k).1.val, (Γ (Fin.last (n+1)) k).2)
          (hΓ _ k) hpoint
      have hΔH (k : ℕ) : (Δ k).1.val ⊥ ∈ H ∩ d.quotientDomain := by
        change reversedPath (Γ (Fin.last (n+1)) k).1.val ⊥ ∈ H ∩ d.quotientDomain
        rw [reversedPath_zero]
        exact hΓH k
      have hΔend : Tendsto (fun k => (Δ k).1.val ⊤) atTop (𝓝 (p (Fin.last n))) := by
        convert hstart (Fin.last n) using 1
        all_goals try with_reducible_and_instances rfl
        funext k
        exact reversedPath_one (Γ (Fin.last (n+1)) k).1.val
      have hΔcost : Tendsto (fun k => physicalTollCost d g m (Δ k).1)
          atTop (𝓝 (A (Fin.last (n+1)))) := by
        convert hcost (Fin.last (n+1)) using 1
        all_goals try with_reducible_and_instances rfl
        funext k
        exact physicalTollCost_reversed d g m (Γ (Fin.last (n+1)) k).1
      have hout : p (Fin.last n) ∉ closure (H ∩ d.quotientDomain) :=
        fun h => hin (closure_mono inter_subset_left h)
      obtain ⟨β, θβ, hβ, hβ0, hβ1, hβc, _⟩ := exists_spherical_oneEnded_collar
        hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad
        ν N Δ hΔ (H ∩ d.quotientDomain) inter_subset_right hΔH
        (p (Fin.last n)) (hpB _) (hp _) hΔend hout
        g hg henergy m hm (A (Fin.last (n+1))) (hA _) hΔcost w hw hpos hpoint hh
      rw [preterminalToll_eq_interior_of_initial_zero β.val m (hm _ hβ0.2)] at hβc
      exact ⟨β, θβ, hβ, hβ0, hβ1, hβc⟩
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_anchor_tail_attachment
    d hU hdisj hdense ν N g hg m hm hpoint F H hF hH (p (Fin.last n))
    ((∑i, A' i) + (∑i, J' i) + ENNReal.ofReal (η/2))
    (A (Fin.last (n+1)) + ENNReal.ofReal (η/2)) (J (Fin.last n)) (hpaid _) hleft hright
  refine ⟨ρ, θ, hρ, hρ0, hρ1, ?_⟩
  have herr : ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) = ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add hh.le hh.le]
    congr 1
    ring
  have hsA := Fin.sum_univ_castSucc A
  have hsJ := Fin.sum_univ_castSucc J
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  rw [hsA, hsJ, ← herr]
  dsimp [A', J']
  ac_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteLimitBlock
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite block of possibly repeated limiting dust junctions can be
replaced by one allowed true path. The original true-piece limits and one
paid toll per junction cover the replacement, up to any positive error. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_14 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_path_replacing_finite_limit_block
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (hF : frontier F ⊆ d.quotientDomain)
    (hH : frontier H ⊆ d.quotientDomain)
    (n : ℕ) (p : Fin n → Sphere)
    (hpB : ∀i, p i ∈ B) (hp : ∀i, p i ≠ π OnePoint.infty)
    (Γ : Fin (n+1) → ℕ → TaggedPhysicalPath d)
    (hΓ : ∀i k, AllowedTaggedPath d ν N ((Γ i k).1.val, (Γ i k).2))
    (hΓF : ∀k, (Γ 0 k).1.val ⊥ ∈ F ∩ d.quotientDomain)
    (hΓH : ∀k, (Γ (Fin.last n) k).1.val ⊤ ∈ H ∩ d.quotientDomain)
    (hstart : ∀i : Fin n, Tendsto (fun k => (Γ i.succ k).1.val ⊥) atTop (𝓝 (p i)))
    (hend : ∀i : Fin n, Tendsto (fun k => (Γ i.castSucc k).1.val ⊤) atTop (𝓝 (p i)))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (A : Fin (n+1) → ℝ≥0∞) (hA : ∀i, A i < ∞)
    (hcost : ∀i, Tendsto (fun k => physicalTollCost d g m (Γ i k).1) atTop (𝓝 (A i)))
    (J : Fin n → ℝ≥0∞) (hpaid : ∀i, m (p i) ≤ J i)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∩ d.quotientDomain ∧ ρ.val ⊤ ∈ H ∩ d.quotientDomain ∧
      physicalTollCost d g m ρ ≤ (∑i, A i) + (∑i, J i) + ENNReal.ofReal η := by
  cases n with
  | zero =>
      have hlt : A 0 < A 0 + ENNReal.ofReal η :=
        ENNReal.lt_add_right (hA 0).ne (ENNReal.ofReal_pos.mpr hη).ne'
      obtain ⟨k, hk⟩ := ((hcost 0).eventually (gt_mem_nhds hlt)).exists
      exact ⟨(Γ 0 k).1, (Γ 0 k).2, hΓ 0 k, hΓF k, hΓH k, by simpa using hk.le⟩
  | succ n =>
      exact exists_path_replacing_anchored_dust_block
        hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense
        ν N F H hF hH n p hpB hp Γ hΓ hΓF hΓH hstart hend
        g hg henergy m hm A hA hcost J hpaid w hw hpos hpoint hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpChainEdges
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete edges in a chain with fixed old jump disks. True edges
are actual allowed physical paths, and jump edges keep their original toll. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem physicalJumpEdge_of_path (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (V : I → Set X) (c : I → ℝ≥0∞)
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hx : Γ.1.val ⊥ ∈ d.quotientDomain) (hy : Γ.1.val ⊤ ∈ d.quotientDomain) :
    physicalJumpEdge d ν N g m V c (Γ.1.val ⊥) (Γ.1.val ⊤) (physicalTollCost d g m Γ.1) :=
  Or.inl ⟨Γ, hΓ, rfl, rfl, hx, hy, rfl⟩

theorem physicalJumpEdge_of_jump (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (V : I → Set X) (c : I → ℝ≥0∞)
    (i : I) {x y : X} (hx : x ∈ V i ∩ d.quotientDomain) (hy : y ∈ V i ∩ d.quotientDomain) :
    physicalJumpEdge d ν N g m V c x y (c i) := Or.inr ⟨i, hx, hy, rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpTollLowerBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive neighborhood width pays the limiting dust junction.
This is the lower bound used in removal of one shrinking jump level. -/

open Set Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem eventually_mem_fixed_thickening {x : ℕ → X} {p : X} {V : ℕ → Set X}
    (hx : Tendsto x atTop (𝓝 p)) (hxV : ∀n, x n ∈ V n) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠn in atTop, p ∈ thickening τ (V n) := by
  have hd : Tendsto (fun n => dist p (x n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := p)).dist hx
  filter_upwards [hd.eventually (gt_mem_nhds hτ)] with n hn
  exact mem_thickening_iff.mpr ⟨x n, hxV n, hn⟩

theorem limiting_fixedWidthJumpToll_ge
    (B : Set X) (m : X → ℝ≥0∞) (ρ : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ)
    {V : ℕ → Set X} {x : ℕ → X} {p : X}
    (hx : Tendsto x atTop (𝓝 p)) (hxV : ∀n, x n ∈ V n) (hp : p ∈ B)
    {A : ℝ≥0∞} (hA : Tendsto (fun n => fixedWidthJumpToll B m ρ τ (V n)) atTop (𝓝 A)) :
    m p ≤ A := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hA
  filter_upwards [eventually_mem_fixed_thickening hx hxV hτ] with n hn
  have hsup : m p ≤ neighborhoodTollSup m (B ∩ thickening τ (V n)) :=
    le_iSup_of_le p (le_iSup_of_le (show p ∈ B ∩ thickening τ (V n) from ⟨hp, hn⟩) le_rfl)
  exact hsup.trans (le_max_right _ _)

theorem fixedWidthJumpToll_ge_floor
    (B : Set X) (m : X → ℝ≥0∞) (ρ : ℝ≥0∞) (τ : ℝ) (V : Set X) :
    ρ ≤ fixedWidthJumpToll B m ρ τ V := le_max_left _ _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpBlockCodes
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete finite chains grouped into true-path blocks separated by
old jumps. The finite code records old disk labels and new-jump counts. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem blockAnchors_frontier {X I : Type*} [TopologicalSpace X] {n : ℕ}
    (F H U : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (hF : frontier F ⊆ U) (hH : frontier H ⊆ U) (hO : ∀i, frontier (O i) ⊆ U) :
    ∀i, frontier (blockAnchors F H O P i) ⊆ U := by
  intro i
  refine Fin.cases (by simpa using hF) (fun j => ?_) i
  refine Fin.lastCases (by simpa [blockAnchors] using hH) (fun j => ?_) j
  simpa [blockAnchors] using hO (P.2.1 j)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_InitialBlockPiece
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace the first true piece of a grouped chain. This operation is
used when consecutive true edges are joined during chain normalization. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem replaceInitialTruePiece_end (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d)
    (hend : γ.1.val ⊤ = (Z.paths 0 0).1.val ⊤) :
    ∀b j, ((replaceInitialTruePiece d P Z γ).paths b j).1.val ⊤ = (Z.paths b j).1.val ⊤ := by
  intro b
  refine Fin.cases ?_ (fun b j => ?_) b
  · intro j
    exact Fin.cases hend (fun _ => rfl) j
  · rfl

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem replaceInitialTruePiece_valid
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F F' H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : IsJumpBlockCode d ν N B F H O P Z)
    (γ : TaggedPhysicalPath d) (hγ : AllowedTaggedPath d ν N (γ.1.val, γ.2))
    (hstart : γ.1.val ⊥ ∈ F' ∩ d.quotientDomain)
    (hend : γ.1.val ⊤ = (Z.paths 0 0).1.val ⊤) :
    IsJumpBlockCode d ν N B F' H O P (replaceInitialTruePiece d P Z γ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hZ.meets⟩
  · intro b
    refine Fin.cases ?_ (fun b j => hZ.allowed b.succ j) b
    intro j
    exact Fin.cases hγ (fun j => hZ.allowed 0 j.succ) j
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · simpa [replaceInitialTruePiece] using hstart
    · simpa only [replaceInitialTruePiece, Fin.cons_succ, Fin.castSucc_succ,
        blockAnchors, Fin.cons_succ] using hZ.start b.succ
  · intro b
    rw [replaceInitialTruePiece_end d P Z γ hend]
    simpa only [blockAnchors, Fin.cons_succ] using hZ.finish b
  · intro b i
    rw [replaceInitialTruePiece_end d P Z γ hend]
    exact hZ.left b i
  · intro b
    refine Fin.cases (fun i => ?_) (fun b i => hZ.right b.succ i) b
    exact hZ.right 0 i

omit [MeasurableSpace X] in
theorem replaceInitialTruePiece_cost
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (a : ℝ≥0∞)
    (hc : physicalTollCost d g m γ.1 = a + physicalTollCost d g m (Z.paths 0 0).1) :
    jumpBlockCost d B g m r τ T P (replaceInitialTruePiece d P Z γ) =
      a + jumpBlockCost d B g m r τ T P Z := by
  simp only [jumpBlockCost, replaceInitialTruePiece, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  rw [hc]
  ac_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrependNewBlockJump
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prepend one new jump and its initial true piece to a grouped chain.
The original first true piece follows the new jump unchanged. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem prependNewBlockJump_finish (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (V : Set X) :
    ∀b, ((prependNewBlockJump d P Z γ V).paths b
      (Fin.last ((prependNewJumpPattern P).2.2 b).val)).1.val ⊤ =
      (Z.paths b (Fin.last (P.2.2 b).val)).1.val ⊤ := by
  intro b
  refine Fin.cases ?_ (fun _ => rfl) b
  change ((Fin.cons γ (Z.paths 0) : Fin ((P.2.2 0).val+2) → TaggedPhysicalPath d)
    (Fin.last ((P.2.2 0).val+1))).1.val ⊤ = _
  rw [← Fin.succ_last, Fin.cons_succ]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem prependNewBlockJump_valid
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F F' H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : IsJumpBlockCode d ν N B F H O P Z)
    (γ : TaggedPhysicalPath d) (hγ : AllowedTaggedPath d ν N (γ.1.val, γ.2))
    (V : Set X) (hstart : γ.1.val ⊥ ∈ F' ∩ d.quotientDomain)
    (hleft : γ.1.val ⊤ ∈ V) (hright : (Z.paths 0 0).1.val ⊥ ∈ V)
    (hmeet : (V ∩ B).Nonempty) :
    IsJumpBlockCode d ν N B F' H O (prependNewJumpPattern P) (prependNewBlockJump d P Z γ V) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    refine Fin.cases ?_ (fun b j => hZ.allowed b.succ j) b
    intro j
    exact Fin.cases hγ (fun j => hZ.allowed 0 j) j
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · change γ.1.val ⊥ ∈ F' ∩ d.quotientDomain
      exact hstart
    · change (Z.paths b.succ 0).1.val ⊥ ∈
        blockAnchors F' H O P b.succ.castSucc ∩ d.quotientDomain
      rw [blockAnchors_internal]
      have h := hZ.start b.succ
      rw [blockAnchors_internal] at h
      exact h
  · intro b
    rw [prependNewBlockJump_finish]
    change (Z.paths b (Fin.last (P.2.2 b).val)).1.val ⊤ ∈
      blockAnchors F' H O P b.succ ∩ d.quotientDomain
    rw [show blockAnchors F' H O P b.succ = blockAnchors F H O P b.succ from rfl]
    exact hZ.finish b
  · intro b
    refine Fin.cases ?_ (fun b i => hZ.left b.succ i) b
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hleft
    · change (Z.paths 0 i.castSucc).1.val ⊤ ∈ Z.disks 0 i
      exact hZ.left 0 i
  · intro b
    refine Fin.cases ?_ (fun b i => hZ.right b.succ i) b
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hright
    · exact hZ.right 0 i
  · intro b
    refine Fin.cases ?_ (fun b i => hZ.meets b.succ i) b
    intro i
    exact Fin.cases hmeet (fun i => hZ.meets 0 i) i

omit [MeasurableSpace X] in
theorem prependNewBlockJump_cost
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (V : Set X) :
    jumpBlockCost d B g m r τ T (prependNewJumpPattern P) (prependNewBlockJump d P Z γ V) =
      physicalTollCost d g m γ.1 + fixedWidthJumpToll B m r τ V +
        jumpBlockCost d B g m r τ T P Z := by
  let Z' := prependNewBlockJump d P Z γ V
  have hpath : (∑j, physicalTollCost d g m (Z'.paths 0 j).1) =
      physicalTollCost d g m γ.1 + ∑j, physicalTollCost d g m (Z.paths 0 j).1 := by
    change (∑j : Fin ((P.2.2 0).val+2), physicalTollCost d g m
      ((Fin.cons γ (Z.paths 0) : Fin ((P.2.2 0).val+2) → TaggedPhysicalPath d) j).1) = _
    rw [Fin.sum_univ_succ]
    rfl
  have hdisk : (∑i, fixedWidthJumpToll B m r τ (Z'.disks 0 i)) =
      fixedWidthJumpToll B m r τ V + ∑i, fixedWidthJumpToll B m r τ (Z.disks 0 i) := by
    change (∑i : Fin ((P.2.2 0).val+1), fixedWidthJumpToll B m r τ
      ((Fin.cons V (Z.disks 0) : Fin ((P.2.2 0).val+1) → Set X) i)) = _
    rw [Fin.sum_univ_succ]
    rfl
  have htail (b : Fin P.1.val) :
      (∑j, physicalTollCost d g m (Z'.paths b.succ j).1) =
        ∑j, physicalTollCost d g m (Z.paths b.succ j).1 := rfl
  have hdtail (b : Fin P.1.val) :
      (∑i, fixedWidthJumpToll B m r τ (Z'.disks b.succ i)) =
        ∑i, fixedWidthJumpToll B m r τ (Z.disks b.succ i) := rfl
  change ((∑b, ((∑j, physicalTollCost d g m (Z'.paths b j).1) +
      ∑i, fixedWidthJumpToll B m r τ (Z'.disks b i))) + ∑i, T (P.2.1 i)) =
    physicalTollCost d g m γ.1 + fixedWidthJumpToll B m r τ V +
      ((∑b, ((∑j, physicalTollCost d g m (Z.paths b j).1) +
        ∑i, fixedWidthJumpToll B m r τ (Z.disks b i))) + ∑i, T (P.2.1 i))
  conv_lhs => rw [Fin.sum_univ_succ]
  conv_rhs => rw [Fin.sum_univ_succ]
  rw [hpath, hdisk]
  simp_rw [htail, hdtail]
  ac_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PrependOldBlockJump
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prepend an old jump, creating a new first block with one true piece.
The old disk label and its toll are retained exactly. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem blockAnchors_prependOld_tail {X I : Type*} {n : ℕ}
    (F H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n) (i : I)
    (k : Fin (P.1.val+2)) :
    blockAnchors F H O (prependOldJumpPattern P i) k.succ = blockAnchors (O i) H O P k := by
  have hlabels : (fun j => O ((prependOldJumpPattern P i).2.1 j)) =
      Fin.cons (O i) (fun j => O (P.2.1 j)) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp only [blockAnchors, Fin.cons_succ, hlabels]
  rw [← Fin.cons_snoc_eq_snoc_cons]

theorem blockAnchors_change_first_succ {X I : Type*} {n : ℕ}
    (F F' H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (k : Fin (P.1.val+1)) :
    blockAnchors F H O P k.succ = blockAnchors F' H O P k.succ := rfl

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] {n : ℕ}

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem prependOldBlockJump_valid
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F F' H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : IsJumpBlockCode d ν N B F H O P Z)
    (γ : TaggedPhysicalPath d) (hγ : AllowedTaggedPath d ν N (γ.1.val, γ.2))
    (i : I) (hstart : γ.1.val ⊥ ∈ F' ∩ d.quotientDomain)
    (hleft : γ.1.val ⊤ ∈ O i ∩ d.quotientDomain)
    (hright : (Z.paths 0 0).1.val ⊥ ∈ O i ∩ d.quotientDomain) :
    IsJumpBlockCode d ν N B F' H O (prependOldJumpPattern P i) (prependOldBlockJump d P Z γ i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact Fin.cases (fun _ => hγ) (fun b j => hZ.allowed b j) b
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · change γ.1.val ⊥ ∈ F' ∩ d.quotientDomain
      exact hstart
    · rw [Fin.castSucc_succ, blockAnchors_prependOld_tail]
      refine Fin.cases ?_ (fun b => ?_) b
      · change (Z.paths 0 0).1.val ⊥ ∈ O i ∩ d.quotientDomain
        exact hright
      · change (Z.paths b.succ 0).1.val ⊥ ∈
          blockAnchors (O i) H O P b.succ.castSucc ∩ d.quotientDomain
        rw [blockAnchors_internal]
        have h := hZ.start b.succ
        rw [blockAnchors_internal] at h
        exact h
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · change γ.1.val ⊤ ∈ blockAnchors F' H O (prependOldJumpPattern P i) (0 : Fin (P.1.val+2)).succ ∩ _
      rw [blockAnchors_prependOld_tail, blockAnchors_zero]
      exact hleft
    · rw [blockAnchors_prependOld_tail]
      change (Z.paths b (Fin.last (P.2.2 b).val)).1.val ⊤ ∈
        blockAnchors (O i) H O P b.succ ∩ d.quotientDomain
      rw [blockAnchors_change_first_succ (O i) F H O P]
      exact hZ.finish b
  · intro b
    exact Fin.cases (fun j => Fin.elim0 j) (fun b j => hZ.left b j) b
  · intro b
    exact Fin.cases (fun j => Fin.elim0 j) (fun b j => hZ.right b j) b
  · intro b
    exact Fin.cases (fun j => Fin.elim0 j) (fun b j => hZ.meets b j) b

omit [MeasurableSpace X] in
theorem prependOldBlockJump_cost
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (γ : TaggedPhysicalPath d) (i : I) :
    jumpBlockCost d B g m r τ T (prependOldJumpPattern P i) (prependOldBlockJump d P Z γ i) =
      physicalTollCost d g m γ.1 + T i + jumpBlockCost d B g m r τ T P Z := by
  let Z' := prependOldBlockJump d P Z γ i
  have hpath : (∑j, physicalTollCost d g m (Z'.paths 0 j).1) =
      physicalTollCost d g m γ.1 := by
    change (∑j : Fin 1, physicalTollCost d g m γ.1) = _
    simp
  have hdisk : (∑k, fixedWidthJumpToll B m r τ (Z'.disks 0 k)) = 0 := by
    change (∑k : Fin 0, fixedWidthJumpToll B m r τ (Z'.disks 0 k)) = 0
    simp
  have htail (b : Fin (P.1.val+1)) :
      (∑j, physicalTollCost d g m (Z'.paths b.succ j).1) =
        ∑j, physicalTollCost d g m (Z.paths b j).1 := rfl
  have hdtail (b : Fin (P.1.val+1)) :
      (∑k, fixedWidthJumpToll B m r τ (Z'.disks b.succ k)) =
        ∑k, fixedWidthJumpToll B m r τ (Z.disks b k) := rfl
  have hlabel : (∑k, T ((prependOldJumpPattern P i).2.1 k)) =
      T i + ∑k, T (P.2.1 k) := by
    change (∑k : Fin (P.1.val+1), T ((Fin.cons i P.2.1 : Fin (P.1.val+1) → I) k)) = _
    rw [Fin.sum_univ_succ]
    rfl
  change ((∑b, ((∑j, physicalTollCost d g m (Z'.paths b j).1) +
      ∑k, fixedWidthJumpToll B m r τ (Z'.disks b k))) +
        ∑k, T ((prependOldJumpPattern P i).2.1 k)) =
    physicalTollCost d g m γ.1 + T i +
      ((∑b, ((∑j, physicalTollCost d g m (Z.paths b j).1) +
        ∑k, fixedWidthJumpToll B m r τ (Z.disks b k))) + ∑k, T (P.2.1 k))
  conv_lhs => rw [Fin.sum_univ_succ]
  rw [hpath, hdisk, hlabel]
  simp_rw [htail, hdtail]
  simp only [add_zero]
  ac_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ReanchorBlockCode
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The outer anchors of a grouped chain may be changed when its actual
first and last endpoints lie in the new anchors. Internal jumps are untouched. -/

open Set MeasureTheory

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] {n : ℕ}

theorem reanchor_jumpBlockCode
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F H F' H' : Set X) (O : I → Set X) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : IsJumpBlockCode d ν N B F H O P Z)
    (hstart : (Z.paths 0 0).1.val ⊥ ∈ F' ∩ d.quotientDomain)
    (hend : (Z.paths (Fin.last P.1.val) (Fin.last (P.2.2 (Fin.last P.1.val)).val)).1.val ⊤ ∈
      H' ∩ d.quotientDomain) :
    IsJumpBlockCode d ν N B F' H' O P Z := by
  refine ⟨hZ.allowed, ?_, ?_, hZ.left, hZ.right, hZ.meets⟩
  · intro b
    refine Fin.cases ?_ (fun b => ?_) b
    · simpa using hstart
    · rw [blockAnchors_internal]
      have h := hZ.start b.succ
      rw [blockAnchors_internal] at h
      exact h
  · intro b
    refine Fin.lastCases ?_ (fun b => ?_) b
    · simpa only [Fin.succ_last, blockAnchors_last] using hend
    · rw [Fin.succ_castSucc, blockAnchors_internal]
      have h := hZ.finish b.castSucc
      rw [Fin.succ_castSucc, blockAnchors_internal] at h
      exact h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SinglePieceBlock
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single true path as a grouped chain with no old or new jumps. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem singlePieceBlock_valid
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F H : Set X) (O : I → Set X) (γ : TaggedPhysicalPath d)
    (hγ : AllowedTaggedPath d ν N (γ.1.val, γ.2))
    (hstart : γ.1.val ⊥ ∈ F ∩ d.quotientDomain)
    (hend : γ.1.val ⊤ ∈ H ∩ d.quotientDomain) :
    IsJumpBlockCode d ν N B F H O (singlePiecePattern I) (singlePieceBlock d γ) := by
  refine ⟨fun _ _ => hγ, ?_, ?_, fun _ i => Fin.elim0 i,
    fun _ i => Fin.elim0 i, fun _ i => Fin.elim0 i⟩
  · intro b
    have hb : b = 0 := by
      apply Fin.ext
      have hlt : b.val < 1 := b.isLt
      omega
    subst b
    simpa [singlePieceBlock] using hstart
  · intro b
    have hb : b = 0 := by
      apply Fin.ext
      have hlt : b.val < 1 := b.isLt
      omega
    subst b
    change γ.1.val ⊤ ∈ H ∩ d.quotientDomain
    exact hend

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_BlockCodeInvariants
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Domain-endpoint and disk-origin invariants for normalization of mixed
paid chains into grouped jump codes. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity

variable {X Y I K : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] {n : ℕ}

theorem jumpBlockCode_initial_eq
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B H : Set X) (O : I → Set X) (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P)
    {x : X} (hZ : IsJumpBlockCode d ν N B {x} H O P Z) : (Z.paths 0 0).1.val ⊥ = x := by
  have h := (hZ.start 0).1
  simpa only [Fin.castSucc_zero, blockAnchors_zero, mem_singleton_iff] using h

theorem jumpBlockCode_terminal_eq
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F : Set X) (O : I → Set X) (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P)
    {y : X} (hZ : IsJumpBlockCode d ν N B F {y} O P Z) :
    (Z.paths (Fin.last P.1.val) (Fin.last (P.2.2 (Fin.last P.1.val)).val)).1.val ⊤ = y := by
  have h := (hZ.finish (Fin.last P.1.val)).1
  simpa only [Fin.succ_last, blockAnchors_last, mem_singleton_iff] using h

omit [MeasurableSpace X] in
theorem singlePieceBlock_inDomain (d : PathCodeData X Y) (γ : TaggedPhysicalPath d)
    (h0 : γ.1.val ⊥ ∈ d.quotientDomain) (h1 : γ.1.val ⊤ ∈ d.quotientDomain) :
    BlockPathsInDomain d (singlePiecePattern I) (singlePieceBlock d γ) := fun _ _ => ⟨h0, h1⟩

omit [MeasurableSpace X] in
theorem singlePieceBlock_disksFrom (d : PathCodeData X Y) (γ : TaggedPhysicalPath d) (W : K → Set X) :
    BlockDisksFrom d W (singlePiecePattern I) (singlePieceBlock d γ) := fun _ i => Fin.elim0 i

omit [MeasurableSpace X] in
theorem replaceInitialTruePiece_inDomain (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : BlockPathsInDomain d P Z) (γ : TaggedPhysicalPath d)
    (h0 : γ.1.val ⊥ ∈ d.quotientDomain) (h1 : γ.1.val ⊤ ∈ d.quotientDomain) :
    BlockPathsInDomain d P (replaceInitialTruePiece d P Z γ) := by
  intro b
  refine Fin.cases ?_ (fun b j => hZ b.succ j) b
  intro j
  exact Fin.cases ⟨h0, h1⟩ (fun j => hZ 0 j.succ) j

omit [MeasurableSpace X] in
theorem replaceInitialTruePiece_disksFrom (d : PathCodeData X Y) (W : K → Set X)
    (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) (hZ : BlockDisksFrom d W P Z)
    (γ : TaggedPhysicalPath d) : BlockDisksFrom d W P (replaceInitialTruePiece d P Z γ) := hZ

omit [MeasurableSpace X] in
theorem prependNewBlockJump_inDomain (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : BlockPathsInDomain d P Z) (γ : TaggedPhysicalPath d) (V : Set X)
    (h0 : γ.1.val ⊥ ∈ d.quotientDomain) (h1 : γ.1.val ⊤ ∈ d.quotientDomain) :
    BlockPathsInDomain d (prependNewJumpPattern P) (prependNewBlockJump d P Z γ V) := by
  intro b
  refine Fin.cases ?_ (fun b j => hZ b.succ j) b
  intro j
  exact Fin.cases ⟨h0, h1⟩ (fun j => hZ 0 j) j

omit [MeasurableSpace X] in
theorem prependNewBlockJump_disksFrom (d : PathCodeData X Y) (W : K → Set X)
    (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) (hZ : BlockDisksFrom d W P Z)
    (γ : TaggedPhysicalPath d) (k : K) :
    BlockDisksFrom d W (prependNewJumpPattern P) (prependNewBlockJump d P Z γ (W k)) := by
  intro b
  refine Fin.cases ?_ (fun b i => hZ b.succ i) b
  intro i
  exact Fin.cases ⟨k, rfl⟩ (fun i => hZ 0 i) i

omit [MeasurableSpace X] in
theorem prependOldBlockJump_inDomain (d : PathCodeData X Y) (P : BoundedBlockPattern I n)
    (Z : JumpBlockCode d P) (hZ : BlockPathsInDomain d P Z) (γ : TaggedPhysicalPath d) (i : I)
    (h0 : γ.1.val ⊥ ∈ d.quotientDomain) (h1 : γ.1.val ⊤ ∈ d.quotientDomain) :
    BlockPathsInDomain d (prependOldJumpPattern P i) (prependOldBlockJump d P Z γ i) := by
  intro b
  exact Fin.cases (fun _ => ⟨h0, h1⟩) (fun b j => hZ b j) b

omit [MeasurableSpace X] in
theorem prependOldBlockJump_disksFrom (d : PathCodeData X Y) (W : K → Set X)
    (P : BoundedBlockPattern I n) (Z : JumpBlockCode d P) (hZ : BlockDisksFrom d W P Z)
    (γ : TaggedPhysicalPath d) (i : I) :
    BlockDisksFrom d W (prependOldJumpPattern P i) (prependOldBlockJump d P Z γ i) := by
  intro b
  exact Fin.cases (fun j => Fin.elim0 j) (fun b j => hZ b j) b

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_MixedChainNormalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize an arbitrary mixed paid chain into grouped old-jump blocks.
Consecutive true pieces are joined; a jump receives a zero-cost constant
true piece when needed. Total cost and all new disk labels are preserved. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I K : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_grouped_code_of_paid_chain
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B : Set X) (O : I → Set X) (W : K → Set X) (hW : ∀k, (W k ∩ B).Nonempty)
    (T : I → ℝ≥0∞) (r : ℝ≥0∞) (τ : ℝ)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {x y : X} {c : ℝ≥0∞}
    (hc : PaidChain (physicalJumpEdge d ν N g m (Sum.elim O W)
      (Sum.elim T (fun k => fixedWidthJumpToll B m r τ (W k)))) x y c)
    (hx : x ∈ d.quotientDomain) (hy : y ∈ d.quotientDomain) :
    ∃n : ℕ, ∃P : BoundedBlockPattern I n, ∃Z : JumpBlockCode d P,
      IsJumpBlockCode d ν N B {x} {y} O P Z ∧ jumpBlockCost d B g m r τ T P Z = c ∧
      BlockPathsInDomain d P Z ∧ BlockDisksFrom d W P Z := by
  classical
  induction hc with
  | refl x =>
      obtain ⟨γ, θ, hγ, heq, hcost⟩ := exists_allowed_constant_physical_path d hdisj ν N hx g m (hm _ hx)
      let Γ : TaggedPhysicalPath d := (γ, θ)
      refine ⟨0, singlePiecePattern I, singlePieceBlock d Γ, ?_, ?_, ?_, ?_⟩
      · exact singlePieceBlock_valid d ν N B {x} {x} O Γ hγ
          ⟨heq ⊥, (heq ⊥).symm ▸ hx⟩ ⟨heq ⊤, (heq ⊤).symm ▸ hx⟩
      · rw [singlePieceBlock_cost]
        exact hcost
      · exact singlePieceBlock_inDomain d Γ ((heq ⊥).symm ▸ hx) ((heq ⊤).symm ▸ hx)
      · exact singlePieceBlock_disksFrom d Γ W
  | @cons x y z a b hedge _ ih =>
      rcases hedge with ⟨Γ, hΓ, hΓ0, hΓ1, hxU, hyU, hΓcost⟩ | ⟨i, hxV, hyV, ha⟩
      · obtain ⟨n, P, Z, hZ, hZcost, hdom, hfrom⟩ := ih hyU hy
        have hinit := jumpBlockCode_initial_eq d ν N B {z} O P Z hZ
        obtain ⟨γ, hγ, hγ0, hγ1, hγcost⟩ := exists_allowed_joined_full_cost d hU ν N g hg m hm
          Γ (Z.paths 0 0) hΓ (hZ.allowed 0 0) (hΓ0.symm ▸ hxU) (hΓ1.symm ▸ hyU)
          (hdom 0 0).2 (hΓ1.trans hinit.symm) hpoint
        have hstart : γ.1.val ⊥ ∈ {x} ∩ d.quotientDomain :=
          ⟨hγ0.trans hΓ0, (hγ0.trans hΓ0).symm ▸ hxU⟩
        have hpcost : physicalTollCost d g m γ.1 = a + physicalTollCost d g m (Z.paths 0 0).1 := by
          rw [hγcost, hΓcost]
        refine ⟨n, P, replaceInitialTruePiece d P Z γ, ?_, ?_, ?_, ?_⟩
        · exact replaceInitialTruePiece_valid d ν N B {y} {x} {z} O P Z hZ γ hγ hstart hγ1
        · rw [replaceInitialTruePiece_cost d B g m r τ T P Z γ a hpcost, hZcost]
        · exact replaceInitialTruePiece_inDomain d P Z hdom γ hstart.2 (hγ1.symm ▸ (hdom 0 0).2)
        · exact replaceInitialTruePiece_disksFrom d W P Z hfrom γ
      · cases i with
        | inl i =>
            obtain ⟨n, P, Z, hZ, hZcost, hdom, hfrom⟩ := ih hyV.2 hy
            have hinit := jumpBlockCode_initial_eq d ν N B {z} O P Z hZ
            obtain ⟨γ, θ, hγ, heq, hγcost⟩ := exists_allowed_constant_physical_path
              d hdisj ν N hxV.2 g m (hm _ hxV.2)
            let Γ : TaggedPhysicalPath d := (γ, θ)
            have hstart : Γ.1.val ⊥ ∈ {x} ∩ d.quotientDomain :=
              ⟨heq ⊥, (heq ⊥).symm ▸ hxV.2⟩
            have hleft : Γ.1.val ⊤ ∈ O i ∩ d.quotientDomain := (heq ⊤).symm ▸ hxV
            have hright : (Z.paths 0 0).1.val ⊥ ∈ O i ∩ d.quotientDomain := hinit.symm ▸ hyV
            refine ⟨n+1, prependOldJumpPattern P i, prependOldBlockJump d P Z Γ i, ?_, ?_, ?_, ?_⟩
            · exact prependOldBlockJump_valid d ν N B {y} {x} {z} O P Z hZ Γ hγ i hstart hleft hright
            · rw [prependOldBlockJump_cost, hγcost, zero_add, hZcost]
              exact congrArg (fun t => t + b) ha.symm
            · exact prependOldBlockJump_inDomain d P Z hdom Γ i hstart.2 hleft.2
            · exact prependOldBlockJump_disksFrom d W P Z hfrom Γ i
        | inr k =>
            obtain ⟨n, P, Z, hZ, hZcost, hdom, hfrom⟩ := ih hyV.2 hy
            have hinit := jumpBlockCode_initial_eq d ν N B {z} O P Z hZ
            obtain ⟨γ, θ, hγ, heq, hγcost⟩ := exists_allowed_constant_physical_path
              d hdisj ν N hxV.2 g m (hm _ hxV.2)
            let Γ : TaggedPhysicalPath d := (γ, θ)
            have hstart : Γ.1.val ⊥ ∈ {x} ∩ d.quotientDomain :=
              ⟨heq ⊥, (heq ⊥).symm ▸ hxV.2⟩
            have hleft : Γ.1.val ⊤ ∈ W k := (heq ⊤).symm ▸ hxV.1
            have hright : (Z.paths 0 0).1.val ⊥ ∈ W k := hinit.symm ▸ hyV.1
            refine ⟨n+1, prependNewJumpPattern P, prependNewBlockJump d P Z Γ (W k), ?_, ?_, ?_, ?_⟩
            · exact prependNewBlockJump_valid d ν N B {y} {x} {z} O P Z hZ Γ hγ (W k)
                hstart hleft hright (hW k)
            · rw [prependNewBlockJump_cost, hγcost, zero_add, hZcost]
              exact congrArg (fun t => t + b) ha.symm
            · exact prependNewBlockJump_inDomain d P Z hdom Γ (W k) hstart.2 ((heq ⊤).symm ▸ hxV.2)
            · exact prependNewBlockJump_disksFrom d W P Z hfrom Γ k

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteJumpFloor
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finitely many positive old tolls and the positive new-jump floor have
one common positive real lower bound. -/

open scoped ENNReal

namespace CircleDomainRigidity

theorem exists_common_positive_jump_floor {I : Type*} [Fintype I]
    (r : ℝ≥0∞) (hr : 0 < r) (T : I → ℝ≥0∞) (hT : ∀i, 0 < T i) :
    ∃δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ r ∧ ∀i, ENNReal.ofReal δ ≤ T i := by
  classical
  let c : Option I → ℝ≥0∞ := fun i => i.elim r T
  have hne : (Finset.univ : Finset (Option I)).Nonempty := ⟨none, Finset.mem_univ _⟩
  have hc : 0 < Finset.univ.inf' hne c := by
    apply (Finset.lt_inf'_iff hne).mpr
    intro i _
    cases i with
    | none => exact hr
    | some i => exact hT i
  obtain ⟨δ, hδ, hd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have hle (i : Option I) : ENNReal.ofReal (δ : ℝ) ≤ c i := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hd.le.trans (Finset.inf'_le c (Finset.mem_univ i))
  refine ⟨δ, ?_, hle none, fun i => hle (some i)⟩
  exact_mod_cast (ENNReal.coe_pos.mp hδ)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteJumpCompactness
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common compactness for finitely many shrinking new jumps and true
pieces, retaining fixed old-jump costs in the limiting total budget. -/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X I P : Type*} [MetricSpace X] [CompactSpace X] [Fintype I] [Fintype P]

theorem exists_joint_finite_jump_limits
    (B : Set X) (hB : IsClosed B) (m : X → ℝ≥0∞) (r : ℝ≥0∞)
    {τ : ℝ} (hτ : 0 < τ) (V : I → ℕ → Set X) (x y : I → ℕ → X)
    (c : P → ℕ → ℝ≥0∞)
    (hx : ∀i k, x i k ∈ V i k) (hy : ∀i k, y i k ∈ V i k)
    (hmeet : ∀i k, (V i k ∩ B).Nonempty)
    (hdiam : ∀i, Tendsto (fun k => diam (V i k)) atTop (𝓝 0))
    (K M : ℝ≥0∞)
    (hbudget : ∀k, (∑i, c i k) + (∑i, fixedWidthJumpToll B m r τ (V i k)) + K ≤ M) :
    ∃ (s : ℕ → ℕ) (p : I → X) (A : P → ℝ≥0∞) (J : I → ℝ≥0∞),
      StrictMono s ∧ (∀i, p i ∈ B) ∧
      (∀i, Tendsto (x i ∘ s) atTop (𝓝 (p i))) ∧
      (∀i, Tendsto (y i ∘ s) atTop (𝓝 (p i))) ∧
      (∀i, Tendsto (c i ∘ s) atTop (𝓝 (A i))) ∧
      (∀i, Tendsto (fun k => fixedWidthJumpToll B m r τ (V i (s k))) atTop (𝓝 (J i))) ∧
      (∀i, m (p i) ≤ J i) ∧ (∑i, A i) + (∑i, J i) + K ≤ M := by
  let v : ℕ → (I → X) × (P → ℝ≥0∞) × (I → ℝ≥0∞) :=
    fun k => (fun i => x i k, (fun i => c i k),
      (fun i => fixedWidthJumpToll B m r τ (V i k)))
  obtain ⟨q, _, s, hs, hv⟩ := isCompact_univ.tendsto_subseq (fun k => mem_univ (v k))
  have hxs (i : I) : Tendsto (x i ∘ s) atTop (𝓝 (q.1 i)) :=
    ((continuous_apply i).tendsto q.1).comp ((continuous_fst.tendsto q).comp hv)
  have hAs (i : P) : Tendsto (c i ∘ s) atTop (𝓝 (q.2.1 i)) :=
    ((continuous_apply i).tendsto q.2.1).comp
      ((continuous_fst.tendsto q.2).comp ((continuous_snd.tendsto q).comp hv))
  have hJs (i : I) :
      Tendsto (fun k => fixedWidthJumpToll B m r τ (V i (s k))) atTop (𝓝 (q.2.2 i)) :=
    ((continuous_apply i).tendsto q.2.2).comp
      ((continuous_snd.tendsto q.2).comp ((continuous_snd.tendsto q).comp hv))
  have hclose (i : I) (z : ℕ → X) (hz : ∀k, z k ∈ V i k) :
      Tendsto (fun k => dist (x i (s k)) (z (s k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ ((hdiam i).comp hs.tendsto_atTop)
    intro k
    exact dist_le_diam_of_mem
      ((isCompact_univ : IsCompact (univ : Set X)).isBounded.subset (subset_univ (V i (s k))))
      (hx i (s k)) (hz (s k))
  have hpB (i : I) : q.1 i ∈ B := by
    choose b hb using hmeet i
    exact hB.mem_of_tendsto ((hxs i).congr_dist (hclose i b (fun k => (hb k).1)))
      (Eventually.of_forall (fun k => (hb (s k)).2))
  have hys (i : I) : Tendsto (y i ∘ s) atTop (𝓝 (q.1 i)) :=
    (hxs i).congr_dist (hclose i (y i) (hy i))
  have hpaid (i : I) : m (q.1 i) ≤ q.2.2 i :=
    limiting_fixedWidthJumpToll_ge B m r hτ (hxs i) (fun k => hx i (s k)) (hpB i) (hJs i)
  have htotal : Tendsto (fun k => (∑i, c i (s k)) +
      (∑i, fixedWidthJumpToll B m r τ (V i (s k))) + K) atTop
      (𝓝 ((∑i, q.2.1 i) + (∑i, q.2.2 i) + K)) :=
    ((tendsto_finsetSum _ (fun i _ => hAs i)).add
      (tendsto_finsetSum _ (fun i _ => hJs i))).add tendsto_const_nhds
  exact ⟨s, q.1, q.2.1, q.2.2, hs, hpB, hxs, hys, hAs, hJs, hpaid,
    le_of_tendsto htotal (Eventually.of_forall (fun k => hbudget (s k)))⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FixedPatternJumpRemoval
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove all new shrinking jumps from a fixed finite old-jump pattern.
All blocks use one common subsequence, so the total budget is retained. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_15 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_old_chain_of_shrinking_blocks
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (q : ℕ) (E : Fin (q+2) → Set Sphere)
    (hE : ∀i, frontier (E i) ⊆ d.quotientDomain) (T : Fin q → ℝ≥0∞)
    (shape : Fin (q+1) → ℕ)
    (Γ : ∀b, Fin (shape b + 1) → ℕ → TaggedPhysicalPath d)
    (hΓ : ∀b j k, AllowedTaggedPath d ν N ((Γ b j k).1.val, (Γ b j k).2))
    (hΓF : ∀b k, (Γ b 0 k).1.val ⊥ ∈ E b.castSucc ∩ d.quotientDomain)
    (hΓH : ∀b k, (Γ b (Fin.last (shape b)) k).1.val ⊤ ∈ E b.succ ∩ d.quotientDomain)
    (V : ∀b, Fin (shape b) → ℕ → Set Sphere)
    (hleft : ∀b i k, (Γ b i.castSucc k).1.val ⊤ ∈ V b i k)
    (hright : ∀b i k, (Γ b i.succ k).1.val ⊥ ∈ V b i k)
    (hmeet : ∀b i k, (V b i k ∩ B).Nonempty)
    (hdiam : ∀b i, Tendsto (fun k => Metric.diam (V b i k)) atTop (𝓝 0))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (M : ℝ≥0∞) (hM : M < ∞)
    (hbudget : ∀k, (∑b, ((∑j, physicalTollCost d g m (Γ b j k).1) +
      ∑i, fixedWidthJumpToll B m r τ (V b i k))) + (∑i, T i) ≤ M)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃x ∈ E 0 ∩ d.quotientDomain, ∃y ∈ E (Fin.last (q+1)) ∩ d.quotientDomain,
      ∃c : ℝ≥0∞,
        PaidChain (physicalJumpEdge d ν N g m (fun i : Fin q => E i.succ.castSucc) T) x y c ∧
        c ≤ M + ENNReal.ofReal η := by
  let I := Σb : Fin (q+1), Fin (shape b)
  let P := Σb : Fin (q+1), Fin (shape b + 1)
  let V' : I → ℕ → Set Sphere := fun i k => V i.1 i.2 k
  let x' : I → ℕ → Sphere := fun i k => (Γ i.1 i.2.castSucc k).1.val ⊤
  let y' : I → ℕ → Sphere := fun i k => (Γ i.1 i.2.succ k).1.val ⊥
  let c' : P → ℕ → ℝ≥0∞ := fun i k => physicalTollCost d g m (Γ i.1 i.2 k).1
  have hb (k : ℕ) : (∑i, c' i k) + (∑i, fixedWidthJumpToll B m r τ (V' i k)) +
      (∑i, T i) ≤ M := by
    simpa only [I, P, V', c', Fintype.sum_sigma, Finset.sum_add_distrib] using hbudget k
  obtain ⟨s, p, A, J, hs, hpB, hend, hstart, hcost, hJcost, hpaid, htotal⟩ :=
    exists_joint_finite_jump_limits B hB m r hτ V' x' y' c'
      (fun i k => hleft i.1 i.2 k) (fun i k => hright i.1 i.2 k)
      (fun i k => hmeet i.1 i.2 k) (fun i => hdiam i.1 i.2) (∑i, T i) M hb
  have hp (i : I) : p i ≠ π OnePoint.infty := fun heq => hinfty (heq ▸ hpB i)
  have hA (i : P) : A i < ∞ := by
    have hi : A i ≤ ∑j, A j := Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ _)
    exact lt_of_le_of_lt (hi.trans ((le_add_right (le_add_right le_rfl)).trans htotal)) hM
  let C : Fin (q+1) → ℝ≥0∞ := fun b => (∑j, A ⟨b, j⟩) + (∑i, J ⟨b, i⟩)
  let R := physicalJumpEdge d ν N g m (fun i : Fin q => E i.succ.castSucc) T
  let E' : Fin (q+2) → Set Sphere := fun i => E i ∩ d.quotientDomain
  have hblocks (b : Fin (q+1)) (ε : ℝ) (hε : 0 < ε) :
      ∃x ∈ E' b.castSucc, ∃y ∈ E' b.succ, ∃c : ℝ≥0∞,
        PaidChain R x y c ∧ c ≤ C b + ENNReal.ofReal ε := by
    obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_path_replacing_finite_limit_block
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense
      ν N (E b.castSucc) (E b.succ) (hE _) (hE _) (shape b)
      (fun i => p ⟨b, i⟩) (fun i => hpB ⟨b, i⟩) (fun i => hp ⟨b, i⟩)
      (fun j k => Γ b j (s k)) (fun j k => hΓ b j (s k))
      (fun k => hΓF b (s k)) (fun k => hΓH b (s k))
      (fun i => hstart ⟨b, i⟩) (fun i => hend ⟨b, i⟩)
      g hg henergy m hm (fun j => A ⟨b, j⟩) (fun j => hA ⟨b, j⟩)
      (fun j => hcost ⟨b, j⟩) (fun i => J ⟨b, i⟩) (fun i => hpaid ⟨b, i⟩)
      w hw hpos hpoint hε
    exact ⟨ρ.val ⊥, hρ0, ρ.val ⊤, hρ1, physicalTollCost d g m ρ,
      PaidChain.single (physicalJumpEdge_of_path d ν N g m _ T (ρ, θ) hρ hρ0.2 hρ1.2), hc⟩
  have hjumps (i : Fin q) (x : Sphere) (hx : x ∈ E' i.succ.castSucc)
      (y : Sphere) (hy : y ∈ E' i.succ.castSucc) : R x y (T i) :=
    physicalJumpEdge_of_jump d ν N g m _ T i hx hy
  obtain ⟨x, hx, y, hy, c, hc, hbound⟩ :=
    exists_paid_chain_from_approximate_blocks R q E' C T hjumps hblocks hη
  refine ⟨x, hx, y, hy, c, hc, hbound.trans ?_⟩
  apply add_le_add _ le_rfl
  simpa only [C, P, I, Fintype.sum_sigma, Finset.sum_add_distrib] using htotal

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_BoundedJumpRemoval
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove all new shrinking jumps from a fixed finite old-jump pattern.
All blocks use one common subsequence, so the total budget is retained. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable {I : Type*} [Fintype I] [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_16 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_mesh_preserving_bounded_chain_lower_bound
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (O : I → Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (hO : ∀i, frontier (O i) ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (T : I → ℝ≥0∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {β Δ : ℝ} (hΔ : 0 < Δ) (hΔβ : Δ < β)
    (hlower : ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
      PaidChain (physicalJumpEdge d ν N g m O T) x y c → ENNReal.ofReal β ≤ c)
    (n : ℕ) :
    ∃ε : ℝ, 0 < ε ∧ ∀P : BoundedBlockPattern I n, ∀Z : JumpBlockCode d P,
      IsJumpBlockCode d ν N B F H O P Z →
      (∀b i, Metric.diam (Z.disks b i) ≤ ε) →
      ENNReal.ofReal (β-Δ) ≤ jumpBlockCost d B g m r τ T P Z := by
  classical
  by_contra h
  push Not at h
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε] <;> positivity
  choose P hP using (fun k => h (ε k) (hε k))
  obtain ⟨P₀, s, hs, heq⟩ := exists_constant_finite_pattern_subsequence P
  have hviolations (k : ℕ) : ∃Z : JumpBlockCode d P₀,
      IsJumpBlockCode d ν N B F H O P₀ Z ∧
      (∀b i, Metric.diam (Z.disks b i) ≤ ε (s k)) ∧
      jumpBlockCost d B g m r τ T P₀ Z < ENNReal.ofReal (β-Δ) := by
    have hk := hP (s k)
    rw [heq k] at hk
    exact hk
  choose Z hZ hmesh hcost using hviolations
  have heps : Tendsto (ε ∘ s) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hs.tendsto_atTop
  have hdiam (b : Fin (P₀.1.val+1)) (i : Fin (P₀.2.2 b).val) :
      Tendsto (fun k => Metric.diam ((Z k).disks b i)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => Metric.diam_nonneg) (fun k => hmesh k b i) heps
  let E := blockAnchors F H O P₀
  let T' : Fin P₀.1.val → ℝ≥0∞ := fun i => T (P₀.2.1 i)
  have hbudget (k : ℕ) :
      (∑b, ((∑j, physicalTollCost d g m ((Z k).paths b j).1) +
        ∑i, fixedWidthJumpToll B m r τ ((Z k).disks b i))) + (∑i, T' i) ≤
      ENNReal.ofReal (β-Δ) := (hcost k).le
  have hhalf : 0 < Δ/2 := by positivity
  obtain ⟨x, hx, y, hy, c, hc, hcb⟩ := exists_old_chain_of_shrinking_blocks
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N P₀.1.val E (blockAnchors_frontier F H d.quotientDomain O P₀ hF hH hO) T'
    (fun b => (P₀.2.2 b).val) (fun b j k => (Z k).paths b j)
    (fun b j k => (hZ k).allowed b j) (fun b k => (hZ k).start b)
    (fun b k => (hZ k).finish b) (fun b i k => (Z k).disks b i)
    (fun b i k => (hZ k).left b i) (fun b i k => (hZ k).right b i)
    (fun b i k => (hZ k).meets b i) hdiam
    g hg henergy m hm r hτ (ENNReal.ofReal (β-Δ)) ENNReal.ofReal_lt_top hbudget
    w hw hpos hpoint hhalf
  have hcOld : PaidChain (physicalJumpEdge d ν N g m O T) x y c := by
    clear hx hy hcb
    induction hc with
    | refl x => exact PaidChain.refl x
    | @cons x y z a b hxy _ ih =>
      apply PaidChain.cons ?_ ih
      rcases hxy with hpath | ⟨i, hxi, hyi, ha⟩
      · exact Or.inl hpath
      · change x ∈ blockAnchors F H O P₀ i.succ.castSucc ∩ d.quotientDomain at hxi
        change y ∈ blockAnchors F H O P₀ i.succ.castSucc ∩ d.quotientDomain at hyi
        rw [blockAnchors_internal] at hxi hyi
        exact Or.inr ⟨P₀.2.1 i, hxi, hyi, ha⟩
  have hxF : x ∈ F ∩ d.quotientDomain := by simpa [E] using hx
  have hyH : y ∈ H ∩ d.quotientDomain := by simpa [E] using hy
  have hstrict : ENNReal.ofReal (β-Δ) + ENNReal.ofReal (Δ/2) < ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ β-Δ) hhalf.le]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < β) |>.mpr (by linarith)
  exact (hlower x hxF y hyH c hcOld).not_gt (hcb.trans_lt hstrict)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpBlockCountBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive toll floor gives one finite code space for every chain
under a fixed budget, independent of its original code bound. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] in
theorem exists_uniform_block_pattern_bound
    (d : PathCodeData X Y) (B : Set X) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (r : ℝ≥0∞) (τ : ℝ) (T : I → ℝ≥0∞) {δ : ℝ} (hδ : 0 < δ)
    (hr : ENNReal.ofReal δ ≤ r) (hT : ∀i, ENNReal.ofReal δ ≤ T i)
    {M : ℝ≥0∞} (hM : M < ∞) :
    ∃N : ℕ, ∀n : ℕ, ∀P : BoundedBlockPattern I n, ∀Z : JumpBlockCode d P,
      jumpBlockCost d B g m r τ T P Z ≤ M →
      P.1.val ≤ N ∧ ∀b, (P.2.2 b).val ≤ N := by
  obtain ⟨N, hN⟩ := exists_uniform_jump_count_bound hδ hM
  refine ⟨N, fun n P Z hc => ⟨?_, fun b => ?_⟩⟩
  · apply hN P.1.val (fun i => T (P.2.1 i)) (fun i => hT (P.2.1 i))
    exact (le_add_left le_rfl).trans hc
  · apply hN (P.2.2 b).val (fun i => fixedWidthJumpToll B m r τ (Z.disks b i))
      (fun i => hr.trans (fixedWidthJumpToll_ge_floor B m r τ (Z.disks b i)))
    have hsingle : (∑j, physicalTollCost d g m (Z.paths b j).1) +
        (∑i, fixedWidthJumpToll B m r τ (Z.disks b i)) ≤
        ∑a, ((∑j, physicalTollCost d g m (Z.paths a j).1) +
          (∑i, fixedWidthJumpToll B m r τ (Z.disks a i))) :=
      Finset.single_le_sum
        (f := fun a : Fin (P.1.val+1) => (∑j, physicalTollCost d g m (Z.paths a j).1) +
          (∑i, fixedWidthJumpToll B m r τ (Z.disks a i)))
        (fun _ _ => zero_le) (Finset.mem_univ b)
    exact (le_add_left le_rfl).trans (hsingle.trans ((le_add_right le_rfl).trans hc))

omit [MeasurableSpace Y] [BorelSpace Y] in
theorem reboundJumpBlock_valid (d : PathCodeData X Y) (ν : Measure X)
    (Ntags : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (B F H : Set X) (O : I → Set X) {n N : ℕ} (P : BoundedBlockPattern I n)
    (hold : P.1.val ≤ N) (hnew : ∀b, (P.2.2 b).val ≤ N) (Z : JumpBlockCode d P)
    (hZ : IsJumpBlockCode d ν Ntags B F H O P Z) :
    IsJumpBlockCode d ν Ntags B F H O (reboundBlockPattern P hold hnew)
      (reboundJumpBlock d P hold hnew Z) :=
  ⟨hZ.allowed, hZ.start, hZ.finish, hZ.left, hZ.right, hZ.meets⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_JumpLevelRemoval
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove all new shrinking jumps from a fixed finite old-jump pattern.
All blocks use one common subsequence, so the total budget is retained. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable {I : Type*} [Fintype I] [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_17 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_mesh_preserving_chain_lower_bound
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (O : I → Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (hO : ∀i, frontier (O i) ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (T : I → ℝ≥0∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {β Δ : ℝ} (hΔ : 0 < Δ) (hΔβ : Δ < β)
    (hlower : ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
      PaidChain (physicalJumpEdge d ν N g m O T) x y c → ENNReal.ofReal β ≤ c)
    {δ : ℝ} (hδ : 0 < δ) (hrfloor : ENNReal.ofReal δ ≤ r)
    (hT : ∀i, ENNReal.ofReal δ ≤ T i) :
    ∃ε : ℝ, 0 < ε ∧ ∀n : ℕ, ∀P : BoundedBlockPattern I n, ∀Z : JumpBlockCode d P,
      IsJumpBlockCode d ν N B F H O P Z →
      (∀b i, Metric.diam (Z.disks b i) ≤ ε) →
      ENNReal.ofReal (β-Δ) ≤ jumpBlockCost d B g m r τ T P Z := by
  obtain ⟨K, hK⟩ := exists_uniform_block_pattern_bound d B g m r τ T hδ hrfloor hT
    (M := ENNReal.ofReal (β-Δ)) ENNReal.ofReal_lt_top
  obtain ⟨ε, hε, hmeshBound⟩ := exists_mesh_preserving_bounded_chain_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H O hF hH hO g hg henergy m hm r hτ T w hw hpos hpoint hΔ hΔβ hlower K
  refine ⟨ε, hε, fun n P Z hZ hmesh => ?_⟩
  by_contra hlow
  have hc : jumpBlockCost d B g m r τ T P Z < ENNReal.ofReal (β-Δ) := lt_of_not_ge hlow
  obtain ⟨hold, hnew⟩ := hK n P Z hc.le
  have hc' := hmeshBound (reboundBlockPattern P hold hnew) (reboundJumpBlock d P hold hnew Z)
    (reboundJumpBlock_valid d ν N B F H O P hold hnew Z hZ) hmesh
  exact hc.not_ge (by simpa using hc')

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_PositiveTollJumpRemoval
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove all new shrinking jumps from a fixed finite old-jump pattern.
All blocks use one common subsequence, so the total budget is retained. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable {I : Type*} [Fintype I] [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_18 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_mesh_preserving_positive_toll_chain_lower_bound
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (O : I → Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (hO : ∀i, frontier (O i) ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (T : I → ℝ≥0∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {β Δ : ℝ} (hΔ : 0 < Δ) (hΔβ : Δ < β)
    (hlower : ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
      PaidChain (physicalJumpEdge d ν N g m O T) x y c → ENNReal.ofReal β ≤ c)
    (hrpos : 0 < r) (hTpos : ∀i, 0 < T i) :
    ∃ε : ℝ, 0 < ε ∧ ∀n : ℕ, ∀P : BoundedBlockPattern I n, ∀Z : JumpBlockCode d P,
      IsJumpBlockCode d ν N B F H O P Z →
      (∀b i, Metric.diam (Z.disks b i) ≤ ε) →
      ENNReal.ofReal (β-Δ) ≤ jumpBlockCost d B g m r τ T P Z := by
  obtain ⟨δ, hδ, hrfloor, hT⟩ := exists_common_positive_jump_floor r hrpos T hTpos
  exact exists_mesh_preserving_chain_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H O hF hH hO g hg henergy m hm r hτ T w hw hpos hpoint hΔ hΔβ hlower hδ hrfloor hT

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SafeDustCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite small disjoint dust neighborhoods inside a prescribed safe open
set. Empty dust pieces are discarded, and every boundary avoids all dust. -/

open Set Metric Function Filter
open scoped Topology

namespace CircleDomainRigidity

theorem exists_safe_small_dust_cover
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {B W : Set X} (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    (hW : IsOpen W) (hBW : B ⊆ W) {ε : ℝ} (hε : 0 < ε) :
    ∃n : ℕ, ∃V : Fin n → Set X,
      (∀i, IsOpen (V i)) ∧ B ⊆ ⋃i, V i ∧
      Pairwise (Disjoint on fun i => closure (V i)) ∧
      (∀i, closure (V i) ⊆ W) ∧
      (∀i, diam (V i) < ε) ∧
      (∀i, (V i ∩ B).Nonempty) ∧
      (∀i, Disjoint (frontier (V i)) B) := by
  classical
  obtain ⟨A, hAo, hBA, hAW⟩ := hB.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hBW)
  obtain ⟨n, U, hUo, hBU, hUd, hdiam⟩ :=
    exists_small_disjoint_open_cover_of_compact_dust hB hTD hε
  let V₀ : Fin n → Set X := fun i => U i ∩ A
  let J := {i : Fin n // (V₀ i ∩ B).Nonempty}
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let V : Fin (Fintype.card J) → Set X := fun i => V₀ (e.symm i).val
  have hsub (i : Fin (Fintype.card J)) : closure (V i) ⊆ closure (U (e.symm i).val) :=
    closure_mono inter_subset_left
  have hcover : B ⊆ ⋃i, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hBU hx)
    let j : J := ⟨i, ⟨x, ⟨hi, hBA hx⟩, hx⟩⟩
    exact mem_iUnion.mpr ⟨e j, by simpa only [V, e.symm_apply_apply] using (show x ∈ V₀ i from ⟨hi, hBA hx⟩)⟩
  have hpair : Pairwise (Disjoint on fun i => closure (V i)) := by
    intro i j hij
    apply (hUd (show (e.symm i).val ≠ (e.symm j).val from ?_)).mono (hsub i) (hsub j)
    intro h
    exact hij (e.symm.injective (Subtype.ext h))
  refine ⟨Fintype.card J, V, fun i => (hUo _).inter hAo, hcover, hpair, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (closure_mono (show V i ⊆ A from inter_subset_right)).trans hAW
  · intro i
    exact (diam_mono ((subset_closure : V i ⊆ closure (V i)).trans (hsub i))
      (isClosed_closure.isCompact.isBounded)).trans_lt (hdiam _)
  · intro i
    exact (e.symm i).property
  · intro i
    apply Set.disjoint_left.mpr
    intro x hx hxB
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hxB)
    by_cases hij : i = j
    · subst j
      have hVo : IsOpen (V i) := (hUo _).inter hAo
      rw [hVo.frontier_eq] at hx
      exact hx.2 hj
    · exact Set.disjoint_left.mp (hpair hij) (frontier_subset_closure hx) (subset_closure hj)

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_NewJumpLevel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete new finite jump level inside the safe region. Its mesh may
be made arbitrarily small while retaining the old chain lower bound minus
the prescribed loss. Every new jump has positive toll and a domain boundary. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable {I : Type*} [Fintype I] [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_19 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_safe_new_jump_level
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere) (O : I → Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (hO : ∀i, frontier (O i) ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (r : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ) (T : I → ℝ≥0∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {β Δ : ℝ} (hΔ : 0 < Δ) (hΔβ : Δ < β)
    (hlower : ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
      PaidChain (physicalJumpEdge d ν N g m O T) x y c → ENNReal.ofReal β ≤ c)
    (hrpos : 0 < r) (hTpos : ∀i, 0 < T i)
    (hBU : Bᶜ ⊆ d.quotientDomain) (S : Set Sphere) (hS : IsOpen S) (hBS : B ⊆ S)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃n : ℕ, ∃V : Fin n → Set Sphere,
      (∀i, IsOpen (V i)) ∧ B ⊆ ⋃i, V i ∧
      Pairwise (Disjoint on fun i => closure (V i)) ∧
      (∀i, closure (V i) ⊆ S) ∧ (∀i, Metric.diam (V i) < mesh) ∧
      (∀i, (V i ∩ B).Nonempty) ∧
      (∀i, frontier (V i) ⊆ d.quotientDomain) ∧
      (∀i, 0 < fixedWidthJumpToll B m r τ (V i)) ∧
      ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
        PaidChain (physicalJumpEdge d ν N g m (Sum.elim O V)
          (Sum.elim T (fun i => fixedWidthJumpToll B m r τ (V i)))) x y c →
        ENNReal.ofReal (β-Δ) ≤ c := by
  obtain ⟨ε, hε, hbound⟩ := exists_mesh_preserving_positive_toll_chain_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H O hF hH hO g hg henergy m hm r hτ T w hw hpos hpoint hΔ hΔβ hlower hrpos hTpos
  obtain ⟨n, V, hVo, hcover, hpair, hsafe, hdiam, hmeet, hfront⟩ :=
    exists_safe_small_dust_cover hB.isCompact hTD hS hBS (lt_min hε hmesh)
  refine ⟨n, V, hVo, hcover, hpair, hsafe, fun i => (hdiam i).trans_le (min_le_right _ _),
    hmeet, ?_, ?_, ?_⟩
  · intro i x hx
    apply hBU
    exact fun hxB => Set.disjoint_left.mp (hfront i) hx hxB
  · intro i
    exact hrpos.trans_le (le_max_left _ _)
  · intro x hx y hy c hc
    obtain ⟨k, P, Z, hZ, hcost, _, hfrom⟩ := exists_grouped_code_of_paid_chain
      d hU hdisj ν N B O V hmeet T r τ g hg m hm hpoint hc hx.2 hy.2
    have hstart := jumpBlockCode_initial_eq d ν N B {y} O P Z hZ
    have hend := jumpBlockCode_terminal_eq d ν N B {x} O P Z hZ
    have hZa := reanchor_jumpBlockCode d ν N B {x} {y} F H O P Z hZ
      (hstart.symm ▸ hx) (hend.symm ▸ hy)
    rw [← hcost]
    apply hbound k P Z hZa
    intro b i
    obtain ⟨j, hj⟩ := hfrom b i
    rw [hj]
    exact (hdiam j).le.trans (min_le_left _ _)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_IncreasingChainRelations
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite chain in an increasing union already belongs to one finite
stage. This passes the retained barrier lower bound to all installed levels. -/

open Set
open scoped ENNReal

namespace CircleDomainRigidity

namespace PaidChain

variable {X : Type*} {R S : X → X → ℝ≥0∞ → Prop}

theorem mono_relation (hRS : ∀x y c, R x y c → S x y c)
    {x y : X} {c : ℝ≥0∞} (hc : PaidChain R x y c) : PaidChain S x y c := by
  induction hc with
  | refl x => exact .refl x
  | cons h _ ih => exact .cons (hRS _ _ _ h) ih

theorem exists_stage {R : ℕ → X → X → ℝ≥0∞ → Prop}
    (hmono : ∀n k, n ≤ k → ∀x y c, R n x y c → R k x y c)
    {x y : X} {c : ℝ≥0∞}
    (hc : PaidChain (fun x y c => ∃n, R n x y c) x y c) :
    ∃n, PaidChain (R n) x y c := by
  induction hc with
  | refl x => exact ⟨0, .refl x⟩
  | @cons x y z a b h _ ih =>
      obtain ⟨n, hn⟩ := h
      obtain ⟨k, hk⟩ := ih
      exact ⟨max n k, .cons (hmono n _ (le_max_left _ _) _ _ _ hn)
        (hk.mono_relation (hmono k _ (le_max_right _ _)))⟩

end PaidChain

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FiniteJumpSystems
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite jump systems and their successive extensions. The label type is
retained, so adjoining a level preserves every previously installed edge. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

namespace FiniteJumpSystem

variable {X : Type*}

variable {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem edge_append_old (A : FiniteJumpSystem X) (n : ℕ) (V : Fin n → Set X)
    (T : Fin n → ℝ≥0∞) (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) {x y : X} {a : ℝ≥0∞}
    (h : A.edge d ν N g m x y a) : (A.append n V T).edge d ν N g m x y a := by
  rcases h with h | ⟨i, hx, hy, ha⟩
  · exact Or.inl h
  · exact Or.inr ⟨Sum.inl i, hx, hy, ha⟩

theorem edge_append_new (A : FiniteJumpSystem X) (n : ℕ) (V : Fin n → Set X)
    (T : Fin n → ℝ≥0∞) (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (i : Fin n) {x y : X}
    (hx : x ∈ V i ∩ d.quotientDomain) (hy : y ∈ V i ∩ d.quotientDomain) :
    (A.append n V T).edge d ν N g m x y (T i) :=
  Or.inr ⟨Sum.inr i, hx, hy, rfl⟩

end FiniteJumpSystem

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_TrueChainConcatenation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite chain containing only true paths concatenates to one allowed
true path with exactly the same full cost. This supplies the initial stage. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_path_of_true_paid_chain
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {x y : X} {c : ℝ≥0∞}
    (hc : PaidChain ((FiniteJumpSystem.empty : FiniteJumpSystem X).edge d ν N g m) x y c)
    (hx : x ∈ d.quotientDomain) (hy : y ∈ d.quotientDomain) :
    ∃Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) ∧
      Γ.1.val ⊥ = x ∧ Γ.1.val ⊤ = y ∧ physicalTollCost d g m Γ.1 = c := by
  induction hc with
  | refl x =>
      obtain ⟨γ, θ, hγ, heq, hcost⟩ := exists_allowed_constant_physical_path
        d hdisj ν N hx g m (hm _ hx)
      exact ⟨(γ, θ), hγ, heq ⊥, heq ⊤, hcost⟩
  | @cons x y z a b hedge _ ih =>
      rcases hedge with ⟨Γ, hΓ, hΓ0, hΓ1, hxU, hyU, hΓcost⟩ | ⟨i, _⟩
      · obtain ⟨Δ, hΔ, hΔ0, hΔ1, hΔcost⟩ := ih hyU hy
        obtain ⟨ρ, hρ, hρ0, hρ1, hρcost⟩ := exists_allowed_joined_full_cost
          d hU ν N g hg m hm Γ Δ hΓ hΔ (hΓ0.symm ▸ hxU) (hΓ1.symm ▸ hyU)
          (hΔ1.symm ▸ hy) (hΓ1.trans hΔ0.symm) hpoint
        refine ⟨ρ, hρ, hρ0.trans hΓ0, hρ1.trans hΔ1, ?_⟩
        rw [hρcost, hΓcost, hΔcost]
      · exact PEmpty.elim i

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProgressiveJumpSystems
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Install all finite jump levels while retaining a common separation bound.
Each stage is obtained from the proved jump-removal theorem, and every finite
chain in the union is reduced to one finite stage. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_20 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_progressive_barrier_jump_system
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (htrue : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ F → Γ.1.val ⊤ ∈ H → ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1)
    (hBU : Bᶜ ⊆ d.quotientDomain) (S : Set Sphere) (hS : IsOpen S) (hBS : B ⊆ S)
    (ρ : ℕ → ℝ≥0∞) (hρ : ∀n, 0 < ρ n)
    (τ mesh : ℕ → ℝ) (hτ : ∀n, 0 < τ n) (hmesh : ∀n, 0 < mesh n) :
    ∃J : ℕ → FiniteJumpSystem Sphere,
      (∀n i, frontier ((J n).region i) ⊆ d.quotientDomain) ∧
      (∀n i, 0 < (J n).toll i) ∧
      (∀n x y c, (J n).edge d ν N g m x y c → (J (n+1)).edge d ν N g m x y c) ∧
      (∀n, ∃k : ℕ, ∃V : Fin k → Set Sphere,
        (∀i, IsOpen (V i)) ∧ B ⊆ ⋃i, V i ∧
        Pairwise (Disjoint on fun i => closure (V i)) ∧
        (∀i, closure (V i) ⊆ S) ∧ (∀i, Metric.diam (V i) < mesh n) ∧
        (∀i, (V i ∩ B).Nonempty) ∧
        ∀i x, x ∈ V i ∩ d.quotientDomain → ∀y, y ∈ V i ∩ d.quotientDomain →
          (J (n+1)).edge d ν N g m x y (fixedWidthJumpToll B m (ρ n) (τ n) (V i))) ∧
      ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
        PaidChain (fun x y c => ∃n, (J n).edge d ν N g m x y c) x y c →
          ENNReal.ofReal ((1 : ℝ)/4) ≤ c := by
  classical
  let Good (n : ℕ) (A : FiniteJumpSystem Sphere) : Prop :=
    (∀i, frontier (A.region i) ⊆ d.quotientDomain) ∧ (∀i, 0 < A.toll i) ∧
    ∀x ∈ F ∩ d.quotientDomain, ∀y ∈ H ∩ d.quotientDomain, ∀c,
      PaidChain (A.edge d ν N g m) x y c → ENNReal.ofReal (barrierStageLower n) ≤ c
  let Stage (n : ℕ) := {A : FiniteJumpSystem Sphere // Good n A}
  let Step (n : ℕ) (A C : FiniteJumpSystem Sphere) : Prop :=
    (∀x y c, A.edge d ν N g m x y c → C.edge d ν N g m x y c) ∧
    ∃k : ℕ, ∃V : Fin k → Set Sphere,
      (∀i, IsOpen (V i)) ∧ B ⊆ ⋃i, V i ∧
      Pairwise (Disjoint on fun i => closure (V i)) ∧
      (∀i, closure (V i) ⊆ S) ∧ (∀i, Metric.diam (V i) < mesh n) ∧
      (∀i, (V i ∩ B).Nonempty) ∧
      ∀i x, x ∈ V i ∩ d.quotientDomain → ∀y, y ∈ V i ∩ d.quotientDomain →
        C.edge d ν N g m x y (fixedWidthJumpToll B m (ρ n) (τ n) (V i))
  have hnext (n : ℕ) (A : Stage n) : ∃C : Stage (n+1), Step n A.val C.val := by
    let := A.val.finite
    obtain ⟨k, V, hVo, hcover, hpair, hsafe, hdiam, hmeet, hfront, hpositive, hlower⟩ :=
      exists_safe_new_jump_level hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj
        hr he hB hTD hbad hUB hdense hinfty ν N F H A.val.region hF hH A.property.1
        g hg henergy m hm (ρ n) (hτ n) A.val.toll w hw hpos hpoint
        (barrierStageLoss_pos n) (barrierStageLoss_lt n) A.property.2.2
        (hρ n) A.property.2.1 hBU S hS hBS (hmesh n)
    let C := A.val.append k V (fun i => fixedWidthJumpToll B m (ρ n) (τ n) (V i))
    have hC : Good (n+1) C := by
      refine ⟨?_, ?_, ?_⟩
      · intro i
        change A.val.Label ⊕ Fin k at i
        cases i with
        | inl i => exact A.property.1 i
        | inr i => exact hfront i
      · intro i
        change A.val.Label ⊕ Fin k at i
        cases i with
        | inl i => exact A.property.2.1 i
        | inr i => exact hpositive i
      · intro x hx y hy c hc
        have h := hlower x hx y hy c hc
        rw [barrierStageLower_sub_loss] at h
        exact h
    refine ⟨⟨C, hC⟩, ?_, k, V, hVo, hcover, hpair, hsafe, hdiam, hmeet, ?_⟩
    · intro x y c hc
      exact A.val.edge_append_old k V _ d ν N g m hc
    · intro i x hx y hy
      exact A.val.edge_append_new k V _ d ν N g m i hx hy
  have hzero : Good 0 FiniteJumpSystem.empty := by
    refine ⟨fun i => PEmpty.elim i, fun i => PEmpty.elim i, ?_⟩
    intro x hx y hy c hc
    obtain ⟨Γ, hΓ, hΓ0, hΓ1, hcost⟩ := exists_path_of_true_paid_chain
      d hU hdisj ν N g hg m hm hpoint hc hx.2 hy.2
    rw [barrierStageLower_zero, ← hcost]
    exact htrue Γ hΓ (hΓ0.symm ▸ hx.1) (hΓ1.symm ▸ hy.1)
  let A₀ : Stage 0 := ⟨FiniteJumpSystem.empty, hzero⟩
  let A : ∀n, Stage n := fun n => Nat.rec A₀ (fun n C => Classical.choose (hnext n C)) n
  have hstep (n : ℕ) : Step n (A n).val (A (n+1)).val :=
    Classical.choose_spec (hnext n (A n))
  let J : ℕ → FiniteJumpSystem Sphere := fun n => (A n).val
  have hmono (n k : ℕ) (hnk : n ≤ k) :
      ∀x y c, (J n).edge d ν N g m x y c → (J k).edge d ν N g m x y c := by
    induction k, hnk using Nat.le_induction with
    | base => exact fun _ _ _ h => h
    | succ k hk ih => exact fun x y c hc => (hstep k).1 x y c (ih x y c hc)
  refine ⟨J, fun n => (A n).property.1, fun n => (A n).property.2.1,
    fun n => (hstep n).1, fun n => (hstep n).2, ?_⟩
  intro x hx y hy c hc
  obtain ⟨n, hn⟩ := hc.exists_stage hmono
  exact (ENNReal.ofReal_le_ofReal (quarter_lt_barrierStageLower n).le).trans
    ((A n).property.2.2 x hx y hy c hn)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SupportedJumpTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For a dust-supported toll, restricting the neighborhood supremum to
the dust has no effect. -/

open Set
open scoped ENNReal

namespace CircleDomainRigidity

variable {X : Type*}

theorem neighborhoodTollSup_inter_eq (B V : Set X) (m : X → ℝ≥0∞)
    (hm : ∀x ∉ B, m x = 0) : neighborhoodTollSup m (B ∩ V) = neighborhoodTollSup m V := by
  unfold neighborhoodTollSup
  apply le_antisymm
  · exact iSup_le fun x => iSup_le fun hx => le_iSup_of_le x (le_iSup_of_le hx.2 le_rfl)
  · refine iSup_le fun x => iSup_le fun hx => ?_
    by_cases hxB : x ∈ B
    · exact le_iSup_of_le x (le_iSup_of_le ⟨hxB, hx⟩ le_rfl)
    · rw [hm x hxB]
      exact bot_le

variable [MetricSpace X]

theorem fixedWidthJumpToll_eq_neighborhood (B : Set X) (V : Set X)
    (m : X → ℝ≥0∞) (hm : ∀x ∉ B, m x = 0) (ρ : ℝ≥0∞) (τ : ℝ) :
    fixedWidthJumpToll B m ρ τ V = max ρ (neighborhoodTollSup m (Metric.thickening τ V)) := by
  rw [fixedWidthJumpToll, neighborhoodTollSup_inter_eq B _ m hm]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SymmetricJumpEdges
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! True path reversal and symmetric jumps make every installed chain
relation symmetric, with exactly the same costs. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem physicalJumpEdge_symmetric
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (V : I → Set X) (T : I → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {x y : X} {a : ℝ≥0∞} (h : physicalJumpEdge d ν N g m V T x y a) :
    physicalJumpEdge d ν N g m V T y x a := by
  rcases h with ⟨Γ, hΓ, hΓ0, hΓ1, hxU, hyU, hcost⟩ | ⟨i, hx, hy, ha⟩
  · refine Or.inl ⟨reversedTaggedPhysicalPath d Γ, ?_, ?_, ?_, hyU, hxU, ?_⟩
    · exact allowedTaggedPath_reversed d ν N (Γ.1.val, Γ.2) hΓ hpoint
    · change Γ.1.val (unitInterval.symm 0) = y
      rw [unitInterval.symm_zero]
      exact hΓ1
    · change Γ.1.val (unitInterval.symm 1) = x
      rw [unitInterval.symm_one]
      exact hΓ0
    · exact (physicalTollCost_reversed d g m Γ.1).trans hcost
  · exact Or.inr ⟨i, hy, hx, ha⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SeparatingChainPotential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual truncated chain distance separates the anchor and terminal
collar, obeys every true-path cost inequality, and has pointwise dust bands
bounded by four times the original toll. No barrier function is assumed. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_21 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_separating_chain_potential
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F H : Set Sphere)
    (hF : frontier F ⊆ d.quotientDomain) (hH : frontier H ⊆ d.quotientDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (htrue : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ F → Γ.1.val ⊤ ∈ H → ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1)
    (hBU : Bᶜ ⊆ d.quotientDomain) (S : Set Sphere) (hS : IsOpen S) (hBS : B ⊆ S)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞) :
    ∃u : Sphere → ℝ,
      (∀x, u x ∈ Icc 0 1) ∧
      (∀x ∈ F ∩ d.quotientDomain, u x = 0) ∧
      (∀x ∈ H ∩ d.quotientDomain, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  classical
  let q : ℕ → ℝ := fun n => (1/2)^n
  have hq (n : ℕ) : 0 < q n := pow_pos (by norm_num) n
  have hqlim : Tendsto q atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hρlim : Tendsto (fun n => ENNReal.ofReal (q n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hqlim
  obtain ⟨J, _, _, _, hlevels, hlower⟩ := exists_progressive_barrier_jump_system
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N F H hF hH g hg henergy m hm w hw hpos hpoint htrue hBU S hS hBS
    (fun n => ENNReal.ofReal (q n)) (fun n => ENNReal.ofReal_pos.mpr (hq n)) q q hq hq
  let R : Sphere → Sphere → ℝ≥0∞ → Prop := fun x y c => ∃n, (J n).edge d ν N g m x y c
  have hR (x y : Sphere) (c : ℝ≥0∞) (h : R x y c) : R y x c := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, physicalJumpEdge_symmetric d ν N g m (J n).region (J n).toll hpoint hn⟩
  let E := F ∩ d.quotientDomain
  refine ⟨realChainPotential R E, realChainPotential_mem_Icc R E, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change (chainPotential R E x).toReal = 0
    rw [chainPotential_anchor R hx]
    rfl
  · intro y hy
    have hsep : chainPotential R E y = 1 := chainPotential_separated R (fun x hx c hc => by
      simpa using hlower x hx y hy c hc)
    change (chainPotential R E y).toReal = 1
    rw [hsep]
    rfl
  · intro Γ hΓ hx hy
    apply realChainPotential_difference R hR
    exact ⟨0, physicalJumpEdge_of_path d ν N g m (J 0).region (J 0).toll Γ hΓ hx hy⟩
  · intro s hs
    choose k V hVo hcover _ _ hdiam _ hedge using hlevels
    have hindex (n : ℕ) : ∃i, s ∈ V n i := mem_iUnion.mp (hcover n hs)
    choose i hi using hindex
    let W : ℕ → Set Sphere := fun n => V n (i n)
    have hW (n : ℕ) : W n ∈ 𝓝 s := (hVo n (i n)).mem_nhds (hi n)
    have hWsmall (n : ℕ) : W n ⊆ Metric.ball s (q n) := by
      intro x hx
      exact (Metric.dist_le_diam_of_mem (Bornology.IsBounded.subset isCompact_univ.isBounded (subset_univ _))
        hx (hi n)).trans_lt (hdiam n (i n))
    have hmsupport (x : Sphere) (hx : x ∉ B) : m x = 0 := hm x (hBU hx)
    have hj (n : ℕ) (x : Sphere) (hx : x ∈ d.quotientDomain ∩ W n)
        (y : Sphere) (hy : y ∈ d.quotientDomain ∩ W n) :
        R x y (max (ENNReal.ofReal (q n)) (neighborhoodTollSup m (Metric.thickening (q n) (W n)))) := by
      have h := hedge n (i n) x ⟨hx.2, hx.1⟩ y ⟨hy.2, hy.1⟩
      rw [fixedWidthJumpToll_eq_neighborhood B _ m hmsupport] at h
      exact ⟨n+1, h⟩
    have hsclosure : s ∈ closure d.quotientDomain := by
      rw [hdense.closure_eq]
      trivial
    exact chainPotential_boundary_band R hR E d.quotientDomain hm₂ hsclosure hW hWsmall
      hqlim hqlim hρlim hj

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RawGatedBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combine the proved finite-gate penalty with the actual chain-distance
construction. This is the bounded raw barrier, before Sobolev regularization
and the compatibility argument for the new smooth coordinate. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_22 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_raw_gated_barrier
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (hUB : Disjoint d.quotientDomain B) (hdense : Dense d.quotientDomain)
    (hinfty : π OnePoint.infty ∉ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E H : Set Sphere) (hE : IsClosed E) (hH : IsClosed H)
    (hEU : E ⊆ d.quotientDomain) (hHU : H ⊆ d.quotientDomain)
    (k : ℕ) (C : ℕ → Set Sphere)
    (hC : ∀j ≤ k, IsCompact (C j)) (hCU : ∀j ≤ k, C j ⊆ d.quotientDomain)
    (hEC : ∀j ≤ k, Disjoint E (C j))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hgood : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ H →
      (∀j ≤ k, GateRule (C j) (Subtype.val '' (f ⁻¹' W₂)) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1)
    (hBU : Bᶜ ⊆ d.quotientDomain) (hm₂ : (∑' x, m x ^ 2) ≠ ∞) :
    ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞, ∃u : Sphere → ℝ,
      IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      (∀x, u x ∈ Icc 0 1) ∧ (∀x ∈ E, u x = 0) ∧ (∀x ∈ H, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g₁ m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  obtain ⟨O, g₁, hOo, hOU, hEO, hOW, hg₁, hgg₁, hoff, henergy, hlower⟩ :=
    exists_geometric_gate_penalty d hU π hπ he ν N E H hE k C hC hCU hEC
      f hf W₁ W₂ hW₁ hW₂ hW₁₂ g hg henergy m hgood
  let S := (E ∪ H)ᶜ
  have hSo : IsOpen S := (hE.union hH).isOpen_compl
  have hBS : B ⊆ S := by
    intro s hs hmem
    rcases hmem with hsE | hsH
    · exact Set.disjoint_left.mp hUB (hEU hsE) hs
    · exact Set.disjoint_left.mp hUB (hHU hsH) hs
  have hFE : frontier E ⊆ d.quotientDomain := by
    exact frontier_subset_closure.trans (by simpa only [hE.closure_eq] using hEU)
  have hFH : frontier H ⊆ d.quotientDomain := by
    exact frontier_subset_closure.trans (by simpa only [hH.closure_eq] using hHU)
  obtain ⟨u, hub, huE, huH, hupath, huband⟩ := exists_separating_chain_potential
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N E H hFE hFH g₁ hg₁ henergy m hm w hw (fun z hz => (hpos z hz).trans (hgg₁ z))
    hpoint hlower hBU S hSo hBS hm₂
  exact ⟨O, g₁, u, hOo, hOU, hEO, hOW, hg₁, hgg₁, hoff, henergy, hub,
    fun x hx => huE x ⟨hx, hEU hx⟩, fun x hx => huH x ⟨hx, hHU hx⟩, hupath, huband⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FirstEntryRange
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cut a path at its first arrival in a closed collar. The retained
prefix avoids the open collar and has no greater full cost. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_first_entry_prefix_with_range
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    {W : Set X} (hW : IsOpen W) (hstart : Γ.1.val ⊥ ∉ closure W)
    (hend : Γ.1.val ⊤ ∈ closure W)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ = Γ.1.val ⊥ ∧ ρ.1.val ⊤ ∈ frontier W ∧
      range ρ.1.val ⊆ Wᶜ ∧ range ρ.1.val ⊆ range Γ.1.val ∧
      physicalTollCost d g m ρ.1 ≤ physicalTollCost d g m Γ.1 := by
  let V := (closure W)ᶜ
  have hV : IsOpen V := isClosed_closure.isOpen_compl
  have hstop : Γ.1.val ⊤ ∉ V := fun h => h hend
  have hpos := firstExit_pos Γ.1.val hV hstart hstop
  let ρ := restrictTaggedPhysicalPath d hU Γ hpos
  have hlast : ρ.1.val ⊤ = Γ.1.val (firstExitTime Γ.1.val V) :=
    restrictTaggedPhysicalPath_one d hU Γ hpos
  refine ⟨ρ, restrictTaggedPhysicalPath_allowed d hU ν N Γ hΓ hpoint hpos,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact restrictTaggedPhysicalPath_zero d hU Γ hpos
  · rw [hlast]
    have h := firstExit_frontier Γ.1.val hV hstart hstop
    rw [frontier_compl] at h
    exact frontier_closure_subset h
  · rw [restrictTaggedPhysicalPath_range d hU Γ hpos]
    rintro x ⟨t, ht, rfl⟩
    apply closure_minimal (compl_subset_compl.mpr subset_closure) hW.isClosed_compl
    exact firstExit_initial_segment Γ.1.val hV hstart hstop ht.2
  · rw [restrictTaggedPhysicalPath_range d hU Γ hpos]
    exact image_subset_range _ _
  · exact physicalTollCost_affine_le d hU Γ.1 hpos g hg m

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ProjectedLevelTollZero
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short physical regular-level arcs descend through the actual domain
homeomorphism. Their cost is unchanged and their dust toll vanishes. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_23 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_small_projected_regular_level_arcs_of_level_toll_zero
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    {f : ℂ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {t : ℝ}
    (hreg : IsPlanarRegularValue f t)
    (hgood : ∀z, f z = t → (z : Sphere) ∈ d.physicalDomain)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻z in {z | f z = t}, g (z : Sphere) ∂(μH[1] : Measure ℂ)) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀z : ℂ, f z = t → m (π (z : Sphere)) = 0)
    {z : ℂ} (hz : f z = t) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Set Sphere, IsOpen W ∧ π (z : Sphere) ∈ W ∧
      ∀a ∈ W ∩ (π '' (((↑) : ℂ → Sphere) '' {z | f z = t})),
      ∀b ∈ W ∩ (π '' (((↑) : ℂ → Sphere) '' {z | f z = t})),
        ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧
          range ρ.1.val ⊆ π '' (((↑) : ℂ → Sphere) '' {z | f z = t}) ∧
          physicalTollCost d g m ρ.1 < ε := by
  obtain ⟨V, hV, hzV, hsmall⟩ := exists_small_sphere_regular_level_arcs
    hf hreg g hg hfinite hz hε
  let W : Set Sphere := Subtype.val '' (d.domainEquiv '' (Subtype.val ⁻¹' V))
  have hW : IsOpen W := hU.isOpenMap_subtype_val _
    (d.domainEquiv.isOpenMap _ (hV.preimage continuous_subtype_val))
  have hzW : π (z : Sphere) ∈ W := by
    refine ⟨d.domainEquiv ⟨(z : Sphere), hgood z hz⟩, ?_, he _⟩
    exact ⟨⟨(z : Sphere), hgood z hz⟩, hzV, rfl⟩
  refine ⟨W, hW, hzW, ?_⟩
  intro a ha b hb
  obtain ⟨_, ⟨za, hza, rfl⟩, rfl⟩ := ha.2
  obtain ⟨_, ⟨zb, hzb, rfl⟩, rfl⟩ := hb.2
  have hpre : ∀w : ℂ, f w = t → π (w : Sphere) ∈ W → (w : Sphere) ∈ V := by
    intro w hw hWw
    obtain ⟨u, ⟨v, hv, rfl⟩, hval⟩ := hWw
    have heq : d.domainEquiv v = d.domainEquiv ⟨(w : Sphere), hgood w hw⟩ :=
      Subtype.ext (hval.trans (he ⟨(w : Sphere), hgood w hw⟩).symm)
    have hvw := congrArg Subtype.val (d.domainEquiv.injective heq)
    change (v : Sphere) = (w : Sphere) at hvw
    change (w : Sphere) ∈ V
    rw [← hvw]
    exact hv
  obtain ⟨α, hα0, hα1, hαrange, hαcost⟩ := hsmall (za : Sphere)
    ⟨hpre za hza ha.1, ⟨za, hza, rfl⟩⟩ (zb : Sphere)
    ⟨hpre zb hzb hb.1, ⟨zb, hzb, rfl⟩⟩
  have hα : ∀s, α.val s ∈ d.physicalDomain := by
    intro s
    obtain ⟨w, hw, heq⟩ := hαrange (mem_range_self s)
    exact heq ▸ hgood w hw
  let ρ := finiteProjectedPhysicalPath d.domainEquiv d.basePoint α hα
  have hρval (s : PathTime) : ρ.val s = π (α.val s) := he ⟨α.val s, hα s⟩
  have hzero : boundaryToll ρ.val m = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro s
    rw [hρval]
    obtain ⟨w, hw, heq⟩ := hαrange (mem_range_self s)
    rw [← heq]
    exact hm w hw
  refine ⟨(ρ, fun _ => inactiveTag), projected_physical_path_allowed d hdisj ν N α hα,
    ?_, ?_, ?_, ?_⟩
  · exact (hρval ⊥).trans (congrArg π hα0)
  · exact (hρval ⊤).trans (congrArg π hα1)
  · rintro q ⟨s, rfl⟩
    exact ⟨α.val s, hαrange (mem_range_self s), (hρval s).symm⟩
  · change (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      boundaryToll ρ.val m < ε
    rw [hzero, add_zero]
    change (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint
      (finiteProjectedPhysicalPath d.domainEquiv d.basePoint α hα)) < ε
    rwa [dyadicPhysicalOccupation_project]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarLevelTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual weighted collars supply the local short joining arcs
required for splicing. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_24 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_small_weighted_collar_arcs_of_level_toll_zero
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞)
    {B : Set Sphere} {p : Sphere}
    (D : WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hm : ∀z : ℂ, D.function z = D.level → m (π (z : Sphere)) = 0)
    (hD : IsOpen D.region) {T : Set Sphere}
    (hlevel : {z | D.function z = D.level} ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' T)
    {x : Sphere} (hx : x ∈ frontier D.region) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Set Sphere, W ∈ 𝓝 x ∧
      ∀a ∈ W ∩ frontier D.region, ∀b ∈ W ∩ frontier D.region,
        ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
          ρ.1.val ⊥ = a ∧ ρ.1.val ⊤ = b ∧ range ρ.1.val ⊆ T ∧
          physicalTollCost d g m ρ.1 ≤ ε := by
  have hfront := D.frontier_region_subset hπ hD
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hfront hx
  obtain ⟨W, hW, hzW, hsmall⟩ := exists_small_projected_regular_level_arcs_of_level_toll_zero
    d hU hdisj π he ν N D.smooth D.regular
    (fun z hz => (D.level_good z hz).1) g hg D.cost_finite m hm hz hε
  refine ⟨W, hW.mem_nhds hzW, ?_⟩
  intro a ha b hb
  obtain ⟨ρ, hρ, hρ0, hρ1, hρrange, hρcost⟩ :=
    hsmall a ⟨ha.1, hfront ha.2⟩ b ⟨hb.1, hfront hb.2⟩
  refine ⟨ρ, hρ, hρ0, hρ1, hρrange.trans ?_, hρcost.le⟩
  rintro y ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact hlevel hw

namespace WeightedCollar

theorem frontier_toll_zero
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar d.physicalDomain π B p g) (hD : IsOpen D.region)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀z : ℂ, D.function z = D.level → m (π (z : Sphere)) = 0) :
    ∀x ∈ frontier D.region, m x = 0 := by
  intro x hx
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := D.frontier_region_subset hπ hD hx
  exact hm z hz

end WeightedCollar
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedOneEndedLevelTolls
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-ended splicing using actual weighted smooth collars, retaining
an original initial point in the prescribed set. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_25 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_weighted_oneEnded_splicing_of_level_toll_zero
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hzero : ∀n, m ((Γ n).1.val ⊥) = 0)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hm : ∀j z, (D j).function z = (D j).level → m (π (z : Sphere)) = 0)
    (hnest : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hlevel : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hDF : Disjoint F (closure (D 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η := by
  have hD (j : ℕ) : IsOpen (D j).region := (D j).isOpen_region hπ hclosed hsurj hr
  have hDn (j : ℕ) : (D j).region ∈ 𝓝 p :=
    (hD j).mem_nhds ((D j).point_mem_region hsurj hp)
  obtain ⟨s, hs, hsends⟩ := exists_subsequence_in_nested_endpoint_neighborhoods
    (fun n => (Γ n).1.val ⊤) (fun n => (Γ n).1.val ⊤) hend hend
    (fun j => (D j).region) (fun j => (D j).region) hDn hDn
  apply exists_actual_oneEnded_collar_splicing d hU hG ν N (fun n => Γ (s n))
    (fun n => hΓ (s n)) F (fun n => hstart (s n)) p (fun j => (D j).region)
    hD hnest hshrink
    (fun n hx => Set.disjoint_left.mp hDF (hstart (s n)) hx)
    (fun n => (hsends n).1) g hg m
    (fun j => (D j).frontier_toll_zero d π hπ (hD j) m (hm j))
    (fun n => hzero (s n)) A hA (hcost.comp hs.tendsto_atTop)
  · intro j z hz ε hε
    exact exists_small_weighted_collar_arcs_of_level_toll_zero d hU hdisj π hπ he ν N g hg m
      (D (j+1)) (hm (j+1)) (hD (j+1)) (T := closure (D j).region)
      (fun z hz => (show π (z : Sphere) ∈ closure (D j).region from subset_closure (hlevel j hz))) hz hε
  · intro z hz ε hε
    exact exists_small_weighted_collar_arcs_of_level_toll_zero d hU hdisj π hπ he ν N g hg m
      (D 0) (hm 0) (hD 0) (T := univ) (fun _ _ => mem_univ _) hz hε
  · exact hw
  · exact hpos
  · exact hpoint
  · exact hη

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarAvoidance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collar splicing preserves avoidance of any set missed by both the
original paths and the chosen collar levels, including forbidden gate hits. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

private theorem collar_level_exclusion_zero
    (d : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) {B : Set Sphere} {p : Sphere} {g : ℂ → ℝ≥0∞}
    (D : WeightedCollar d.physicalDomain π B p g)
    (havoid : ∀z, D.function z = D.level → π (z : Sphere) ∉ S) :
    ∀z, D.function z = D.level → exclusionToll S m (π (z : Sphere)) = 0 := by
  intro z hz
  rw [exclusionToll_eq S m (havoid z hz)]
  apply hm
  rw [← he ⟨(z : Sphere), (D.level_good z hz).1⟩]
  exact (d.domainEquiv _).property

local instance localInst_rbc6963_26 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_weighted_oneEnded_splicing_avoiding_set
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (havoid : ∀n t, (Γ n).1.val t ∉ S)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hlevelAvoid : ∀j z, (D j).function z = (D j).level → π (z : Sphere) ∉ S)
    (hnest : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hlevel : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hDF : Disjoint F (closure (D 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η ∧
      ∀t < (⊤ : PathTime), ρ.val t ∉ S := by
  have hcostS : Tendsto (fun n => physicalTollCost d g (exclusionToll S m) (Γ n).1)
      atTop (𝓝 A) := by
    convert hcost using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact physicalTollCost_exclusion d g m S (Γ n).1 (havoid n)
  have hzeroS (n : ℕ) : exclusionToll S m ((Γ n).1.val ⊥) = 0 := by
    rw [exclusionToll_eq S m (havoid n ⊥)]
    exact hm _ (hF (hstart n))
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC⟩ := exists_weighted_oneEnded_splicing_of_level_toll_zero
    d hU hG hdisj π hπ hclosed hsurj hr he ν N Γ hΓ F hstart p hp hend
    g hg (exclusionToll S m) hzeroS D
    (fun j => collar_level_exclusion_zero d π he m hm S (D j) (hlevelAvoid j))
    hnest hshrink hlevel hDF A hA hcostS w hw hpos hpoint hη
  have hfinite : preterminalToll ρ.val (exclusionToll S m) < ∞ :=
    (show preterminalToll ρ.val (exclusionToll S m) ≤
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
      preterminalToll ρ.val (exclusionToll S m) from le_add_self).trans_lt
      (hC.trans_lt (ENNReal.add_lt_top.mpr ⟨hA, ENNReal.ofReal_lt_top⟩))
  refine ⟨ρ, θ, hρ, hρ0, hρ1,
    (add_le_add le_rfl (preterminalToll_mono ρ.val (le_exclusionToll S m))).trans hC, ?_⟩
  rw [preterminalToll_eq_timeToll] at hfinite
  exact avoids_of_finite_exclusionToll ρ.val _ S m hfinite

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_GatedCollarSplicing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One-ended collar splicing preserves all prescribed hit locations when
the joining levels miss the hit contours. Dust avoidance is retained at
all nonterminal times in the very same constructed path. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_27 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_weighted_oneEnded_splicing_preserving_gates
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ : ℕ → TaggedPhysicalPath d) (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain) (hstart : ∀n, (Γ n).1.val ⊥ ∈ F)
    (p : Sphere) (hp : p ≠ π OnePoint.infty)
    (hend : Tendsto (fun n => (Γ n).1.val ⊤) atTop (𝓝 p))
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (S : Set Sphere) (havoid : ∀n t, (Γ n).1.val t ∉ S)
    (C K : ℕ → Set Sphere) (hgate : ∀n, GateRules C K (Γ n).1.val)
    (hpgate : ∀i, p ∉ C i)
    {B : Set Sphere}
    (D : ℕ → WeightedCollar d.physicalDomain π B p (fun z => g (z : Sphere)))
    (hlevelAvoid : ∀j z, (D j).function z = (D j).level → π (z : Sphere) ∉ S)
    (hlevelGate : ∀j z, (D j).function z = (D j).level → ∀i, π (z : Sphere) ∉ C i)
    (hnest : ∀j, closure (D (j+1)).region ⊆ (D j).region)
    (hshrink : ∀O ∈ 𝓝 p, ∃k : ℕ, ∀j ≥ k, closure (D j).region ⊆ O)
    (hlevel : ∀j, {z | (D (j+1)).function z = (D (j+1)).level} ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D j).region)
    (hDF : Disjoint F (closure (D 0).region))
    (A : ℝ≥0∞) (hA : A < ∞)
    (hcost : Tendsto (fun n => physicalTollCost d g m (Γ n).1) atTop (𝓝 A))
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ ∈ F ∧ ρ.val ⊤ = p ∧
      (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m ≤ A + ENNReal.ofReal η ∧
      GateRules C K ρ.val ∧ ∀t < (⊤ : PathTime), ρ.val t ∉ S := by
  let T := S ∪ gateForbiddenSet C K
  have hΓT (n : ℕ) (t : PathTime) : (Γ n).1.val t ∉ T := by
    rintro (hs | hg)
    · exact havoid n t hs
    · exact (gateRules_iff_avoids C K (Γ n).1.val).mp (hgate n) t hg
  have hlevelT (j : ℕ) (z : ℂ) (hz : (D j).function z = (D j).level) :
      π (z : Sphere) ∉ T := by
    rintro (hs | hg)
    · exact hlevelAvoid j z hz hs
    · exact avoids_gateForbiddenSet_of_avoids_contours C K (hlevelGate j z hz) hg
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, hρT⟩ := exists_weighted_oneEnded_splicing_avoiding_set
    d hU hG hdisj π hπ hclosed hsurj hr he ν N Γ hΓ F hF hstart p hp hend
    g hg m hm T hΓT D hlevelT hnest hshrink hlevel hDF A hA hcost w hw hpos hpoint hη
  refine ⟨ρ, θ, hρ, hρ0, hρ1, hC, ?_, ?_⟩
  · apply (gateRules_iff_avoids C K ρ.val).mpr
    intro t ht
    by_cases htop : t = ⊤
    · rw [htop, hρ1] at ht
      exact avoids_gateForbiddenSet_of_avoids_contours C K hpgate ht
    · exact hρT t (lt_top_iff_ne_top.mpr htop) (Or.inr ht)
  · intro t ht hs
    exact hρT t ht (Or.inl hs)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCollarTopology
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual projected Jordan collars have connected complements and
their closed regions miss the image of physical infinity. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem isConnected_sphere_jordan_exterior (H : ℂ ≃ₜ ℂ) :
    IsConnected ((((↑) : ℂ → Sphere) '' jordanInterior H)ᶜ) := by
  have hi : (H.onePointCongr : Sphere → Sphere) ''
      (((↑) : ℂ → Sphere) '' Metric.ball (0 : ℂ) 1) =
      ((↑) : ℂ → Sphere) '' jordanInterior H := by
    rw [image_image, jordanInterior, image_image]
    rfl
  rw [← hi, ← H.onePointCongr.image_compl]
  exact (isConnected_sphere_exterior_ball 0 zero_lt_one).image _ H.onePointCongr.continuous.continuousOn

namespace WeightedCollar

variable {G : Set Sphere} {π : Sphere → Sphere} {B : Set Sphere}
  {p : Sphere} {g : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g)

theorem isConnected_compl_region (hπ : Continuous π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsConnected D.regionᶜ := by
  let S : Set Sphere := ((↑) : ℂ → Sphere) '' jordanInterior D.disk
  have hsat : π ⁻¹' (π '' S) = S := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr D.disk (fun z hz => (D.level_good z (D.frontier_level hz)).1)
  have heq : π '' Sᶜ = D.regionᶜ := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩ hx
      exact hz (hsat ▸ hx)
    · intro hx
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, fun hz => hx ⟨z, hz, rfl⟩, rfl⟩
  rw [← heq]
  exact (isConnected_sphere_jordan_exterior D.disk).image π hπ.continuousOn

theorem infty_notMem_closure_region (hπ : Continuous π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    π OnePoint.infty ∉ closure D.region := by
  intro hinfty
  obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := D.closure_region_subset_image hπ hinfty
  have hsat := preimage_image_jordanInterior_of_component_collapse
    G π hsurj hr D.disk (fun z hz => (D.level_good z (D.frontier_level hz)).1)
  have hznot : z ∉ jordanInterior D.disk := by
    intro hzin
    have hi : π OnePoint.infty ∈ D.region := heq ▸ ⟨(z : Sphere), ⟨z, hzin, rfl⟩, rfl⟩
    have hi' : OnePoint.infty ∈ π ⁻¹' (π '' (((↑) : ℂ → Sphere) '' jordanInterior D.disk)) := hi
    rw [hsat] at hi'
    exact OnePoint.infty_notMem_image_coe hi'
  have hzfront : z ∈ frontier (jordanInterior D.disk) := by
    rw [(jordanInterior_isOpen D.disk).frontier_eq]
    exact ⟨hz, hznot⟩
  rcases (hr (z : Sphere) OnePoint.infty).mp heq with h | ⟨h, _⟩
  · exact OnePoint.coe_ne_infty z h
  · exact h (D.level_good z (D.frontier_level hzfront)).1

end WeightedCollar
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedAnnularCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-cost smooth collar around a connected compact set, avoiding
an outer closed obstacle. Used to place joining levels between fixed gates. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

private theorem isClosed_diff_of_frontier_disjoint {X : Type*} [TopologicalSpace X]
    {A F : Set X} (hA : IsClosed A) (hF : IsClosed F) (hFA : Disjoint F (frontier A)) :
    IsClosed (F \ A) := by
  have heq : F \ A = F \ interior A := by
    ext x
    constructor
    · intro h
      exact ⟨h.1, fun hx => h.2 (interior_subset hx)⟩
    · rintro ⟨hxF, hxI⟩
      refine ⟨hxF, ?_⟩
      intro hxA
      exact Set.disjoint_left.mp hFA hxF ⟨hA.closure_eq.symm ▸ hxA, hxI⟩
  rw [heq]
  exact hF.inter isOpen_interior.isClosed_compl

theorem exists_weighted_collar_around_compact
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    {A F V : Set ℂ} (hA : IsCompact A) (hconn : IsConnected A)
    (hF : IsClosed F) (hFA : Disjoint F (frontier A))
    (hV : IsOpen V) (hAV : A ⊆ V)
    (hVc : IsPreconnected Vᶜ) (hVun : ¬ Bornology.IsBounded Vᶜ)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (f : ℂ → ℝ) (t : ℝ),
      A ⊆ jordanInterior H ∧ closure (jordanInterior H) ⊆ V ∧
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) (↑(⊤ : ℕ∞)) γ ∧ Topology.IsEmbedding γ ∧
      frontier (jordanInterior H) = range γ ∧
      frontier (jordanInterior H) ⊆ {z | f z = t} ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ IsPlanarRegularValue f t ∧
      {z | f z = t} ⊆ V \ (A ∪ F) ∧
      (∫⁻z in {z | f z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
  have hdiff : IsClosed ((A ∪ F) \ A) := by
    simpa only [union_sdiff_distrib, sdiff_self, empty_union] using
      isClosed_diff_of_frontier_disjoint hA.isClosed hF hFA
  obtain ⟨f, t, γ, H, s, hf, hreg, hlevel, havoid, hcost, _, hcover, hpair,
    hinside, hcurves⟩ := exists_finite_weighted_jordan_cover hcoarea hsard hsch
      hA subset_union_left hdiff hV hAV hVc hVun g hg hg2
  have hpair' : Pairwise (Disjoint on fun i : s => jordanInterior (H i)) := by
    intro i j hij
    exact (hpair i.property j.property (fun h => hij (Subtype.ext h))).mono
      subset_closure subset_closure
  have hcover' : A ⊆ ⋃i : s, jordanInterior (H i) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨i, hi⟩ := exists_member_containing_connected_set hconn
    (fun i : s => jordanInterior (H i)) (fun i => jordanInterior_isOpen (H i)) hpair' hcover'
  obtain ⟨hγ, hemb, hfront, _, hfrontlevel⟩ := hcurves i i.property
  refine ⟨H i, γ i, f, t, hi, hinside i i.property, hγ, hemb, hfront,
    hfrontlevel, hf, hreg, ?_, hcost⟩
  intro z hz
  exact ⟨hlevel hz, fun h => Set.disjoint_left.mp havoid hz h⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedIntermediateCollar
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual weighted collar between an inner physical Jordan disk and
an outer quotient disk. Its entire joining level stays in the intervening annulus. -/

open Set Function MeasureTheory
open scoped Topology Manifold ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_weighted_intermediate_collar
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hbad : ∀x ∈ Gᶜ, π x ∈ B)
    {p : Sphere} {g₀ : ℂ → ℝ≥0∞} (D : WeightedCollar G π B p g₀)
    {V : Set Sphere} (hV : IsOpen V) (hVc : IsConnected Vᶜ)
    (hinfty : π OnePoint.infty ∉ closure V)
    (hinside : closure (jordanInterior D.disk) ⊆ (fun z : ℂ => π (z : Sphere)) ⁻¹' V)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ E : WeightedCollar G π B p g,
      closure D.region ⊆ E.region ∧ closure E.region ⊆ V ∧
      {z | E.function z = E.level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (V \ closure D.region) := by
  let A := closure (jordanInterior D.disk)
  let F := (fun z : ℂ => π (z : Sphere)) ⁻¹' B
  let U := (fun z : ℂ => π (z : Sphere)) ⁻¹' V
  have hq : Continuous (fun z : ℂ => π (z : Sphere)) := hπ.comp OnePoint.continuous_coe
  have hA : IsCompact A := isCompact_closure_jordanInterior D.disk
  have hFA : Disjoint F (frontier A) := by
    apply Set.disjoint_left.mpr
    intro z hzF hzA
    exact (D.level_good z (D.frontier_level (frontier_closure_subset hzA))).2 hzF
  obtain ⟨hUconn, hUun⟩ := physical_exterior_connected_unbounded_of_component_collapse
    G π hπ hclosed hsurj hr hV hVc hinfty
  obtain ⟨H, γ, f, t, hAH, hHV, hγ, hemb, hfront, hfrontlevel,
    hf, hreg, hlevel, hcost⟩ := exists_weighted_collar_around_compact
      hcoarea hsard hsch hA (isConnected_jordanInterior D.disk).closure
      (hB.preimage hq) hFA (hV.preimage hq) hinside hUconn hUun g hg hg2
  have hgood (z : ℂ) (hz : f z = t) : (z : Sphere) ∈ G ∧ π (z : Sphere) ∉ B := by
    have hnot : π (z : Sphere) ∉ B := fun h => (hlevel hz).2 (Or.inr h)
    refine ⟨?_, hnot⟩
    by_contra h
    exact hnot (hbad _ h)
  let E : WeightedCollar G π B p g :=
    ⟨H, γ, f, t, D.fiber_inside.trans (subset_closure.trans hAH),
      hγ, hemb, hfront, hfrontlevel, hf, hreg, hgood, hcost⟩
  refine ⟨E, ?_, E.closure_region_subset hπ hHV, ?_⟩
  · intro x hx
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := D.closure_region_subset_image hπ hx
    exact ⟨(z : Sphere), ⟨z, hAH hz, rfl⟩, rfl⟩
  · intro z hz
    refine ⟨(hlevel hz).1, ?_⟩
    intro hx
    obtain ⟨_, ⟨u, hu, rfl⟩, heq⟩ := D.closure_region_subset_image hπ hx
    have hzu : (z : Sphere) = (u : Sphere) := by
      rcases (hr (z : Sphere) (u : Sphere)).mp heq.symm with h | ⟨h, _⟩
      · exact h
      · exact (h ((hgood z hz).1)).elim
    have hzu' : z = u := OnePoint.coe_injective hzu
    exact (hlevel hz).2 (Or.inl (hzu'.symm ▸ hu))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_InterposedWeightedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interpose weighted collars between successive pairs of prescribed
collars. All joining levels miss every prescribed boundary. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_interposed_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hbad : ∀x ∈ Gᶜ, π x ∈ B)
    {p : Sphere} {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar G π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ E : ℕ → WeightedCollar G π B p g,
      closure (E 0).region ⊆ (D 0).region ∧
      (∀n, closure (E (n+1)).region ⊆ (E n).region) ∧
      (∀n, {z | (E (n+1)).function z = (E (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (E n).region) ∧
      (∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (E n).region ⊆ V) ∧
      (∀n z, (E n).function z = (E n).level → ∀j, π (z : Sphere) ∉ frontier (D j).region) ∧
      (∀n, {z | (E n).function z = (E n).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D 0).region) := by
  have ha : Antitone (fun n => (D n).region) :=
    antitone_nat_of_succ_le (fun n => subset_closure.trans (hnest n))
  have hq : Continuous (fun z : ℂ => π (z : Sphere)) := hπ.comp OnePoint.continuous_coe
  have hphysical (n : ℕ) : closure (jordanInterior (D (2*n+1)).disk) ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D (2*n)).region := by
    intro z hz
    have hm := (image_closure_subset_closure_image hq) ⟨z, hz, rfl⟩
    have heq : (fun z : ℂ => π (z : Sphere)) '' jordanInterior (D (2*n+1)).disk =
        (D (2*n+1)).region := by
      simp only [WeightedCollar.region, image_image]
    rw [heq] at hm
    exact hnest (2*n) hm
  have hex (n : ℕ) := exists_weighted_intermediate_collar hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hbad (D (2*n+1))
    ((D (2*n)).isOpen_region hπ hclosed hsurj hr) ((D (2*n)).isConnected_compl_region hπ hsurj hr)
    ((D (2*n)).infty_notMem_closure_region hπ hsurj hr)
    (hphysical n) g hg hg2
  choose E hEin hEout hElev using hex
  have hstep (n : ℕ) : (D (2*(n+1))).region ⊆ (E n).region :=
    (ha (by omega : 2*n+1 ≤ 2*(n+1))).trans (subset_closure.trans (hEin n))
  refine ⟨E, hEout 0, fun n => (hEout (n+1)).trans (hstep n), ?_, ?_, ?_, ?_⟩
  · intro n z hz
    exact hstep n (hElev (n+1) hz).1
  · intro V hV
    obtain ⟨k, hk⟩ := hshrink V hV
    refine ⟨k, fun n hn => (hEout n).trans ?_⟩
    exact (subset_closure.trans (hk (2*n) (by omega)))
  · intro n z hz j hj
    have hloc := hElev n hz
    by_cases hle : j ≤ 2*n
    · have hm := ha hle hloc.1
      have ho := (D j).isOpen_region hπ hclosed hsurj hr
      exact (ho.frontier_eq ▸ hj).2 hm
    · have hle' : 2*n+1 ≤ j := by omega
      exact hloc.2 (closure_mono (ha hle') (frontier_subset_closure hj))

  · intro n z hz
    exact ha (Nat.zero_le _) (hElev n hz).1

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LocalInterposedCollars
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interpose weighted collars between successive pairs of prescribed
collars. All joining levels miss every prescribed boundary. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_interposed_weighted_collars_of_local_energy
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hbad : ∀x ∈ Gᶜ, π x ∈ B)
    {p : Sphere} {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar G π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z in (fun z : ℂ => π (z : Sphere)) ⁻¹' (D 0).region, g z ^ 2) < ∞) :
    ∃ E : ℕ → WeightedCollar G π B p g,
      closure (E 0).region ⊆ (D 0).region ∧
      (∀n, closure (E (n+1)).region ⊆ (E n).region) ∧
      (∀n, {z | (E (n+1)).function z = (E (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (E n).region) ∧
      (∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (E n).region ⊆ V) ∧
      (∀n z, (E n).function z = (E n).level → ∀j, π (z : Sphere) ∉ frontier (D j).region) ∧
      (∀n, {z | (E n).function z = (E n).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D 0).region) := by
  let P := (fun z : ℂ => π (z : Sphere)) ⁻¹' (D 0).region
  have hP : MeasurableSet P :=
    (((D 0).isOpen_region hπ hclosed hsurj hr).preimage
      (hπ.comp OnePoint.continuous_coe)).measurableSet
  let q := P.indicator g
  have hq : Measurable q := hg.indicator hP
  have hq2 : (∫⁻z, q z ^ 2) < ∞ := by
    have heq : (fun z => q z ^ 2) = P.indicator (fun z => g z ^ 2) := by
      funext z
      by_cases hz : z ∈ P <;> simp [q, hz]
    rw [heq, lintegral_indicator hP]
    exact hg2
  obtain ⟨E, hE0, hEn, hEl, hEs, hEa, hEp⟩ := exists_interposed_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hbad D hnest hshrink q hq hq2
  have hcost (n : ℕ) : (∫⁻z in {z | (E n).function z = (E n).level}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
    have hm : MeasurableSet {z | (E n).function z = (E n).level} :=
      (isClosed_eq (E n).smooth.continuous continuous_const).measurableSet
    have heq : (∫⁻z in {z | (E n).function z = (E n).level}, g z ∂(μH[1] : Measure ℂ)) =
        ∫⁻z in {z | (E n).function z = (E n).level}, q z ∂(μH[1] : Measure ℂ) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hm] with z hz
      exact (indicator_of_mem (hEp n hz) g).symm
    rw [heq]
    exact (E n).cost_finite
  let H : ℕ → WeightedCollar G π B p g := fun n =>
    ⟨(E n).disk, (E n).curve, (E n).function, (E n).level, (E n).fiber_inside,
      (E n).curve_smooth, (E n).curve_embedding, (E n).frontier_eq, (E n).frontier_level,
      (E n).smooth, (E n).regular, (E n).level_good, hcost n⟩
  exact ⟨H, hE0, hEn, hEl, hEs, hEa, hEp⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteGatedCollarSeparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_cutoffCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_mem_sphericalCore _root_.OAI.CircleDomainRigidity.FiniteTransfer.infty_not_mem_sphericalDiskUnion _root_.OAI.CircleDomainRigidity.FiniteTransfer.realChartDomain_union _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.affineSphere_coe _root_.OAI.CircleDomainRigidity.affineSphere_infty _root_.OAI.CircleDomainRigidity.centeredJordanCoordinate_self _root_.OAI.CircleDomainRigidity.chartSymm_coe_apply _root_.OAI.CircleDomainRigidity.chart_coe_apply _root_.OAI.CircleDomainRigidity.chart_infty_apply _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.extendAtInfinity_coe _root_.OAI.CircleDomainRigidity.extendAtInfinity_infty _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.sphereInv_infty _root_.OAI.CircleDomainRigidity.sphereInv_sphereInv _root_.OAI.CircleDomainRigidity.sphereInv_zero _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Step 1 of the gated compatible-barrier argument: first-arrival
separation at the dust point implies separation at a finite collar. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_28 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_finite_gated_collar_cost_lower_bound
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (F : Set Sphere) (hF : F ⊆ d.quotientDomain)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hFD : Disjoint F (closure (D 0).region)) (K : ℕ → Set Sphere)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ F → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region) K ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m) :
    ∃k : ℕ, ∀Γ : TaggedPhysicalPath d,
      AllowedTaggedPath d ν N (Γ.1.val, Γ.2) → Γ.1.val ⊥ ∈ F →
      Γ.1.val ⊤ ∈ frontier (D k).region →
      (∀j ≤ k, GateRule (frontier (D j).region) (K j) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1 := by
  classical
  by_contra hn
  push Not at hn
  choose Γ hΓ hΓF hΓend hΓgate hΓcost using hn
  have hD (n : ℕ) := (D n).isOpen_region hπ hclosed hsurj hr
  have hpD (n : ℕ) := (D n).point_mem_region hsurj hp
  have ha : Antitone (fun n => (D n).region) :=
    antitone_nat_of_succ_le (fun n => subset_closure.trans (hnest n))
  have hFDn (n : ℕ) : Disjoint F (closure (D n).region) :=
    hFD.mono_right (closure_mono (ha (Nat.zero_le n)))
  have hprefix (n : ℕ) := exists_allowed_first_entry_prefix_with_range d hU ν N (Γ n) (hΓ n)
    (hD n) (fun h => Set.disjoint_left.mp (hFDn n) (hΓF n) h)
    (frontier_subset_closure (hΓend n)) g hg m hpoint
  choose Δ hΔ hΔstart hΔend hΔrange hΔsub hΔcost using hprefix
  have hΔgate (n : ℕ) : GateRules (fun j => frontier (D j).region) K (Δ n).1.val := by
    intro j t ht
    by_cases hj : j ≤ n
    · obtain ⟨s, hs⟩ := hΔsub n (mem_range_self t)
      exact hs ▸ hΓgate n j hj s (hs.symm ▸ ht)
    · have hm := hnest n (closure_mono (ha (by omega : n+1 ≤ j)) (frontier_subset_closure ht))
      exact ((hΔrange n (mem_range_self t)) hm).elim
  have hcost (n : ℕ) : physicalTollCost d g m (Δ n).1 < ENNReal.ofReal ((1 : ℝ)/2) :=
    (hΔcost n).trans_lt (hΓcost n)
  obtain ⟨A, hA, s, hs, hlim⟩ := isCompact_Icc.tendsto_subseq
    (fun n => (show physicalTollCost d g m (Δ n).1 ∈ Icc 0 (ENNReal.ofReal ((1 : ℝ)/2)) from
      ⟨bot_le, (hcost n).le⟩))
  have hend : Tendsto (fun n => (Δ n).1.val ⊤) atTop (𝓝 p) := by
    apply tendsto_def.mpr
    intro V hV
    obtain ⟨k, hk⟩ := hshrink V hV
    filter_upwards [eventually_ge_atTop k] with n hn
    exact hk n hn (frontier_subset_closure (hΔend n))
  have havoid (n : ℕ) (t : PathTime) : (Δ n).1.val t ≠ p := by
    intro ht
    exact (hΔrange n (mem_range_self t)) (ht ▸ hpD n)
  have hgD := planar_energy_quotient_neighborhood_finite π hπ
    ((D 0).infty_notMem_closure_region hπ hsurj hr) g hg henergy
  obtain ⟨E, hE0, hEn, hEl, hEs, hEa, _⟩ := exists_interposed_weighted_collars_of_local_energy
    hcoarea hsard hsch d.physicalDomain π hπ hclosed hsurj hr hB hbad D
    hnest hshrink (fun z : ℂ => g (z : Sphere))
    (hg.comp OnePoint.continuous_coe.measurable) hgD
  have hlevelAvoid (j : ℕ) (z : ℂ) (hz : (E j).function z = (E j).level) :
      π (z : Sphere) ∉ ({p} : Set Sphere) := by
    intro heq
    have hx : π (z : Sphere) ∈ d.quotientDomain := by
      rw [← he ⟨(z : Sphere), ((E j).level_good z hz).1⟩]
      exact (d.domainEquiv _).property
    exact Set.disjoint_left.mp hdisj ((mem_singleton_iff.mp heq) ▸ hx) hpDust
  have hpgate (j : ℕ) : p ∉ frontier (D j).region := by
    rw [(hD j).frontier_eq]
    exact fun h => h.2 (hpD j)
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hC, hgate, hfirst'⟩ :=
    exists_weighted_oneEnded_splicing_preserving_gates d hU hG hdisj π hπ hclosed hsurj hr he
      ν N (fun n => Δ (s n)) (fun n => hΔ (s n)) F hF
      (fun n => (hΔstart (s n)) ▸ hΓF (s n)) p hp (hend.comp hs.tendsto_atTop)
      g hg m hm {p} (fun n t => havoid (s n) t)
      (fun j => frontier (D j).region) K (fun n => hΔgate (s n)) hpgate
      E hlevelAvoid hEa hEn hEs hEl
      (hFD.mono_right (hE0.trans subset_closure))
      A (hA.2.trans_lt ENNReal.ofReal_lt_top) hlim w hw hpos hpoint
      (η := (1 : ℝ)/4) (by norm_num)
  have hfirst (t : PathTime) (ht : t < ⊤) : ρ.val t ≠ p := hfirst' t ht
  have hcontr : (1 : ℝ≥0∞) < 1 := calc
    1 ≤ _ := hunit ρ θ hρ hρ0 hρ1 hfirst hgate
    _ ≤ A + ENNReal.ofReal ((1 : ℝ)/4) := hC
    _ ≤ ENNReal.ofReal ((1 : ℝ)/2) + ENNReal.ofReal ((1 : ℝ)/4) :=
      add_le_add hA.2 le_rfl
    _ < 1 := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (0 : ℝ) ≤ 1/4), ← ENNReal.ofReal_one,
        ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
      norm_num
  exact (lt_irrefl _) hcontr

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FirstArrivalBarrierPotential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-arrival hypothesis gives a bounded separating
potential with controlled dust bands. Finite collar separation, the geometric
gate penalty and all progressively shrinking jumps are constructed here. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_29 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_first_arrival_barrier_potential
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hUB : Disjoint d.quotientDomain B) (hBU : Bᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E : Set Sphere) (hE : IsClosed E) (hEU : E ⊆ d.quotientDomain)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint E (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ E → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m) :
    ∃k : ℕ, ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞, ∃u : Sphere → ℝ,
      IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      (∀x, u x ∈ Icc 0 1) ∧ (∀x ∈ E, u x = 0) ∧
      (∀x ∈ frontier (D k).region, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g₁ m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  let K : ℕ → Set Sphere := fun _ => Subtype.val '' (f ⁻¹' closure W₂)
  obtain ⟨k, hk⟩ := exists_finite_gated_collar_cost_lower_bound
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hbad ν N
    E hEU p hpDust hp D hnest hshrink hED K g hg henergy m hm w hw hpos hpoint hunit
  have hDo (j : ℕ) : IsOpen (D j).region := (D j).isOpen_region hπ hclosed hsurj hr
  have hDsub (j : ℕ) : frontier (D j).region ⊆ d.quotientDomain :=
    (D j).frontier_region_subset_quotient d π hπ he (hDo j)
  have ha : Antitone (fun j => (D j).region) :=
    antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hEDj (j : ℕ) : Disjoint E (frontier (D j).region) :=
    hED.mono_right (frontier_subset_closure.trans (closure_mono (ha (Nat.zero_le j))))
  have hgood : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ E → Γ.1.val ⊤ ∈ frontier (D k).region →
      (∀j ≤ k, GateRule (frontier (D j).region) (Subtype.val '' (f ⁻¹' W₂)) Γ.1.val) →
      ENNReal.ofReal ((1 : ℝ)/2) ≤ physicalTollCost d g m Γ.1 := by
    intro Γ hΓ hΓ0 hΓ1 hgates
    apply hk Γ hΓ hΓ0 hΓ1
    intro j hj t ht
    exact image_mono (preimage_mono subset_closure) (hgates j hj t ht)
  obtain ⟨O, g₁, u, h⟩ := exists_raw_gated_barrier
    hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hbad hUB hdense hinfty
    ν N E (frontier (D k).region) hE isClosed_frontier hEU (hDsub k)
    k (fun j => frontier (D j).region) (fun _ _ => isClosed_frontier.isCompact)
    (fun j _ => hDsub j) (fun j _ => hEDj j) f hf W₁ W₂ hW₁ hW₂ hW₁₂
    g hg henergy m hm w hw hpos hpoint hgood hBU hm₂
  exact ⟨k, O, g₁, u, h⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FillRegionPotential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filling the terminal collar with the constant value one preserves the
true-path cost inequality. At dust points away from its boundary, the band
is either unchanged or collapses to the constant value. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

theorem fillRegionOne_mem_Icc (V : Set X) (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1) (x : X) :
    fillRegionOne V u x ∈ Icc 0 1 := by
  by_cases hx : x ∈ V
  · simp [fillRegionOne, hx]
  · simpa only [fillRegionOne, ite_eq_right hx] using hu x

variable {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem one_sided_cost_to_constant_frontier
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (V : Set X) (hV : IsOpen V) (hfront : frontier V ⊆ d.quotientDomain)
    (u : X → ℝ) (hone : ∀x ∈ frontier V, u x = 1)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (hineq : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hx : Γ.1.val ⊥ ∈ d.quotientDomain)
    (hstart : Γ.1.val ⊥ ∉ V) (hend : Γ.1.val ⊤ ∈ V) :
    ENNReal.ofReal |1 - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1 := by
  by_cases hcl : Γ.1.val ⊥ ∈ closure V
  · have hf : Γ.1.val ⊥ ∈ frontier V := by
      rw [hV.frontier_eq]
      exact ⟨hcl, hstart⟩
    rw [hone _ hf, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  · obtain ⟨ρ, hρ, hρ0, hρ1, _, _, hcost⟩ := exists_allowed_first_entry_prefix_with_range
      d hU ν N Γ hΓ hV hcl (subset_closure hend) g hg m hpoint
    have hi := hineq ρ hρ (hρ0.symm ▸ hx) (hfront hρ1)
    rw [hone _ hρ1, hρ0] at hi
    exact hi.trans (mul_le_mul' le_rfl hcost)

theorem fillRegionOne_path_inequality
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (V : Set X) (hV : IsOpen V) (hfront : frontier V ⊆ d.quotientDomain)
    (u : X → ℝ) (hone : ∀x ∈ frontier V, u x = 1)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    (hineq : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hx : Γ.1.val ⊥ ∈ d.quotientDomain) (hy : Γ.1.val ⊤ ∈ d.quotientDomain) :
    ENNReal.ofReal |fillRegionOne V u (Γ.1.val ⊤) - fillRegionOne V u (Γ.1.val ⊥)| ≤
      4 * physicalTollCost d g m Γ.1 := by
  by_cases h0 : Γ.1.val ⊥ ∈ V
  · by_cases h1 : Γ.1.val ⊤ ∈ V
    · simp [fillRegionOne, h0, h1]
    · let Δ := reversedTaggedPhysicalPath d Γ
      have hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2) :=
        allowedTaggedPath_reversed d ν N (Γ.1.val, Γ.2) hΓ hpoint
      have hΔ0 : Δ.1.val ⊥ = Γ.1.val ⊤ := reversedPath_zero Γ.1.val
      have hΔ1 : Δ.1.val ⊤ = Γ.1.val ⊥ := reversedPath_one Γ.1.val
      have hi := one_sided_cost_to_constant_frontier d hU ν N V hV hfront u hone g hg m hpoint hineq
        Δ hΔ (hΔ0.symm ▸ hy) (hΔ0.symm ▸ h1) (hΔ1.symm ▸ h0)
      have he : physicalTollCost d g m Δ.1 = physicalTollCost d g m Γ.1 :=
        physicalTollCost_reversed d g m Γ.1
      rw [hΔ0, he] at hi
      simpa only [fillRegionOne, ite_eq_left h0, ite_eq_right h1, abs_sub_comm] using hi
  · by_cases h1 : Γ.1.val ⊤ ∈ V
    · simpa only [fillRegionOne, ite_eq_right h0, ite_eq_left h1] using
        one_sided_cost_to_constant_frontier d hU ν N V hV hfront u hone g hg m hpoint hineq Γ hΓ hx h0 h1
    · simpa only [fillRegionOne, ite_eq_right h0, ite_eq_right h1] using hineq Γ hΓ hx hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_FillRegionBands
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filling an open region by one cannot enlarge a boundary band at any
point away from the region's frontier. This assertion is pointwise. -/

open Set Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem fillRegionOne_band
    (G V : Set X) (hV : IsOpen V) (u : X → ℝ) {s : X}
    (hs : s ∈ closure G) (hsfront : s ∉ frontier V) (a : ℝ≥0∞)
    (hband : ENNReal.ofReal (limsup u (𝓝[G] s) - liminf u (𝓝[G] s)) ≤ a) :
    ENNReal.ofReal (limsup (fillRegionOne V u) (𝓝[G] s) -
      liminf (fillRegionOne V u) (𝓝[G] s)) ≤ a := by
  let : NeBot (𝓝[G] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  by_cases hsV : s ∈ V
  · have hev : ∀ᶠx in 𝓝[G] s, x ∈ V := nhdsWithin_le_nhds (hV.mem_nhds hsV)
    have heq : fillRegionOne V u =ᶠ[𝓝[G] s] fun _ => (1 : ℝ) := by
      filter_upwards [hev] with x hx
      exact ite_eq_left hx
    rw [limsup_congr heq, liminf_congr heq, limsup_const, liminf_const,
      sub_self, ENNReal.ofReal_zero]
    exact bot_le
  · have hscl : s ∉ closure V := by
      intro h
      apply hsfront
      rw [hV.frontier_eq]
      exact ⟨h, hsV⟩
    have hev : ∀ᶠx in 𝓝[G] s, x ∉ closure V :=
      nhdsWithin_le_nhds (isClosed_closure.isOpen_compl.mem_nhds hscl)
    have heq : fillRegionOne V u =ᶠ[𝓝[G] s] u := by
      filter_upwards [hev] with x hx
      exact ite_eq_right (fun h => hx (subset_closure h))
    rwa [limsup_congr heq, liminf_congr heq]

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FilledFirstArrivalBarrier
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first-arrival barrier can be chosen equal to one throughout a closed
terminal collar while retaining its path inequality and all dust-band bounds. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel

variable [MeasurableSpace C(PathTime, Sphere)]

local instance localInst_rbc6963_30 : BorelSpace Sphere := ⟨rfl⟩
theorem exists_filled_first_arrival_barrier_potential_oai
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (d : PathCodeData Sphere Sphere) (hU : IsOpen d.quotientDomain)
    (hG : IsOpen d.physicalDomain) (hdisj : Disjoint d.quotientDomain d.dust)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨
      (x ∈ d.physicalDomainᶜ ∧ y ∈ connectedComponentIn d.physicalDomainᶜ x))
    (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hUB : Disjoint d.quotientDomain B) (hBU : Bᶜ ⊆ d.quotientDomain)
    (hdense : Dense d.quotientDomain) (hinfty : π OnePoint.infty ∉ B)
    (hbad : ∀x ∈ d.physicalDomainᶜ, π x ∈ B)
    (ν : Measure Sphere) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (E : Set Sphere) (hE : IsClosed E) (hEU : E ⊆ d.quotientDomain)
    (p : Sphere) (hpDust : p ∈ d.dust) (hp : p ≠ π OnePoint.infty)
    {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar d.physicalDomain π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (hED : Disjoint E (closure (D 0).region))
    (f : d.quotientDomain → Sphere) (hf : Continuous f)
    (W₁ W₂ : Set Sphere) (hW₁ : IsClosed W₁) (hW₂ : IsOpen W₂) (hW₁₂ : W₁ ⊆ W₂)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞)
    (m : Sphere → ℝ≥0∞) (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hm₂ : (∑' x, m x ^ 2) ≠ ∞)
    (w : ℝ≥0∞) (hw : w ≠ 0) (hpos : ∀z ∈ d.physicalDomain, w ≤ g z)
    (hpoint : ∀i z, volume {t | (t, z) ∈ d.levels i} ≤ d.levelWeights i z)
    (hunit : ∀(ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) → ρ.val ⊥ ∈ E → ρ.val ⊤ = p →
      (∀t < (⊤ : PathTime), ρ.val t ≠ p) →
      GateRules (fun j => frontier (D j).region)
        (fun _ => Subtype.val '' (f ⁻¹' closure W₂)) ρ.val →
      1 ≤ (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) +
        preterminalToll ρ.val m) :
    ∃k : ℕ, ∃O : Set Sphere, ∃g₁ : Sphere → ℝ≥0∞, ∃u : Sphere → ℝ,
      IsOpen O ∧ closure O ⊆ d.quotientDomain ∧ Disjoint E (closure O) ∧
      (∀x : d.quotientDomain, x.val ∈ closure O → f x ∉ W₁) ∧
      Measurable g₁ ∧ (∀y, g y ≤ g₁ y) ∧ (∀y, π y ∉ O → g₁ y = g y) ∧
      (∫⁻y, g₁ y ^ 2 ∂sphericalArea) < ∞ ∧
      (∀x, u x ∈ Icc 0 1) ∧ (∀x ∈ E, u x = 0) ∧
      (∀x ∈ closure (D k).region, u x = 1) ∧
      (∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
        Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
        ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g₁ m Γ.1) ∧
      ∀s ∈ B, ENNReal.ofReal (limsup u (𝓝[d.quotientDomain] s) -
        liminf u (𝓝[d.quotientDomain] s)) ≤ 4 * m s := by
  obtain ⟨k, O, g₁, u, hO, hOU, hEO, hfO, hg₁, hgg₁, hagree, henergy₁,
    hu, huE, huD, hpath, hband⟩ := exists_first_arrival_barrier_potential
      hcoarea hsard hsch d hU hG hdisj π hπ hclosed hsurj hr he hB hTD hUB hBU
      hdense hinfty hbad ν N E hE hEU p hpDust hp D hnest hshrink hED f hf W₁ W₂
      hW₁ hW₂ hW₁₂ g hg henergy m hm hm₂ w hw hpos hpoint hunit
  have hDo : IsOpen (D k).region := (D k).isOpen_region hπ hclosed hsurj hr
  have hDU : frontier (D k).region ⊆ d.quotientDomain :=
    (D k).frontier_region_subset_quotient d π hπ he hDo
  have ha : Antitone (fun j => (D j).region) :=
    antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  have hEk : Disjoint E (D k).region :=
    hED.mono_right ((ha (Nat.zero_le k)).trans subset_closure)
  refine ⟨k, O, g₁, fillRegionOne (D k).region u, hO, hOU, hEO, hfO,
    hg₁, hgg₁, hagree, henergy₁, fillRegionOne_mem_Icc _ _ hu, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxD : x ∉ (D k).region := fun h => Set.disjoint_left.mp hEk hx h
    simpa only [fillRegionOne, ite_eq_right hxD] using huE x hx
  · intro x hx
    by_cases hxD : x ∈ (D k).region
    · exact ite_eq_left hxD
    · have hxf : x ∈ frontier (D k).region := by
        rw [hDo.frontier_eq]
        exact ⟨hx, hxD⟩
      simpa only [fillRegionOne, ite_eq_right hxD] using huD x hxf
  · exact fillRegionOne_path_inequality d hU ν N (D k).region hDo hDU u huD
      g₁ hg₁ m hpoint hpath
  · intro s hs
    apply fillRegionOne_band d.quotientDomain (D k).region hDo u
      (by simpa only [hdense.closure_eq] using (Set.mem_univ s))
      (fun hf => Set.disjoint_left.mp hUB (hDU hf) hs) (4 * m s)
    exact hband s hs

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential_oai := @OAI.CircleDomainRigidity.exists_filled_first_arrival_barrier_potential_oai
