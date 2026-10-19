-- Prove2me | solution 1 for OAI.Erdos3.scalarCubeResidueWeights_riemann_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:51:39.66216+00:00
-- url     : https://prove2.me/submissions/78b7a2ed-6d92-46f0-a4e8-a6e8155b9db6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B110
import Definitions.Def_OAIE3v2B113

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberVolumeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem product_measureReal_le_of_fiber_bound {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (s : Set (A × B)) (hs : MeasurableSet s) (hsfin : (μ.prod ν) s ≠ ⊤)
    (T : Set A) (hT : MeasurableSet T) (hTfin : μ T ≠ ⊤)
    (hbase : ∀ z ∈ s, z.1 ∈ T) {b : ℝ}
    (hbound : ∀ x, ν.real {y | (x, y) ∈ s} ≤ b) :
    (μ.prod ν).real s ≤ μ.real T * b := by
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) (μ.prod ν) :=
    (integrableOn_const hsfin).integrable_indicator hs
  have hmajor : Integrable (T.indicator (fun _ => b)) μ :=
    (integrableOn_const hTfin).integrable_indicator hT
  rw [← integral_indicator_one hs]
  change (∫ z, s.indicator (fun _ => (1 : ℝ)) z ∂μ.prod ν) ≤ _
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ x, T.indicator (fun _ => b) x ∂μ := by
      apply integral_mono hi.integral_prod_left hmajor
      intro x
      change (∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂ν) ≤ T.indicator (fun _ => b) x
      rw [integral_indicator_fiber ν s hs]
      by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]
        exact hbound x
      · have hempty : {y | (x, y) ∈ s} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hx (hbase (x, y) hy)
        rw [hempty, measureReal_empty, Set.indicator_of_notMem hx]
    _ = _ := by rw [integral_indicator_const _ hT, smul_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RectangularLatticeCells
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem latticeSample_measurable (a S : ℝ) : Measurable (latticeSample a S) := by
  unfold latticeSample
  fun_prop

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

omit [Fintype J] in
theorem rectangularLatticeSample_measurable (a S : J → ℝ) :
    Measurable (rectangularLatticeSample a S) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (latticeSample_measurable (a j) (S j)).comp (measurable_pi_apply j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteRectangularHistogram_mul_test {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (w f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) (x : J → ℝ) :
    finiteRectangularHistogram s w a S x * f (rectangularLatticeRound a S x) =
      finiteRectangularHistogram s (fun k => w k * f k) a S x := by
  unfold finiteRectangularHistogram
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hx : x ∈ rectangularLatticeCell a S k
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      (rectangularLatticeCell_iff a S hS x k).mp hx]
  · simp only [Set.indicator_of_notMem hx, zero_mul]

theorem finiteRectangularHistogram_test_integral {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (w f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, finiteRectangularHistogram s w a S x * f (rectangularLatticeRound a S x)) =
      (∑ k ∈ s, w k * f k) / (∏ j, S j) := by
  simp_rw [finiteRectangularHistogram_mul_test s w f a S hS]
  exact finiteRectangularHistogram_integral s _ a S hS

theorem finiteRectangularHistogram_normalized_mean {J : Type*} [Fintype J]
    (s : Finset (J → ℤ)) (f : (J → ℤ) → ℝ) (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, (finiteRectangularHistogram s (fun _ => 1) a S x /
      (∫ y, finiteRectangularHistogram s (fun _ => 1) a S y)) * f (rectangularLatticeRound a S x)) =
      𝔼 k ∈ s, f k := by
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, finiteRectangularHistogram_test_integral s (fun _ => 1) f a S hS,
    finiteRectangularHistogram_integral s (fun _ => 1) a S hS]
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hP : (∏ j, S j) ≠ 0 := (Finset.prod_pos (fun j _ => hS j)).ne'
  rw [div_div_div_cancel_right₀ hP]
  exact (Finset.expect_eq_sum_div_card s f).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedDensityL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem positive_mass_inverse_difference {I J : ℝ} (hI : 0 < I) (hJ : 0 < J) :
    J * |1 / I - 1 / J| = |I - J| / I := by
  have he : 1 / I - 1 / J = (J - I) / (I * J) := by field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hI, abs_of_pos hJ, abs_sub_comm J I]
  field_simp

theorem normalized_density_l1 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hg0 : ∀ x, 0 ≤ g x) (hI : 0 < ∫ x, f x ∂μ) (hJ : 0 < ∫ x, g x ∂μ) :
    (∫ x, |f x / (∫ y, f y ∂μ) - g x / (∫ y, g y ∂μ)| ∂μ) ≤
      2 * (∫ x, |f x - g x| ∂μ) / (∫ x, f x ∂μ) := by
  let I := ∫ x, f x ∂μ
  let J := ∫ x, g x ∂μ
  have hI' : 0 < I := hI
  have hJ' : 0 < J := hJ
  have habs : Integrable (fun x => |f x - g x|) μ := (hf.sub hg).abs
  have hpoint (x : X) : |f x / I - g x / J| ≤
      |f x - g x| / I + g x * |1 / I - 1 / J| := by
    have he : f x / I - g x / J = (f x - g x) / I + g x * (1 / I - 1 / J) := by ring
    rw [he]
    simpa only [abs_div, abs_of_pos hI', abs_mul, abs_of_nonneg (hg0 x)] using
      abs_add_le ((f x - g x) / I) (g x * (1 / I - 1 / J))
  have hbound := integral_mono ((hf.div_const I).sub (hg.div_const J)).abs
    ((habs.div_const I).add (hg.mul_const |1 / I - 1 / J|)) hpoint
  dsimp only [Pi.sub_apply, Pi.add_apply] at hbound
  rw [integral_add (habs.div_const I) (hg.mul_const _), integral_div, integral_mul_const] at hbound
  change (∫ x, |f x / I - g x / J| ∂μ) ≤
    (∫ x, |f x - g x| ∂μ) / I + J * |1 / I - 1 / J| at hbound
  rw [positive_mass_inverse_difference hI' hJ'] at hbound
  have hm := abs_integral_le_integral_abs (f := fun x => f x - g x) (μ := μ)
  rw [integral_sub hf hg] at hm
  have hd := div_le_div_of_nonneg_right hm hI'.le
  change |I - J| / I ≤ (∫ x, |f x - g x| ∂μ) / I at hd
  change (∫ x, |f x / I - g x / J| ∂μ) ≤ 2 * (∫ x, |f x - g x| ∂μ) / I
  calc
    _ ≤ (∫ x, |f x - g x| ∂μ) / I + |I - J| / I := hbound
    _ ≤ (∫ x, |f x - g x| ∂μ) / I + (∫ x, |f x - g x| ∂μ) / I :=
      by linarith
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeJoin_none {α : Type*} (z : (α → ℝ) × ℝ) : scalarCubeJoin z none = z.2 := rfl

theorem scalarCubeJoin_some {α : Type*} (z : (α → ℝ) × ℝ) (i : α) :
    scalarCubeJoin z (some i) = z.1 i := rfl

theorem scalarCubeJoin_measurable (α : Type*) : Measurable (@scalarCubeJoin α) :=
  (MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)).symm.measurable

theorem scalarCubeJoin_measurePreserving (α : Type*) [Fintype α] :
    MeasurePreserving (@scalarCubeJoin α) volume volume := by
  refine ⟨scalarCubeJoin_measurable α, ?_⟩
  exact Measure.pi_map_piOptionEquivProd (fun _ : Option α => (volume : Measure ℝ))

theorem scalarCubeJoin_value {α : Type*} [Fintype α] [DecidableEq α]
    (z : (α → ℝ) × ℝ) (t : Finset α) :
    scalarCubeValue (scalarCubeJoin z) t = z.2 + ∑ i ∈ t, z.1 i := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature, scalarCubeJoin_none,
    scalarCubeJoin_some, ite_mul]

theorem scalarCubeJoin_face {α : Type*} [Fintype α] [DecidableEq α]
    (z : (α → ℝ) × ℝ) (i : Bool × Finset α) :
    scalarCubeFace i (scalarCubeJoin z) =
      if i.1 then 1 - (z.2 + ∑ k ∈ i.2, z.1 k) else z.2 + ∑ k ∈ i.2, z.1 k := by
  simp only [scalarCubeFace, scalarCubeJoin_value]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeMeasure_integral {α : Type*} [Fintype α] [DecidableEq α]
    (f : (Option α → ℝ) → ℝ) :
    (∫ a, f a ∂scalarCubeMeasure α) = scalarCubeDomainDensity α * ∫ a in scalarCubeDomain α, f a := by
  rw [scalarCubeMeasure, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomain_subset_closed (α : Type*) [Fintype α] [DecidableEq α] :
    scalarCubeDomain α ⊆ closedScalarCubeDomain α :=
  fun _ ha t => ⟨(ha t).1.le, (ha t).2.le⟩

theorem closedScalarCubeDomain_isClosed (α : Type*) [Fintype α] [DecidableEq α] :
    IsClosed (closedScalarCubeDomain α) := by
  have heq : closedScalarCubeDomain α = ⋂ t : Finset α, {a | scalarCubeValue a t ∈ Set.Icc (0 : ℝ) 1} := by
    ext a
    simp [closedScalarCubeDomain]
  rw [heq]
  exact isClosed_iInter (fun t => isClosed_Icc.preimage (scalarCubeValue_contDiff t).continuous)

theorem closedScalarCubeDomain_iff_faces {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) : a ∈ closedScalarCubeDomain α ↔ ∀ i, 0 ≤ scalarCubeFace i a := by
  constructor
  · intro ha i
    rcases i with ⟨side, t⟩
    cases side with
    | false => exact (ha t).1
    | true => exact sub_nonneg.mpr (ha t).2
  · intro ha t
    have hlo : 0 ≤ scalarCubeValue a t := ha (false, t)
    have hhi : 0 ≤ 1 - scalarCubeValue a t := ha (true, t)
    exact ⟨hlo, by linarith⟩

theorem closedScalarCubeDomain_compact (α : Type*) [Fintype α] [DecidableEq α] :
    IsCompact (closedScalarCubeDomain α) := by
  apply Metric.isCompact_of_isClosed_isBounded (closedScalarCubeDomain_isClosed α)
  apply (Metric.isBounded_closedBall (x := (0 : Option α → ℝ)) (r := 1)).subset
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  simpa only [Real.norm_eq_abs] using closedScalarCubeDomain_coordinate_abs_le_one ha r

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem closedScalarCubeFace_zero_volume {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) :
    volume (closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0}) = 0 := by
  let Z := closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0}
  have hZm : MeasurableSet Z := (closedScalarCubeDomain_isClosed α).measurableSet.inter
    (measurableSet_eq_fun (scalarCubeFace_contDiff i).continuous.measurable measurable_const)
  have hZfin : volume Z ≠ ⊤ := ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt
    (closedScalarCubeDomain_compact α).measure_lt_top)
  let s : Set ((α → ℝ) × ℝ) := scalarCubeJoin ⁻¹' Z
  have hs : MeasurableSet s := hZm.preimage (scalarCubeJoin_measurable α)
  have hm := (scalarCubeJoin_measurePreserving α).measure_preimage hZm.nullMeasurableSet
  have hmr := (scalarCubeJoin_measurePreserving α).measureReal_preimage hZm.nullMeasurableSet
  have hsfin : (volume : Measure ((α → ℝ) × ℝ)) s ≠ ⊤ := by
    change volume (scalarCubeJoin ⁻¹' Z) ≠ ⊤
    rw [hm]
    exact hZfin
  have hbase : ∀ z ∈ s, z.1 ∈ Metric.closedBall (0 : α → ℝ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    have h := closedScalarCubeDomain_coordinate_abs_le_one hz.1 (some k)
    simpa only [Real.norm_eq_abs, scalarCubeJoin_some] using h
  have hbound : ∀ b : α → ℝ, volume.real {y | (b, y) ∈ s} ≤ 0 := by
    intro b
    let c : ℝ := if i.1 then 1 - ∑ k ∈ i.2, b k else -(∑ k ∈ i.2, b k)
    have hsub : {y | (b, y) ∈ s} ⊆ {c} := by
      intro y hy
      have heq : scalarCubeFace i (scalarCubeJoin (b, y)) = 0 := hy.2
      rw [scalarCubeJoin_face] at heq
      apply Set.mem_singleton_iff.mpr
      dsimp [c]
      split_ifs at heq ⊢ <;> linarith
    have h := measureReal_mono (μ := volume) hsub (by simp)
    simpa [measureReal_def] using h
  have h := product_measureReal_le_of_fiber_bound
    (volume : Measure (α → ℝ)) (volume : Measure ℝ) s hs hsfin
    (Metric.closedBall (0 : α → ℝ) 1) measurableSet_closedBall
    (isCompact_closedBall _ _).measure_ne_top hbase hbound
  change volume.real s ≤ _ at h
  rw [hmr, mul_zero] at h
  exact (measureReal_eq_zero_iff hZfin).mp (le_antisymm h measureReal_nonneg)

theorem closedScalarCubeDomain_boundary_null (α : Type*) [Fintype α] [DecidableEq α] :
    volume (closedScalarCubeDomain α \ scalarCubeDomain α) = 0 := by
  have hsub : closedScalarCubeDomain α \ scalarCubeDomain α ⊆
      ⋃ i : Bool × Finset α, closedScalarCubeDomain α ∩ {a | scalarCubeFace i a = 0} := by
    intro a ha
    have hn : ¬ ∀ i, 0 < scalarCubeFace i a := by
      intro hp
      apply ha.2
      rw [← positiveInequalityDomain_scalarCubeFace α]
      exact hp
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hz : scalarCubeFace i a = 0 := le_antisymm (le_of_not_gt hi)
      ((closedScalarCubeDomain_iff_faces a).mp ha.1 i)
    exact Set.mem_iUnion.mpr ⟨i, ha.1, hz⟩
  exact measure_mono_null hsub (measure_iUnion_null closedScalarCubeFace_zero_volume)

theorem scalarCubeDomain_ae_closed (α : Type*) [Fintype α] [DecidableEq α] :
    scalarCubeDomain α =ᵐ[volume] closedScalarCubeDomain α := by
  apply ae_eq_set.mpr
  constructor
  · have he : scalarCubeDomain α \ closedScalarCubeDomain α = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact ha.2 (scalarCubeDomain_subset_closed α ha.1)
    rw [he, measure_empty]
  · exact closedScalarCubeDomain_boundary_null α

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem halfOpenScalarCubeDomain_measurable (I : Type*) [Fintype I] [DecidableEq I] :
    MeasurableSet (halfOpenScalarCubeDomain I) := by
  have he : halfOpenScalarCubeDomain I = ⋂ t : Finset I,
      (fun x => scalarCubeValue x t) ⁻¹' Set.Ico (0 : ℝ) 1 := by
    ext x
    simp only [halfOpenScalarCubeDomain, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  rw [he]
  exact MeasurableSet.iInter (fun (t : Finset I) =>
    measurableSet_Ico.preimage (scalarCubeValue_contDiff t).continuous.measurable)

theorem scalarCubeDomain_subset_halfOpen (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomain I ⊆ halfOpenScalarCubeDomain I :=
  fun _ hx t => ⟨(hx t).1.le, (hx t).2⟩

theorem halfOpenScalarCubeDomain_ae (I : Type*) [Fintype I] [DecidableEq I] :
    halfOpenScalarCubeDomain I =ᵐ[volume] scalarCubeDomain I := by
  filter_upwards [scalarCubeDomain_ae_closed I] with x hx
  apply propext
  have hx' : x ∈ scalarCubeDomain I ↔ x ∈ closedScalarCubeDomain I := iff_of_eq hx
  constructor
  · intro h
    exact hx'.mpr (halfOpenScalarCubeDomain_subset_closed I h)
  · exact fun h => scalarCubeDomain_subset_halfOpen I h

theorem scalarCubeIndicator_range (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) : 0 ≤ scalarCubeIndicator I x ∧ scalarCubeIndicator I x ≤ 1 := by
  unfold scalarCubeIndicator
  split_ifs <;> norm_num

theorem scalarCubeIndicator_integrable (I : Type*) [Fintype I] [DecidableEq I] :
    Integrable (scalarCubeIndicator I) := by
  change Integrable ((halfOpenScalarCubeDomain I).indicator (fun _ => (1 : ℝ)))
  exact (integrableOn_const ((measure_mono (halfOpenScalarCubeDomain_subset_closed I)).trans_lt
    (closedScalarCubeDomain_compact I).measure_lt_top).ne).integrable_indicator
    (halfOpenScalarCubeDomain_measurable I)

theorem scalarCubeIndicator_integral (I : Type*) [Fintype I] [DecidableEq I] :
    (∫ x, scalarCubeIndicator I x) = volume.real (scalarCubeDomain I) := by
  have he : scalarCubeIndicator I =ᵐ[volume] (scalarCubeDomain I).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [halfOpenScalarCubeDomain_ae I] with x hx
    have hx' : (x ∈ halfOpenScalarCubeDomain I) = (x ∈ scalarCubeDomain I) := hx
    change (if x ∈ halfOpenScalarCubeDomain I then 1 else 0) =
      if x ∈ scalarCubeDomain I then 1 else 0
    rw [hx']
  rw [integral_congr_ae he]
  exact integral_indicator_one (scalarCubeDomain_isOpen I).measurableSet

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeFaceSlab_measurable {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : MeasurableSet (scalarCubeFaceSlab i u) :=
  measurableSet_closedBall.inter (measurableSet_le
    (scalarCubeFace_contDiff i).continuous.abs.measurable measurable_const)

theorem scalarCubeFaceSlab_finite {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) (u : ℝ) : volume (scalarCubeFaceSlab i u) ≠ ⊤ :=
  ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt (isCompact_closedBall _ _).measure_lt_top)

theorem scalarCubeFaceSlab_fiber_bound {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) {u : ℝ} (hu : 0 ≤ u) (b : I → ℝ) :
    volume.real {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceSlab i u} ≤ 2*u := by
  let c : ℝ := if i.1 then 1 - ∑ k ∈ i.2, b k else -(∑ k ∈ i.2, b k)
  have hsub : {y | scalarCubeJoin (b, y) ∈ scalarCubeFaceSlab i u} ⊆ Set.Icc (c-u) (c+u) := by
    intro y hy
    have hraw : |scalarCubeFace i (scalarCubeJoin (b,y))| ≤ u := hy.2
    have h := abs_le.mp hraw
    rw [scalarCubeJoin_face] at h
    dsimp only [c]
    split_ifs at h ⊢ <;> constructor <;> linarith
  have hv : volume.real (Set.Icc (c-u) (c+u)) = 2*u := by
    rw [Real.volume_real_Icc]
    simp only [show c+u-(c-u) = 2*u by ring, max_eq_left (by positivity : 0 ≤ 2*u)]
  exact (measureReal_mono (μ := volume) hsub (by simp [Real.volume_Icc])).trans_eq hv

theorem scalarCubeFaceSlab_volume_le {I : Type*} [Fintype I] [DecidableEq I]
    (i : Bool × Finset I) {u : ℝ} (hu : 0 ≤ u) :
    volume.real (scalarCubeFaceSlab i u) ≤ (4 : ℝ)^Fintype.card I * (2*u) := by
  let s := scalarCubeJoin ⁻¹' scalarCubeFaceSlab i u
  have hs : MeasurableSet s := (scalarCubeFaceSlab_measurable i u).preimage (scalarCubeJoin_measurable I)
  have hm := (scalarCubeJoin_measurePreserving I).measure_preimage (scalarCubeFaceSlab_measurable i u).nullMeasurableSet
  have hmr := (scalarCubeJoin_measurePreserving I).measureReal_preimage (scalarCubeFaceSlab_measurable i u).nullMeasurableSet
  have hfin : (volume : Measure ((I → ℝ) × ℝ)) s ≠ ⊤ := by
    change volume (scalarCubeJoin ⁻¹' scalarCubeFaceSlab i u) ≠ ⊤
    rw [hm]
    exact scalarCubeFaceSlab_finite i u
  have hb : ∀ z ∈ s, z.1 ∈ Metric.closedBall (0 : I → ℝ) 2 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro k
    have hh : ‖scalarCubeJoin z‖ ≤ 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
    exact (norm_le_pi_norm (scalarCubeJoin z) (some k)).trans hh
  have h := product_measureReal_le_of_fiber_bound
    (volume : Measure (I → ℝ)) (volume : Measure ℝ) s hs hfin
    (Metric.closedBall (0 : I → ℝ) 2) measurableSet_closedBall (isCompact_closedBall _ _).measure_ne_top
    hb (scalarCubeFaceSlab_fiber_bound i hu)
  change volume.real s ≤ _ at h
  rw [hmr] at h
  have hbase : volume.real (Metric.closedBall (0 : I → ℝ) 2) = (4 : ℝ)^Fintype.card I := by
    rw [measureReal_def, Real.volume_pi_closedBall _ (by norm_num)]
    norm_num
  rwa [hbase] at h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeIndicator_disagreement {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (he : ‖y-x‖ ≤ δ)
    (hne : scalarCubeIndicator I y ≠ scalarCubeIndicator I x) :
    ∃ i : Bool × Finset I, x ∈ scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ) := by
  have hv (t : Finset I) := scalarCubeValue_sub_bound y x hδ he t
  have hxnorm (hy : y ∈ halfOpenScalarCubeDomain I) : ‖x‖ ≤ 2 := by
    have ht : ‖x‖ ≤ ‖y-x‖ + ‖y‖ := by
      calc
        ‖x‖ = ‖-(y-x)+y‖ := by congr 1; abel
        _ ≤ ‖-(y-x)‖ + ‖y‖ := norm_add_le _ _
        _ = _ := by rw [norm_neg]
    linarith [halfOpenScalarCubeDomain_norm_le hy]
  by_cases hx : x ∈ halfOpenScalarCubeDomain I
  · have hy : y ∉ halfOpenScalarCubeDomain I := by
      intro hy
      exact hne (by simp only [scalarCubeIndicator, hx, hy, ite_true])
    obtain ⟨t, ht⟩ := not_forall.mp hy
    have hbox : x ∈ Metric.closedBall 0 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (halfOpenScalarCubeDomain_norm_le hx).trans (by norm_num : (1 : ℝ) ≤ 2)
    have hxval := hx t
    have hdiff := abs_le.mp (hv t)
    by_cases hlo : scalarCubeValue y t < 0
    · refine ⟨(false,t), hbox, ?_⟩
      change |scalarCubeValue x t| ≤ _
      rw [abs_of_nonneg hxval.1]
      linarith [hxval.1, hxval.2, hdiff.1, hdiff.2]
    · have hhi : 1 ≤ scalarCubeValue y t := by
        by_contra! hn
        exact ht ⟨le_of_not_gt hlo, hn⟩
      refine ⟨(true,t), hbox, ?_⟩
      change |1-scalarCubeValue x t| ≤ _
      rw [abs_of_nonneg (by linarith [hxval.2])]
      linarith [hxval.1, hxval.2, hdiff.1, hdiff.2]
  · have hy : y ∈ halfOpenScalarCubeDomain I := by
      by_contra hy
      exact hne (by simp only [scalarCubeIndicator, hx, hy, ite_false])
    obtain ⟨t, ht⟩ := not_forall.mp hx
    have hbox : x ∈ Metric.closedBall 0 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxnorm hy
    have hyval := hy t
    have hdiff := abs_le.mp (hv t)
    by_cases hlo : scalarCubeValue x t < 0
    · refine ⟨(false,t), hbox, ?_⟩
      change |scalarCubeValue x t| ≤ _
      rw [abs_of_neg hlo]
      linarith [hyval.1, hyval.2, hdiff.1, hdiff.2]
    · have hhi : 1 ≤ scalarCubeValue x t := by
        by_contra! hn
        exact ht ⟨le_of_not_gt hlo, hn⟩
      refine ⟨(true,t), hbox, ?_⟩
      change |1-scalarCubeValue x t| ≤ _
      rw [abs_of_nonpos (by linarith)]
      linarith [hyval.1, hyval.2, hdiff.1, hdiff.2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityTestParameter
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem density_bounded_test_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (φ : X → ℝ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(∫ x, f x * φ x ∂μ) - ∫ x, g x * φ x ∂μ| ≤ B * ∫ x, |f x-g x| ∂μ := by
  rw [← integral_sub (hf.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))
    (hg.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ x, B * |f x-g x| ∂μ := by
      apply integral_mono
      · exact ((hf.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)).sub
          (hg.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb))).abs
      · exact (hf.sub hg).abs.const_mul B
      · intro x
        change |f x * φ x - g x * φ x| ≤ B * |f x-g x|
        rw [← sub_mul, abs_mul, mul_comm B]
        exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hb x) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

theorem density_rounding_test_error {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hg0 : ∀ x, 0 ≤ g x) (hgmass : (∫ x, g x ∂μ) = 1)
    (R : X → X) (hR : Measurable R) {δ ε B : ℝ} (hB : 0 ≤ B)
    (herr : ∫ x, |f x-g x| ∂μ ≤ ε) (hmove : ∀ x, dist (R x) x ≤ δ)
    (φ : X → ℝ) {K : ℝ≥0} (hφ : LipschitzWith K φ) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(∫ x, f x * φ (R x) ∂μ) - ∫ x, g x * φ x ∂μ| ≤ B*ε + K*δ := by
  have hφR : Measurable (fun x => φ (R x)) := hφ.continuous.measurable.comp hR
  have hfirst := density_bounded_test_error μ f g hf hg (φ ∘ R) hφR (fun x => hb (R x))
  have hsecond : |(∫ x, g x * φ (R x) ∂μ) - ∫ x, g x * φ x ∂μ| ≤ K*δ := by
    rw [← integral_sub (hg.mul_bdd hφR.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => hb (R x))))
      (hg.mul_bdd hφ.continuous.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hb))]
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ x, g x * (K*δ) ∂μ := by
        apply integral_mono
        · exact ((hg.mul_bdd hφR.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => hb (R x)))).sub
            (hg.mul_bdd hφ.continuous.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hb))).abs
        · exact hg.mul_const _
        · intro x
          change |g x * φ (R x) - g x * φ x| ≤ g x * (K*δ)
          rw [← mul_sub, abs_mul, abs_of_nonneg (hg0 x)]
          apply mul_le_mul_of_nonneg_left _ (hg0 x)
          exact (hφ.dist_le_mul (R x) x).trans (mul_le_mul_of_nonneg_left (hmove x) K.coe_nonneg)
      _ = _ := by rw [integral_mul_const, hgmass, one_mul]
  have ht := abs_sub_le (∫ x, f x * φ (R x) ∂μ) (∫ x, g x * φ (R x) ∂μ) (∫ x, g x * φ x ∂μ)
  exact ht.trans (add_le_add (hfirst.trans (mul_le_mul_of_nonneg_left herr hB)) hsecond)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem scalarCubeGridHistogram_eq (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (x : Option I → ℝ) :
    scalarCubeGridHistogram I a S x = scalarCubeIndicator I (rectangularLatticeSample a S x) :=
  rectangularWeightHistogram_eq _ a S hS (scalarCubeIndicator_zero_outside I) x

theorem scalarCubeGridHistogram_integrable (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : Integrable (scalarCubeGridHistogram I a S) :=
  rectangularWeightHistogram_integrable _ a S 1

theorem scalarCubeGridHistogram_point_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) (x : Option I → ℝ) :
    |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x| ≤
      ∑ i : Bool × Finset I, (scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ)).indicator
        (fun _ => (1 : ℝ)) x := by
  rw [scalarCubeGridHistogram_eq I a S hS]
  have hnonneg (i : Bool × Finset I) : 0 ≤
      (scalarCubeFaceSlab i ((Fintype.card I + 1 : ℝ)*δ)).indicator (fun _ => (1 : ℝ)) x := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases heq : scalarCubeIndicator I (rectangularLatticeSample a S x) = scalarCubeIndicator I x
  · rw [heq, sub_self, abs_zero]
    exact Finset.sum_nonneg (fun i _ => hnonneg i)
  · obtain ⟨i, hi⟩ := scalarCubeIndicator_disagreement x (rectangularLatticeSample a S x)
      hδ hδ1 (rectangularLatticeSample_error a S hS hδ hmesh x) heq
    have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Bool × Finset I))) => hnonneg j)
      (Finset.mem_univ i)
    rw [Set.indicator_of_mem hi] at hle
    have h₁ := scalarCubeIndicator_range I (rectangularLatticeSample a S x)
    have h₂ := scalarCubeIndicator_range I x
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans hle

theorem scalarCubeGridHistogram_l1_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) :
    (∫ x, |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x|) ≤
      scalarCubeGridBoundaryConstant I * δ := by
  let u := (Fintype.card I + 1 : ℝ)*δ
  have hi (i : Bool × Finset I) : Integrable ((scalarCubeFaceSlab i u).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (scalarCubeFaceSlab_finite i u)).integrable_indicator (scalarCubeFaceSlab_measurable i u)
  have h := integral_mono ((scalarCubeGridHistogram_integrable I a S).sub (scalarCubeIndicator_integrable I)).abs
    (integrable_finsetSum _ (fun i _ => hi i)) (scalarCubeGridHistogram_point_error I a S hS hδ hδ1 hmesh)
  calc
    _ ≤ ∫ x, ∑ i : Bool × Finset I, (scalarCubeFaceSlab i u).indicator (fun _ => (1 : ℝ)) x := h
    _ = ∑ i : Bool × Finset I, volume.real (scalarCubeFaceSlab i u) := by
      rw [integral_finsetSum _ (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_indicator_one (scalarCubeFaceSlab_measurable i u)
    _ ≤ ∑ _i : Bool × Finset I, (4 : ℝ)^Fintype.card I * (2*u) :=
      Finset.sum_le_sum (fun i _ => scalarCubeFaceSlab_volume_le i (by dsimp [u]; positivity))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, u, scalarCubeGridBoundaryConstant]; ring

theorem scalarCubeGridHistogram_mass_error (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) :
    |(∫ x, scalarCubeGridHistogram I a S x) - volume.real (scalarCubeDomain I)| ≤
      scalarCubeGridBoundaryConstant I * δ := by
  rw [← scalarCubeIndicator_integral I, ← integral_sub (scalarCubeGridHistogram_integrable I a S)
    (scalarCubeIndicator_integrable I)]
  exact (abs_integral_le_integral_abs).trans (scalarCubeGridHistogram_l1_error I a S hS hδ hδ1 hmesh)

theorem scalarCubeGridHistogram_mass_pos (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ)
    (hsmall : scalarCubeGridBoundaryConstant I * δ < volume.real (scalarCubeDomain I)) :
    0 < ∫ x, scalarCubeGridHistogram I a S x := by
  have h := (abs_le.mp (scalarCubeGridHistogram_mass_error I a S hS hδ hδ1 hmesh)).1
  linarith

theorem scalarCubeGridHistogram_normalized_l1 (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x) :
    (∫ x, |scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y) -
      scalarCubeIndicator I x / volume.real (scalarCubeDomain I)|) ≤
      2 * scalarCubeGridBoundaryConstant I * δ / volume.real (scalarCubeDomain I) := by
  have hV : 0 < volume.real (scalarCubeDomain I) := by
    exact ENNReal.toReal_pos (scalarCubeDomain_volume_pos I).ne' (scalarCubeDomain_volume_lt_top I).ne
  have hn := normalized_density_l1 volume (scalarCubeIndicator I) (scalarCubeGridHistogram I a S)
    (scalarCubeIndicator_integrable I) (scalarCubeGridHistogram_integrable I a S)
    (fun x => by rw [scalarCubeGridHistogram_eq I a S hS]; exact (scalarCubeIndicator_range I _).1)
    (by rwa [scalarCubeIndicator_integral I]) hpos
  rw [scalarCubeIndicator_integral I] at hn
  have he := scalarCubeGridHistogram_l1_error I a S hS hδ hδ1 hmesh
  have hn' : (∫ x, |scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y) -
      scalarCubeIndicator I x / volume.real (scalarCubeDomain I)|) ≤
      2 * (∫ x, |scalarCubeGridHistogram I a S x - scalarCubeIndicator I x|) /
        volume.real (scalarCubeDomain I) := by
    simpa only [abs_sub_comm] using hn
  apply hn'.trans
  calc
    _ ≤ 2 * (scalarCubeGridBoundaryConstant I * δ) / volume.real (scalarCubeDomain I) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hV.le
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem scalarCubeGridHistogram_finite (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) : scalarCubeGridHistogram I a S =
      finiteRectangularHistogram (scalarCubeGridSet I a S) (fun _ => 1) a S := by
  funext x
  unfold scalarCubeGridHistogram rectangularWeightHistogram finiteRectangularHistogram scalarCubeGridSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : rectangularLatticePoint a S k ∈ halfOpenScalarCubeDomain I
  · simp only [rectangularWeight, scalarCubeIndicator, hk, ite_true]
  · simp only [rectangularWeight, scalarCubeIndicator, hk, ite_false, Set.indicator_zero]

theorem scalarCubeGridHistogram_mean (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (φ : (Option I → ℝ) → ℝ) :
    (∫ x, (scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y)) *
      φ (rectangularLatticeSample a S x)) =
      𝔼 k ∈ scalarCubeGridSet I a S, φ (rectangularLatticePoint a S k) := by
  rw [scalarCubeGridHistogram_finite]
  exact finiteRectangularHistogram_normalized_mean (scalarCubeGridSet I a S)
    (fun k => φ (rectangularLatticePoint a S k)) a S hS

theorem scalarCubeIndicator_test (I : Type*) [Fintype I] [DecidableEq I]
    (φ : (Option I → ℝ) → ℝ) :
    (∫ x, (scalarCubeIndicator I x / volume.real (scalarCubeDomain I)) * φ x) =
      ∫ x, φ x ∂scalarCubeMeasure I := by
  rw [scalarCubeMeasure_integral]
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]
  have he : (fun x => scalarCubeIndicator I x * φ x) =ᵐ[volume]
      (scalarCubeDomain I).indicator φ := by
    filter_upwards [halfOpenScalarCubeDomain_ae I] with x hx
    have hx' : (x ∈ halfOpenScalarCubeDomain I) = (x ∈ scalarCubeDomain I) := hx
    simp only [scalarCubeIndicator, hx']
    by_cases h : x ∈ scalarCubeDomain I
    · simp only [h, ite_true, one_mul, Set.indicator_of_mem h]
    · simp only [h, ite_false, zero_mul, Set.indicator_of_notMem h]
  rw [integral_congr_ae he, integral_indicator (scalarCubeDomain_isOpen I).measurableSet]
  simp only [scalarCubeDomainDensity, div_eq_mul_inv, mul_comm]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeGrid_comparison (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ i, 1 / S i ≤ δ) (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x)
    (φ : (Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(𝔼 k ∈ scalarCubeGridSet I a S, φ (rectangularLatticePoint a S k)) -
      ∫ x, φ x ∂scalarCubeMeasure I| ≤
      B * (2 * scalarCubeGridBoundaryConstant I * δ / volume.real (scalarCubeDomain I)) + K*δ := by
  have hV := scalarCubeDomain_volumeReal_pos I
  have hmass : (∫ x, scalarCubeIndicator I x / volume.real (scalarCubeDomain I)) = 1 := by
    rw [integral_div, scalarCubeIndicator_integral I, div_self hV.ne']
  have h := density_rounding_test_error volume
    (fun x => scalarCubeGridHistogram I a S x / (∫ y, scalarCubeGridHistogram I a S y))
    (fun x => scalarCubeIndicator I x / volume.real (scalarCubeDomain I))
    ((scalarCubeGridHistogram_integrable I a S).div_const _)
    ((scalarCubeIndicator_integrable I).div_const _)
    (fun x => div_nonneg (scalarCubeIndicator_range I x).1 hV.le) hmass
    (rectangularLatticeSample a S) (rectangularLatticeSample_measurable a S) hB
    (scalarCubeGridHistogram_normalized_l1 I a S hS hδ hδ1 hmesh hpos)
    (fun x => by simpa only [dist_eq_norm] using rectangularLatticeSample_error a S hS hδ hmesh x)
    φ hφ hb
  rwa [scalarCubeGridHistogram_mean I a S hS φ, scalarCubeIndicator_test I φ] at h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeResidueWeights_grid_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (φ : (Option I → ℝ) → ℝ) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean
      (fun z => φ (fun i => (z i : ℝ) / L)) =
      𝔼 k ∈ scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m),
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k) := by
  rw [scalarCubeResidueWeights_mean]
  let e := scalarCubeResidueGridEquiv I L hL m r hm
  have he (k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))) :
      rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k.val =
        fun i => ((e k).val i : ℝ) / L := by
    rw [scalarResidueGrid_normalized hL m r hm]
    funext i
    rfl
  calc
    _ = 𝔼 k : ↥(scalarCubeGridSet I (scalarResidueGridOffset m r) (scalarResidueGridScale L m)),
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k.val) := by
      symm
      exact Fintype.expect_equiv e _ _ (fun k => congrArg φ (he k))
    _ = _ := by
      rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe]
      congr 1
      exact Finset.sum_coe_sort _ (fun k =>
        φ (rectangularLatticePoint (scalarResidueGridOffset m r) (scalarResidueGridScale L m) k))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeResidueWeights_riemann_s2_oai (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (hsmall : scalarCubeGridBoundaryConstant I * ((M : ℝ)/L) < volume.real (scalarCubeDomain I))
    (φ : (Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean
        (fun z => φ (fun i => (z i : ℝ) / L)) - ∫ x, φ x ∂scalarCubeMeasure I| ≤
      (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) * ((M : ℝ)/L) := by
  rw [scalarCubeResidueWeights_grid_mean]
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hML : M ≤ L := by nlinarith
  have hδ : (0 : ℝ) ≤ (M : ℝ)/L := by positivity
  have hδ1 : (M : ℝ)/L ≤ 1 := (div_le_one hLp).mpr (by exact_mod_cast hML)
  have hS := scalarResidueGridScale_pos hL m hm
  have hmesh (i : Option I) : 1 / scalarResidueGridScale L m i ≤ (M : ℝ)/L := by
    simp only [scalarResidueGridScale, one_div_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmM i) hLp.le
  have hpos := scalarCubeGridHistogram_mass_pos I (scalarResidueGridOffset m r) _ hS hδ hδ1 hmesh hsmall
  exact (scalarCubeGrid_comparison I _ _ hS hδ hδ1 hmesh hpos φ hφ hB hb).trans_eq (by ring)

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.scalarCubeResidueWeights_riemann_s2_oai.{u_1} := @OAI.Erdos3.scalarCubeResidueWeights_riemann_s2_oai.{u_1}
