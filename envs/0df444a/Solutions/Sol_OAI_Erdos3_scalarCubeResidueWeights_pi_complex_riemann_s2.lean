-- Prove2me | solution 1 for OAI.Erdos3.scalarCubeResidueWeights_pi_complex_riemann_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:51:38.936581+00:00
-- url     : https://prove2.me/submissions/eb93089d-4960-4f85-9eb1-b713ccc6ce21

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B110
import Definitions.Def_OAIE3v2B113
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B117

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem abs_sub_eq_add_sub_two_min (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem measured_density_overlap {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmass : (∫ x, f x ∂μ) = 1) (hgmass : (∫ x, g x ∂μ) = 1) :
    (∫ x, min (f x) (g x) ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      (∫ x, |f x-g x| ∂μ) = 2 - 2 * ∫ x, min (f x) (g x) ∂μ := by
  have hm : Integrable (fun x => min (f x) (g x)) μ := hf.inf hg
  have hsum : Integrable (fun x => f x + g x) μ := hf.add hg
  constructor
  · exact ⟨integral_nonneg (fun x => le_min (hf0 x) (hg0 x)),
      (integral_mono hm hf (fun x => min_le_left _ _)).trans_eq hfmass⟩
  · simp_rw [abs_sub_eq_add_sub_two_min]
    rw [integral_sub hsum (hm.const_mul 2), integral_add hf hg,
      integral_const_mul, hfmass, hgmass]
    norm_num

theorem tensor_density_l1_le_sum {D : Type*} [Fintype D] [DecidableEq D]
    {X : D → Type*} [∀ d, MeasurableSpace (X d)] (μ : ∀ d, Measure (X d)) [∀ d, SigmaFinite (μ d)]
    (f g : ∀ d, X d → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hg : ∀ d, Integrable (g d) (μ d))
    (hf0 : ∀ d x, 0 ≤ f d x) (hg0 : ∀ d x, 0 ≤ g d x)
    (hfmass : ∀ d, (∫ x, f d x ∂μ d) = 1) (hgmass : ∀ d, (∫ x, g d x ∂μ d) = 1) :
    (∫ x, |(∏ d, f d (x d)) - ∏ d, g d (x d)| ∂Measure.pi μ) ≤
      ∑ d, ∫ x, |f d x-g d x| ∂μ d := by
  let F := fun x : ∀ d, X d => ∏ d, f d (x d)
  let G := fun x : ∀ d, X d => ∏ d, g d (x d)
  let H := fun x : ∀ d, X d => ∏ d, min (f d (x d)) (g d (x d))
  let mass := fun d => ∫ x, min (f d x) (g d x) ∂μ d
  have hF : Integrable F (Measure.pi μ) := Integrable.fintype_prod_dep hf
  have hG : Integrable G (Measure.pi μ) := Integrable.fintype_prod_dep hg
  have hH : Integrable H (Measure.pi μ) := Integrable.fintype_prod_dep (fun d => (hf d).inf (hg d))
  have hpoint (x : ∀ d, X d) : |F x-G x| ≤ F x+G x-2*H x := by
    have hl : H x ≤ F x := Finset.prod_le_prod
      (fun d _ => le_min (hf0 d _) (hg0 d _)) (fun d _ => min_le_left _ _)
    have hr : H x ≤ G x := Finset.prod_le_prod
      (fun d _ => le_min (hf0 d _) (hg0 d _)) (fun d _ => min_le_right _ _)
    rw [abs_sub_eq_add_sub_two_min]
    have hh := le_min hl hr
    linarith
  have hFm : (∫ x, F x ∂Measure.pi μ) = 1 := by
    rw [show F = (fun x => ∏ d, f d (x d)) from rfl, integral_fintype_prod_eq_prod]
    simp only [hfmass, Finset.prod_const_one]
  have hGm : (∫ x, G x ∂Measure.pi μ) = 1 := by
    rw [show G = (fun x => ∏ d, g d (x d)) from rfl, integral_fintype_prod_eq_prod]
    simp only [hgmass, Finset.prod_const_one]
  have hHm : (∫ x, H x ∂Measure.pi μ) = ∏ d, mass d :=
    integral_fintype_prod_eq_prod (fun d x => min (f d x) (g d x))
  have hsum : Integrable (fun x => F x + G x) (Measure.pi μ) := hF.add hG
  have he := integral_mono (hF.sub hG).abs ((hF.add hG).sub (hH.const_mul 2)) hpoint
  change (∫ x, |F x-G x| ∂Measure.pi μ) ≤
    ∫ x, F x+G x-2*H x ∂Measure.pi μ at he
  rw [integral_sub hsum (hH.const_mul 2), integral_add hF hG,
    integral_const_mul, hFm, hGm, hHm] at he
  have hm (d) := measured_density_overlap (μ d) (f d) (g d) (hf d) (hg d)
    (hf0 d) (hg0 d) (hfmass d) (hgmass d)
  have hp := one_sub_sum_le_positive_prod Finset.univ mass (fun d => 1-mass d)
    (fun d _ => (hm d).1.1) (fun d _ => ⟨by linarith [(hm d).1.2], by linarith [(hm d).1.1]⟩)
    (fun d _ => by linarith)
  have hh : (∑ d, ∫ x, |f d x-g d x| ∂μ d) = 2 * ∑ d, (1-mass d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [(hm d).2]
    dsimp only [mass]
    ring
  rw [hh]
  change (∫ x, |F x-G x| ∂Measure.pi μ) ≤ _
  linarith

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

open scoped BigOperators

theorem FiniteProbabilityWeights.complexMean_im {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (F : X → ℂ) :
    (p.complexMean F).im = p.mean (fun x => (F x).im) := by
  simp [complexMean, mean, Complex.mul_im]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeHistogramMeasure
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

theorem imageMeasure_probability {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) : IsProbabilityMeasure (p.imageMeasure F) := by
  constructor
  simp only [imageMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x), p.total, ENNReal.ofReal_one]

theorem imageMeasure_apply {X Y : Type*} [Fintype X] [MeasurableSpace Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (s : Set Y) (hs : MeasurableSet s) :
    p.imageMeasure F s = ∑ x, if F x ∈ s then ENNReal.ofReal (p.weight x) else 0 := by
  simp only [imageMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Set.indicator_apply, Pi.one_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem imageMeasure_integral {X Y : Type*} [Fintype X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (φ : Y → ℝ) :
    (∫ y, φ y ∂p.imageMeasure F) = p.mean (fun x => φ (F x)) := by
  rw [imageMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (p.nonneg _),
      smul_eq_mul, mean]
  · intro x _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators Classical

theorem imageMeasure_pi {D : Type*} [Fintype D] [DecidableEq D]
    {X Y : D → Type*} [∀ d, Fintype (X d)] [∀ d, MeasurableSpace (Y d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (F : ∀ d, X d → Y d) :
    Measure.pi (fun d => (p d).imageMeasure (F d)) =
      (pi p).imageMeasure (fun x d => F d (x d)) := by
  let : ∀ d, IsProbabilityMeasure ((p d).imageMeasure (F d)) := fun d => imageMeasure_probability _ _
  apply Measure.pi_eq
  intro s hs
  rw [imageMeasure_apply _ _ _ (MeasurableSet.univ_pi hs)]
  simp_rw [imageMeasure_apply _ _ _ (hs _)]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hw : ENNReal.ofReal ((pi p).weight x) = ∏ d, ENNReal.ofReal ((p d).weight (x d)) :=
    ENNReal.ofReal_prod_of_nonneg (fun d _ => (p d).nonneg (x d))
  rw [hw]
  by_cases hx : ∀ d, F d (x d) ∈ s d
  · have hm : (fun d => F d (x d)) ∈ Set.univ.pi s := fun d _ => hx d
    simp only [hm, ite_true, hx]
  · have hm : (fun d => F d (x d)) ∉ Set.univ.pi s := fun h => hx (fun d => h d (Set.mem_univ _))
    rw [if_neg hm]
    obtain ⟨d,hd⟩ := not_forall.mp hx
    exact (Finset.prod_eq_zero (Finset.mem_univ d) (if_neg hd)).symm

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeProbabilityDensity_measurable (I : Type*) [Fintype I] [DecidableEq I] :
    Measurable (scalarCubeProbabilityDensity I) := by
  have hm : Measurable (scalarCubeIndicator I) :=
    measurable_const.indicator (halfOpenScalarCubeDomain_measurable I)
  exact hm.div_const _

theorem scalarCubeProbabilityDensity_spec (I : Type*) [Fintype I] [DecidableEq I] :
    Integrable (scalarCubeProbabilityDensity I) ∧
      (∀ x, 0 ≤ scalarCubeProbabilityDensity I x) ∧ (∫ x, scalarCubeProbabilityDensity I x) = 1 := by
  have hV := scalarCubeDomain_volumeReal_pos I
  refine ⟨(scalarCubeIndicator_integrable I).div_const _,
    fun x => div_nonneg (scalarCubeIndicator_range I x).1 hV.le, ?_⟩
  change (∫ x, scalarCubeIndicator I x / volume.real (scalarCubeDomain I)) = 1
  rw [integral_div, scalarCubeIndicator_integral, div_self hV.ne']

theorem scalarCubeProbabilityDensity_measure (I : Type*) [Fintype I] [DecidableEq I] :
    realDensityMeasure volume (scalarCubeProbabilityDensity I) = scalarCubeMeasure I := by
  have h := scalarCubeProbabilityDensity_spec I
  let : IsFiniteMeasure (realDensityMeasure volume (scalarCubeProbabilityDensity I)) :=
    realDensityMeasure_finite volume _ h.1 h.2.1
  apply finiteMeasure_eq_of_integrals
  intro φ _
  rw [realDensityMeasure_integral _ _ (scalarCubeProbabilityDensity_measurable I) h.2.1]
  exact scalarCubeIndicator_test I φ

theorem scalarCubeGridDensity_measurable (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) : Measurable (scalarCubeGridDensity I a S) := by
  have hm : Measurable (scalarCubeIndicator I) :=
    measurable_const.indicator (halfOpenScalarCubeDomain_measurable I)
  have hh : Measurable (scalarCubeGridHistogram I a S) := by
    have he : scalarCubeGridHistogram I a S =
        fun x => scalarCubeIndicator I (rectangularLatticeSample a S x) :=
      funext (scalarCubeGridHistogram_eq I a S hS)
    rw [he]
    exact hm.comp (rectangularLatticeSample_measurable a S)
  exact hh.div_const _

theorem scalarCubeGridDensity_spec (I : Type*) [Fintype I] [DecidableEq I]
    (a S : Option I → ℝ) (hS : ∀ i, 0 < S i) (hpos : 0 < ∫ x, scalarCubeGridHistogram I a S x) :
    Integrable (scalarCubeGridDensity I a S) ∧ (∀ x, 0 ≤ scalarCubeGridDensity I a S x) ∧
      (∫ x, scalarCubeGridDensity I a S x) = 1 := by
  refine ⟨(scalarCubeGridHistogram_integrable I a S).div_const _, ?_, ?_⟩
  · intro x
    unfold scalarCubeGridDensity
    rw [scalarCubeGridHistogram_eq I a S hS]
    exact div_nonneg (scalarCubeIndicator_range I _).1 hpos.le
  · unfold scalarCubeGridDensity
    rw [integral_div, div_self hpos.ne']

theorem scalarCubeResidue_imageMeasure (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (hpos : 0 < ∫ x, scalarCubeGridHistogram I (scalarResidueGridOffset m r) (scalarResidueGridScale L m) x) :
    (scalarCubeResidueWeights I L M hL m r hm hmM hsize).imageMeasure
      (fun z i => (z i : ℝ) / L) =
      (realDensityMeasure volume (scalarCubeGridDensity I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))).map
        (rectangularLatticeSample (scalarResidueGridOffset m r) (scalarResidueGridScale L m)) := by
  have hS := scalarResidueGridScale_pos hL m hm
  have hs := scalarCubeGridDensity_spec I _ _ hS hpos
  have hmeas := scalarCubeGridDensity_measurable I (scalarResidueGridOffset m r)
    (scalarResidueGridScale L m) hS
  let : IsProbabilityMeasure ((scalarCubeResidueWeights I L M hL m r hm hmM hsize).imageMeasure
      (fun z i => (z i : ℝ) / L)) := FiniteProbabilityWeights.imageMeasure_probability _ _
  let : IsFiniteMeasure (realDensityMeasure volume
      (scalarCubeGridDensity I (scalarResidueGridOffset m r) (scalarResidueGridScale L m))) :=
    realDensityMeasure_finite _ _ hs.1 hs.2.1
  apply finiteMeasure_eq_of_integrals
  intro φ hφ
  rw [FiniteProbabilityWeights.imageMeasure_integral,
    integral_map (rectangularLatticeSample_measurable _ _).aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_integral _ _ hmeas hs.2.1]
  rw [scalarCubeResidueWeights_grid_mean]
  exact (scalarCubeGridHistogram_mean I _ _ hS φ).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointCoefficientRetainedTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem product_density_rounding_error {J X : Type*} [Fintype J] [DecidableEq J]
    [PseudoMetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : J → Measure X) [∀ j, SigmaFinite (μ j)] (f g : J → X → ℝ)
    (hf : ∀ j, Integrable (f j) (μ j)) (hg : ∀ j, Integrable (g j) (μ j))
    (hf0 : ∀ j x, 0 ≤ f j x) (hg0 : ∀ j x, 0 ≤ g j x)
    (hfm : ∀ j, (∫ x, f j x ∂μ j) = 1) (hgm : ∀ j, (∫ x, g j x ∂μ j) = 1)
    (R : J → X → X) (hR : ∀ j, Measurable (R j)) (δ ε : J → ℝ)
    (hδ : ∀ j, 0 ≤ δ j) (he : ∀ j, (∫ x, |f j x-g j x| ∂μ j) ≤ ε j)
    (hm : ∀ j x, dist (R j x) x ≤ δ j)
    (φ : (J → X) → ℝ) {K : ℝ≥0} {B : ℝ} (hφ : LipschitzWith K φ)
    (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(∫ x, (∏ j, f j (x j)) * φ (fun j => R j (x j)) ∂Measure.pi μ) -
      ∫ x, (∏ j, g j (x j)) * φ x ∂Measure.pi μ| ≤ B * (∑ j, ε j) + K * (∑ j, δ j) := by
  have herr := (tensor_density_l1_le_sum μ f g hf hg hf0 hg0 hfm hgm).trans
    (Finset.sum_le_sum (fun j _ => he j))
  have hmove (x : J → X) : dist (fun j => R j (x j)) x ≤ ∑ j, δ j := by
    apply (dist_pi_le_iff (Finset.sum_nonneg (fun j _ => hδ j))).mpr
    intro j
    exact (hm j (x j)).trans (Finset.single_le_sum (fun k _ => hδ k) (Finset.mem_univ j))
  have hmass : (∫ x, (∏ j, g j (x j)) ∂Measure.pi μ) = 1 := by
    rw [integral_fintype_prod_eq_prod]
    simp only [hgm, Finset.prod_const_one]
  exact density_rounding_test_error (Measure.pi μ) _ _ (Integrable.fintype_prod_dep hf)
    (Integrable.fintype_prod_dep hg) (fun x => Finset.prod_nonneg (fun j _ => hg0 j (x j)))
    hmass (fun x j => R j (x j)) (measurable_pi_iff.mpr (fun j => (hR j).comp (measurable_pi_apply j)))
    hB herr hmove φ hφ hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeProductDensity_measure (J I : Type*) [Fintype J] [Fintype I] [DecidableEq I] :
    scalarCubeProductMeasure J I =
      realDensityMeasure volume (tensorCutoffWeight (fun _ : J => scalarCubeProbabilityDensity I)) := by
  rw [scalarCubeProductMeasure, ← scalarCubeProbabilityDensity_measure I]
  exact realDensityMeasure_pi (fun _ => volume) _
    (fun _ => (scalarCubeProbabilityDensity_spec I).1)
    (fun _ => (scalarCubeProbabilityDensity_spec I).2.1)

theorem scalarCubeResidue_pi_imageMeasure {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (hpos : ∀ j, 0 < ∫ x, scalarCubeGridHistogram I (scalarResidueGridOffset (m j) (r j))
      (scalarResidueGridScale (L j) (m j)) x) :
    (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).imageMeasure (fun z j i => (z j i : ℝ) / L j) =
      (realDensityMeasure volume (tensorCutoffWeight (fun j =>
        scalarCubeGridDensity I (scalarResidueGridOffset (m j) (r j)) (scalarResidueGridScale (L j) (m j))))).map
      (fun x j => rectangularLatticeSample (scalarResidueGridOffset (m j) (r j))
        (scalarResidueGridScale (L j) (m j)) (x j)) := by
  let f := fun j => scalarCubeGridDensity I (scalarResidueGridOffset (m j) (r j))
    (scalarResidueGridScale (L j) (m j))
  have hs (j : J) := scalarCubeGridDensity_spec I _ _ (scalarResidueGridScale_pos (hL j) (m j) (hm j)) (hpos j)
  let : ∀ j, IsFiniteMeasure (realDensityMeasure volume (f j)) :=
    fun j => realDensityMeasure_finite volume (f j) (hs j).1 (hs j).2.1
  rw [← FiniteProbabilityWeights.imageMeasure_pi
    (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j))
    (fun j z i => (z i : ℝ) / L j)]
  simp_rw [scalarCubeResidue_imageMeasure I _ _ _ _ _ _ _ _ (hpos _)]
  rw [← Measure.pi_map_pi (fun j => (rectangularLatticeSample_measurable
    (scalarResidueGridOffset (m j) (r j)) (scalarResidueGridScale (L j) (m j))).aemeasurable)]
  rw [realDensityMeasure_pi (fun _ => volume) f (fun j => (hs j).1) (fun j => (hs j).2.1)]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeResidueWeights_pi_riemann {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ)/L j) <
      volume.real (scalarCubeDomain I))
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i => (z j i : ℝ) / L j)) -
      ∫ x, φ x ∂scalarCubeProductMeasure J I| ≤
      (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        ∑ j, (M j : ℝ)/L j := by
  let a := fun j => scalarResidueGridOffset (m j) (r j)
  let S := fun j => scalarResidueGridScale (L j) (m j)
  let δ := fun j => (M j : ℝ)/L j
  let f := fun j => scalarCubeGridDensity I (a j) (S j)
  let g := fun _ : J => scalarCubeProbabilityDensity I
  have hS (j) : ∀ i, 0 < S j i := scalarResidueGridScale_pos (hL j) (m j) (hm j)
  have hδ (j) : 0 ≤ δ j := by dsimp only [δ]; positivity
  have hδ1 (j) : δ j ≤ 1 := by
    have hML : M j ≤ L j := by nlinarith [hsize j]
    exact (div_le_one (by exact_mod_cast hL j)).mpr (by exact_mod_cast hML)
  have hmesh (j) (i : Option I) : 1 / S j i ≤ δ j := by
    dsimp only [S, δ, scalarResidueGridScale]
    rw [one_div_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmM j i) (by positivity)
  have hpos (j) : 0 < ∫ x, scalarCubeGridHistogram I (a j) (S j) x :=
    scalarCubeGridHistogram_mass_pos I _ _ (hS j) (hδ j) (hδ1 j) (hmesh j) (hsmall j)
  have hf (j) := scalarCubeGridDensity_spec I (a j) (S j) (hS j) (hpos j)
  have hg := scalarCubeProbabilityDensity_spec I
  have hfm : Measurable (tensorCutoffWeight f) := by
    apply Finset.measurable_prod
    intro j _
    exact (scalarCubeGridDensity_measurable I (a j) (S j) (hS j)).comp (measurable_pi_apply j)
  have hgm : Measurable (tensorCutoffWeight g) := by
    apply Finset.measurable_prod
    intro j _
    exact (scalarCubeProbabilityDensity_measurable I).comp (measurable_pi_apply j)
  have hR : Measurable (fun (x : J → Option I → ℝ) j => rectangularLatticeSample (a j) (S j) (x j)) :=
    measurable_pi_iff.mpr (fun j => (rectangularLatticeSample_measurable _ _).comp (measurable_pi_apply j))
  rw [← FiniteProbabilityWeights.imageMeasure_integral _ _ φ,
    scalarCubeResidue_pi_imageMeasure L M hL m r hm hmM hsize hpos,
    integral_map hR.aemeasurable hφ.continuous.measurable.aestronglyMeasurable,
    realDensityMeasure_integral _ _ hfm (tensorCutoffWeight_nonneg f (fun j => (hf j).2.1)),
    scalarCubeProductDensity_measure,
    realDensityMeasure_integral _ _ hgm (tensorCutoffWeight_nonneg g (fun _ => hg.2.1))]
  have he (j) : (∫ x, |f j x-g j x|) ≤
      (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I)) * δ j :=
    (scalarCubeGridHistogram_normalized_l1 I (a j) (S j) (hS j) (hδ j) (hδ1 j)
      (hmesh j) (hpos j)).trans_eq (by ring)
  have hmove (j) (x) : dist (rectangularLatticeSample (a j) (S j) x) x ≤ δ j := by
    rw [dist_eq_norm]
    exact rectangularLatticeSample_error _ _ (hS j) (hδ j) (hmesh j) x
  exact (product_density_rounding_error (fun _ => volume) f g
    (fun j => (hf j).1) (fun _ => hg.1) (fun j => (hf j).2.1) (fun _ => hg.2.1)
    (fun j => (hf j).2.2) (fun _ => hg.2.2) (fun j => rectangularLatticeSample (a j) (S j))
    (fun j => rectangularLatticeSample_measurable (a j) (S j)) δ _ hδ he hmove φ hφ hB hb).trans_eq
      (by rw [← Finset.mul_sum]; dsimp only [δ]; ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.OriginalKernelResidueRetained
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem scalarCubeResidueWeights_pi_complex_riemann_s2_oai {G I : Type*}
    [Fintype G] [DecidableEq G] [Fintype I] [DecidableEq I]
    (L M : G → ℕ) (hL : ∀ g, 0 < L g) (m : G → Option I → ℕ)
    (r : ∀ g i, ZMod (m g i)) (hm : ∀ g i, 0 < m g i)
    (hmM : ∀ g i, m g i ≤ M g)
    (hsize : ∀ g, (Fintype.card I + 1) * M g ≤ L g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant I * ((M g : ℝ) / L g) <
      volume.real (scalarCubeDomain I))
    (φ : (G → Option I → ℝ) → ℂ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    ‖(FiniteProbabilityWeights.pi (fun g => scalarCubeResidueWeights I (L g) (M g) (hL g)
      (m g) (r g) (hm g) (hmM g) (hsize g))).complexMean
        (fun z => φ (fun g i => (z g i : ℝ) / L g)) -
      ∫ x, φ x ∂scalarCubeProductMeasure G I‖ ≤
      2 * (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        ∑ g, (M g : ℝ) / L g := by
  have hreLip : LipschitzWith K (fun x => (φ x).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans
      (by simpa only [dist_eq_norm] using hφ.dist_le_mul x y)
  have himLip : LipschitzWith K (fun x => (φ x).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans
      (by simpa only [dist_eq_norm] using hφ.dist_le_mul x y)
  have hre := scalarCubeResidueWeights_pi_riemann L M hL m r hm hmM hsize hsmall
    (fun x => (φ x).re) hreLip hB
    (fun x => (Complex.abs_re_le_norm _).trans (hb x))
  have him := scalarCubeResidueWeights_pi_riemann L M hL m r hm hmM hsize hsmall
    (fun x => (φ x).im) himLip hB
    (fun x => (Complex.abs_im_le_norm _).trans (hb x))
  have hi : Integrable φ (scalarCubeProductMeasure G I) :=
    Integrable.mono' (integrable_const B) hφ.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  have hire : (∫ x, φ x ∂scalarCubeProductMeasure G I).re =
      ∫ x, (φ x).re ∂scalarCubeProductMeasure G I := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hi).symm
  have hiim : (∫ x, φ x ∂scalarCubeProductMeasure G I).im =
      ∫ x, (φ x).im ∂scalarCubeProductMeasure G I := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hi).symm
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have h := add_le_add hre him
  simpa only [Complex.sub_re, Complex.sub_im, FiniteProbabilityWeights.complexMean_re,
    FiniteProbabilityWeights.complexMean_im, hire, hiim, ← two_mul, mul_assoc] using h

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.scalarCubeResidueWeights_pi_complex_riemann_s2_oai.{u_1, u_2} := @OAI.Erdos3.scalarCubeResidueWeights_pi_complex_riemann_s2_oai.{u_1, u_2}
