-- Prove2me | solution 1 for OAI.Falconer.controlled_endpoint_angular_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:07:12.248756+00:00
-- url     : https://prove2.me/submissions/13e38c5e-1129-499a-a08e-671a83b53358

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_dyadic_original_slice_costs

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_sub (w u v : E) :
    perpendicularPart w (u-v) = perpendicularPart w u - perpendicularPart w v := by
  simp only [perpendicularPart, inner_sub_right, sub_smul]
  abel

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_smul (w v : E) (a : ℝ) :
    perpendicularPart w (a • v) = a • perpendicularPart w v := by
  simp only [perpendicularPart,inner_smul_right,smul_sub,smul_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TubeAnchorNet
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite bounded anchor nets for the original direction-wise tube covers -/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem bounded_anchor_longitudinal (w : Sphere d) {x a : Space d} {D : ℝ}
    (hx : ‖x‖ ≤ D) (ha : ‖a‖ ≤ D) : |inner ℝ (w:Space d) (x-a)| ≤ 2*D := by
  calc
    _ ≤ ‖(w:Space d)‖*‖x-a‖ := abs_real_inner_le_norm _ _
    _ = ‖x-a‖ := by rw [sphere_norm,one_mul]
    _ ≤ ‖x‖+‖a‖ := norm_sub_le _ _
    _ ≤ 2*D := by linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledConditional
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual affine rescaling of a conditional class probability -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_radius_bracket {m : ℕ} {r : ℝ}
    (hmin : 1/(2:ℝ)^m ≤ r) (hmax : r ≤ 1) :
    ∃ j ≤ m, r ≤ 1/(2:ℝ)^j ∧ 1/(2:ℝ)^j ≤ 2*r := by
  induction m with
  | zero =>
    refine ⟨0,le_rfl,?_,?_⟩
    · simpa using hmax
    · norm_num at hmin ⊢
      linarith
  | succ m ih =>
    by_cases hcoarse : 1/(2:ℝ)^m ≤ r
    · obtain ⟨j,hj,hr,hjr⟩ := ih hcoarse
      exact ⟨j,hj.trans (Nat.le_succ m),hr,hjr⟩
    · refine ⟨m,Nat.le_succ m,(lt_of_not_ge hcoarse).le,?_⟩
      have he : 1/(2:ℝ)^m = 2*(1/(2:ℝ)^(m+1)) := by rw [pow_succ]; field_simp
      rw [he]
      linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual orthogonal-band geometry for the angular slicing argument -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem directionSliceBand_projection_lower (V : Submodule ℝ (Space d))
    {w : Sphere d} {δ : ℝ} (hw : w ∈ directionSliceBand V δ) :
    1-δ ≤ ‖V.starProjection (w:Space d)‖ := by
  have he : (w:Space d) = V.starProjection (w:Space d)+Vᗮ.starProjection (w:Space d) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hh := norm_add_le (V.starProjection (w:Space d)) (Vᗮ.starProjection (w:Space d))
  rw [← he,sphere_norm] at hh
  change ‖Vᗮ.starProjection (w:Space d)‖ ≤ δ at hw
  linarith

theorem norm_sub_normalize (v : Space d) (hv : v ≠ 0) :
    ‖v-normalize v‖ = |‖v‖-1| := by
  calc
    _ = ‖(‖v‖-1) • normalize v‖ := by
      congr 1
      rw [sub_smul,norm_smul_normalize,one_smul]
    _ = _ := by rw [norm_smul,norm_normalize hv,Real.norm_eq_abs,mul_one]

theorem directionSliceBand_normalize_error (V : Submodule ℝ (Space d))
    {w : Sphere d} {δ : ℝ} (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) :
    ‖normalize (V.starProjection (w:Space d))-(w:Space d)‖ ≤ 2*δ := by
  have hp : V.starProjection (w:Space d) ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr hδ).trans_le (directionSliceBand_projection_lower V hw))
  have herr : ‖V.starProjection (w:Space d)-(w:Space d)‖ ≤ δ := by
    change ‖Vᗮ.starProjection (w:Space d)‖ ≤ δ at hw
    simpa only [Submodule.starProjection_orthogonal_val,norm_sub_rev] using hw
  have hnorm : |‖V.starProjection (w:Space d)‖-1| ≤ δ := by
    simpa only [sphere_norm] using (abs_norm_sub_norm_le _ (w:Space d)).trans herr
  calc
    _ ≤ ‖normalize (V.starProjection (w:Space d))-V.starProjection (w:Space d)‖+
        ‖V.starProjection (w:Space d)-(w:Space d)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ+δ := add_le_add (by rw [norm_sub_rev,norm_sub_normalize _ hp]; exact hnorm) herr
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Second moments of the actual Gaussian direction bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianDirectionBand_measurable (A : Fin h → Space d) (r : ℝ) :
    MeasurableSet (gaussianDirectionBand A r) := by
  simp only [gaussianDirectionBand,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Point bands in the actual Gaussian row coordinates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianPointBand_measurable (A : Fin h → Space d) (z : Space h) (r : ℝ) :
    MeasurableSet (gaussianPointBand A z r) := by
  simp only [gaussianPointBand,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem gaussianPointBand_pair_difference (A : Fin h → Space d) (z : Space h) {r : ℝ}
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r) :
    ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r := by
  intro i
  calc
    _ = |(inner ℝ x (A i)-z i)-(inner ℝ y (A i)-z i)| := by rw [inner_sub_left]; congr 1; ring
    _ ≤ |inner ℝ x (A i)-z i|+|inner ℝ y (A i)-z i| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (inner ℝ x (A i)-z i) (inner ℝ y (A i)-z i)
    _ ≤ 2*r := by linarith [hx i,hy i]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active original tube-anchor counts in the Gaussian point parameter -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianActiveAnchorCount_eq_sum (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) (z : Space h) :
    (gaussianActiveAnchorCount A S a r z : ℝ≥0∞) =
      ∑ i ∈ S, {v : Space h | a i ∈ gaussianPointBand A v r}.indicator (fun _ => (1:ℝ≥0∞)) z := by
  classical
  simp only [gaussianActiveAnchorCount,Finset.natCast_card_filter,Set.indicator_apply,mem_ofPred_eq]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveFamily
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active counts for measurable original-label tube lists -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussianActiveFamily_measurable (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (r : ℝ) :
    Measurable (fun p : ((Fin h → Space d) × Space h) × Sphere d =>
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞)) := by
  classical
  have he (p : ((Fin h → Space d) × Space h) × Sphere d) :
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞) =
      ∑ i : ι, {q : ((Fin h → Space d) × Space h) × Sphere d |
        i ∈ J q.2 ∧ a i ∈ gaussianPointBand q.1.1 q.1.2 r}.indicator (fun _ => (1:ℝ≥0∞)) p := by
    rw [gaussianActiveAnchorCount_eq_sum]
    simp only [Set.indicator_apply,mem_ofPred_eq]
    calc
      _ = ∑ i ∈ J p.2, (if i ∈ J p.2 ∧ a i ∈ gaussianPointBand p.1.1 p.1.2 r then
          (1:ℝ≥0∞) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hi,true_and]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp only [hi,false_and,ite_false, if_false])
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  apply ((hJ i).preimage measurable_snd).inter
  change MeasurableSet {q : ((Fin h → Space d) × Space h) × Sphere d |
    ∀ j, |inner ℝ (a i) (q.1.1 j)-q.1.2 j| ≤ r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BallTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enforcing ball bounds by deleting points of excessive local mass -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology X] in
theorem restricted_good_ball_bound (μ : Measure X) [SFinite μ] (r : ℝ) (B : ℝ≥0∞) :
    ∀ a : X, (μ.restrict {x | μ (ball x (2*r)) ≤ B}) (ball a r) ≤ B := by
  intro a
  rw [Measure.restrict_apply measurableSet_ball]
  by_cases hne : (ball a r ∩ {x | μ (ball x (2*r)) ≤ B}).Nonempty
  · obtain ⟨x,hxa,hx⟩ := hne
    have hsub : ball a r ∩ {x | μ (ball x (2*r)) ≤ B} ⊆ ball x (2*r) := by
      rintro y ⟨hy,_⟩
      rw [mem_ball] at hxa hy ⊢
      have htri := dist_triangle y a x
      rw [dist_comm a x] at htri
      linarith
    exact (measure_mono hsub).trans hx
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,measure_empty]
    exact bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteBallPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneously enforcing the finitely many slice ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]

omit [SecondCountableTopology X] [Fintype ι] in
theorem finiteBallGood_ball_bound (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) (i : ι) (a : X) :
    (μ.restrict (finiteBallGood μ r B)) (ball a (r i)) ≤ B i := by
  calc
    _ ≤ (μ.restrict {x | μ (ball x (2*r i)) ≤ B i}) (ball a (r i)) :=
      Measure.restrict_mono_set μ (s := finiteBallGood μ r B)
        (t := {x | μ (ball x (2*r i)) ≤ B i}) (fun _ hx => hx i) _
    _ ≤ _ := restricted_good_ball_bound μ (r i) (B i) a

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized direction-slice masses and their second moment -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianDirectionMass_measurable (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ) :
    Measurable (gaussianDirectionMass (h := h) ν r) := by
  apply Measurable.const_mul
  let S : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBallMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint measurability of the ball tests used to prune Gaussian slices -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_ball_mass_measurable (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) :
    Measurable (fun p : (Fin h → Space d) × Sphere d =>
      gaussianDirectionSliceMeasure ν p.1 r (ball p.2 ρ)) := by
  simp only [gaussianDirectionSliceMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_ball]
  apply Measurable.const_mul
  let S : Set (((Fin h → Space d) × Sphere d) × Sphere d) :=
    {p | dist p.2 p.1.2 < ρ ∧ ∀ i, |inner ℝ (p.2:Space d) (p.1.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_and,ofPred_forall]
    apply MeasurableSet.inter (measurableSet_lt (by fun_prop) measurable_const)
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  convert (measurable_measure_prodMk_left (ν := ν) hS) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  congr 1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPruningSets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable restrictions used in Gaussian slice selection -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussianDirectionGood_measurable_joint (ν : Measure (Sphere d)) [SFinite ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) :
    MeasurableSet {p : (Fin h → Space d) × Sphere d | p.2 ∈ gaussianDirectionGood ν δ r T M p.1} := by
  change MeasurableSet {p : (Fin h → Space d) × Sphere d |
    gaussianDirectionMass ν δ p.1 ≤ M ∧
    ∀ i, gaussianDirectionSliceMeasure ν p.1 δ (ball p.2 (2*r i)) ≤ T i}
  simp only [ofPred_and,ofPred_forall]
  apply MeasurableSet.inter
  · exact measurableSet_le ((gaussianDirectionMass_measurable ν δ).comp measurable_fst) measurable_const
  · exact MeasurableSet.iInter (fun i => measurableSet_le
      (gaussian_direction_ball_mass_measurable ν δ (2*r i)) measurable_const)

omit [Fintype ι] in
theorem gaussianPointGood_ball (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (p : (Fin h → Space d) × Space h) (i : ι) (a : Space d) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p))
      (ball a (r i)) ≤ T i := finiteBallGood_ball_bound _ r T i a

omit [Fintype ι] in
theorem gaussianDirectionGood_mass (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r T M A)) univ ≤ M := by
  by_cases hm : gaussianDirectionMass ν δ A ≤ M
  · calc
      _ ≤ gaussianDirectionSliceMeasure ν A δ univ := Measure.restrict_le_self _
      _ = gaussianDirectionMass ν δ A := by
        simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
      _ ≤ _ := hm
  · have he : gaussianDirectionGood ν δ r T M A = ∅ := by ext w; simp [gaussianDirectionGood,hm]
    simp only [he,Measure.restrict_empty,Measure.coe_zero,Pi.zero_apply]
    exact zero_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform masses and support of the pruned original slice laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianPointSliceMeasure_ae_of_ae
    (μ : Measure (Space d)) (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    {P : Space d → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂gaussianPointSliceMeasure μ A z δ, P x := by
  exact Measure.ae_smul_measure (ae_restrict_of_ae hP) _

theorem gaussianPointGood_mass
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞)
    (p : (Fin h → Space d) × Space h) {D : ℝ}
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (i : ι) (hi : D < r i) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)) univ ≤ T i := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)
  have ha : ∀ᵐ x ∂α, x ∈ ball 0 (r i) := by
    filter_upwards [ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ p.1 p.2 δ hμ)] with x hx
    simpa only [mem_ball,dist_zero_right] using hx.trans_lt hi
  have he : α (ball 0 (r i)) = α univ := measure_congr (by
    filter_upwards [ha] with x hx
    exact propext ⟨fun _ => mem_univ x,fun _ => hx⟩)
  rw [← he]
  exact gaussianPointGood_ball μ δ r T p i 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowMap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear maps and kernel planes for the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRowMap_adjoint_basis (A : Fin h → Space d) (i : Fin h) :
    (gaussianRowMap A).adjoint (EuclideanSpace.basisFun (Fin h) ℝ i) = A i := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner,gaussianRowMap_apply]
  exact real_inner_comm _ _

theorem coordinate_norm_le_card_mul (x : Space h) {r : ℝ}
    (hx : ∀ i, |x i| ≤ r) : ‖x‖ ≤ (h:ℝ)*r := by
  calc
    _ = ‖∑ i : Fin h, x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := by
      exact congrArg norm ((EuclideanSpace.basisFun (Fin h) ℝ).sum_repr x).symm
    _ ≤ ∑ i : Fin h, ‖x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := norm_sum_le _ _
    _ = ∑ i : Fin h, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one,mul_one]
    _ ≤ ∑ _ : Fin h, r := Finset.sum_le_sum (fun i _ => hx i)
    _ = _ := by simp

theorem gaussianRowMap_norm_le_of_bands (A : Fin h → Space d) (x : Space d) {r : ℝ}
    (hx : ∀ i, |inner ℝ x (A i)| ≤ r) : ‖gaussianRowMap A x‖ ≤ (h:ℝ)*r :=
  coordinate_norm_le_card_mul _ (by simpa only [gaussianRowMap_apply] using hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianKernelGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from Gaussian row bands to their actual kernel planes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem linearMap_orthogonal_kernel_projection (L : Space d →L[ℝ] Space h) (x : Space d) :
    L (L.kerᗮ.starProjection x) = L x := by
  rw [Submodule.starProjection_orthogonal_val,map_sub]
  have hz : L (L.ker.starProjection x) = 0 := (L.ker.orthogonalProjectionOnto x).property
  rw [hz,sub_zero]

theorem gaussian_direction_band_kernel_distance (A : Fin h → Space d)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {w : Sphere d} (hw : w ∈ gaussianDirectionBand A r) :
    ‖(gaussianRowMap A).kerᗮ.starProjection (w:Space d)‖ ≤ K*((h:ℝ)*r) := by
  exact (hbound w).trans (mul_le_mul_of_nonneg_left (gaussianRowMap_norm_le_of_bands A w hw) hK)

theorem gaussian_point_band_kernel_difference (A : Fin h → Space d) (z : Space h)
    {K r : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r) :
    ‖(gaussianRowMap A).kerᗮ.starProjection (x-y)‖ ≤ K*((h:ℝ)*(2*r)) :=
  (hbound (x-y)).trans (mul_le_mul_of_nonneg_left
    (gaussianRowMap_norm_le_of_bands A (x-y) (gaussianPointBand_pair_difference A z hx hy)) hK)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowStability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative kernel geometry near a fixed orthonormal row frame -/

namespace Falconer
open Set MeasureTheory
variable {d h : ℕ}

theorem gaussianRowMap_adjoint_apply (A : Fin h → Space d) (a : Space h) :
    (gaussianRowMap A).adjoint a = ∑ i, a i • A i := by
  calc
    _ = (gaussianRowMap A).adjoint
        (∑ i, a i • EuclideanSpace.basisFun (Fin h) ℝ i) := by
      congr 1
      exact (EuclideanSpace.basisFun (Fin h) ℝ).sum_repr a |>.symm
    _ = _ := by simp only [map_sum,map_smul,gaussianRowMap_adjoint_basis]

theorem row_adjoint_near_isometry (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (a : Space h) :
    ‖(gaussianRowMap A).adjoint a-e a‖ ≤ (h:ℝ)*ε*‖a‖ := by
  have he : e a = ∑ i, a i • e (EuclideanSpace.basisFun (Fin h) ℝ i) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin h) ℝ).sum_repr a]
    simp only [map_sum,map_smul]
    rfl
  rw [gaussianRowMap_adjoint_apply,he,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin h, ‖a i • A i-a i • e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : Fin h, ‖a‖*ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [← smul_sub,norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le a i) (hA i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem row_adjoint_lower_near_isometry (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) (a : Space h) :
    ‖a‖ ≤ 2*‖(gaussianRowMap A).adjoint a‖ := by
  have h1 := row_adjoint_near_isometry A e hA a
  have h2 := norm_sub_norm_le (e a) ((gaussianRowMap A).adjoint a)
  rw [e.norm_map,norm_sub_rev] at h2
  have h3 := mul_le_mul_of_nonneg_right hε (norm_nonneg a)
  nlinarith

theorem kernel_projection_bound_of_adjoint_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hK : 0 ≤ K) (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖)
    (x : Space d) : ‖L.kerᗮ.starProjection x‖ ≤ K*‖L x‖ := by
  let y := L.kerᗮ.starProjection x
  have hy : y ∈ L.kerᗮ := L.kerᗮ.starProjection_apply_mem x
  have hr : y ∈ L.adjoint.range := by
    rw [← ContinuousLinearMap.adjoint_toLinearMap,← LinearMap.orthogonal_ker]
    exact hy
  obtain ⟨a,ha⟩ := hr
  change L.adjoint a = y at ha
  have hnorm : ‖y‖^2 ≤ ‖a‖*‖L x‖ := by
    calc
      _ = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
      _ = inner ℝ (L.adjoint a) y := by rw [ha]
      _ = inner ℝ a (L y) := ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = inner ℝ a (L x) := congrArg (inner ℝ a)
        (linearMap_orthogonal_kernel_projection L x)
      _ ≤ _ := real_inner_le_norm _ _
  have hla := hL a
  rw [ha] at hla
  have hh := mul_le_mul_of_nonneg_right hla (norm_nonneg (L x))
  by_cases hz : ‖y‖ = 0
  · change ‖y‖ ≤ _
    rw [hz]
    exact mul_nonneg hK (norm_nonneg _)
  · have hp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖y‖ ≤ _
    nlinarith

theorem row_kernel_projection_bound (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) (x : Space d) :
    ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖ :=
  kernel_projection_bound_of_adjoint_lower _ (by norm_num)
    (row_adjoint_lower_near_isometry A e hA hε) x

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowDimension
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dimension of kernel slices in the controlled row chart -/

namespace Falconer
variable {d h : ℕ}

theorem adjoint_injective_of_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖) :
    Function.Injective L.adjoint := by
  apply LinearMap.ker_eq_bot.mp
  apply (LinearMap.ker_eq_bot').mpr
  intro a ha
  change L.adjoint a = 0 at ha
  have hn := hL a
  rw [ha,norm_zero,mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem kernel_finrank_of_adjoint_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖) :
    Module.finrank ℝ L.ker = d-h := by
  have hr := LinearMap.finrank_range_of_inj (adjoint_injective_of_lower L hL)
  have ha := LinearMap.finrank_range_adjoint L.toLinearMap
  rw [ContinuousLinearMap.adjoint_toLinearMap] at ha
  have hn := L.toLinearMap.finrank_range_add_finrank_ker
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hr hn
  omega

theorem row_kernel_finrank (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) :
    Module.finrank ℝ (gaussianRowMap A).ker = d-h :=
  kernel_finrank_of_adjoint_lower _ (row_adjoint_lower_near_isometry A e hA hε)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianParameterSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded point-parameter region for bounded original source laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRowNeighborhood_norm {n : ℕ} (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} {A : Fin h → Space (n+1)}
    (hA : A ∈ gaussianRowNeighborhood B ε) (i : Fin h) : ‖A i‖ ≤ ε+1 := by
  calc
    _ ≤ ‖A i-B i‖+‖B i‖ := by simpa only [sub_add_cancel] using norm_add_le (A i-B i) (B i)
    _ ≤ _ := add_le_add (hA i) (hB i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair incidence after the active-cover deletion -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] in
theorem gaussianActiveRelation_measurable (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R : ℝ) (T : ℝ≥0∞) (good : Bool) :
    MeasurableSet (gaussianActiveRelation (h := h) E J a R T good) := by
  have hm := (gaussianActiveFamily_measurable (h := h) J hJ a R).comp
    (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
      (q.1,q.2.2)) from by fun_prop)
  cases good
  · exact (hE.preimage measurable_snd).inter (measurableSet_lt measurable_const hm)
  · exact (hE.preimage measurable_snd).inter (measurableSet_le hm measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianKernelCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Metric control in the kernel coordinates of a Gaussian slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d h : ℕ}

theorem gaussian_point_kernel_pair_distance (A : Fin h → Space d) (z : Space h)
    {K r s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r)
    (hxy : ‖(gaussianRowMap A).ker.starProjection x-
      (gaussianRowMap A).ker.starProjection y‖ ≤ s) :
    ‖x-y‖ ≤ s+K*((h:ℝ)*(2*r)) := by
  have he : x-y = (gaussianRowMap A).ker.starProjection (x-y)+
      (gaussianRowMap A).kerᗮ.starProjection (x-y) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  calc
    _ ≤ ‖(gaussianRowMap A).ker.starProjection (x-y)‖+
        ‖(gaussianRowMap A).kerᗮ.starProjection (x-y)‖ := by
      conv_lhs => rw [he]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add (by simpa only [map_sub] using hxy)
      (gaussian_point_band_kernel_difference A z hK hbound hx hy)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceTubeGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original tube anchors and projected tube widths in an orthogonal slice -/

namespace Falconer
open NormedSpace
variable {d : ℕ}

theorem slice_projected_tube_width (V : Submodule ℝ (Space d)) {w : Sphere d}
    {δ : ℝ} (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) (x a : Space d) :
    ‖perpendicularPart (normalize (V.starProjection (w:Space d)))
      (V.starProjection x-V.starProjection a)‖ ≤ ‖perpendicularPart (w:Space d) (x-a)‖ := by
  let v := V.starProjection (w:Space d)
  let u := normalize v
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have hv : v ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr hδ).trans_le (directionSliceBand_projection_lower V hw))
  have hu : ‖u‖ = 1 := norm_normalize hv
  have hperp : perpendicularPart u v = 0 := by
    have hv' : v = ‖v‖ • u := (norm_smul_normalize v).symm
    rw [hv',perpendicularPart_smul]
    simp [perpendicularPart,hu]
  have hsplit : V.starProjection x-V.starProjection a = t • v+V.starProjection e := by
    dsimp [v,t,e,perpendicularPart]
    simp only [map_sub,map_smul]
    module
  change ‖perpendicularPart u (V.starProjection x-V.starProjection a)‖ ≤ ‖e‖
  rw [hsplit]
  have he : perpendicularPart u (t • v+V.starProjection e) = perpendicularPart u (V.starProjection e) := by
    calc
      _ = t • perpendicularPart u v+perpendicularPart u (V.starProjection e) := by
        simp only [perpendicularPart,inner_add_right,inner_smul_right,add_smul]
        module
      _ = _ := by rw [hperp,smul_zero,zero_add]
  rw [he]
  exact (norm_perpendicularPart_le hu _).trans (V.norm_starProjection_apply_le e)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianTubeGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original tube labels and active anchors for Gaussian row slices -/

namespace Falconer
variable {d h : ℕ}

theorem gaussian_active_anchor (A : Fin h → Space d) (z : Space h)
    {w : Sphere d} {x a : Space d} {δ ε L M : ℝ} (_hM : 0 ≤ M)
    (hA : ∀ i, ‖A i‖ ≤ M) (hw : w ∈ gaussianDirectionBand A δ)
    (hx : x ∈ gaussianPointBand A z δ)
    (htube : ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε)
    (hlength : |inner ℝ (w:Space d) (x-a)| ≤ L) :
    a ∈ gaussianPointBand A z (δ+L*δ+ε*M) := by
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have he : a = x-t • (w:Space d)-e := by dsimp [t,e,perpendicularPart]; module
  intro i
  have hi : inner ℝ a (A i)-z i =
      (inner ℝ x (A i)-z i)-t*inner ℝ (w:Space d) (A i)-inner ℝ e (A i) := by
    rw [he,inner_sub_left,inner_sub_left,real_inner_smul_left]
    ring
  have ht : |t*inner ℝ (w:Space d) (A i)| ≤ L*δ := by
    rw [abs_mul]
    exact mul_le_mul hlength (hw i) (abs_nonneg _) ((abs_nonneg _).trans hlength)
  have hp : |inner ℝ e (A i)| ≤ ε*M :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul htube (hA i) (norm_nonneg _)
      ((norm_nonneg _).trans htube))
  rw [hi]
  exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (add_le_add (add_le_add (hx i) ht) hp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The projected fiber cover keeps the original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianActiveAnchors_card (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (R : ℝ) :
    (gaussianActiveAnchors A z J a R).card = gaussianActiveAnchorCount A J a R z := rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_TransverseFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniformly transverse row frame for each fixed spherical chart -/

namespace Falconer
variable {n h : ℕ}

theorem transverse_frame_chart_bound (e : Space h →ₗᵢ[ℝ] Space (n+1))
    (w₀ : Space (n+1))
    (he : ∀ i, inner ℝ w₀ (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    {w : Space (n+1)} {ρ : ℝ} (hw : dist w w₀ ≤ ρ) (i : Fin h) :
    |inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i))| ≤ ρ := by
  let b := e (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hi : inner ℝ w b = inner ℝ (w-w₀) b := by rw [inner_sub_left,he i,sub_zero]
  rw [hi]
  calc
    _ ≤ ‖w-w₀‖*‖b‖ := abs_real_inner_le_norm _ _
    _ = dist w w₀ := by
      rw [show ‖b‖ = 1 from (e.norm_map _).trans
        ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i),mul_one,dist_eq_norm]
    _ ≤ _ := hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_OrientedSlice
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isometric slice coordinates aligned with the center of a direction chart -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem slice_isometry_normalize (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (x : V) : e (normalize x) = normalize (e x) := by
  simp only [NormedSpace.normalize,map_smul,e.norm_map]

theorem slice_isometry_perpendicular (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (w x : V) :
    e (perpendicularPart w x) = perpendicularPart (e w) (e x) := by
  simp only [perpendicularPart,map_sub,map_smul,e.inner_map_map]

theorem oriented_slice_tube_width (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) {w : Sphere d} {δ : ℝ}
    (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) (x a : Space d) :
    ‖perpendicularPart (normalize (e (V.orthogonalProjectionOnto (w:Space d))))
      (e (V.orthogonalProjectionOnto x)-e (V.orthogonalProjectionOnto a))‖ ≤
      ‖perpendicularPart (w:Space d) (x-a)‖ := by
  rw [← slice_isometry_normalize V e,← map_sub,← slice_isometry_perpendicular V e,e.norm_map]
  exact slice_projected_tube_width V hδ hw x a

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CappedActiveCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded anchor lists for every original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {κ : Type*}

theorem cappedActiveAnchors_card (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ((cappedActiveAnchors A z J a R t).card : ℝ) ≤ t := by
  unfold cappedActiveAnchors
  split_ifs with hc
  · exact hc
  · simpa only [Finset.card_empty,Nat.cast_zero] using ht

theorem cappedActiveAnchors_eq (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hc : (gaussianActiveAnchorCount A J a R z : ℝ≥0∞) ≤ ENNReal.ofReal t) :
    cappedActiveAnchors A z J a R t = gaussianActiveAnchors A z J a R := by
  apply ite_eq_left
  apply (ENNReal.ofReal_le_ofReal_iff ht).mp
  simpa only [ENNReal.ofReal_natCast,gaussianActiveAnchors_card] using hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CappedOriginalCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The capped slice cover still consists of original tube anchors -/

namespace Falconer
open Set
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussian_capped_original_cover
    (A : Fin h → Space d) (z : Space h)
    (E : Set (Space d × Sphere d)) (J : Sphere d → Finset ι) (a : ι → Space d)
    {δ ε D M t : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hA : ∀ i, ‖A i‖ ≤ M)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ D)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖a i‖ ≤ D)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ ε)
    {x : Space d} {w : Sphere d}
    (hx : x ∈ gaussianPointBand A z δ) (hw : w ∈ gaussianDirectionBand A δ)
    (hE : ((A,z),(x,w)) ∈ gaussianActiveRelation E J a (δ+(2*D)*δ+ε*M) (ENNReal.ofReal t) true) :
    ∃ c ∈ (cappedActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) t).image a,
      ‖perpendicularPart (w:Space d) (x-c)‖ ≤ ε := by
  classical
  obtain ⟨i,hi,hperp⟩ := hcover (x,w) hE.1
  have hlength := bounded_anchor_longitudinal (w := w) (hbounded (x,w) hE.1) (hanchor w i hi)
  have hactive : i ∈ gaussianActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) :=
    Finset.mem_filter.mpr ⟨hi,gaussian_active_anchor A z hM hA hw hx hperp hlength⟩
  have hi' : i ∈ cappedActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) t := by
    rw [cappedActiveAnchors_eq A z (J w) a _ ht hE.2]
    exact hactive
  exact ⟨a i,Finset.mem_image.mpr ⟨i,hi',rfl⟩,hperp⟩

theorem capped_original_cover_card
    (A : Fin h → Space d) (z : Space h) (J : Finset ι) (a : ι → Space d)
    (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (((cappedActiveAnchors A z J a R t).image a).card:ℝ) ≤ t := by
  classical
  exact (Nat.cast_le.mpr Finset.card_image_le).trans (cappedActiveAnchors_card A z J a R ht)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem northLift_continuous (n : ℕ) : Continuous (@northLift n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · simpa only [Fin.cons_succ] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

theorem gnomonicChart_continuous (n : ℕ) : Continuous (@gnomonicChart n) := by
  apply Continuous.subtype_mk
  exact ((northLift_continuous n).norm.inv₀ (fun x =>
    norm_ne_zero_iff.mpr (northLift_ne_zero x))).smul (northLift_continuous n)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GnomonicSliceLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian direction slices retain the original affine chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gaussianChartSlice_map (μ : Measure (Space n))
    (A : Fin h → Space (n+1)) (r : ℝ) :
    Measure.map gnomonicChart (gaussianChartSliceMeasure μ A r) =
      gaussianDirectionSliceMeasure (Measure.map gnomonicChart μ) A r := by
  unfold gaussianChartSliceMeasure gaussianDirectionSliceMeasure
  rw [Measure.map_smul,
    Measure.restrict_map (gnomonicChart_continuous n).measurable (gaussianDirectionBand_measurable A r)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicPrunedLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact transport of restricted original chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

lemma gaussianDirectionGood_measurable_fixed {d : ℕ} {ι : Type*} [Fintype ι]
    (ν : Measure (Sphere d)) [SFinite ν] (δ : ℝ) (r : ι → ℝ)
    (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) :
    MeasurableSet (gaussianDirectionGood ν δ r T M A) := by
  let f : Sphere d → (Fin h → Space d) × Sphere d := fun w => (A,w)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  have hj : MeasurableSet {p : (Fin h → Space d) × Sphere d |
      p.2 ∈ gaussianDirectionGood ν δ r T M p.1} :=
    gaussianDirectionGood_measurable_joint (h := h) ν δ r T M
  change MeasurableSet (f ⁻¹' {p : (Fin h → Space d) × Sphere d |
    p.2 ∈ gaussianDirectionGood ν δ r T M p.1})
  exact hj.preimage hf

theorem gnomonic_restricted_slice_map (ν₀ : Measure (Space n))
    (A : Fin h → Space (n+1)) (δ : ℝ) (D : Set (Sphere (n+1)))
    (hD : MeasurableSet D) :
    Measure.map gnomonicChart
      ((gaussianChartSliceMeasure ν₀ A δ).restrict (gnomonicChart ⁻¹' D)) =
      (gaussianDirectionSliceMeasure (Measure.map gnomonicChart ν₀) A δ).restrict D := by
  rw [← Measure.restrict_map (gnomonicChart_continuous n).measurable hD,
    gaussianChartSlice_map]

theorem gnomonic_restricted_slice_mass (ν₀ : Measure (Space n))
    (A : Fin h → Space (n+1)) (δ : ℝ) (D : Set (Sphere (n+1)))
    (hD : MeasurableSet D) :
    ((gaussianChartSliceMeasure ν₀ A δ).restrict (gnomonicChart ⁻¹' D)) univ =
      ((gaussianDirectionSliceMeasure (Measure.map gnomonicChart ν₀) A δ).restrict D) univ := by
  rw [← gnomonic_restricted_slice_map ν₀ A δ D hD,
    Measure.map_apply (gnomonicChart_continuous n).measurable MeasurableSet.univ,
    preimage_univ]

theorem gnomonic_incidence_transport {X : Type*} [MeasurableSpace X]
    (α : Measure X) (β : Measure (Space n)) [SFinite α] [SFinite β]
    (E : Set (X × Sphere (n+1))) (hE : MeasurableSet E) :
    (α.prod β) {p | (p.1,gnomonicChart p.2) ∈ E} =
      (α.prod (Measure.map gnomonicChart β)) E := by
  have hm : Measurable (Prod.map (id : X → X) (gnomonicChart : Space n → Sphere (n+1))) :=
    measurable_id.prodMap (gnomonicChart_continuous n).measurable
  have hmap : Measure.map (Prod.map (id : X → X) gnomonicChart) (α.prod β) =
      α.prod (Measure.map gnomonicChart β) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map α β measurable_id (gnomonicChart_continuous n).measurable).symm
  rw [← hmap,Measure.map_apply hm hE]
  rfl

theorem gnomonic_pruned_mass (ν₀ : Measure (Space n)) [IsFiniteMeasure ν₀]
    {ι : Type*} [Fintype ι] (A : Fin h → Space (n+1)) (δ : ℝ)
    (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) :
    ((gaussianChartSliceMeasure ν₀ A δ).restrict
      (gnomonicChart ⁻¹' gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r T M A))
      univ ≤ M := by
  have hD : MeasurableSet (gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r T M A) :=
    gaussianDirectionGood_measurable_fixed (Measure.map (gnomonicChart : Space n → Sphere (n+1)) ν₀) δ r T M A
  rw [gnomonic_restricted_slice_mass ν₀ A δ _ hD]
  exact gaussianDirectionGood_mass (Measure.map gnomonicChart ν₀) δ r T M A

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianChartTripleAverage
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Gaussian averaging on triples of the original affine chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gaussian_chart_triple_identity (μ : Measure (Space n)) [SFinite μ]
    (A : Fin h → Space (n+1)) (r : ℝ) (E : Set (Space n × Space n × Space n))
    (hE : MeasurableSet E) :
    ((gaussianChartSliceMeasure μ A r).prod
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r))) E =
      (ENNReal.ofReal (r^(-(h:ℝ))))^3*(μ.prod (μ.prod μ)) (E ∩ chartTripleBand A r) := by
  simp only [gaussianChartSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hE,
    chartTripleBand,pow_succ,pow_zero,one_mul,mul_assoc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_BadTripleRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable bad-triple relation on retained original labels -/

namespace Falconer
open Set MeasureTheory
variable {n : ℕ}

lemma chartTripleVolume_measurable : Measurable (chartTripleVolume (n := n)) := by
  have h₁ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.1 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp measurable_fst)
  have h₂ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.2.1 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
  have h₃ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.2.2 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
  unfold chartTripleVolume tripleGram
  simp only [Matrix.det_fin_three,Matrix.gram_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  fun_prop

lemma badChartTriples_measurable {G : Set (Space n × Space n)} (hG : MeasurableSet G)
    (W : ℝ) : MeasurableSet (badChartTriples G W) := by
  have h₁ := hG.preimage (show Measurable (fun w : Space n × Space n × Space n =>
    (w.1,w.2.1)) from by fun_prop)
  have h₂ := hG.preimage (show Measurable (fun w : Space n × Space n × Space n =>
    (w.1,w.2.2)) from by fun_prop)
  have hn₁ : MeasurableSet {w : Space n × Space n × Space n | ‖w.1‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hn₂ : MeasurableSet {w : Space n × Space n × Space n | ‖w.2.1‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hn₃ : MeasurableSet {w : Space n × Space n × Space n | ‖w.2.2‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  exact hn₁.inter (hn₂.inter (hn₃.inter
    (h₁.inter (h₂.inter (measurableSet_lt chartTripleVolume_measurable measurable_const)))))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredPairFailure
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original pair deletions in three-label slice incidence -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

lemma firstAnchoredPair_measurable {E : Set (Space n × Space n)} (hE : MeasurableSet E) :
    MeasurableSet (firstAnchoredPair E) := hE.preimage (by fun_prop)

lemma secondAnchoredPair_measurable {E : Set (Space n × Space n)} (hE : MeasurableSet E) :
    MeasurableSet (secondAnchoredPair E) := hE.preimage (by fun_prop)

lemma firstAnchoredPair_mass (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {E : Set (Space n × Space n)} (hE : MeasurableSet E) :
    (μ.prod (μ.prod μ)) (firstAnchoredPair E) = μ univ*(μ.prod μ) E := by
  rw [Measure.prod_apply (firstAnchoredPair_measurable hE)]
  have hs (x : Space n) : Prod.mk x ⁻¹' firstAnchoredPair E = (Prod.mk x ⁻¹' E) ×ˢ univ := by ext w; simp [firstAnchoredPair]
  simp_rw [hs,Measure.prod_prod,mul_comm _ (μ univ)]
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _),← Measure.prod_apply hE]

lemma secondAnchoredPair_mass (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {E : Set (Space n × Space n)} (hE : MeasurableSet E) :
    (μ.prod (μ.prod μ)) (secondAnchoredPair E) = μ univ*(μ.prod μ) E := by
  rw [Measure.prod_apply (secondAnchoredPair_measurable hE)]
  have hs (x : Space n) : Prod.mk x ⁻¹' secondAnchoredPair E = univ ×ˢ (Prod.mk x ⁻¹' E) := by ext w; simp [secondAnchoredPair]
  simp_rw [hs,Measure.prod_prod]
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _),← Measure.prod_apply hE]

lemma endpointExceptionalTriples_measurable {G : Set (Space n × Space n)}
    (hG : MeasurableSet G) (W : ℝ) : MeasurableSet (endpointExceptionalTriples G W) :=
  (badChartTriples_measurable hG W).union
    ((firstAnchoredPair_measurable hG.compl).union (secondAnchoredPair_measurable hG.compl))

lemma endpointExceptionalTriples_mass (μ : Measure (Space n)) [IsFiniteMeasure μ]
    {G : Set (Space n × Space n)} (hG : MeasurableSet G) (W : ℝ) :
    (μ.prod (μ.prod μ)) (endpointExceptionalTriples G W) ≤
      (μ.prod (μ.prod μ)) (badChartTriples G W)+2*μ univ*(μ.prod μ) Gᶜ := by
  apply (measure_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measure_union_le _ _).trans_eq
  rw [firstAnchoredPair_mass μ hG.compl,secondAnchoredPair_mass μ hG.compl]
  ring

lemma endpointExceptionalTriples_volume {G : Set (Space n × Space n)} {W : ℝ}
    {w : Space n × Space n × Space n} (hw : w ∉ endpointExceptionalTriples G W)
    (h₁ : ‖w.1‖ ≤ 1) (h₂ : ‖w.2.1‖ ≤ 1) (h₃ : ‖w.2.2‖ ≤ 1) :
    W ≤ chartTripleVolume w := by
  have hpq : (w.1,w.2.1) ∈ G := by
    by_contra hn
    exact hw (Or.inr (Or.inl hn))
  have hpz : (w.1,w.2.2) ∈ G := by
    by_contra hn
    exact hw (Or.inr (Or.inr hn))
  by_contra hv
  exact hw (Or.inl ⟨h₁,h₂,h₃,hpq,hpz,lt_of_not_ge hv⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_DyadicSliceSelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a slice directly from the two original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gaussianPruningWeight_eq (h : ℕ) (s : ℝ) {N : ℕ} (g : Fin (N+1)) :
    gaussianPruningWeight h s g = (1/(2:ℝ)^g.val)^(s-(h:ℝ)) := by
  unfold gaussianPruningWeight
  rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartCostMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable original pair and triple costs as functions of the Gaussian rows -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

lemma chart_pair_cost_measurable (μ : Measure (Space n)) [SFinite μ]
    (r : ℝ) (E : Set (Space n × Space n)) (hE : MeasurableSet E) :
    Measurable (fun A : Fin h → Space (n+1) =>
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r)) E) := by
  let B : Set ((Fin h → Space (n+1)) × (Space n × Space n)) :=
    {p | p.2 ∈ E ∧ ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2 : Space (n+1)) (p.1 i)| ≤ r}
  have hb : MeasurableSet B := by
    have hc : MeasurableSet {p : (Fin h → Space (n+1)) × (Space n × Space n) | ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
        |inner ℝ (gnomonicChart p.2.2 : Space (n+1)) (p.1 i)| ≤ r} := by
      simp only [ofPred_forall,ofPred_and]
      apply MeasurableSet.iInter
      intro i
      have h₁ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n) =>
          (gnomonicChart p.2.1 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      have h₂ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n) =>
          (gnomonicChart p.2.2 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      exact (measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_le (by fun_prop) measurable_const)
    exact (hE.preimage measurable_snd).inter hc
  have hm := (measurable_measure_prodMk_left (ν := μ.prod μ) hb).const_mul
    ((ENNReal.ofReal (r^(-(h:ℝ))))^2)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext A
  simp only [gaussianChartSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hE,pow_two,mul_assoc]
  have hs : E ∩ ((gnomonicChart ⁻¹' gaussianDirectionBand A r) ×ˢ
      (gnomonicChart ⁻¹' gaussianDirectionBand A r)) = Prod.mk A ⁻¹' B := by
    ext w
    simp only [B,mem_preimage,mem_ofPred_eq,mem_inter_iff,mem_prod,gaussianDirectionBand,forall_and]
  rw [hs]

theorem chart_triple_cost_measurable (μ : Measure (Space n)) [SFinite μ]
    (r : ℝ) (E : Set (Space n × Space n × Space n)) (hE : MeasurableSet E) :
    Measurable (fun A : Fin h → Space (n+1) =>
      ((gaussianChartSliceMeasure μ A r).prod
        ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r))) E) := by
  let B : Set ((Fin h → Space (n+1)) × (Space n × Space n × Space n)) :=
    {p | p.2 ∈ E ∧ ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2.2 : Space (n+1)) (p.1 i)| ≤ r}
  have hb : MeasurableSet B := by
    have hc : MeasurableSet {p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) | ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
        |inner ℝ (gnomonicChart p.2.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
        |inner ℝ (gnomonicChart p.2.2.2 : Space (n+1)) (p.1 i)| ≤ r} := by
      simp only [ofPred_forall,ofPred_and]
      apply MeasurableSet.iInter
      intro i
      have h₁ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
          (gnomonicChart p.2.1 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      have h₂ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
          (gnomonicChart p.2.2.1 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      have h₃ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
          (gnomonicChart p.2.2.2 : Space (n+1))) :=
        measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
      exact (measurableSet_le (by fun_prop) measurable_const).inter
        ((measurableSet_le (by fun_prop) measurable_const).inter
          (measurableSet_le (by fun_prop) measurable_const))
    exact (hE.preimage measurable_snd).inter hc
  have hm := (measurable_measure_prodMk_left (ν := μ.prod (μ.prod μ)) hb).const_mul
    ((ENNReal.ofReal (r^(-(h:ℝ))))^3)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext A
  rw [gaussian_chart_triple_identity μ A r E hE]
  have hs : E ∩ chartTripleBand A r = Prod.mk A ⁻¹' B := by
    ext w
    simp only [B,chartTripleBand,mem_preimage,mem_ofPred_eq,mem_inter_iff,mem_prod,
      gaussianDirectionBand,forall_and]
  rw [hs]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_EndpointSliceCosts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two concrete radial costs used in endpoint slice selection -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ}

theorem endpointPairCost_measurable (ν : Measure (Space n)) [SFinite ν] (δ : ℝ)
    {G : Set (Space n × Space n)} (hG : MeasurableSet G) :
    Measurable (endpointPairCost (h := h) ν δ G) := chart_pair_cost_measurable ν δ Gᶜ hG.compl

theorem endpointTripleCost_measurable (ν : Measure (Space n)) [SFinite ν] (δ W : ℝ)
    {G : Set (Space n × Space n)} (hG : MeasurableSet G) :
    Measurable (endpointTripleCost (h := h) ν δ W G) :=
  chart_triple_cost_measurable ν δ (badChartTriples G W) (badChartTriples_measurable hG W)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CubicIncidence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cubic incidence lower bound needed by three-dimensional slices -/

namespace Falconer
open MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

private theorem cube_rpow (x : ℝ≥0∞) (a : ℝ) : (x^a)^3 = x^(a*3) := by
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

theorem cubic_incidence_moment (μ : Measure X) (F : X → ℝ≥0∞) (hF : AEMeasurable F μ) :
    (∫⁻ x, F x ∂μ)^3 ≤ (∫⁻ x, (F x)^3 ∂μ)*(μ Set.univ)^2 := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (3:ℝ).HolderConjugate (3/2) by norm_num [Real.holderConjugate_iff]) hF
    (aemeasurable_const : AEMeasurable (fun _ : X => (1:ℝ≥0∞)) μ)
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_one] at hH
  have hp := pow_le_pow_left' hH 3
  apply hp.trans_eq
  rw [mul_pow]
  rw [cube_rpow,cube_rpow]
  norm_num [ENNReal.rpow_natCast]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CommonTripleIncidence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common point incidence of three original direction labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem commonTripleRelation_measurable (E : Set (X × W)) (hE : MeasurableSet E) :
    MeasurableSet (commonTripleRelation E) := by
  exact (hE.preimage (show Measurable (fun p : X × (W × W × W) => (p.1,p.2.1)) from by fun_prop)).inter
    ((hE.preimage (show Measurable (fun p : X × (W × W × W) => (p.1,p.2.2.1)) from by fun_prop)).inter
      (hE.preimage (show Measurable (fun p : X × (W × W × W) => (p.1,p.2.2.2)) from by fun_prop)))

omit [MeasurableSpace X] in
theorem commonTripleRelation_fiber (ν : Measure W) [SFinite ν]
    (E : Set (X × W)) (x : X) :
    (ν.prod (ν.prod ν)) (Prod.mk x ⁻¹' commonTripleRelation E) =
      (ν (Prod.mk x ⁻¹' E))^3 := by
  have he : Prod.mk x ⁻¹' commonTripleRelation E =
      (Prod.mk x ⁻¹' E) ×ˢ ((Prod.mk x ⁻¹' E) ×ˢ (Prod.mk x ⁻¹' E)) := rfl
  rw [he,Measure.prod_prod,Measure.prod_prod]
  ring

theorem common_triple_incidence_moment
    (μ : Measure X) (ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (X × W)) (hE : MeasurableSet E) :
    ((μ.prod ν) E)^3 ≤
      (μ.prod (ν.prod (ν.prod ν))) (commonTripleRelation E)*(μ univ)^2 := by
  have hf : Measurable (fun x : X => ν (Prod.mk x ⁻¹' E)) := measurable_measure_prodMk_left hE
  have hh := cubic_incidence_moment μ (fun x : X => ν (Prod.mk x ⁻¹' E)) hf.aemeasurable
  rw [Measure.prod_apply hE,Measure.prod_apply (commonTripleRelation_measurable E hE)]
  simpa only [commonTripleRelation_fiber] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SelectBoundedCommonTriple
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A good original triple for slice laws of bounded, unnormalized mass -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem exists_good_common_triple_bounded (μ : Measure X) (ν : Measure W)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (X × W)) (hE : MeasurableSet E)
    (B : Set (W × W × W)) (hB : MeasurableSet B)
    {M a : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hμ : μ univ ≤ ENNReal.ofReal M) (hν : ν univ ≤ ENNReal.ofReal M)
    (hI : ENNReal.ofReal a ≤ (μ.prod ν) E)
    (hbad : (ν.prod (ν.prod ν)) B ≤ ENNReal.ofReal (a^3/(4*M^3))) :
    ∃ w ∉ B, ENNReal.ofReal (a^3/(2*M^5)) < μ {x | (x,w) ∈ commonTripleRelation E} := by
  let ξ := ν.prod (ν.prod ν)
  let F := commonTripleRelation E ∩ (univ ×ˢ Bᶜ)
  have hF : MeasurableSet F := (commonTripleRelation_measurable E hE).inter
    (MeasurableSet.univ.prod hB.compl)
  have hξ : ξ univ ≤ ENNReal.ofReal (M^3) := by
    simp only [ξ,← univ_prod_univ,Measure.prod_prod]
    calc
      _ ≤ ENNReal.ofReal M*(ENNReal.ofReal M*ENNReal.ofReal M) := mul_le_mul' hν (mul_le_mul' hν hν)
      _ = _ := by rw [ENNReal.ofReal_pow hM.le]; ring
  by_contra! hn
  have hfiber (w : W × W × W) : μ ((fun x => (x,w)) ⁻¹' F) ≤ ENNReal.ofReal (a^3/(2*M^5)) := by
    by_cases hw : w ∈ B
    · have he : (fun x => (x,w)) ⁻¹' F = ∅ := by
        ext x
        simp only [F,mem_preimage,mem_inter_iff,mem_prod,mem_univ,mem_compl_iff,hw,
          not_true_eq_false,and_false,mem_empty_iff_false]
      simp only [he,measure_empty,zero_le]
    · exact (measure_mono (fun _ hx => hx.1)).trans (hn w hw)
  have hgood : (μ.prod ξ) F ≤ ENNReal.ofReal ((a^3/(2*M^5))*M^3) := by
    rw [Measure.prod_apply_symm hF]
    calc
      _ ≤ ∫⁻ _w, ENNReal.ofReal (a^3/(2*M^5)) ∂ξ := lintegral_mono hfiber
      _ = ENNReal.ofReal (a^3/(2*M^5))*ξ univ := by rw [lintegral_const,mul_comm]
      _ ≤ ENNReal.ofReal (a^3/(2*M^5))*ENNReal.ofReal (M^3) := mul_le_mul' le_rfl hξ
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hsub : commonTripleRelation E ⊆ F ∪ (univ ×ˢ B) := by
    intro p hp
    by_cases hb : p.2 ∈ B
    · exact Or.inr ⟨mem_univ _,hb⟩
    · exact Or.inl ⟨hp,mem_univ _,hb⟩
  have htotal : (μ.prod ξ) (commonTripleRelation E) ≤
      ENNReal.ofReal ((a^3/(2*M^5))*M^3+M*(a^3/(4*M^3))) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
    apply add_le_add hgood
    rw [Measure.prod_prod]
    exact (mul_le_mul' hμ hbad).trans_eq (ENNReal.ofReal_mul hM.le).symm
  have hmain : ENNReal.ofReal (a^3) ≤
      ENNReal.ofReal (((a^3/(2*M^5))*M^3+M*(a^3/(4*M^3)))*M^2) := by
    rw [ENNReal.ofReal_pow ha.le]
    apply (pow_le_pow_left' hI 3).trans
    apply (common_triple_incidence_moment μ ν E hE).trans
    apply (mul_le_mul' htotal (pow_le_pow_left' hμ 2)).trans_eq
    rw [← ENNReal.ofReal_pow hM.le,← ENNReal.ofReal_mul (by positivity)]
  have heq : ((a^3/(2*M^5))*M^3+M*(a^3/(4*M^3)))*M^2 = 3*a^3/4 := by
    field_simp
    ring
  rw [heq] at hmain
  have hlt : ENNReal.ofReal (3*a^3/4) < ENNReal.ofReal (a^3) :=
    ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by nlinarith [pow_pos ha 3])
  exact (not_lt_of_ge hmain) hlt

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SelectTransverseChartTriple
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A transverse triple with common incidence in the original chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

theorem exists_transverse_common_chart_triple
    (μ : Measure X) (ν : Measure (Space n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (X × Space n)) (hE : MeasurableSet E)
    (hbounded : ∀ u ∈ E, ‖u.2‖ ≤ 1)
    (G : Set (Space n × Space n)) (hG : MeasurableSet G) (W : ℝ)
    {M a : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hμ : μ univ ≤ ENNReal.ofReal M) (hν : ν univ ≤ ENNReal.ofReal M)
    (hI : ENNReal.ofReal a ≤ (μ.prod ν) E)
    (hbad : (ν.prod (ν.prod ν)) (badChartTriples G W)+
      2*ν univ*(ν.prod ν) Gᶜ ≤ ENNReal.ofReal (a^3/(4*M^3))) :
    ∃ w : Space n × Space n × Space n, W ≤ chartTripleVolume w ∧
      (w.1,w.2.1) ∈ G ∧ (w.1,w.2.2) ∈ G ∧
      ENNReal.ofReal (a^3/(2*M^5)) < μ {x | (x,w) ∈ commonTripleRelation E} := by
  obtain ⟨w,hw,hcommon⟩ := exists_good_common_triple_bounded μ ν E hE
    (endpointExceptionalTriples G W) (endpointExceptionalTriples_measurable hG W)
    hM ha hμ hν hI ((endpointExceptionalTriples_mass ν hG W).trans hbad)
  have hn : {x | (x,w) ∈ commonTripleRelation E}.Nonempty := by
    by_contra h
    have he : {x | (x,w) ∈ commonTripleRelation E} = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [he,measure_empty] at hcommon
    exact (not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ _)) hcommon
  obtain ⟨x,hx⟩ := hn
  change (x,w.1) ∈ E ∧ (x,w.2.1) ∈ E ∧ (x,w.2.2) ∈ E at hx
  have hw₁ : ‖w.1‖ ≤ 1 := hbounded (x,w.1) hx.1
  have hw₂ : ‖w.2.1‖ ≤ 1 := hbounded (x,w.2.1) hx.2.1
  have hw₃ : ‖w.2.2‖ ≤ 1 := hbounded (x,w.2.2) hx.2.2
  have hvol : W ≤ chartTripleVolume w := endpointExceptionalTriples_volume hw hw₁ hw₂ hw₃
  refine ⟨w,hvol,?_,?_,hcommon⟩
  · by_contra hp
    apply hw
    change w ∈ badChartTriples G W ∨ (w.1,w.2.1) ∈ Gᶜ ∨ (w.1,w.2.2) ∈ Gᶜ
    exact Or.inr (Or.inl hp)
  · by_contra hp
    apply hw
    change w ∈ badChartTriples G W ∨ (w.1,w.2.1) ∈ Gᶜ ∨ (w.1,w.2.2) ∈ Gᶜ
    exact Or.inr (Or.inr hp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EuclideanCross
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three-dimensional dual directions and the Gram determinant -/

namespace Falconer
open scoped Matrix

theorem euclideanCross_norm_sq (u v : Space 3) :
    ‖euclideanCross u v‖^2 = pairGram u v := by
  rw [← real_inner_self_eq_norm_sq,euclidean_inner_dot]
  change (WithLp.ofLp u ⨯₃ WithLp.ofLp v) ⬝ᵥ
    (WithLp.ofLp u ⨯₃ WithLp.ofLp v) = _
  rw [cross_dot_cross,← euclidean_inner_dot,← euclidean_inner_dot,
    ← euclidean_inner_dot,← euclidean_inner_dot,real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  unfold pairGram
  simp only [real_inner_comm]
  ring

theorem euclideanCross_norm_le_one {u v : Space 3} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖euclideanCross u v‖ ≤ 1 := by
  have hh := euclideanCross_norm_sq u v
  have hp : ‖u‖^2*‖v‖^2 ≤ 1 := by
    calc
      _ ≤ (1:ℝ)^2*1^2 := by gcongr
      _ = _ := by norm_num
  unfold pairGram at hh
  nlinarith [sq_nonneg (inner ℝ u v),norm_nonneg (euclideanCross u v)]

theorem gram_eq_rowMatrix_mul_transpose (v : Fin 3 → Space 3) :
    Matrix.gram ℝ v = Matrix.of (fun i j => (v i j : ℝ)) *
      (Matrix.of (fun i j => (v i j : ℝ)))ᵀ := by
  ext i j
  simp only [Matrix.gram_apply,euclidean_inner_dot,Matrix.mul_apply,Matrix.transpose_apply,
    dotProduct,Matrix.of_apply]

theorem euclideanCross_triple_sq (u v w : Space 3) :
    (inner ℝ u (euclideanCross v w))^2 = tripleGram u v w := by
  have hs : inner ℝ u (euclideanCross v w) =
      Matrix.det (Matrix.of (fun i j => ((![u,v,w] i) j : ℝ))) := by
    rw [euclidean_inner_dot]
    change (WithLp.ofLp u) ⬝ᵥ ((WithLp.ofLp v) ⨯₃ (WithLp.ofLp w)) = _
    rw [triple_product_eq_det]
    rfl
  rw [hs,tripleGram,gram_eq_rowMatrix_mul_transpose,Matrix.det_mul,Matrix.det_transpose,pow_two]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TripleColumns
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit cofactor coordinates for three transverse directions -/

namespace Falconer
open scoped BigOperators

theorem tripleColumnEquiv_symm_apply (u v w : Space 3)
    (ht : inner ℝ u (euclideanCross v w) ≠ 0) (x : Space 3) :
    (tripleColumnEquiv u v w ht).symm x = tripleDualCoordinates u v w x := by
  have hh := tripleDualCoordinates_column u v w ht ((tripleColumnEquiv u v w ht).symm x)
  rw [← tripleColumnEquiv_apply u v w ht,ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh.symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TripleFrameBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative inverse bounds for the actual three-direction frame -/

namespace Falconer
open scoped BigOperators

theorem tripleCofactors_norm_le_one {u v w : Space 3}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (i : Fin 3) :
    ‖tripleCofactors u v w i‖ ≤ 1 := by
  fin_cases i
  · exact euclideanCross_norm_le_one hv hw
  · exact euclideanCross_norm_le_one hw hu
  · exact euclideanCross_norm_le_one hu hv

theorem tripleDualCoordinates_norm {u v w : Space 3}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (x : Space 3) :
    ‖tripleDualCoordinates u v w x‖ ≤ (3/|inner ℝ u (euclideanCross v w)|)*‖x‖ := by
  have hh := coordinate_norm_le_card_mul (tripleDualCoordinates u v w x)
    (r := ‖x‖/|inner ℝ u (euclideanCross v w)|) (by
      intro i
      change |inner ℝ (tripleCofactors u v w i) x / inner ℝ u (euclideanCross v w)| ≤ _
      rw [abs_div]
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      exact (abs_real_inner_le_norm _ _).trans (by
        have hi := tripleCofactors_norm_le_one hu hv hw i
        nlinarith [norm_nonneg x]))
  norm_num only [Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

theorem tripleColumnLinear_norm {u v w : Space 3}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (x : Space 3) :
    ‖tripleColumnLinear u v w x‖ ≤ 3*‖x‖ := by
  have hn (i : Fin 3) : ‖![u,v,w] i‖ ≤ 1 := by
    fin_cases i
    · exact hu
    · exact hv
    · exact hw
  calc
    _ ≤ ∑ i : Fin 3, ‖x i • (![u,v,w] i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      have hx : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
      exact (mul_le_mul hx (hn i) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

theorem exists_transverse_triple_frame {u v w : Space 3}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgram : Δ ≤ Real.sqrt (tripleGram u v w)) :
    ∃ e : Space 3 ≃L[ℝ] Space 3,
      (∀ x, e x = tripleColumnLinear u v w x) ∧
      (∀ i j : Fin 3, j ≠ i → (e.symm (![u,v,w] i)) j = 0) ∧
      ‖e.toContinuousLinearMap‖ ≤ 3 ∧ ‖e.symm.toContinuousLinearMap‖ ≤ 3/Δ := by
  have heq : Real.sqrt (tripleGram u v w) = |inner ℝ u (euclideanCross v w)| := by
    rw [← euclideanCross_triple_sq,Real.sqrt_sq_eq_abs]
  have ht : inner ℝ u (euclideanCross v w) ≠ 0 := by
    have hh := hΔ.trans_le hgram
    rw [heq] at hh
    exact abs_pos.mp hh
  let e := tripleColumnEquiv u v w ht
  refine ⟨e,fun _ => rfl,?_,?_,?_⟩
  · intro i j hji
    rw [tripleColumnEquiv_symm_apply]
    change inner ℝ (tripleCofactors u v w j) (![u,v,w] i) /
      inner ℝ u (euclideanCross v w) = 0
    rw [tripleCofactors_inner,ite_eq_right hji,zero_div]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    exact tripleColumnLinear_norm hu hv hw
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖e.symm x‖ ≤ _
    rw [tripleColumnEquiv_symm_apply]
    apply (tripleDualCoordinates_norm hu hv hw x).trans
    have hh : 3/|inner ℝ u (euclideanCross v w)| ≤ 3/Δ := by
      rw [← heq]
      gcongr
    exact mul_le_mul_of_nonneg_right hh (norm_nonneg x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerRectangle
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer rectangles arising from projected tube covers -/

namespace Falconer

theorem integer_near_real_bounds (z : ℤ) (x r : ℝ) (L : ℕ)
    (hz : |(z:ℝ)-x| ≤ r) (hL : r+1/2 ≤ (L:ℝ)) :
    round x-(L:ℤ) ≤ z ∧ z ≤ round x+(L:ℤ) := by
  have hh : |(z:ℝ)-(round x:ℝ)| ≤ (L:ℝ) :=
    ((abs_sub_le (z:ℝ) x (round x:ℝ)).trans
      (add_le_add hz (abs_sub_round x))).trans hL
  have hi : |z-round x| ≤ (L:ℤ) := by exact_mod_cast hh
  have h := abs_le.mp hi
  constructor <;> omega

theorem integer_rectangle_card (T : Finset (ℤ × ℤ)) (x y r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hT : ∀ z ∈ T, |(z.1:ℝ)-x| ≤ r ∧ |(z.2:ℝ)-y| ≤ r) :
    T.card ≤ (2*L+1)^2 := by
  have hsub : T ⊆
      (Finset.Icc (round x-(L:ℤ)) (round x+(L:ℤ))).product
        (Finset.Icc (round y-(L:ℤ)) (round y+(L:ℤ))) := by
    intro z hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (integer_near_real_bounds z.1 x r L (hT z hz).1 hL),
        Finset.mem_Icc.mpr (integer_near_real_bounds z.2 y r L (hT z hz).2 hL)⟩
  have hx : (Finset.Icc (round x-(L:ℤ)) (round x+(L:ℤ))).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  have hy : (Finset.Icc (round y-(L:ℤ)) (round y+(L:ℤ))).card = 2*L+1 := by
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans_eq (by
    rw [Finset.product_eq_sprod,Finset.card_product,hx,hy,pow_two])

theorem integer_rectangle_cover_card {ι : Type*} [DecidableEq ι]
    (T : Finset (ℤ × ℤ)) (A : Finset ι) (x y : ι → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hcover : ∀ z ∈ T, ∃ a ∈ A, |(z.1:ℝ)-x a| ≤ r ∧ |(z.2:ℝ)-y a| ≤ r) :
    T.card ≤ A.card*(2*L+1)^2 := by
  classical
  let F : ι → Finset (ℤ × ℤ) := fun a =>
    T.filter (fun z => |(z.1:ℝ)-x a| ≤ r ∧ |(z.2:ℝ)-y a| ≤ r)
  have hsub : T ⊆ A.biUnion F := by
    intro z hz
    obtain ⟨a,ha,hza⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hz,hza⟩⟩
  calc
    _ ≤ (A.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ A, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2*L+1)^2 := Finset.sum_le_sum (fun a _ =>
      integer_rectangle_card (F a) (x a) (y a) r L hL
        (fun z hz => (Finset.mem_filter.mp hz).2))
    _ = _ := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TransverseGridCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling physical tube tests back to transverse coordinates -/

namespace Falconer
variable {d : ℕ}

theorem inverse_coordinate_tube_bound (e : Space d ≃L[ℝ] Space d)
    (v x a : Space d) (j : Fin d) (hj : (e.symm v) j = 0) :
    |(e.symm x) j-(e.symm a) j| ≤
      ‖e.symm.toContinuousLinearMap‖*‖perpendicularPart v (x-a)‖ := by
  have he : (e.symm (perpendicularPart v (x-a))) j = (e.symm x) j-(e.symm a) j := by
    simp only [perpendicularPart,map_sub,map_smul,PiLp.sub_apply,PiLp.smul_apply,
      smul_eq_mul,hj,mul_zero,sub_zero]
  calc
    _ = ‖(e.symm (perpendicularPart v (x-a))) j‖ := by rw [he,Real.norm_eq_abs]
    _ ≤ ‖e.symm (perpendicularPart v (x-a))‖ := PiLp.norm_apply_le _ _
    _ ≤ _ := e.symm.toContinuousLinearMap.le_opNorm _

theorem transverse_grid_coordinate (e : Space 3 ≃L[ℝ] Space 3)
    (v a : Space 3) (z : ℤ × ℤ × ℤ) (j : Fin 3)
    {δ C : ℝ} (hδ : 0 < δ) (hj : (e.symm v) j = 0)
    (htube : ‖perpendicularPart v (e (tripleGridPoint δ z)-a)‖ ≤ C*δ) :
    |tripleGridPoint δ z j/δ-(e.symm a) j/δ| ≤
      ‖e.symm.toContinuousLinearMap‖*C := by
  have hh := inverse_coordinate_tube_bound e v (e (tripleGridPoint δ z)) a j hj
  rw [e.symm_apply_apply] at hh
  have hb := hh.trans (mul_le_mul_of_nonneg_left htube (norm_nonneg _))
  rw [← sub_div,abs_div,abs_of_pos hδ]
  apply (div_le_iff₀ hδ).mpr
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TripleGridRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounding bounded physical point sets in transverse coordinates -/

namespace Falconer
open Set Metric

theorem round_mesh_error {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |t-δ*(round (t/δ):ℝ)| ≤ δ/2 := by
  have he : t-δ*(round (t/δ):ℝ) = δ*(t/δ-(round (t/δ):ℝ)) := by field_simp
  rw [he,abs_mul,abs_of_pos hδ]
  have hh := mul_le_mul_of_nonneg_left (abs_sub_round (t/δ)) hδ.le
  nlinarith

theorem tripleRound_distance {δ : ℝ} (hδ : 0 < δ) (x : Space 3) :
    dist x (tripleGridPoint δ (tripleRound δ x)) ≤ 3*δ/2 := by
  rw [dist_eq_norm]
  have hh := coordinate_norm_le_card_mul (x-tripleGridPoint δ (tripleRound δ x))
    (r := δ/2) (by
      intro i
      fin_cases i <;> exact round_mesh_error hδ _)
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem round_bound {δ R : ℝ} (hδ : 0 < δ) (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ))
    (t : ℝ) (ht : |t| ≤ R) : -(L:ℤ) ≤ round (t/δ) ∧ round (t/δ) ≤ (L:ℤ) := by
  have hh : |(round (t/δ):ℝ)| ≤ (L:ℝ) := by
    have hs := abs_sub_round (t/δ)
    have htri := abs_sub_le (round (t/δ):ℝ) (t/δ) 0
    rw [sub_zero,sub_zero,abs_sub_comm (round (t/δ):ℝ)] at htri
    have hd : |t/δ| ≤ R/δ := by
      rw [abs_div,abs_of_pos hδ]
      exact div_le_div_of_nonneg_right ht hδ.le
    linarith
  have hi : |round (t/δ)| ≤ (L:ℤ) := by exact_mod_cast hh
  exact abs_le.mp hi

theorem tripleRound_mem_box {δ R : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hL : R/δ+1 ≤ (L:ℝ)) (x : Space 3) (hx : ‖x‖ ≤ R) :
    tripleRound δ x ∈ tripleIntegerBox L := by
  have hb (i : Fin 3) : -(L:ℤ) ≤ round (x i/δ) ∧ round (x i/δ) ≤ (L:ℤ) :=
    round_bound hδ L hL (x i) ((PiLp.norm_apply_le x i).trans hx)
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hb 0),
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hb 1),Finset.mem_Icc.mpr (hb 2)⟩⟩

theorem roundedTripleGrid_mem {E : Set (Space 3)} {δ R : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ)) (hE : ∀ x ∈ E, ‖x‖ ≤ R)
    {x : Space 3} (hx : x ∈ E) : tripleRound δ x ∈ roundedTripleGrid E δ L := by
  classical
  exact Finset.mem_filter.mpr ⟨tripleRound_mem_box hδ L hL x (hE x hx),x,hx,rfl⟩

theorem roundedTripleGrid_original {E : Set (Space 3)} {δ : ℝ} {L : ℕ}
    {z : ℤ × ℤ × ℤ} (hz : z ∈ roundedTripleGrid E δ L) :
    ∃ x ∈ E, tripleRound δ x = z := by
  classical
  exact (Finset.mem_filter.mp hz).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteTripleCounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite three-coordinate counting inequality for endpoint slices -/

namespace Falconer
open scoped BigOperators
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

theorem finite_triangle_square_bound (f : X → Y → ℝ) (g : Y → Z → ℝ) (h : Z → X → ℝ) :
    (∑ x, ∑ y, ∑ z, f x y*g y z*h z x)^2 ≤
      (∑ x, ∑ y, (f x y)^2)*(∑ y, ∑ z, (g y z)^2)*(∑ z, ∑ x, (h z x)^2) := by
  let G : Y → ℝ := fun y => ∑ z, (g y z)^2
  let H : X → ℝ := fun x => ∑ z, (h z x)^2
  have hrow (x : X) (y : Y) : (∑ z, g y z*h z x)^2 ≤ G y*H x :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun z => g y z) (fun z => h z x)
  have hrows : (∑ x, ∑ y, (∑ z, g y z*h z x)^2) ≤ (∑ y, G y)*(∑ x, H x) := by
    calc
      _ ≤ ∑ x, ∑ y, G y*H x :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hrow x y))
      _ = _ := by simp only [← Finset.sum_mul,← Finset.mul_sum]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : X × Y => f p.1 p.2) (fun p : X × Y => ∑ z, g p.2 z*h z p.1)
  simp only [Fintype.sum_prod_type] at hCS
  have hnonneg : 0 ≤ ∑ x, ∑ y, (f x y)^2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hh := hCS.trans (mul_le_mul_of_nonneg_left hrows hnonneg)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  · dsimp [G,H]
    rw [Finset.sum_comm (f := fun x : X => fun z : Z => (h z x)^2)]
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LoomisWhitneyThree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three-dimensional finite Loomis--Whitney counting -/

namespace Falconer
open scoped BigOperators
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem finite_loomis_whitney_three (S : Finset (X × Y × Z)) :
    (S.card : ℝ)^2 ≤
      ((S.image (fun p => (p.1,p.2.1))).card : ℝ)*
      ((S.image (fun p => (p.2.1,p.2.2))).card : ℝ)*
      ((S.image (fun p => (p.2.2,p.1))).card : ℝ) := by
  classical
  let A := S.image (fun p => (p.1,p.2.1))
  let B := S.image (fun p => (p.2.1,p.2.2))
  let C := S.image (fun p => (p.2.2,p.1))
  let f : X → Y → ℝ := fun x y => if (x,y) ∈ A then 1 else 0
  let g : Y → Z → ℝ := fun y z => if (y,z) ∈ B then 1 else 0
  let h : Z → X → ℝ := fun z x => if (z,x) ∈ C then 1 else 0
  have hpoint (p : X × Y × Z) :
      (if p ∈ S then (1:ℝ) else 0) ≤ f p.1 p.2.1*g p.2.1 p.2.2*h p.2.2 p.1 := by
    by_cases hp : p ∈ S
    · have ha : (p.1,p.2.1) ∈ A := Finset.mem_image.mpr ⟨p,hp,rfl⟩
      have hb : (p.2.1,p.2.2) ∈ B := Finset.mem_image.mpr ⟨p,hp,rfl⟩
      have hc : (p.2.2,p.1) ∈ C := Finset.mem_image.mpr ⟨p,hp,rfl⟩
      simp only [hp,ite_true, if_true,f,g,h,ha,hb,hc,one_mul,le_refl]
    · simp only [hp,ite_false, if_false]
      dsimp [f,g,h]
      positivity
  have hcount : (S.card:ℝ) ≤ ∑ x, ∑ y, ∑ z, f x y*g y z*h z x := by
    calc
      _ = ∑ p : X × Y × Z, if p ∈ S then (1:ℝ) else 0 := by simp
      _ ≤ ∑ p : X × Y × Z, f p.1 p.2.1*g p.2.1 p.2.2*h p.2.2 p.1 :=
        Finset.sum_le_sum (fun p _ => hpoint p)
      _ = _ := by simp only [Fintype.sum_prod_type]
  have ha : (∑ x, ∑ y, (f x y)^2) = (A.card:ℝ) := by
    rw [← Fintype.sum_prod_type (fun p : X × Y => (f p.1 p.2)^2)]
    simp [f]
  have hb : (∑ y, ∑ z, (g y z)^2) = (B.card:ℝ) := by
    rw [← Fintype.sum_prod_type (fun p : Y × Z => (g p.1 p.2)^2)]
    simp [g]
  have hc : (∑ z, ∑ x, (h z x)^2) = (C.card:ℝ) := by
    rw [← Fintype.sum_prod_type (fun p : Z × X => (h p.1 p.2)^2)]
    simp [h]
  have ht := finite_triangle_square_bound f g h
  rw [ha,hb,hc] at ht
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2).trans ht

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteLoomisWhitney
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three-coordinate count for finite subsets of infinite grids -/

namespace Falconer
variable {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

theorem finite_loomis_whitney_three_arbitrary (S : Finset (X × Y × Z)) :
    (S.card : ℝ)^2 ≤
      ((S.image (fun p => (p.1,p.2.1))).card : ℝ)*
      ((S.image (fun p => (p.2.1,p.2.2))).card : ℝ)*
      ((S.image (fun p => (p.2.2,p.1))).card : ℝ) := by
  classical
  let A := S.image (fun p => p.1)
  let B := S.image (fun p => p.2.1)
  let C := S.image (fun p => p.2.2)
  let lift : {p // p ∈ S} → A × B × C := fun p =>
    (⟨p.val.1,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩,
      ⟨p.val.2.1,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩,
      ⟨p.val.2.2,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩)
  let T := S.attach.image lift
  have hlift : Function.Injective lift := by
    intro p q he
    apply Subtype.ext
    exact congrArg (fun z : A × B × C => (z.1.val,z.2.1.val,z.2.2.val)) he
  have hc : T.card = S.card := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  have hxy : (T.image (fun p => (p.1,p.2.1))).card =
      (S.image (fun p => (p.1,p.2.1))).card := by
    let f : A × B → X × Y := fun p => (p.1.val,p.2.val)
    have hf : Function.Injective f := by
      rintro ⟨a,b⟩ ⟨a',b'⟩ he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
    rw [← Finset.card_image_of_injective _ hf]
    congr 1
    dsimp [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun p => (p.val.1,p.val.2.1)) = _
    calc
      _ = (S.attach.image Subtype.val).image (fun p : X × Y × Z => (p.1,p.2.1)) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val)
          (g := fun p : X × Y × Z => (p.1,p.2.1))).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hyz : (T.image (fun p => (p.2.1,p.2.2))).card =
      (S.image (fun p => (p.2.1,p.2.2))).card := by
    let f : B × C → Y × Z := fun p => (p.1.val,p.2.val)
    have hf : Function.Injective f := by
      rintro ⟨a,b⟩ ⟨a',b'⟩ he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
    rw [← Finset.card_image_of_injective _ hf]
    congr 1
    dsimp [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun p => (p.val.2.1,p.val.2.2)) = _
    calc
      _ = (S.attach.image Subtype.val).image (fun p : X × Y × Z => (p.2.1,p.2.2)) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val)
          (g := fun p : X × Y × Z => (p.2.1,p.2.2))).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hzx : (T.image (fun p => (p.2.2,p.1))).card =
      (S.image (fun p => (p.2.2,p.1))).card := by
    let f : C × A → Z × X := fun p => (p.1.val,p.2.val)
    have hf : Function.Injective f := by
      rintro ⟨a,b⟩ ⟨a',b'⟩ he
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)
    rw [← Finset.card_image_of_injective _ hf]
    congr 1
    dsimp [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun p => (p.val.2.2,p.val.1)) = _
    calc
      _ = (S.attach.image Subtype.val).image (fun p : X × Y × Z => (p.2.2,p.1)) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val)
          (g := fun p : X × Y × Z => (p.2.2,p.1))).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hh := finite_loomis_whitney_three T
  rw [hc,hxy,hyz,hzx] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_TransverseTubeCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting physical tube intersections in transverse grid coordinates -/

namespace Falconer

theorem transverse_grid_tube_count (e : Space 3 ≃L[ℝ] Space 3)
    (v : Fin 3 → Space 3) (A : Fin 3 → Finset (Space 3))
    (S : Finset (ℤ × ℤ × ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (haxis : ∀ i j : Fin 3, j ≠ i → (e.symm (v i)) j = 0)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*C+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin 3, ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (tripleGridPoint δ z)-a)‖ ≤ C*δ) :
    (S.card:ℝ)^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*(2*(L:ℝ)+1)^6 := by
  classical
  have hxy : (S.image (fun z => (z.1,z.2.1))).card ≤ (A 2).card*(2*L+1)^2 := by
    apply integer_rectangle_cover_card _ (A 2)
      (fun a => (e.symm a) 0/δ) (fun a => (e.symm a) 1/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover 2 w hw
    refine ⟨a,ha,?_,?_⟩
    · have hh := transverse_grid_coordinate e (v 2) a w 0 hδ (haxis 2 0 (by decide)) ht
      simpa [hδ.ne'] using hh
    · have hh := transverse_grid_coordinate e (v 2) a w 1 hδ (haxis 2 1 (by decide)) ht
      simpa [hδ.ne'] using hh
  have hyz : (S.image (fun z => (z.2.1,z.2.2))).card ≤ (A 0).card*(2*L+1)^2 := by
    apply integer_rectangle_cover_card _ (A 0)
      (fun a => (e.symm a) 1/δ) (fun a => (e.symm a) 2/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover 0 w hw
    refine ⟨a,ha,?_,?_⟩
    · have hh := transverse_grid_coordinate e (v 0) a w 1 hδ (haxis 0 1 (by decide)) ht
      simpa [hδ.ne'] using hh
    · have hh := transverse_grid_coordinate e (v 0) a w 2 hδ (haxis 0 2 (by decide)) ht
      simpa [hδ.ne'] using hh
  have hzx : (S.image (fun z => (z.2.2,z.1))).card ≤ (A 1).card*(2*L+1)^2 := by
    apply integer_rectangle_cover_card _ (A 1)
      (fun a => (e.symm a) 2/δ) (fun a => (e.symm a) 0/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover 1 w hw
    refine ⟨a,ha,?_,?_⟩
    · have hh := transverse_grid_coordinate e (v 1) a w 2 hδ (haxis 1 2 (by decide)) ht
      simpa [hδ.ne'] using hh
    · have hh := transverse_grid_coordinate e (v 1) a w 0 hδ (haxis 1 0 (by decide)) ht
      simpa [hδ.ne'] using hh
  have hxy' : ((S.image (fun z => (z.1,z.2.1))).card:ℝ) ≤
      ((A 2).card:ℝ)*(2*(L:ℝ)+1)^2 := by exact_mod_cast hxy
  have hyz' : ((S.image (fun z => (z.2.1,z.2.2))).card:ℝ) ≤
      ((A 0).card:ℝ)*(2*(L:ℝ)+1)^2 := by exact_mod_cast hyz
  have hzx' : ((S.image (fun z => (z.2.2,z.1))).card:ℝ) ≤
      ((A 1).card:ℝ)*(2*(L:ℝ)+1)^2 := by exact_mod_cast hzx
  calc
    _ ≤ ((S.image (fun z => (z.1,z.2.1))).card:ℝ)*
        ((S.image (fun z => (z.2.1,z.2.2))).card:ℝ)*
        ((S.image (fun z => (z.2.2,z.1))).card:ℝ) := finite_loomis_whitney_three_arbitrary S
    _ ≤ (((A 2).card:ℝ)*(2*(L:ℝ)+1)^2)*
        (((A 0).card:ℝ)*(2*(L:ℝ)+1)^2)*
        (((A 1).card:ℝ)*(2*(L:ℝ)+1)^2) := by gcongr
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PhysicalTubeCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite ball cover of an actual three-direction tube intersection -/

namespace Falconer
open Set Metric

theorem physical_three_tube_cover (e : Space 3 ≃L[ℝ] Space 3)
    (he : ‖e.toContinuousLinearMap‖ ≤ 3) (v : Fin 3 → Space 3)
    (hv : ∀ i, ‖v i‖ = 1)
    (haxis : ∀ i j : Fin 3, j ≠ i → (e.symm (v i)) j = 0)
    (E : Set (Space 3)) (A : Fin 3 → Finset (Space 3)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*(C+5)+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    ∃ P : Finset (Space 3), (∀ x ∈ E, ∃ p ∈ P, dist x p ≤ 5*δ) ∧
      (P.card:ℝ)^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*(2*(L:ℝ)+1)^6 := by
  classical
  let E' := e.symm '' E
  obtain ⟨N,hN⟩ := exists_nat_ge (‖e.symm.toContinuousLinearMap‖*R/δ+1)
  have hE' : ∀ y ∈ E', ‖y‖ ≤ ‖e.symm.toContinuousLinearMap‖*R := by
    rintro y ⟨x,hx,rfl⟩
    exact (e.symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left (hE x hx) (norm_nonneg _))
  let S := roundedTripleGrid E' δ N
  have hclose (y : Space 3) :
      dist (e y) (e (tripleGridPoint δ (tripleRound δ y))) ≤ 5*δ := by
    calc
      _ = ‖e (y-tripleGridPoint δ (tripleRound δ y))‖ := by rw [dist_eq_norm,map_sub]
      _ ≤ ‖e.toContinuousLinearMap‖*‖y-tripleGridPoint δ (tripleRound δ y)‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ 3*(3*δ/2) := by
        apply mul_le_mul he
          (by simpa only [dist_eq_norm] using tripleRound_distance hδ y)
          (norm_nonneg _) (by norm_num)
      _ ≤ _ := by linarith
  have hgrid : ∀ i : Fin 3, ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (tripleGridPoint δ z)-a)‖ ≤ (C+5)*δ := by
    intro i z hz
    obtain ⟨y,hy,hz'⟩ := roundedTripleGrid_original hz
    obtain ⟨x,hx,rfl⟩ := hy
    obtain ⟨a,ha,hta⟩ := hcover i x hx
    have hd := hclose (e.symm x)
    rw [e.apply_symm_apply,hz',dist_comm] at hd
    have herr : ‖perpendicularPart (v i) (e (tripleGridPoint δ z)-a)-
        perpendicularPart (v i) (x-a)‖ ≤ 5*δ := by
      rw [← perpendicularPart_sub,sub_sub_sub_cancel_right]
      exact (norm_perpendicularPart_le (hv i) _).trans (by simpa only [dist_eq_norm] using hd)
    refine ⟨a,ha,?_⟩
    calc
      _ = ‖(perpendicularPart (v i) (e (tripleGridPoint δ z)-a)-
          perpendicularPart (v i) (x-a))+perpendicularPart (v i) (x-a)‖ := by congr 1; abel
      _ ≤ ‖perpendicularPart (v i) (e (tripleGridPoint δ z)-a)-
          perpendicularPart (v i) (x-a)‖+‖perpendicularPart (v i) (x-a)‖ := norm_add_le _ _
      _ ≤ 5*δ+C*δ := add_le_add herr hta
      _ = _ := by ring
  let P := S.image (fun z => e (tripleGridPoint δ z))
  refine ⟨P,?_,?_⟩
  · intro x hx
    have hy : e.symm x ∈ E' := mem_image_of_mem _ hx
    have hz : tripleRound δ (e.symm x) ∈ S := roundedTripleGrid_mem hδ N hN hE' hy
    refine ⟨e (tripleGridPoint δ (tripleRound δ (e.symm x))),Finset.mem_image.mpr ⟨_,hz,rfl⟩,?_⟩
    simpa only [e.apply_symm_apply] using hclose (e.symm x)
  · have hcard : (P.card:ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2).trans
      (transverse_grid_tube_count e v A S hδ haxis L hL hgrid)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TransversePhysicalCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative three-transverse-tube covering estimate -/

namespace Falconer
open Set Metric

theorem three_transverse_tube_cover (v : Fin 3 → Space 3)
    (hv : ∀ i, ‖v i‖ = 1) {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (tripleGram (v 0) (v 1) (v 2)))
    (E : Set (Space 3)) (A : Fin 3 → Finset (Space 3)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    ∃ P : Finset (Space 3), (∀ x ∈ E, ∃ p ∈ P, dist x p ≤ 5*δ) ∧
      (P.card:ℝ)^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*((6*C+35)/Δ)^6 := by
  obtain ⟨e,_,haxis,he,hei⟩ := exists_transverse_triple_frame
    (le_of_eq (hv 0)) (le_of_eq (hv 1)) (le_of_eq (hv 2)) hΔ hgram
  have heq : ![v 0,v 1,v 2] = v := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at haxis
  let L := Nat.ceil (3*(C+5)/Δ+1/2)
  have hL : ‖e.symm.toContinuousLinearMap‖*(C+5)+1/2 ≤ (L:ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    have hh := mul_le_mul_of_nonneg_right hei (show 0 ≤ C+5 by linarith)
    calc
      _ ≤ (3/Δ)*(C+5)+1/2 := add_le_add_left hh _
      _ = _ := by ring
  have hsize : 2*(L:ℝ)+1 ≤ (6*C+35)/Δ := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 3*(C+5)/Δ+1/2 by positivity)
    change (L:ℝ) < 3*(C+5)/Δ+1/2+1 at hc
    have hm := mul_lt_mul_of_pos_right hc hΔ
    have hd : (3*(C+5)/Δ)*Δ = 3*(C+5) := div_mul_cancel₀ _ hΔ.ne'
    apply (le_div_iff₀ hΔ).mpr
    nlinarith
  obtain ⟨P,hP,hcard⟩ := physical_three_tube_cover e he v hv haxis E A R hE hδ L hL hcover
  refine ⟨P,hP,?_⟩
  exact hcard.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hsize 6) (by positivity))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ThreeTubePullback
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three transverse tube counting on the original point measure -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

theorem three_tube_pullback_mass_sq (μ : Measure X) (f : X → Space 3)
    (v : Fin 3 → Space 3) (hv : ∀ i, ‖v i‖ = 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (tripleGram (v 0) (v 1) (v 2)))
    (E : Set X) (A : Fin 3 → Finset X) (R : ℝ)
    (hE : ∀ x ∈ E, ‖f x‖ ≤ R) {δ C H s : ℝ} (hδ : 0 < δ)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : ∀ p : Space 3, μ (f ⁻¹' ball p (6*δ)) ≤ ENNReal.ofReal (H*(6*δ)^s))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (f x-f a)‖ ≤ C*δ) :
    (μ E).toReal^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*
      ((6*C+35)/Δ)^6*(H*(6*δ)^s)^2 := by
  classical
  let A' (i : Fin 3) := (A i).image f
  have hE' : ∀ y ∈ f '' E, ‖y‖ ≤ R := by
    rintro y ⟨x,hx,rfl⟩
    exact hE x hx
  have hc : ∀ i : Fin 3, ∀ y ∈ f '' E, ∃ a ∈ A' i,
      ‖perpendicularPart (v i) (y-a)‖ ≤ C*δ := by
    rintro i y ⟨x,hx,rfl⟩
    obtain ⟨a,ha,ht⟩ := hcover i x hx
    exact ⟨f a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,ht⟩
  obtain ⟨P,hP,hcard⟩ := three_transverse_tube_cover v hv hΔ hΔ1 hgram (f '' E) A' R hE' hδ hC hc
  have hB : 0 ≤ H*(6*δ)^s := by positivity
  have hmass : μ E ≤ ENNReal.ofReal ((P.card:ℝ)*(H*(6*δ)^s)) := by
    calc
      _ ≤ μ (⋃ p ∈ P, f ⁻¹' ball p (6*δ)) := by
        apply measure_mono
        intro x hx
        obtain ⟨p,hp,hd⟩ := hP (f x) ⟨x,hx,rfl⟩
        exact mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,by change dist (f x) p < 6*δ; linarith⟩⟩
      _ ≤ ∑ p ∈ P, μ (f ⁻¹' ball p (6*δ)) := measure_biUnion_finset_le P _
      _ ≤ ∑ _p ∈ P, ENNReal.ofReal (H*(6*δ)^s) := Finset.sum_le_sum (fun p _ => hball p)
      _ = (P.card:ℝ≥0∞)*ENNReal.ofReal (H*(6*δ)^s) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ = _ := by rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hB)] at hreal
  calc
    _ ≤ ((P.card:ℝ)*(H*(6*δ)^s))^2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 2
    _ = (P.card:ℝ)^2*(H*(6*δ)^s)^2 := by ring
    _ ≤ ((A' 0).card:ℝ)*((A' 1).card:ℝ)*((A' 2).card:ℝ)*
        ((6*C+35)/Δ)^6*(H*(6*δ)^s)^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ ≤ _ := by gcongr <;> exact Finset.card_image_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TripleGramStability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stability of the three-direction Gram determinant under projection -/

namespace Falconer
open scoped BigOperators

private theorem product_three_difference {a b c d e f ε : ℝ}
    (_ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc : |c| ≤ 1)
    (hd : |d| ≤ 1) (he : |e| ≤ 1) (_hf : |f| ≤ 1)
    (had : |a-d| ≤ ε) (hbe : |b-e| ≤ ε) (hcf : |c-f| ≤ ε) :
    |a*b*c-d*e*f| ≤ 3*ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans had
  have h₁ : |(a-d)*b*c| ≤ ε := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ ε*1*1 := by gcongr
      _ = _ := by ring
  have h₂ : |d*(b-e)*c| ≤ ε := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ 1*ε*1 := by gcongr
      _ = _ := by ring
  have h₃ : |d*e*(c-f)| ≤ ε := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ 1*1*ε := by gcongr
      _ = _ := by ring
  have hi : a*b*c-d*e*f = ((a-d)*b*c+d*(b-e)*c)+d*e*(c-f) := by ring
  rw [hi]
  have hh := (abs_add_le ((a-d)*b*c+d*(b-e)*c) (d*e*(c-f))).trans
    (add_le_add (abs_add_le ((a-d)*b*c) (d*(b-e)*c)) le_rfl)
  linarith

private theorem determinant_eq_sum (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.det = ∑ i, determinantTerms A i := by
  rw [Matrix.det_fin_three]
  simp only [determinantTerms,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  ring

theorem determinant_three_stability (A B : Matrix (Fin 3) (Fin 3) ℝ) {ε : ℝ}
    (hA : ∀ i j, |A i j| ≤ 1) (hB : ∀ i j, |B i j| ≤ 1)
    (hAB : ∀ i j, |A i j-B i j| ≤ ε) : |A.det-B.det| ≤ 18*ε := by
  have hp (i j k l m n : Fin 3) :
      |A i j*A k l*A m n-B i j*B k l*B m n| ≤ 3*ε :=
    product_three_difference (hA i j) (hA k l) (hA m n)
      (hB i j) (hB k l) (hB m n) (hAB i j) (hAB k l) (hAB m n)
  have ht (i : Fin 6) : |determinantTerms A i-determinantTerms B i| ≤ 3*ε := by
    fin_cases i
    · exact hp 0 0 1 1 2 2
    · change |-(A 0 0*A 1 2*A 2 1)-(-(B 0 0*B 1 2*B 2 1))| ≤ _
      rw [neg_sub_neg,abs_sub_comm]
      exact hp 0 0 1 2 2 1
    · change |-(A 0 1*A 1 0*A 2 2)-(-(B 0 1*B 1 0*B 2 2))| ≤ _
      rw [neg_sub_neg,abs_sub_comm]
      exact hp 0 1 1 0 2 2
    · exact hp 0 1 1 2 2 0
    · exact hp 0 2 1 0 2 1
    · change |-(A 0 2*A 1 1*A 2 0)-(-(B 0 2*B 1 1*B 2 0))| ≤ _
      rw [neg_sub_neg,abs_sub_comm]
      exact hp 0 2 1 1 2 0
  rw [determinant_eq_sum,determinant_eq_sum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 6, |determinantTerms A i-determinantTerms B i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 6, 3*ε := Finset.sum_le_sum (fun i _ => ht i)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem gram_three_stability {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : Fin 3 → E) {ε : ℝ}
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hclose : ∀ i, ‖u i-v i‖ ≤ ε) :
    |(Matrix.gram ℝ u).det-(Matrix.gram ℝ v).det| ≤ 36*ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans (hclose 0)
  have hb (a : Fin 3 → E) (ha : ∀ i, ‖a i‖ ≤ 1) (i j : Fin 3) :
      |inner ℝ (a i) (a j)| ≤ 1 := by
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul (ha i) (ha j) (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hd (i j : Fin 3) : |inner ℝ (u i) (u j)-inner ℝ (v i) (v j)| ≤ 2*ε := by
    have he : inner ℝ (u i) (u j)-inner ℝ (v i) (v j) =
        inner ℝ (u i-v i) (u j)+inner ℝ (v i) (u j-v j) := by
      rw [inner_sub_left,inner_sub_right]
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    have h₁ : |inner ℝ (u i-v i) (u j)| ≤ ε := by
      apply (abs_real_inner_le_norm _ _).trans
      exact (mul_le_mul (hclose i) (hu j) (norm_nonneg _) hε).trans_eq (mul_one _)
    have h₂ : |inner ℝ (v i) (u j-v j)| ≤ ε := by
      apply (abs_real_inner_le_norm _ _).trans
      exact (mul_le_mul (hv i) (hclose j) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    linarith
  have hh := determinant_three_stability (Matrix.gram ℝ u) (Matrix.gram ℝ v)
    (hb u hu) (hb v hv) hd
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceTripleStability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original transverse triples remain transverse in the selected slice -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem gram_slice_isometry (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (u : Fin 3 → V) :
    (Matrix.gram ℝ (fun i => (u i : Space d))).det =
      (Matrix.gram ℝ (fun i => e (u i))).det := by
  congr 1
  ext i j
  exact (e.inner_map_map (u i) (u j)).symm

theorem slice_triple_gram_stability (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (w : Fin 3 → Sphere d) {δ : ℝ}
    (hδ : δ < 1) (hw : ∀ i, w i ∈ directionSliceBand V δ) :
    |(Matrix.gram ℝ (fun i => (w i : Space d))).det -
      (Matrix.gram ℝ (fun i => normalize (e (V.orthogonalProjectionOnto (w i : Space d))))).det|
      ≤ 72*δ := by
  let u : Fin 3 → V := fun i => normalize (V.orthogonalProjectionOnto (w i : Space d))
  have hp (i : Fin 3) : V.orthogonalProjectionOnto (w i : Space d) ≠ 0 := by
    intro hz
    have hlo := directionSliceBand_projection_lower V (hw i)
    have he : V.starProjection (w i : Space d) = 0 := congrArg Subtype.val hz
    rw [he,norm_zero] at hlo
    linarith
  have hn (i : Fin 3) : ‖(u i : Space d)‖ ≤ 1 := by
    change ‖normalize (V.orthogonalProjectionOnto (w i : Space d))‖ ≤ 1
    rw [norm_normalize (hp i)]
  have hc (i : Fin 3) : ‖(w i : Space d)-(u i : Space d)‖ ≤ 2*δ := by
    rw [norm_sub_rev]
    exact directionSliceBand_normalize_error V hδ (hw i)
  have hh := gram_three_stability (fun i => (w i : Space d)) (fun i => (u i : Space d))
    (fun i => (sphere_norm (w i)).le) hn hc
  rw [gram_slice_isometry V e u] at hh
  have he : (fun i => e (u i)) =
      (fun i => normalize (e (V.orthogonalProjectionOnto (w i : Space d)))) := by
    funext i
    exact slice_isometry_normalize V e _
  rw [he] at hh
  linarith

theorem slice_triple_gram_lower (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space 3) (w : Fin 3 → Sphere d) {δ Δ : ℝ}
    (hδ : δ < 1) (hw : ∀ i, w i ∈ directionSliceBand V δ)
    (hΔ : 0 ≤ Δ)
    (hgram : 2*Δ ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (w i : Space d))).det))
    (hsmall : 72*δ ≤ 3*Δ^2) :
    Δ ≤ Real.sqrt ((Matrix.gram ℝ (fun i =>
      normalize (e (V.orthogonalProjectionOnto (w i : Space d))))).det) := by
  have hg0 : 0 ≤ (Matrix.gram ℝ (fun i => (w i : Space d))).det :=
    (Matrix.posSemidef_gram ℝ _).det_nonneg
  have hs0 : 0 ≤ (Matrix.gram ℝ (fun i =>
      normalize (e (V.orthogonalProjectionOnto (w i : Space d))))).det :=
    (Matrix.posSemidef_gram ℝ _).det_nonneg
  have hs := slice_triple_gram_stability V e w hδ hw
  have hsq := Real.sq_sqrt hg0
  have hsq' := Real.sq_sqrt hs0
  have hlow := (abs_le.mp hs).2
  have hroot := Real.sqrt_nonneg ((Matrix.gram ℝ (fun i =>
      normalize (e (V.orthogonalProjectionOnto (w i : Space d))))).det)
  nlinarith [Real.sqrt_nonneg ((Matrix.gram ℝ (fun i => (w i : Space d))).det)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceThreeTubeMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint tube obstruction expressed on the original point law -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem slice_three_tube_mass_sq (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (e : V ≃ₗᵢ[ℝ] Space 3)
    (w : Fin 3 → Sphere d) {η Δ : ℝ} (hη : η < 1)
    (hband : ∀ i, w i ∈ directionSliceBand V η)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : 2*Δ ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (w i : Space d))).det))
    (herror : 72*η ≤ 3*Δ^2)
    (E : Set (Space d)) (A : Fin 3 → Finset (Space d)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C H s : ℝ} (hδ : 0 < δ)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : ∀ p : Space 3, μ {x | dist (e (V.orthogonalProjectionOnto x)) p < 6*δ} ≤
      ENNReal.ofReal (H*(6*δ)^s))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (w i : Space d) (x-a)‖ ≤ C*δ) :
    (μ E).toReal^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*
      ((6*C+35)/Δ)^6*(H*(6*δ)^s)^2 := by
  let f : Space d → Space 3 := fun x => e (V.orthogonalProjectionOnto x)
  let v : Fin 3 → Space 3 := fun i => normalize (f (w i))
  have hv (i : Fin 3) : ‖v i‖ = 1 := by
    have hp : V.orthogonalProjectionOnto (w i : Space d) ≠ 0 := by
      intro hz
      have hh := directionSliceBand_projection_lower V (hband i)
      have he : V.starProjection (w i : Space d) = 0 := congrArg Subtype.val hz
      rw [he,norm_zero] at hh
      linarith
    exact norm_normalize (fun hz => hp (e.injective (by simpa only [map_zero] using hz)))
  have hg : Δ ≤ Real.sqrt (tripleGram (v 0) (v 1) (v 2)) := by
    have hh := slice_triple_gram_lower V e w hη hband hΔ.le hgram herror
    have he : ![v 0,v 1,v 2] = v := by ext i; fin_cases i <;> rfl
    change Δ ≤ Real.sqrt (Matrix.gram ℝ ![v 0,v 1,v 2]).det
    rw [he]
    exact hh
  have hnE : ∀ x ∈ E, ‖f x‖ ≤ R := by
    intro x hx
    exact ((e.norm_map _).le.trans (V.norm_orthogonalProjectionOnto_apply_le x)).trans (hE x hx)
  apply three_tube_pullback_mass_sq μ f v hv hΔ hΔ1 hg E A R hnE hδ hC hH hball
  intro i x hx
  obtain ⟨a,ha,ht⟩ := hcover i x hx
  exact ⟨a,ha,(oriented_slice_tube_width V e hη (hband i) x a).trans ht⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_EndpointSliceObstruction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A transverse original triple cannot carry too much common slice incidence -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem endpoint_slice_obstruction (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (e : V ≃ₗᵢ[ℝ] Space 3)
    (w : Fin 3 → Sphere d) {η δ a κ C s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hη : η < 1) (hband : ∀ i, w i ∈ directionSliceBand V η)
    (hgram : 2*δ^a ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (w i : Space d))).det))
    (herror : 72*η ≤ 3*(δ^a)^2)
    (hbudget : (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 < (δ^κ)^2)
    (E : Set (Space d)) (A : Fin 3 → Finset (Space d)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R)
    (hball : ∀ p : Space 3, μ {x | dist (e (V.orthogonalProjectionOnto x)) p < 6*δ} ≤
      ENNReal.ofReal (δ^(-κ)*(6*δ)^s))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ b ∈ A i,
      ‖perpendicularPart (w i : Space d) (x-b)‖ ≤ C*δ)
    (hcard : ∀ i, ((A i).card:ℝ) ≤ δ^(-1-κ))
    (hmass : δ^κ ≤ (μ E).toReal) : False := by
  have hΔ : 0 < δ^a := Real.rpow_pos_of_pos hδ a
  have hΔ1 : δ^a ≤ 1 := Real.rpow_le_one hδ.le hδ1 ha
  have hm := slice_three_tube_mass_sq μ V e w hη hband hΔ hΔ1 hgram herror
    E A R hE hδ hC (Real.rpow_nonneg hδ.le _) hball hcover
  have hc : ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ) ≤ (δ^(-1-κ))^3 := by
    calc
      _ ≤ δ^(-1-κ)*δ^(-1-κ)*δ^(-1-κ) := by gcongr <;> apply hcard
      _ = _ := by ring
  have hup : (μ E).toReal^2 ≤
      (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 := by
    apply hm.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
  have hlo := pow_le_pow_left₀ (Real.rpow_nonneg hδ.le κ) hmass 2
  exact (not_lt_of_ge (hlo.trans hup)) hbudget

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointChartObstruction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exclusion of common chart incidence by the three-tube estimate -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem endpoint_chart_incidence_obstruction
    (α : Measure (Space (n+1))) (β : Measure (Space n))
    [IsFiniteMeasure α] [IsFiniteMeasure β]
    (V : Submodule ℝ (Space (n+1))) (e : V ≃ₗᵢ[ℝ] Space 3)
    (E : Set (Space (n+1) × Space n)) (hE : MeasurableSet E)
    (G : Set (Space n × Space n)) (hG : MeasurableSet G)
    (J : Space n → Finset (Space (n+1)))
    {δ η a κ C s R M b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (hC : 0 ≤ C) (hη : η < 1)
    (hM : 0 < M) (hb : 0 < b)
    (hα : α univ ≤ ENNReal.ofReal M) (hβ : β univ ≤ ENNReal.ofReal M)
    (hchart : ∀ u ∈ E, ‖u.2‖ ≤ 1)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ R)
    (hband : ∀ u ∈ E, gnomonicChart u.2 ∈ directionSliceBand V η)
    (hball : ∀ p : Space 3, α {x | dist (e (V.orthogonalProjectionOnto x)) p < 6*δ} ≤
      ENNReal.ofReal (δ^(-κ)*(6*δ)^s))
    (hcover : ∀ u ∈ E, ∃ v ∈ J u.2,
      ‖perpendicularPart (gnomonicChart u.2 : Space (n+1)) (u.1-v)‖ ≤ C*δ)
    (hcard : ∀ p, ((J p).card:ℝ) ≤ δ^(-1-κ))
    (hbad : (β.prod (β.prod β)) (badChartTriples G (2*δ^a))+
      2*β univ*(β.prod β) Gᶜ ≤ ENNReal.ofReal (b^3/(4*M^3)))
    (hmass : δ^κ ≤ b^3/(2*M^5))
    (herror : 72*η ≤ 3*(δ^a)^2)
    (hbudget : (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 < (δ^κ)^2) :
    (α.prod β) E < ENNReal.ofReal b := by
  classical
  by_contra! hI
  obtain ⟨w,hvol,_,_,hcommon⟩ := exists_transverse_common_chart_triple α β E hE hchart
    G hG (2*δ^a) hM hb hα hβ hI hbad
  let Q : Set (Space (n+1)) := {x | (x,w) ∈ commonTripleRelation E}
  let v : Fin 3 → Sphere (n+1) := ![gnomonicChart w.1,gnomonicChart w.2.1,gnomonicChart w.2.2]
  let L : Fin 3 → Finset (Space (n+1)) := ![J w.1,J w.2.1,J w.2.2]
  have hQ (x : Space (n+1)) (hx : x ∈ Q) :
      (x,w.1) ∈ E ∧ (x,w.2.1) ∈ E ∧ (x,w.2.2) ∈ E := hx
  have hn : Q.Nonempty := by
    by_contra hn
    have he : Q = ∅ := not_nonempty_iff_eq_empty.mp hn
    change ENNReal.ofReal (b^3/(2*M^5)) < α Q at hcommon
    rw [he,measure_empty] at hcommon
    exact not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ _) hcommon
  obtain ⟨x,hx⟩ := hn
  have hvband : ∀ i, v i ∈ directionSliceBand V η := by
    intro i
    fin_cases i
    · exact hband (x,w.1) (hQ x hx).1
    · exact hband (x,w.2.1) (hQ x hx).2.1
    · exact hband (x,w.2.2) (hQ x hx).2.2
  have hvgram : 2*δ^a ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (v i : Space (n+1)))).det) := hvol
  have hQbound : ∀ y ∈ Q, ‖y‖ ≤ R := fun y hy => hbounded (y,w.1) (hQ y hy).1
  have hQcover : ∀ i : Fin 3, ∀ y ∈ Q, ∃ c ∈ L i,
      ‖perpendicularPart (v i : Space (n+1)) (y-c)‖ ≤ C*δ := by
    intro i y hy
    fin_cases i
    · exact hcover (y,w.1) (hQ y hy).1
    · exact hcover (y,w.2.1) (hQ y hy).2.1
    · exact hcover (y,w.2.2) (hQ y hy).2.2
  have hLcard : ∀ i, ((L i).card:ℝ) ≤ δ^(-1-κ) := by
    intro i
    fin_cases i
    · exact hcard w.1
    · exact hcard w.2.1
    · exact hcard w.2.2
  have hQmass : δ^κ ≤ (α Q).toReal := hmass.trans (by
    have hh := ENNReal.toReal_mono (measure_ne_top α Q) hcommon.le
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ b^3/(2*M^5))] using hh)
  exact endpoint_slice_obstruction α V e v hδ hδ1 ha hC hη hvband hvgram herror hbudget
    Q L R hQbound hball hQcover hLcard hQmass

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointChartSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer the original radial costs to a restricted chart slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {X : Type*} [MeasurableSpace X]

theorem restricted_chart_exceptional_triples
    (ν₀ : Measure (Space n)) [IsFiniteMeasure ν₀]
    (A : Fin h → Space (n+1)) (δ : ℝ) (D : Set (Space n))
    (G : Set (Space n × Space n)) (W : ℝ)
    {M P T : ℝ≥0∞}
    (hmass : ((gaussianChartSliceMeasure ν₀ A δ).restrict D) univ ≤ M)
    (hpair : ((gaussianChartSliceMeasure ν₀ A δ).prod
      (gaussianChartSliceMeasure ν₀ A δ)) Gᶜ ≤ P)
    (htriple : ((gaussianChartSliceMeasure ν₀ A δ).prod
      ((gaussianChartSliceMeasure ν₀ A δ).prod (gaussianChartSliceMeasure ν₀ A δ)))
      (badChartTriples G W) ≤ T) :
    let β := (gaussianChartSliceMeasure ν₀ A δ).restrict D
    (β.prod (β.prod β)) (badChartTriples G W)+2*β univ*(β.prod β) Gᶜ ≤ T+2*M*P := by
  intro β
  have hβ : β ≤ gaussianChartSliceMeasure ν₀ A δ := Measure.restrict_le_self
  have hp : (β.prod β) Gᶜ ≤ P := (Measure.prod_mono hβ hβ _).trans hpair
  have ht : (β.prod (β.prod β)) (badChartTriples G W) ≤ T :=
    (Measure.prod_mono hβ (Measure.prod_mono hβ hβ) _).trans htriple
  exact add_le_add ht (mul_le_mul' (mul_le_mul' le_rfl hmass) hp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarSelectedGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the published planar consequence to a selected original-label slice -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal Topology
variable {d h : ℕ} {κ : Type*}

theorem selectedActiveRelation_measurable [Fintype κ] [DecidableEq κ]
    (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R T : ℝ) :
    MeasurableSet (selectedActiveRelation A z δ E J a R T) := by
  have hs := (gaussianActiveRelation_measurable E hE J hJ a R (ENNReal.ofReal T) true).preimage
    (show Measurable (fun u : Space d × Sphere d => ((A,z),u)) from by fun_prop)
  exact hs.inter ((gaussianPointBand_measurable A z δ).prod (gaussianDirectionBand_measurable A δ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBandRestriction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Making the two slice bands explicit in the original-label relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussian_pruned_incidence_inter_bands
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) :
    gaussianPrunedIncidence μ ν δ r TP TD M
      (E ∩ (gaussianPointBand p.1 p.2 δ ×ˢ gaussianDirectionBand p.1 δ)) p =
      gaussianPrunedIncidence μ ν δ r TP TD M E p := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)
  let β := (gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)
  have hp : ∀ᵐ x ∂α, x ∈ gaussianPointBand p.1 p.2 δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianPointBand_measurable _ _ _)) _)
  have hw : ∀ᵐ w ∂β, w ∈ gaussianDirectionBand p.1 δ :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable _ _)) _)
  change (α.prod β) _ = (α.prod β) E
  apply measure_congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hp,Measure.quasiMeasurePreserving_snd.ae hw] with t ht hu
  exact propext ⟨fun h => h.1,fun h => ⟨h,ht,hu⟩⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SelectedChartRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected incidence in its original affine chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*}

theorem selectedChartRelation_measurable [Fintype κ] [DecidableEq κ]
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) (R T : ℝ) :
    MeasurableSet (selectedChartRelation A z δ E J a R T) := by
  have hm : Measurable (fun u : Space (n+1) × Space n => (u.1,gnomonicChart u.2)) :=
    measurable_fst.prodMk ((gnomonicChart_continuous n).measurable.comp measurable_snd)
  have hn : MeasurableSet {u : Space (n+1) × Space n | ‖u.2‖ ≤ 1} :=
    measurableSet_le (measurable_norm.comp measurable_snd) measurable_const
  exact ((selectedActiveRelation_measurable A z δ E hE J hJ a R T).preimage hm).inter hn

theorem selected_chart_incidence_eq [Fintype ι] [Fintype κ] [DecidableEq κ]
    (μ : Measure (Space (n+1))) (ν₀ : Measure (Space n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀]
    (hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1)
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) (R T : ℝ) :
    let α := (gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))
    let β := (gaussianChartSliceMeasure ν₀ A δ).restrict
      (gnomonicChart ⁻¹' gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r TD M A)
    (α.prod β) (selectedChartRelation A z δ E J a R T) =
      gaussianPrunedPairMass μ (Measure.map gnomonicChart ν₀) δ r TP TD M
        (gaussianActiveRelation E J a R (ENNReal.ofReal T) true) (A,z) := by
  intro α β
  have hD : MeasurableSet (gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r TD M A) :=
    gaussianDirectionGood_measurable_fixed (Measure.map (gnomonicChart : Space n → Sphere (n+1)) ν₀) δ r TD M A
  have hm : Measure.map gnomonicChart β =
      (gaussianDirectionSliceMeasure (Measure.map gnomonicChart ν₀) A δ).restrict
        (gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r TD M A) :=
    gnomonic_restricted_slice_map ν₀ A δ _ hD
  have hnorm : ∀ᵐ p ∂β, ‖p‖ ≤ 1 :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_of_ae hν₀) _)
  have heq : (α.prod β) (selectedChartRelation A z δ E J a R T) =
      (α.prod β) {u | (u.1,gnomonicChart u.2) ∈ selectedActiveRelation A z δ E J a R T} := by
    apply measure_congr
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hnorm] with u hu
    exact propext ⟨fun hx => hx.1,fun hx => ⟨hx,hu⟩⟩
  rw [heq,gnomonic_incidence_transport α β _ (selectedActiveRelation_measurable A z δ E hE J hJ a R T),hm]
  change gaussianPrunedIncidence μ (Measure.map gnomonicChart ν₀) δ r TP TD M
    (selectedActiveRelation A z δ E J a R T) (A,z) = _
  exact gaussian_pruned_incidence_inter_bands μ (Measure.map gnomonicChart ν₀) δ r TP TD M _ (A,z)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SelectedChartGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometry of the retained relation on the original chart labels -/

namespace Falconer
open Set
open scoped ENNReal
variable {n h : ℕ} {ι : Type*}

theorem selectedChartRelation_point_bound
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (J : Sphere (n+1) → Finset ι)
    (v : ι → Space (n+1)) (R T : ℝ) {D : ℝ}
    (hE : ∀ u ∈ E, ‖u.1‖ ≤ D) :
    ∀ u ∈ selectedChartRelation A z δ E J v R T, ‖u.1‖ ≤ D := by
  intro u hu
  exact hE (u.1,gnomonicChart u.2) hu.1.1.1

theorem selectedChartRelation_kernel_band
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (J : Sphere (n+1) → Finset ι)
    (v : ι → Space (n+1)) (R T : ℝ)
    (hprojection : ∀ x : Space (n+1), ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖) :
    ∀ u ∈ selectedChartRelation A z δ E J v R T,
      gnomonicChart u.2 ∈ directionSliceBand (gaussianRowMap A).ker (2*(h:ℝ)*δ) := by
  intro u hu
  have hw : gnomonicChart u.2 ∈ gaussianDirectionBand A δ := hu.1.2.2
  have hh := gaussian_direction_band_kernel_distance A (by norm_num) hprojection hw
  change ‖(gaussianRowMap A).kerᗮ.starProjection (gnomonicChart u.2 : Space (n+1))‖ ≤ 2*(h:ℝ)*δ
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem selectedChartRelation_original_cover
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (J : Sphere (n+1) → Finset ι)
    (v : ι → Space (n+1)) {C M T D : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hA : ∀ i, ‖A i‖ ≤ M) (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ D)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖v i‖ ≤ D)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space (n+1)) (u.1-v i)‖ ≤ C*δ) :
    ∀ u ∈ selectedChartRelation A z δ E J v (δ+(2*D)*δ+(C*δ)*M) T,
      ∃ c ∈ (cappedActiveAnchors A z (J (gnomonicChart u.2)) v (δ+(2*D)*δ+(C*δ)*M) T).image v,
        ‖perpendicularPart (gnomonicChart u.2 : Space (n+1)) (u.1-c)‖ ≤ C*δ := by
  intro u hu
  exact gaussian_capped_original_cover A z E J v hM hT hA hbounded hanchor hcover
    hu.1.2.1 hu.1.2.2 hu.1.1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceMapBalls
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball transport by pairwise metric control on a full-measure support -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

omit [BorelSpace X] in
theorem map_ball_bound_of_pair_control (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (S : Set X) (hS : ∀ᵐ x ∂μ, x ∈ S) {r R : ℝ} {C : ℝ≥0∞}
    (hpair : ∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) < 2*r → dist x y < R)
    (hball : ∀ x, μ (ball x R) ≤ C) (a : Y) :
    (Measure.map f μ) (ball a r) ≤ C := by
  rw [Measure.map_apply hf measurableSet_ball]
  by_cases he : (S ∩ f ⁻¹' ball a r).Nonempty
  · obtain ⟨x,hxS,hxa⟩ := he
    apply (measure_mono_ae ?_).trans (hball x)
    filter_upwards [hS] with y hy hya
    exact hpair y hy x hxS ((dist_triangle (f y) a (f x)).trans_lt
      (by linarith [show dist (f y) a < r from hya,show dist (f x) a < r from hxa,
        dist_comm a (f x)]))
  · have hz : μ (f ⁻¹' ball a r) = 0 := by
      apply measure_mono_null (t := Sᶜ)
      · intro x hx hxS
        exact he ⟨x,hxS,hx⟩
      · exact ae_iff.mp hS
    rw [hz]
    exact zero_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMapBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale ball bounds on the actual kernel-coordinate pushforwards -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_kernel_ball_bound (A : Fin h → Space d) (z : Space h)
    (μ : Measure (Space d)) {δ K s R : ℝ} {C : ℝ≥0∞} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hμ : ∀ᵐ x ∂μ, x ∈ gaussianPointBand A z δ)
    (hball : ∀ x, μ (ball x R) ≤ C) (hR : 2*s+K*((h:ℝ)*(2*δ)) ≤ R) (a : Space d) :
    (Measure.map (gaussianRowMap A).ker.starProjection μ) (ball a s) ≤ C := by
  apply map_ball_bound_of_pair_control μ _
    (gaussianRowMap A).ker.starProjection.continuous.measurable _ hμ _ hball a
  intro x hx y hy hxy
  have hp := gaussian_point_kernel_pair_distance A z hK hbound hx hy
    (le_refl ‖(gaussianRowMap A).ker.starProjection x-(gaussianRowMap A).ker.starProjection y‖)
  rw [dist_eq_norm] at hxy ⊢
  exact hp.trans_lt (by linarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate ball estimates for the actual retained slice laws -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_pruned_point_kernel_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 2*s+K*((h:ℝ)*(2*δ)) ≤ r i) (a : Space d) :
    (Measure.map (gaussianRowMap A).ker.starProjection
      ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))))
        (ball a s) ≤ TP i := by
  apply gaussian_point_kernel_ball_bound A z _ hK hbound _ (fun x => gaussianPointGood_ball μ δ r TP (A,z) i x) hs a
  exact ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianPointBand_measurable _ _ _)) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_OrientedSliceBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Closed-ball bounds in the oriented coordinates of the actual slice -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem oriented_point_ball_eq (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (μ : Measure (Space d)) (c : Space m) (r : ℝ) :
    μ {x | dist (e (V.orthogonalProjectionOnto x)) c < r} =
      (Measure.map V.starProjection μ) (ball (e.symm c : Space d) r) := by
  rw [Measure.map_apply V.starProjection.continuous.measurable measurableSet_ball]
  congr 1
  ext x
  change dist (e (V.orthogonalProjectionOnto x)) c < r ↔
    dist (V.orthogonalProjectionOnto x) (e.symm c) < r
  rw [← e.dist_map (V.orthogonalProjectionOnto x) (e.symm c),e.apply_symm_apply]

theorem gaussian_pruned_oriented_point_closed_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K s : ℝ} (hK : 0 ≤ K) (hspos : 0 < s)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hs : 4*s+K*((h:ℝ)*(2*δ)) ≤ r i) (c : Space m) :
    ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤ TP i := by
  have hss : s < 2*s := by linarith
  calc
    _ ≤ ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c < 2*s} :=
      measure_mono (show {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ⊆
        {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c < 2*s} from
          fun x hx => lt_of_le_of_lt hx hss)
    _ = _ := oriented_point_ball_eq (gaussianRowMap A).ker e _ c (2*s)
    _ ≤ _ := gaussian_pruned_point_kernel_ball μ A z δ r TP i hK hbound (by linarith) _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceScaling
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed spatial rescaling of a selected planar slice -/

namespace Falconer
open NormedSpace
variable {m : ℕ}

theorem slice_scaled_distance {L : ℝ} (hL : 0 < L) (x c : Space m) :
    dist (L⁻¹ • x) c = L⁻¹*dist x (L • c) := by
  have he : L⁻¹ • x-c = L⁻¹ • (x-L • c) := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hL.ne',one_smul]
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL),dist_eq_norm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianDyadicGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dyadic tests controlling scaled point and normalized direction balls -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {ι : Type*}

theorem gaussian_scaled_point_test
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (δ : ℝ) (r : ι → ℝ) (TP : ι → ℝ≥0∞) (i : ι)
    {K L a u : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ha : 0 < a) (hu : 0 < u)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4*L+2*K*(h:ℝ) ≤ a) (hδ : δ ≤ u/(2*a)) (hr : r i = u/2) (c : Space m) :
    ((gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z)))
      {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a)} ≤ TP i := by
  have hs : 0 < u/(2*a) := by positivity
  have he : a*(u/(2*a)) = u/2 := by field_simp
  have h₁ := mul_le_mul_of_nonneg_right haK hs.le
  have h₂ := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 2*K*(h:ℝ))
  have hrad : 4*(L*(u/(2*a)))+K*((h:ℝ)*(2*δ)) ≤ r i := by
    rw [hr]
    nlinarith
  apply (measure_mono (show
    {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a)} ⊆
    {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) (L • c) ≤ L*(u/(2*a))} from ?_)).trans
      (gaussian_pruned_oriented_point_closed_ball μ A z e δ r TP i hK (mul_pos hL hs) hbound hrad _)
  intro x hx
  change dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ u/(2*a) at hx
  rw [slice_scaled_distance hL,mul_comm,← div_eq_mul_inv] at hx
  change dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) (L • c) ≤ L*(u/(2*a))
  simpa only [mul_comm] using (div_le_iff₀ hL).mp hx

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_UnnormalizedSliceBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-radius point estimates before normalizing a slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {d h m : ℕ}

theorem truncated_dyadic_ball_bound_mass
    (μ : Measure X) (p : X → Space m) (N : ℕ) {a H s : ℝ}
    (ha : 1 ≤ a) (hH : 0 ≤ H) (hs : 0 ≤ s) (hmass : μ univ ≤ ENNReal.ofReal H)
    (hdyadic : ∀ g ≤ N, 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g → ∀ c : Space m,
      μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} ≤
        ENNReal.ofReal (H*(1/(2:ℝ)^g)^s)) :
    ∀ (c : Space m) (r : ℝ), 1/(2:ℝ)^N ≤ r →
      μ {x | dist (p x) c ≤ r} ≤ ENNReal.ofReal (H*(4*a*r)^s) := by
  intro c r hr
  have hrp : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hsmall : 2*a*r ≤ 1
  · have hmin : 1/(2:ℝ)^N ≤ 2*a*r := hr.trans (by nlinarith)
    obtain ⟨g,hg,hgr,hrg⟩ := Regularization.dyadic_radius_bracket hmin hsmall
    have hcut : 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g :=
      (mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 2*a)).trans hgr
    have hrad : r ≤ (1/(2:ℝ)^g)/(2*a) := (le_div_iff₀ (by linarith)).mpr (by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hgr)
    calc
      _ ≤ μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} := measure_mono (fun x hx => hx.trans hrad)
      _ ≤ ENNReal.ofReal (H*(1/(2:ℝ)^g)^s) := hdyadic g hg hcut c
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith [hrg]) hs) hH)
  · apply ((measure_mono (subset_univ _)).trans hmass).trans
    apply ENNReal.ofReal_le_ofReal
    have hp : 1 ≤ (4*a*r)^s := Real.one_le_rpow (by linarith) hs
    nlinarith

theorem gaussian_point_unnormalized_frostman
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m) (N : ℕ)
    (r : Fin (N+1) → ℝ) (TP : Fin (N+1) → ℝ≥0∞)
    (hr : ∀ g, r g = (1/(2:ℝ)^g.val)/2)
    {K a P f : ℝ} (hK : 0 ≤ K) (ha : 1 ≤ a) (hP : 0 ≤ P) (hf : 0 ≤ f)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4+2*K*(h:ℝ) ≤ a)
    (hTP : ∀ g, TP g ≤ ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^f))
    (hmass : ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) univ ≤ ENNReal.ofReal P) :
    ∀ c s, 1/(2:ℝ)^N ≤ s →
      ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
        (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤
        ENNReal.ofReal (P*(4*a*s)^f) := by
  apply truncated_dyadic_ball_bound_mass _ _ N ha hP hf hmass
  intro g hg hcut c
  let j : Fin (N+1) := ⟨g,by omega⟩
  have hδ : 1/(2:ℝ)^N ≤ (1/(2:ℝ)^g)/(2*a) :=
    (le_div_iff₀ (by linarith)).mpr (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcut)
  have hb := gaussian_scaled_point_test μ A z e (1/(2:ℝ)^N) r TP j hK
    (by norm_num : (0:ℝ) < 1) (by linarith) (by positivity) hbound
    (by simpa only [mul_one] using haK) hδ (hr j) c
  simp only [inv_one,one_smul] at hb
  exact hb.trans (hTP j)

theorem gaussian_point_endpoint_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 3) (N : ℕ)
    {P s a κ : ℝ} (hP : 0 ≤ P) (hs : 0 ≤ s) (ha : 1 ≤ a)
    (haK : 4+4*(h:ℝ) ≤ a)
    (hprojection : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖)
    (hmass : ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
        (fun g => ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^s)) (A,z))) univ ≤ ENNReal.ofReal P)
    (hcoef : P*(4*a)^s ≤ (1/(2:ℝ)^N)^(-κ)) :
    ∀ p : Space 3, ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
        (fun g => ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^s)) (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) p < 6*(1/(2:ℝ)^N)} ≤
      ENNReal.ofReal ((1/(2:ℝ)^N)^(-κ)*(6*(1/(2:ℝ)^N))^s) := by
  intro p
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hh := gaussian_point_unnormalized_frostman μ A z e N _ _ (fun _ => rfl)
    (by norm_num) ha hP hs hprojection (by nlinarith [haK]) (fun _ => le_rfl)
    hmass p (6*δ) (by linarith)
  have hsub : {x : Space d | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) p < 6*δ} ⊆
      {x : Space d | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) p ≤ 6*δ} := by
    intro x hx
    change dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) p ≤ 6*δ
    exact le_of_lt hx
  apply ((measure_mono hsub).trans hh).trans
  apply ENNReal.ofReal_le_ofReal
  rw [show 4*a*(6*δ) = (4*a)*(6*δ) by ring,Real.mul_rpow (by linarith) (by positivity)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) s)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianEndpointExclusion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint obstruction on the actual pruned Gaussian slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussian_endpoint_slice_exclusion
    (μ : Measure (Space (n+1))) (ν₀ : Measure (Space n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀]
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) (hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1)
    (A : Fin h → Space (n+1)) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 3)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset ι) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (v : ι → Space (n+1)) (TD : Fin (N+1) → ℝ≥0∞)
    (G : Set (Space n × Space n)) (hG : MeasurableSet G)
    {P M Mdir Mrow T a κ C s a₀ b : ℝ} {Bpair Btriple : ℝ≥0∞}
    (hP : 0 ≤ P) (hPM : P ≤ M) (hMdir : Mdir ≤ M) (hM : 0 < M) (hMrow : 0 ≤ Mrow)
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hC : 0 ≤ C) (hs : 0 ≤ s) (hb : 0 < b)
    (ha₀ : 1 ≤ a₀) (haK : 4+4*(h:ℝ) ≤ a₀)
    (hA : ∀ i, ‖A i‖ ≤ Mrow)
    (hprojection : ∀ x : Space (n+1), ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖)
    (hsmall : 2*(h:ℝ)*(1/(2:ℝ)^N) < 1)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ 1/4)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (n+1)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N))
    (hpair : ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
      (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))) Gᶜ ≤ Bpair)
    (htriple : ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
      ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
        (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))))
      (badChartTriples G (2*(1/(2:ℝ)^N)^a)) ≤ Btriple)
    (hbad : Btriple+2*ENNReal.ofReal M*Bpair ≤ ENNReal.ofReal (b^3/(4*M^3)))
    (hmass : (1/(2:ℝ)^N)^κ ≤ b^3/(2*M^5))
    (hcount : T ≤ (1/(2:ℝ)^N)^(-1-κ))
    (hcoef : P*(4*a₀)^s ≤ (1/(2:ℝ)^N)^(-κ))
    (herror : 144*(h:ℝ)*(1/(2:ℝ)^N) ≤ 3*((1/(2:ℝ)^N)^a)^2)
    (hbudget : ((1/(2:ℝ)^N)^(-1-κ))^3*((6*C+35)/(1/(2:ℝ)^N)^a)^6*
      ((1/(2:ℝ)^N)^(-κ)*(6*(1/(2:ℝ)^N))^s)^2 < ((1/(2:ℝ)^N)^κ)^2) :
    gaussianPrunedPairMass μ (Measure.map gnomonicChart ν₀) (1/(2:ℝ)^N)
      (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
      (fun g => ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^s)) TD (ENNReal.ofReal Mdir)
      (gaussianActiveRelation E J v
        ((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+(C*(1/(2:ℝ)^N))*Mrow)
        (ENNReal.ofReal T) true) (A,z) < ENNReal.ofReal b := by
  classical
  let δ : ℝ := 1/(2:ℝ)^N
  let r : Fin (N+1) → ℝ := fun g => (1/(2:ℝ)^g.val)/2
  let TP : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^s)
  let α := (gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))
  let D := gnomonicChart ⁻¹' gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r TD (ENNReal.ofReal Mdir) A
  let β := (gaussianChartSliceMeasure ν₀ A δ).restrict D
  let R := δ+(2*(1/4))*δ+(C*δ)*Mrow
  let F := selectedChartRelation A z δ E J v R T
  let L : Space n → Finset (Space (n+1)) := fun p =>
    (cappedActiveAnchors A z (J (gnomonicChart p)) v R T).image v
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hαP : α univ ≤ ENNReal.ofReal P := by
    have hh := gaussianPointGood_mass μ δ r TP (A,z) hμ 0 (by norm_num [r])
    simpa only [TP,Fin.val_zero,pow_zero,div_one,Real.one_rpow,mul_one] using hh
  have hα : α univ ≤ ENNReal.ofReal M := hαP.trans (ENNReal.ofReal_le_ofReal hPM)
  have hβ : β univ ≤ ENNReal.ofReal M :=
    (gnomonic_pruned_mass ν₀ A δ r TD (ENNReal.ofReal Mdir)).trans (ENNReal.ofReal_le_ofReal hMdir)
  have hF : MeasurableSet F := selectedChartRelation_measurable A z δ E hE J hJ v R T
  have hcost := restricted_chart_exceptional_triples ν₀ A δ D G (2*δ^a) hβ hpair htriple
  have hball := gaussian_point_endpoint_ball μ A z e N hP hs ha₀ haK hprojection hαP hcoef
  have hboundF := selectedChartRelation_point_bound A z δ E J v R T hbounded
  have hbandF := selectedChartRelation_kernel_band A z δ E J v R T hprojection
  have hcoverF := selectedChartRelation_original_cover A z δ E J v hMrow hT hA hbounded hanchor hcover
  have hcardL : ∀ p, ((L p).card:ℝ) ≤ δ^(-1-κ) := fun p =>
    (capped_original_cover_card A z (J (gnomonicChart p)) v R hT).trans hcount
  have hh := endpoint_chart_incidence_obstruction α β (gaussianRowMap A).ker e F hF G hG L
    hδ hδ1
    ha hC hsmall hM hb hα hβ (fun _ hu => hu.2) hboundF hbandF hball hcoverF hcardL
    (hcost.trans hbad) hmass (by nlinarith [herror]) hbudget
  rw [selected_chart_incidence_eq μ ν₀ hν₀ A z δ r TP TD (ENNReal.ofReal Mdir) E hE J hJ v R T] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ControlledEndpointGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint angular gain from the two actual radial slice costs

This is the finite-scale assembly step. Its cost and scalar hypotheses are
verified from the original direction law in the uniform endpoint application.
-/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem controlled_endpoint_angular_gain_oai {h N : ℕ} {t : ℝ}
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
    (ν₀ : Measure (Space (h+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ν₀]
    (hνeq : Measure.map gnomonicChart ν₀ = ν)
    (B : Space h →ₗᵢ[ℝ] Space (h+3)) (w₀ : Sphere (h+3))
    (E : Set (Space (h+3) × Sphere (h+3)))
    (J : Sphere (h+3) → Finset κ) (v : κ → Space (h+3))
    (G : Set (Space (h+2) × Space (h+2))) (hG : MeasurableSet G)
    {ρ Lt Lq K C₀ Nc a κ₀ C a₀ b Bpair Btriple : ℝ}
    (hρ : 0 ≤ ρ) (hδρ : 1/(2:ℝ)^N ≤ ρ)
    (hB : ∀ i, inner ℝ (w₀:Space (h+3)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    (hν : ∀ᵐ w ∂ν, dist w w₀ ≤ ρ)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2)
    (hsmall : 2*(h:ℝ)*(1/(2:ℝ)^N) < 1)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) (hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1)
    (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
    (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t)
    (hμball : ∀ x : Space (h+3), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
    (hνball : ∀ x : Sphere (h+3), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^(h+1:ℝ)))
    (hpair : ∀ᵐ u : Sphere (h+3) × Sphere (h+3) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+3)) (u.2:Space (h+3)))
    (hK : 1 ≤ K) (hNc : 0 < Nc)
    (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀)
    (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h (h+1:ℝ) ≤ C₀)
    (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h (h+1:ℝ)|+1) ≤ C₀)
    (hcard : ((N+1:ℕ):ℝ)*C₀ ≤ K) (hC₀ : C₀ ≤ K)
    (hlarge : 4*(1+2*(2:ℝ)^h+1) ≤ K)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hb : 0 < b)
    (hBp : 0 < Bpair) (hBt : 0 < Btriple)
    (ha₀ : 1 ≤ a₀) (haK : 4+4*(h:ℝ) ≤ a₀)
    (hbad : ENNReal.ofReal Btriple+2*ENNReal.ofReal (K^6)*ENNReal.ofReal Bpair ≤
      ENNReal.ofReal (b^3/(4*(K^6)^3)))
    (hmass : (1/(2:ℝ)^N)^κ₀ ≤ b^3/(2*(K^6)^5))
    (hcount : K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
      (C*(1/(2:ℝ)^N))*((h+3:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-1-κ₀))
    (hcoef : K^6*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-κ₀))
    (herror : 144*(h:ℝ)*(1/(2:ℝ)^N) ≤ 3*((1/(2:ℝ)^N)^a)^2)
    (hbudget : ((1/(2:ℝ)^N)^(-1-κ₀))^3*((6*C+35)/(1/(2:ℝ)^N)^a)^6*
      ((1/(2:ℝ)^N)^(-κ₀)*(6*(1/(2:ℝ)^N))^(t-(h:ℝ)))^2 < ((1/(2:ℝ)^N)^κ₀)^2)
    (hbase :
      ENNReal.ofReal b*volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N))+
      (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*
        volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
        ((∫⁻ A, endpointPairCost ν₀ (1/(2:ℝ)^N) G A
          ∂(gaussianRows (h+3) h).restrict
            (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ))))/
              ENNReal.ofReal Bpair)+
      (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*
        volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
        ((∫⁻ A, endpointTripleCost ν₀ (1/(2:ℝ)^N) (2*(1/(2:ℝ)^N)^a) G A
          ∂(gaussianRows (h+3) h).restrict
            (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ))))/
              ENNReal.ofReal Btriple) ≤ ENNReal.ofReal (1/(4*K)))
    (hE : MeasurableSet E) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
    (hEb : ∀ u ∈ E, ‖u.1‖ ≤ 1/4) (hanchors : ∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+2) ρ^h)*
      (μ.prod ν) E < ENNReal.ofReal (1/K) := by
  classical
  let δ : ℝ := 1/(2:ℝ)^N
  let ε : ℝ := (h+3:ℝ)*(2*ρ)
  let Mrow : ℝ := ε+1
  let R : ℝ := δ+(2*(1/4))*δ+(C*δ)*Mrow
  let T : ℝ := K^11*(Nc*(2*R)^h)
  let rows : Fin h → Space (h+3) := fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hMrow : 0 ≤ Mrow := by dsimp [Mrow]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hrows (i : Fin h) : ‖rows i‖ ≤ 1 := by
    rw [show rows i = B (EuclideanSpace.basisFun (Fin h) ℝ i) from rfl,B.norm_map]
    exact ((EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one i).le
  have hwB : ∀ᵐ (w : Sphere (h+3)) ∂ν, ∀ i, |inner ℝ (w:Space (h+3)) (rows i)| ≤ ρ := by
    filter_upwards [hν] with w hw i
    exact transverse_frame_chart_bound B (w₀:Space (h+3)) hB hw i
  by_contra hnot
  have hmean := le_of_not_gt hnot
  have hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal ((2:ℝ)^h) := by
    simpa only [mul_one] using mul_le_mul' le_rfl hμmass
  have hcast : ((h+2:ℕ):ℝ)+1 = (h+3:ℝ) := by push_cast; ring
  obtain ⟨A,hA,z,_,hp,htc,hbig⟩ := dyadic_original_slice_costs rows hrows μ ν N
    (by norm_num : (1/4:ℝ) < 1/2) hμ hδρ hwB hLt hLq ht (by linarith : (h:ℝ) < h+1)
    hμmass hνmass hμball hνball hpair hKpos (by positivity : 0 ≤ (2:ℝ)^h) hNc hR
    hCpoint hCdir hCmass hcard hC₀ hlarge hfactor E hE J hJ v hJN hmean
    (endpointPairCost ν₀ δ G) (endpointTripleCost ν₀ δ (2*δ^a) G)
    (endpointPairCost_measurable ν₀ δ hG) (endpointTripleCost_measurable ν₀ δ (2*δ^a) hG)
    (ENNReal.ofReal Bpair) (ENNReal.ofReal Btriple) (ENNReal.ofReal b)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hBp)) (ne_of_gt (ENNReal.ofReal_pos.mpr hBt))
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (by simpa only [hcast] using hbase)
  rw [hcast] at hA
  have hdim : Module.finrank ℝ (gaussianRowMap A).ker = 3 := by
    simpa only [Nat.add_assoc,Nat.add_sub_cancel_left] using row_kernel_finrank A B hA hstable
  let e := sliceCoordinates (gaussianRowMap A).ker hdim
  have hdirMass : K^3 ≤ K^6 := pow_le_pow_right₀ hK (by norm_num)
  have hupper := gaussian_endpoint_slice_exclusion μ ν₀ hμ hν₀ A z e E hE J hJ v
    (fun g : Fin (N+1) => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val))) G hG
    (by positivity : 0 ≤ K^6) le_rfl hdirMass (by positivity : 0 < K^6) hMrow
    (by positivity) ha hC (sub_nonneg.mpr ht.le) hb ha₀ haK
    (gaussianRowNeighborhood_norm rows hrows hA) (row_kernel_projection_bound A B hA hstable)
    hsmall hEb hanchors hcover hp.le htc.le hbad hmass hcount hcoef herror hbudget
  rw [← hνeq] at hbig
  have hq : (h+1:ℝ)-(h:ℝ) = 1 := by ring
  simp only [gaussianPruningWeight_eq,hq,Real.rpow_one] at hbig
  exact (not_lt_of_ge hupper.le) hbig

end Falconer

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Falconer.controlled_endpoint_angular_gain_oai.{u_1} := @OAI.Falconer.controlled_endpoint_angular_gain_oai.{u_1}
