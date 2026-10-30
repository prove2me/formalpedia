-- Prove2me | solution 1 for OAI.Falconer.prepared_pair_positive_distance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:29:18.986247+00:00
-- url     : https://prove2.me/submissions/f21ffba0-b440-4b9d-b457-3e7f04765042

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_Regularization_exists_regularization_scalar_shell
import Theorems.Thm_OAI_Falconer_Regularization_uniform_regularizationPairExceptional_bound

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensions
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The all-dimensional Falconer statement and the final measure argument

The Falconer distance conjecture concerns compact subsets of Euclidean
space with Hausdorff dimension greater than half the ambient dimension.
The dimension-independent final measure argument reduces positivity of
the original distance set to absolute continuity of a weighted distance
pushforward.
-/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

section Geometry
variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem distanceSet_eq_image (E : Set X) :
    distanceSet E = (fun z : X × X => dist z.1 z.2) '' (E ×ˢ E) := by
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, hr⟩
    exact ⟨(x, y), ⟨hx, hy⟩, hr⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hr⟩
    exact ⟨x, hx, y, hy, hr⟩

theorem distanceSet_isCompact {E : Set X} (hE : IsCompact E) :
    IsCompact (distanceSet E) := by
  rw [distanceSet_eq_image]
  exact (hE.prod hE).image (continuous_fst.dist continuous_snd)

end Geometry

section Measures
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- A nonzero absolutely continuous measure carried by a set forces positive
Lebesgue measure. -/
theorem positive_volume_of_carried_measure (D : Set ℝ) (τ : Measure ℝ)
    (hmass : 0 < τ univ) (hcarried : τ Dᶜ = 0) (hac : τ ≪ volume) :
    0 < volume D := by
  by_contra h
  have hzero : volume D = 0 := le_antisymm (not_lt.mp h) bot_le
  have hτ : τ D = 0 := hac hzero
  have hz := measure_union_null hτ hcarried
  have : τ univ = 0 := by simpa only [union_compl_self] using hz
  exact (ne_of_gt hmass) this

end Measures
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothReciprocal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth reciprocal of a nonstationary phase derivative

The reciprocal is extended smoothly across zero by a scalar bump. At a
point where the denominator is bounded below, its derivative bounds
depend only on the normalized derivatives of that denominator.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem smoothReciprocal_eq {τ u : ℝ} (hτ : 0 < τ) (hu : τ ≤ |u|) :
    u * smoothReciprocal τ hτ u = 1 := by
  have hb : PlanarFalconer.sineZeroCutoff τ hτ u = 0 :=
    (PlanarFalconer.sineZeroCutoff τ hτ).zero_of_le_dist
      (by simpa [PlanarFalconer.sineZeroCutoff, Real.dist_eq] using hu)
  have hune : u ≠ 0 := by intro he; simp [he] at hu; linarith
  simp [smoothReciprocal,hb,hune]

end Falconer

end OAI
end

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

/-- Moving a unit direction changes the perpendicular test by at most twice
its angular displacement times the size of the tested vector. -/
theorem perpendicularPart_direction_error {w z : E} (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (v : E) :
    ‖perpendicularPart w v - perpendicularPart z v‖ ≤ 2 * ‖w-z‖ * ‖v‖ := by
  have he : perpendicularPart w v - perpendicularPart z v =
      inner ℝ z v • (z-w) + inner ℝ (z-w) v • w := by
    simp only [perpendicularPart, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℝ z v • (z-w)‖ + ‖inner ℝ (z-w) v • w‖ := norm_add_le _ _
    _ = |inner ℝ z v| * ‖z-w‖ + |inner ℝ (z-w) v| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hw, mul_one]
    _ ≤ (‖z‖ * ‖v‖) * ‖z-w‖ + (‖z-w‖ * ‖v‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm z v)
        (norm_nonneg _)) (abs_real_inner_le_norm (z-w) v)
    _ = _ := by rw [hz, one_mul, norm_sub_rev z w]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_BlockRegularization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem blockDepth_gap (N B i : ℕ) : blockDepth N B i - blockDepth N B (i+1) ≤ B := by
  dsimp only [blockDepth]
  rw [Nat.add_mul, one_mul]
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem division_blocks_control {H N : ℕ} (hH : 0 < H) (hN : H ≤ N) :
    0 < N/H ∧ N/(N/H)+1 ≤ 2*H := by
  have hB : 0 < N/H := Nat.div_pos hN hH
  have hrem : N < (N/H+1)*H := by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N hH
  have hmul : (N/H+1)*H ≤ (2*(N/H))*H := Nat.mul_le_mul_right H (by omega)
  have hlt : N < (2*H)*(N/H) := by
    calc
      N < (N/H+1)*H := hrem
      _ ≤ (2*(N/H))*H := hmul
      _ = (2*H)*(N/H) := by ac_rfl
  have hdiv : N/(N/H) < 2*H := (Nat.div_lt_iff_lt_mul hB).mpr hlt
  exact ⟨hB,by omega⟩

theorem division_block_width {H N : ℕ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hH : 1 ≤ lam*(H:ℝ)) : ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) := by
  have hn : (((N/H)*H:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.div_mul_le_self N H
  have h0 : 0 ≤ ((N/H:ℕ):ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hH h0
  have hl := mul_le_mul_of_nonneg_left hn hlam
  simp only [Nat.cast_mul, mul_one] at hh hl
  nlinarith

theorem blockDepth_brackets {N n B : ℕ} (hn : n ≤ N) (hB : 0 < B) :
    let i := (N-n)/B
    i < N/B+1 ∧ blockDepth N B (i+1) ≤ n ∧ n ≤ blockDepth N B i ∧
      blockDepth N B i-n ≤ B ∧ n-blockDepth N B (i+1) ≤ B := by
  dsimp only
  have hlo := Nat.div_mul_le_self (N-n) B
  have hhi := Nat.lt_mul_div_succ (N-n) hB
  have hi : (N-n)/B ≤ N/B := Nat.div_le_div_right (Nat.sub_le _ _)
  simp only [blockDepth]
  rw [Nat.mul_comm B] at hhi
  have hgap := blockDepth_gap N B ((N-n)/B)
  dsimp only [blockDepth] at hgap
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationQuantifiers
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem exists_bounded_regularization_control {lam : ℝ} (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
      ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧
      (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam := by
  let H := Nat.floor (1/lam)+1
  have hH : 0 < H := Nat.succ_pos _
  have hHlo : 1/lam < (H:ℝ) := by simpa only [H,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (1/lam)
  have hHhi : (H:ℝ) ≤ 1/lam+2 := by
    have hh := Nat.floor_le (by positivity : 0 ≤ 1/lam)
    dsimp [H]
    push_cast
    linarith
  have hHl : 1 ≤ lam*(H:ℝ) := by
    simpa only [mul_comm] using ((div_lt_iff₀ hlam).mp hHlo).le
  obtain ⟨M,hM⟩ := exists_nat_gt (((2*H+1:ℕ):ℝ)/lam)
  refine ⟨H,max H M,hH,hHhi,?_⟩
  intro N hN
  have hHN : H ≤ N := (le_max_left _ _).trans hN
  have hMN : M ≤ N := (le_max_right _ _).trans hN
  have hc := division_blocks_control hH hHN
  refine ⟨lt_of_lt_of_le hH hHN,hc.1,hc.2,division_block_width hlam.le hHl,?_⟩
  have hreal : ((2*H+1:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hm := (div_lt_iff₀ hlam).mp hM
    have hn : (M:ℝ) ≤ N := by exact_mod_cast hMN
    exact hm.le.trans (mul_le_mul_of_nonneg_right hn hlam.le)
  have hcount : ((N/(N/H)+2:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hh : N/(N/H)+2 ≤ 2*H+1 := by omega
    have hhR : ((N/(N/H)+2:ℕ):ℝ) ≤ ((2*H+1:ℕ):ℝ) := by exact_mod_cast hh
    exact hhR.trans hreal
  rw [← Real.rpow_natCast (2:ℝ) (N/(N/H)+2),← Real.rpow_natCast (2:ℝ) N,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcount

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyDescriptors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policyDescriptor_origin (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) :
    ∃ b u : ℕ, a ≤ b ∧ u ≤ t ∧ b+100*q < u ∧
      descriptorAnchor d = policyDepth A N q b u ∧ 0 < descriptorLength d ∧
      b ≤ descriptorAnchor d-descriptorLength d ∧ descriptorAnchor d+descriptorLength d ≤ u := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,hb,hu,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  exact ⟨z.1,z.2,hb,hu,hwide,originDescriptor_anchor A hd,
    originDescriptor_length A hq huN hwide hd⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapDenominator
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the cap partition denominator

Only centers whose closed cap contains the point contribute to a derivative.
The proved local packing bound therefore controls the sum independently of
the total number of caps.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capDenominator_ge_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    1 ≤ capDenominator δ hδ S w := by
  obtain ⟨c,hc,hwc⟩ := hcover w
  have hval : capBump δ hδ c w = 1 :=
    (capBump δ hδ c).one_of_mem_closedBall (Metric.mem_closedBall.mpr hwc)
  calc
    1 = capBump δ hδ c w := hval.symm
    _ ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapReciprocal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the cap normalization factor -/

namespace Falconer
open Set
open scoped ContDiff Topology

theorem capDenominator_mul_reciprocal {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    capDenominator δ hδ S w * capReciprocal δ hδ S w = 1 := by
  exact smoothReciprocal_eq zero_lt_one
    ((capDenominator_ge_one hδ S hcover w).trans (le_abs_self _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationLabels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upward regularization labels in arbitrary dimension

The label-preservation argument applies to all-dimensional dyadic paths.
Each extension retains or removes a whole previous child group.
-/

namespace Falconer.Regularization

variable {d : ℕ}

theorem labeledChildren_eq {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) (hf : f p = f q) :
    labeledChildren L f a b p = labeledChildren L f a b q := by
  classical
  simp only [labeledChildren, ha, hf]

theorem labeledChildren_nonempty {L : Finset (CellPath d)} (f : CellPath d → List ℕ)
    (a b : ℕ) {p : CellPath d} (hp : p ∈ L) :
    (labeledChildren L f a b p).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr ⟨p, by simp [hp]⟩

theorem extendLabel_old {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (h : extendLabel L a b f p = extendLabel L a b f q) :
    f p = f q := (List.cons.inj h).2

theorem extendLabel_local {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) :
    extendLabel L a b f p = extendLabel L a b f q ↔ f p = f q := by
  constructor
  · exact extendLabel_old
  · intro hf
    simp only [extendLabel, labeledChildren_eq ha hf, hf]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationCardinality
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent counts for regularization labels

A selected-depth gap of length b-a has at most 2^(d*(b-a))
children, so its logarithmic count bin has d*(b-a)+1 possibilities.
The number of final labels is polynomial in terminal depth when the
number of selected blocks is fixed.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem labeledChildren_subset_extensions {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) :
    labeledChildren L f a b p ⊆ (cubePaths d (b-a)).image (fun q => p.take a ++ q) := by
  classical
  intro c hc
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hq,ha,_⟩ := Finset.mem_filter.mp hq
  have hlen : q.length = N := (mem_cubePaths d N q).mp (hL hq)
  refine Finset.mem_image.mpr ⟨(q.take b).drop a, ?_, ?_⟩
  · simp only [mem_cubePaths, List.length_drop, List.length_take, hlen,
      Nat.min_eq_left hbN]
  · have he := List.take_append_drop a (q.take b)
    simpa only [List.take_take, Nat.min_eq_left hab, ha] using he

theorem labeledChildren_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : (labeledChildren L f a b p).card ≤ 2 ^ (d*(b-a)) :=
  (Finset.card_le_card (labeledChildren_subset_extensions hab hbN hL f p)).trans
    (Finset.card_image_le.trans_eq (card_cubePaths d (b-a)))

theorem child_bin_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : Nat.log 2 (labeledChildren L f a b p).card ≤ d*(b-a) := by
  have hc := labeledChildren_card_le hab hbN hL f p
  have := Nat.log_mono_right (b := 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2)] using this

theorem extendLabel_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ) :
    (L.image (extendLabel L a b f)).card ≤ (d*(b-a)+1) * (L.image f).card := by
  classical
  let S := (Finset.range (d*(b-a)+1)).product (L.image f)
  have hs : L.image (extendLabel L a b f) ⊆ S.image (fun z => z.1 :: z.2) := by
    intro T hT
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨(Nat.log 2 (labeledChildren L f a b p).card, f p),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (child_bin_le hab hbN hL f p)),
        Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩,rfl⟩
  calc
    _ ≤ (S.image (fun z => z.1 :: z.2)).card := Finset.card_le_card hs
    _ ≤ S.card := Finset.card_image_le
    _ = _ := by simp [S]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationClasses
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regularization classes on the original all-dimensional dyadic tree

Classes are literal disjoint unions of half-open leaves. The measure
identities and the discarded mass bounds hold for the original law.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem leafUnion_measurable (Q : DyadicCube d) (L : Finset (CellPath d)) :
    MeasurableSet (leafUnion Q L) :=
  Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

theorem leafUnion_subset (Q : DyadicCube d) (_hQ : 0 < Q.side)
    (L : Finset (CellPath d)) : leafUnion Q L ⊆ Q.carrier := by
  intro z hz
  obtain ⟨p,_,hp⟩ := mem_iUnion₂.mp hz
  exact Q.descendant_subset p hp

theorem leafUnion_disjoint (Q : DyadicCube d) (_hQ : 0 < Q.side) {N : ℕ}
    {L T : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (hT : T ⊆ cubePaths d N) (h : Disjoint L T) :
    Disjoint (leafUnion Q L) (leafUnion Q T) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp hz
  obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz'
  have hne : p ≠ q := by
    intro he; subst q; exact Finset.disjoint_left.mp h hp hq
  exact Set.disjoint_left.mp (Q.descendants_disjoint
    ((mem_cubePaths _ _ _).mp (hL hp) |>.trans ((mem_cubePaths _ _ _).mp (hT hq)).symm)
    hne) hzp hzq

theorem measure_leafUnion (Q : DyadicCube d) (_hQ : 0 < Q.side) (μ : Measure (Space d))
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) :
    μ (leafUnion Q L) = ∑ p ∈ L, μ (Q.descendant p).carrier := by
  apply measure_biUnion_finset
  · intro p hp q hq hne
    exact Q.descendants_disjoint
      (((mem_cubePaths _ _ _).mp (hL hp)).trans ((mem_cubePaths _ _ _).mp (hL hq)).symm)
      hne
  · intro p _; exact (Q.descendant p).measurable

theorem discarded_leaves_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N : ℕ) (t : ℝ≥0∞) :
    μ (leafUnion Q (cubePaths d N \ retainedLeaves Q μ N t)) ≤ (2 : ℝ≥0∞)^(d*N) * t := by
  classical
  rw [measure_leafUnion Q hQ μ Finset.sdiff_subset]
  calc
    _ ≤ ∑ _p ∈ cubePaths d N \ retainedLeaves Q μ N t, t := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_sdiff.mp hp
      have : ¬ t ≤ μ (Q.descendant p).carrier := by
        intro ht
        exact hp'.2 (Finset.mem_filter.mpr ⟨hp'.1,ht⟩)
      exact (lt_of_not_ge this).le
    _ ≤ (2 : ℝ≥0∞)^(d*N) * t := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq (card_cubePaths d N))

theorem classLeaves_disjoint (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (classLeaves L f T) (classLeaves L f U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)

theorem discarded_classes_mass (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (f : CellPath d → List ℕ)
    (t : ℝ≥0∞) :
    μ (⋃ T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t),
      leafUnion Q (classLeaves L f T)) ≤ ((L.image f).card : ℝ≥0∞) * t := by
  classical
  calc
    _ ≤ ∑ T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t),
        μ (leafUnion Q (classLeaves L f T)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _T ∈ (L.image f).filter (fun T => classMeasure Q μ L f T univ < t), t := by
      apply Finset.sum_le_sum
      intro T hT
      simpa only [classMeasure, Measure.restrict_apply_univ] using (Finset.mem_filter.mp hT).2.le
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_left
      exact_mod_cast (Finset.card_filter_le (s := L.image f)
        (fun T => classMeasure Q μ L f T univ < t))

theorem normalizedClass_probability (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (L : Finset (CellPath d))
    (f : CellPath d → List ℕ) (T : List ℕ)
    (h : classMeasure Q μ L f T univ ≠ 0) :
    IsProbabilityMeasure (normalizedClass Q μ L f T) := by
  constructor
  simp only [normalizedClass, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel h
  simp only [classMeasure, Measure.restrict_apply_univ]
  exact measure_ne_top _ _

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LeafMassBins
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original leaf mass bins with the dimension-dependent cutoff -/

namespace Falconer.Regularization
open MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem massBinCandidates_nonempty {N : ℕ} {w : ℝ}
    (hw : 1 ≤ (2:ℝ)^((d+2)*N)*w) : (massBinCandidates d N w).Nonempty := by
  classical
  exact ⟨0,by simp [massBinCandidates,hw]⟩

theorem leafMassBin_le (N : ℕ) (w : ℝ) : leafMassBin d N w ≤ (d+2)*N := by
  classical
  unfold leafMassBin
  split_ifs with h
  · exact Nat.le_of_lt_succ (Finset.mem_range.mp
      (Finset.mem_filter.mp ((massBinCandidates d N w).max'_mem h)).1)
  · omega

theorem leafMassBin_lower {N : ℕ} {w : ℝ} (hw : 1 ≤ (2:ℝ)^((d+2)*N)*w) :
    (2:ℝ)^(leafMassBin d N w) ≤ (2:ℝ)^((d+2)*N)*w := by
  classical
  unfold leafMassBin
  rw [dite_eq_left (massBinCandidates_nonempty hw)]
  exact (Finset.mem_filter.mp ((massBinCandidates d N w).max'_mem (massBinCandidates_nonempty hw))).2

theorem leafMassBin_upper {N : ℕ} {w : ℝ} (hw : w ≤ 1) :
    (2:ℝ)^((d+2)*N)*w < (2:ℝ)^(leafMassBin d N w+1) := by
  classical
  by_cases hk : leafMassBin d N w < (d+2)*N
  · by_contra h
    have hm : leafMassBin d N w+1 ∈ massBinCandidates d N w := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),not_lt.mp h⟩
    have hh : leafMassBin d N w+1 ≤ leafMassBin d N w := by
      conv_rhs => rw [leafMassBin, dite_eq_left ⟨_,hm⟩]
      exact Finset.le_max' _ _ hm
    omega
  · have he : leafMassBin d N w = (d+2)*N := by have := leafMassBin_le (d := d) N w; omega
    rw [he, pow_succ]
    have hp : 0 < (2:ℝ)^((d+2)*N) := by positivity
    nlinarith

theorem leafBinEndpoint_pos (N k : ℕ) : 0 < leafBinEndpoint d N k := by
  unfold leafBinEndpoint; positivity

theorem leaf_mass_bin_bounds {N : ℕ} {w : ℝ}
    (hlo : 1 ≤ (2:ℝ)^((d+2)*N)*w) (hhi : w ≤ 1) :
    leafBinEndpoint d N (leafMassBin d N w) ≤ w ∧
      w < 2 * leafBinEndpoint d N (leafMassBin d N w) := by
  have hp : 0 < (2:ℝ)^((d+2)*N) := by positivity
  constructor
  · exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using leafMassBin_lower hlo)
  · have hu := leafMassBin_upper (d := d) (N := N) hhi
    rw [pow_succ] at hu
    unfold leafBinEndpoint
    rw [← mul_div_assoc]
    exact (lt_div_iff₀ hp).mpr (by simpa only [mul_comm] using hu)

theorem sourceLeafLabel_card_le (Q : DyadicCube d) (μ : Measure (Space d)) (N : ℕ)
    (L : Finset (CellPath d)) : (L.image (sourceLeafLabel Q μ N)).card ≤ (d+2)*N+1 := by
  classical
  have hs : L.image (sourceLeafLabel Q μ N) ⊆
      (Finset.range ((d+2)*N+1)).image (fun k => [k]) := by
    intro T hT
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨leafMassBin d N (μ (Q.descendant p).carrier).toReal,
      Finset.mem_range.mpr (by have := leafMassBin_le (d := d) N (μ (Q.descendant p).carrier).toReal; omega),rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

theorem retained_leaf_mass_bin_bounds (Q : DyadicCube d) (μ : Measure (Space d))
    [IsProbabilityMeasure μ] (N : ℕ) {p : CellPath d}
    (hp : p ∈ retainedLeaves Q μ N ((2:ℝ≥0∞)^((d+2)*N))⁻¹) :
    let w := (μ (Q.descendant p).carrier).toReal
    leafBinEndpoint d N (leafMassBin d N w) ≤ w ∧ w < 2*leafBinEndpoint d N (leafMassBin d N w) := by
  have hm := (Finset.mem_filter.mp hp).2
  have ht := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at ht
  have hp : 0 < (2:ℝ)^((d+2)*N) := by positivity
  apply leaf_mass_bin_bounds
  · exact (inv_le_iff_one_le_mul₀' hp).mp ht
  · have hh : μ (Q.descendant p).carrier ≤ 1 := prob_le_one
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.one_ne_top).mpr hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockRegularization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All-dimensional block regularization

The upward labels preserve complete child groups at every selected depth.
Count bins cost d*N+1 possibilities and leaf mass bins cost (d+2)*N+1.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem blockDepth_antitone (N B : ℕ) : Antitone (blockDepth N B) := by
  intro i j hij
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right B hij) N

theorem blockDepth_terminal (N : ℕ) {B : ℕ} (hB : 0 < B) :
    blockDepth N B (N/B+1) = 0 := by
  have h := Nat.lt_mul_div_succ N hB
  simp only [blockDepth]
  rw [Nat.mul_comm] at h
  omega

theorem blockLabel_old (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i j : ℕ} (hij : i ≤ j) {p q : CellPath d}
    (he : blockLabel L N B f j p = blockLabel L N B f j q) :
    blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact he
  | succ j ih =>
    by_cases heq : i = j+1
    · simpa only [heq] using he
    · exact ih (by omega) (extendLabel_old he)

theorem blockLabel_local (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i j a : ℕ} (hij : i ≤ j) (ha : blockDepth N B i ≤ a)
    {p q : CellPath d} (hpq : p.take a = q.take a) :
    blockLabel L N B f j p = blockLabel L N B f j q ↔
      blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; rfl
    · have hji : i ≤ j := by omega
      rw [blockLabel, extendLabel_local (take_eq_of_take_eq
        ((blockDepth_antitone N B (by omega : i ≤ j+1)).trans ha) hpq)]
      exact ih hji

theorem block_final_children (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i K : ℕ} (hi : i < K) (p : CellPath d) :
    labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p =
    labeledChildren L (blockLabel L N B f i)
      (blockDepth N B (i+1)) (blockDepth N B i) p := by
  classical
  apply congrArg (Finset.image (List.take (blockDepth N B i)))
  apply Finset.filter_congr
  intro q _
  constructor
  · rintro ⟨ha,hf⟩
    exact ⟨ha,blockLabel_old L N B f (by omega) hf⟩
  · rintro ⟨ha,hf⟩
    refine ⟨ha,(blockLabel_local L N B f (by omega : i+1 ≤ K) le_rfl ha).mpr ?_⟩
    exact (extendLabel_local ha).mpr hf

theorem block_final_bin_eq (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i K : ℕ} (hi : i < K) {p q : CellPath d}
    (hclass : blockLabel L N B f K p = blockLabel L N B f K q) :
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p).card =
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) q).card := by
  rw [block_final_children L N B f hi,block_final_children L N B f hi]
  exact (List.cons.inj (blockLabel_old L N B f (by omega : i+1 ≤ K) hclass)).1

theorem blockLabel_card_le {L : Finset (CellPath d)} {N : ℕ} (hL : L ⊆ cubePaths d N)
    (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ) :
    (L.image (blockLabel L N B f K)).card ≤ (d*N+1)^K * (L.image f).card := by
  classical
  induction K with
  | zero => simp [blockLabel]
  | succ K ih =>
    have hs := extendLabel_card_le (blockDepth_antitone N B (Nat.le_succ K))
      (Nat.sub_le N (K*B)) hL (blockLabel L N B f K)
    have hb : d*(blockDepth N B K-blockDepth N B (K+1))+1 ≤ d*N+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left d ((Nat.sub_le _ _).trans (Nat.sub_le N (K*B)))) 1
    calc
      _ ≤ (d*N+1) * (L.image (blockLabel L N B f K)).card :=
        hs.trans (Nat.mul_le_mul_right _ hb)
      _ ≤ (d*N+1)*((d*N+1)^K*(L.image f).card) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ac_rfl

theorem regularization_label_count (Q : DyadicCube d) (μ : MeasureTheory.Measure (Space d))
    (N B : ℕ) :
    ((regularizationLeaves Q μ N).image (regularizationLabel Q μ N B)).card ≤
      (d*N+1)^(N/B+1) * ((d+2)*N+1) := by
  classical
  exact (blockLabel_card_le (Finset.filter_subset _ _) B (sourceLeafLabel Q μ N) _).trans
    (Nat.mul_le_mul_left _ (sourceLeafLabel_card_le Q μ N _))

theorem regularization_label_mass_bin (Q : DyadicCube d) (μ : MeasureTheory.Measure (Space d))
    (N B : ℕ) {p q : CellPath d}
    (h : regularizationLabel Q μ N B p = regularizationLabel Q μ N B q) :
    leafMassBin d N (μ (Q.descendant p).carrier).toReal =
      leafMassBin d N (μ (Q.descendant q).carrier).toReal := by
  have := blockLabel_old (regularizationLeaves Q μ N) N B (sourceLeafLabel Q μ N)
    (Nat.zero_le (N/B+1)) h
  exact List.singleton_inj.mp this

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Selecting the regular classes with their original masses

Classes are disjoint unions of original leaves. Discarding small leaves
costs 2^(-2N), and discarding small classes costs their number times the
class threshold. No lower density of the original law is required.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularizationSet_measurable (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) : MeasurableSet (regularizationSet Q μ N B T) :=
  leafUnion_measurable Q _

theorem regularizationIndex_card (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) :
    (regularizationIndex Q μ N B t).card ≤ (d*N+1)^(N/B+1)*((d+2)*N+1) :=
  (Finset.card_filter_le _ _).trans (regularization_label_count Q μ N B)

theorem regularizationSet_disjoint (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) {T U : List ℕ} (h : T ≠ U) :
    Disjoint (regularizationSet Q μ N B T) (regularizationSet Q μ N B U) :=
  leafUnion_disjoint Q hQ
    (fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
    (fun _ hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
    (classLeaves_disjoint _ _ h)

theorem regularizationSet_mass (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) {T : List ℕ} (hT : T ∈ regularizationIndex Q μ N B t) :
    t ≤ μ (regularizationSet Q μ N B T) := by
  simpa only [regularizationSet,classMeasure,Measure.restrict_apply_univ] using (Finset.mem_filter.mp hT).2

theorem regularization_small_leaves_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N : ℕ) :
    μ (leafUnion Q (cubePaths d N \ regularizationLeaves Q μ N)) ≤ ((2 : ℝ≥0∞)^(2*N))⁻¹ := by
  apply (discarded_leaves_mass Q hQ μ N ((2 : ℝ≥0∞)^((d+2)*N))⁻¹).trans_eq
  rw [Nat.add_mul,pow_add,ENNReal.mul_inv (by simp) (by simp),← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp),one_mul]

theorem regularization_discarded_mass (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (t : ℝ≥0∞) :
    μ (Q.carrier \ ⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T) ≤
      ((2 : ℝ≥0∞)^(2*N))⁻¹ + ((d*N+1)^(N/B+1)*((d+2)*N+1) : ℕ)*t := by
  let L := regularizationLeaves Q μ N
  let f := regularizationLabel Q μ N B
  let bad := (L.image f).filter (fun T => classMeasure Q μ L f T univ < t)
  have hsub : (Q.carrier \ ⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T) ⊆
      leafUnion Q (cubePaths d N \ L) ∪ ⋃ T ∈ bad, leafUnion Q (classLeaves L f T) := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth N hx.1
    by_cases hpL : p ∈ L
    · have hf : f p ∈ L.image f := Finset.mem_image.mpr ⟨p,hpL,rfl⟩
      by_cases hb : classMeasure Q μ L f (f p) univ < t
      · exact Or.inr (mem_iUnion₂.mpr ⟨f p,Finset.mem_filter.mpr ⟨hf,hb⟩,
          mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hpL,rfl⟩,hxp⟩⟩)
      · have hi : f p ∈ regularizationIndex Q μ N B t :=
          Finset.mem_filter.mpr ⟨hf,le_of_not_gt hb⟩
        exact (hx.2 (mem_iUnion₂.mpr ⟨f p,hi,
          mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hpL,rfl⟩,hxp⟩⟩)).elim
    · exact Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hpL⟩,hxp⟩)
  apply (measure_mono hsub).trans (measure_union_le _ _ |>.trans ?_)
  apply add_le_add (regularization_small_leaves_mass Q hQ μ N)
  dsimp only [bad]
  apply (discarded_classes_mass Q μ L f t).trans
  exact mul_le_mul' (by exact_mod_cast regularization_label_count Q μ N B) le_rfl

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial class count and discarded mass in every dimension -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularization_count_polynomial (Q : DyadicCube d) (μ : Measure (Space d))
    {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N) (t : ℝ≥0∞) :
    (regularizationIndex Q μ N (N/H) t).card ≤ N^(4*H+2) := by
  have hN : 1 ≤ N := by omega
  have h₁ : d*N+1 ≤ N^2 := by nlinarith
  have h₂ : (d+2)*N+1 ≤ N^2 := by nlinarith
  have hb := (PlanarFalconer.division_blocks_control hH hNH).2
  calc
    _ ≤ (d*N+1)^(N/(N/H)+1)*((d+2)*N+1) := regularizationIndex_card Q μ N (N/H) t
    _ ≤ (N^2)^(2*H)*N^2 := Nat.mul_le_mul
      ((Nat.pow_le_pow_left h₁ _).trans (Nat.pow_le_pow_right (by positivity) hb)) h₂
    _ = N^(4*H+2) := by rw [← pow_mul,← pow_add]; congr 1; omega

theorem regularization_discarded_global (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (hcarry : μ Q.carrierᶜ = 0)
    {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N) (t : ℝ≥0∞) :
    μ (⋃ T ∈ regularizationIndex Q μ N (N/H) t, regularizationSet Q μ N (N/H) T)ᶜ ≤
      ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^(4*H+2):ℕ)*t := by
  let U := ⋃ T ∈ regularizationIndex Q μ N (N/H) t, regularizationSet Q μ N (N/H) T
  have hsub : Uᶜ ⊆ (Q.carrier \ U) ∪ Q.carrierᶜ := by
    intro x hx
    by_cases h : x ∈ Q.carrier
    · exact Or.inl ⟨h,hx⟩
    · exact Or.inr h
  have hc : (d*N+1)^(N/(N/H)+1)*((d+2)*N+1) ≤ N^(4*H+2) := by
    have hN : 1 ≤ N := by omega
    have h₁ : d*N+1 ≤ N^2 := by nlinarith
    have h₂ : (d+2)*N+1 ≤ N^2 := by nlinarith
    have hb := (PlanarFalconer.division_blocks_control hH hNH).2
    calc
      _ ≤ (N^2)^(2*H)*N^2 := Nat.mul_le_mul
        ((Nat.pow_le_pow_left h₁ _).trans (Nat.pow_le_pow_right (by positivity) hb)) h₂
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega
  calc
    _ ≤ μ (Q.carrier \ U) + μ Q.carrierᶜ := (measure_mono hsub).trans (measure_union_le _ _)
    _ = μ (Q.carrier \ U) := by rw [hcarry,add_zero]
    _ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + ((d*N+1)^(N/(N/H)+1)*((d+2)*N+1):ℕ)*t :=
      regularization_discarded_mass Q hQ μ N (N/H) t
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' (by exact_mod_cast hc) le_rfl)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixCounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional prefix counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem prefixFiber_zero (C : Finset (CellPath d)) : prefixFiber C 0 [] = C := by
  classical
  simp [prefixFiber]

theorem prefixFiber_leaf {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {p : CellPath d} (hp : p ∈ C) : prefixFiber C N p = {p} := by
  classical
  ext q
  have hlen {path : CellPath d} (hpath : path ∈ C) : path.length = N :=
    (mem_cubePaths d N path).mp (hC hpath)
  simp only [prefixFiber, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq,he⟩
    simpa only [← hlen hq, List.take_length] using he
  · intro he; subst q
    exact ⟨hp,by rw [← hlen hp,List.take_length]⟩

theorem prefixFiber_card_sum {C : Finset (CellPath d)} {a b : ℕ} (hab : a ≤ b)
    (P : CellPath d) :
    (prefixFiber C a P).card =
      ∑ c ∈ prefixChildren C a b P, (prefixFiber C b c).card := by
  classical
  rw [Finset.card_eq_sum_card_image (List.take b) (prefixFiber C a P)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [prefixFiber_parent_filter hab hc]

theorem prefixFiber_count_bounds {C : Finset (CellPath d)} {a b lo hi B : ℕ}
    (hab : a ≤ b) (P : CellPath d)
    (hbranch : B ≤ (prefixChildren C a b P).card ∧ (prefixChildren C a b P).card ≤ 2*B)
    (hchild : ∀ c ∈ prefixChildren C a b P,
      lo ≤ (prefixFiber C b c).card ∧ (prefixFiber C b c).card ≤ hi) :
    B*lo ≤ (prefixFiber C a P).card ∧ (prefixFiber C a P).card ≤ 2*B*hi := by
  classical
  rw [prefixFiber_card_sum hab]
  constructor
  · calc
      B*lo ≤ (prefixChildren C a b P).card*lo := Nat.mul_le_mul_right _ hbranch.1
      _ = ∑ _c ∈ prefixChildren C a b P, lo := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (hchild c hc).1)
  · calc
      _ ≤ ∑ _c ∈ prefixChildren C a b P, hi := Finset.sum_le_sum (fun c hc => (hchild c hc).2)
      _ = (prefixChildren C a b P).card*hi := by simp
      _ ≤ 2*B*hi := Nat.mul_le_mul_right _ hbranch.2

theorem prefixChildren_class_eq (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (a b : ℕ) {T : List ℕ} {p : CellPath d} (hp : p ∈ classLeaves L F T) :
    prefixChildren (classLeaves L F T) a b (p.take a) = labeledChildren L F a b p := by
  classical
  have hFp := (Finset.mem_filter.mp hp).2
  apply congrArg (Finset.image (List.take b))
  ext q
  simp only [prefixFiber, classLeaves, Finset.mem_filter, hFp]
  tauto

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockLeafCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional block-leaf counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem blockBin_pos (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : 0 < blockBin L F N B i p := by
  unfold blockBin; positivity

theorem blockProduct_pos (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : 0 < blockProduct L F N B i p := by
  exact Finset.prod_pos (fun j _ => blockBin_pos L F N B j p)

theorem blockClass_child_bounds (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {K i : ℕ} (hi : i < K) (p : CellPath d)
    {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B (i+1)))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockBin L F N B i p ≤ (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ∧
      (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ≤ 2*blockBin L F N B i p := by
  classical
  dsimp only
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  rw [prefixChildren_class_eq L _ _ _ hq]
  have hqL := (Finset.mem_filter.mp hq).1
  have hclass := (Finset.mem_filter.mp hq).2
  unfold blockBin
  rw [block_final_bin_eq L N B f hi hclass.symm]
  have hpos := Finset.card_pos.mpr (labeledChildren_nonempty
    (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) hqL)
  refine ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos), ?_⟩
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
    (labeledChildren L (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) q).card
  simpa only [pow_succ, Nat.mul_comm] using hu.le

theorem blockClass_leaf_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ) (p : CellPath d)
    {i : ℕ} (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p := by
  classical
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hC : C ⊆ cubePaths d N := fun q hq => hL (Finset.mem_filter.mp hq).1
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p
  change P ∈ C.image (List.take (blockDepth N B i)) at hP
  induction i generalizing P with
  | zero =>
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hlen : q.length = N := (mem_cubePaths _ _ _).mp (hC hq)
    simp only [blockDepth, Nat.zero_mul, Nat.sub_zero, ← hlen, List.take_length]
    rw [show q.length = N from hlen, prefixFiber_leaf hC hq]
    simp [blockProduct]
  | succ i ih =>
    have hb := blockClass_child_bounds L N B f (by omega : i < K) p hP
    have hc := prefixFiber_count_bounds (blockDepth_antitone N B (Nat.le_succ i)) P hb
      (fun c hc => ih (by omega) (prefixChildren_mem_image hc))
    dsimp only [blockProduct] at hc ⊢
    rw [Finset.prod_range_succ]
    constructor
    · simpa only [Nat.mul_comm] using hc.1
    · have hh := hc.2
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring

theorem blockClass_root_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    {B : ℕ} (hB : 0 < B) (f : CellPath d → List ℕ) {p : CellPath d} (hp : p ∈ L) :
    let K := N/B+1
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B K p ≤ C.card ∧ C.card ≤ 2^K * blockProduct L F N B K p := by
  classical
  have hpC : p ∈ classLeaves L (blockLabel L N B f (N/B+1)) (blockLabel L N B f (N/B+1) p) := by
    simp [classLeaves,hp]
  have hc := blockClass_leaf_count hL B f (N/B+1) p (le_refl (N/B+1))
    (P := []) (by rw [blockDepth_terminal N hB]; exact Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  simpa only [blockDepth_terminal N hB, prefixFiber_zero] using hc

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_PrefixMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional PrefixMass for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}

open Set MeasureTheory
open scoped ENNReal

theorem descendant_subset_take (Q : DyadicCube d) (_hQ : 0 < Q.side)
    (p : CellPath d) (a : ℕ) : (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  have he := Q.descendant_append (p.take a) (p.drop a)
  rw [List.take_append_drop] at he
  rw [he]
  exact (Q.descendant (p.take a)).descendant_subset _

theorem leafUnion_inter_prefix (Q : DyadicCube d) (hQ : 0 < Q.side)
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {P : CellPath d} (hP : P.length = a) :
    (Q.descendant P).carrier ∩ leafUnion Q C = leafUnion Q (prefixFiber C a P) := by
  classical
  ext z
  constructor
  · rintro ⟨hzP,hzC⟩
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hzC
    have hqN := (mem_cubePaths _ _ _).mp (hC hq)
    have hlen : (q.take a).length = P.length := by simp [List.length_take,hqN,ha,hP]
    have he : q.take a = P := by
      by_contra hne
      exact Set.disjoint_left.mp (Q.descendants_disjoint hlen hne)
        (descendant_subset_take Q hQ q a hzq) hzP
    exact mem_iUnion₂.mpr ⟨q,by simp [prefixFiber,hq,he],hzq⟩
  · intro hz
    obtain ⟨q,hq,hzq⟩ := mem_iUnion₂.mp hz
    obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
    refine ⟨?_,mem_iUnion₂.mpr ⟨q,hq,hzq⟩⟩
    rw [← he]
    exact descendant_subset_take Q hQ q a hzq

theorem restriction_prefix_mass (Q : DyadicCube d) (hQ : 0 < Q.side) (μ : Measure (Space d))
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {P : CellPath d} (hP : P.length = a) :
    (μ.restrict (leafUnion Q C)) (Q.descendant P).carrier =
      ∑ q ∈ prefixFiber C a P, μ (Q.descendant q).carrier := by
  rw [Measure.restrict_apply (Q.descendant P).measurable,
    leafUnion_inter_prefix Q hQ ha hC hP]
  exact measure_leafUnion Q hQ μ (fun q hq => hC (Finset.mem_filter.mp hq).1)

theorem restriction_prefix_mass_real (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {P : CellPath d} (hP : P.length = a) :
    ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal =
      ∑ q ∈ prefixFiber C a P, (μ (Q.descendant q).carrier).toReal := by
  rw [restriction_prefix_mass Q hQ μ ha hC hP, ENNReal.toReal_sum]
  intro q _
  exact measure_ne_top _ _

theorem restriction_prefix_mass_bounds (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N a : ℕ} (ha : a ≤ N) {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {P : CellPath d} (hP : P.length = a) {s : ℝ}
    (hm : ∀ q ∈ C, s ≤ (μ (Q.descendant q).carrier).toReal ∧
      (μ (Q.descendant q).carrier).toReal ≤ 2*s) :
    (prefixFiber C a P).card * s ≤
      ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal ∧
    ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal ≤
      (prefixFiber C a P).card * (2*s) := by
  rw [restriction_prefix_mass_real Q hQ μ ha hC hP]
  constructor
  · calc
      _ = ∑ _q ∈ prefixFiber C a P, s := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hm q (Finset.mem_filter.mp hq).1).1
  · calc
      _ ≤ ∑ _q ∈ prefixFiber C a P, 2*s :=
        Finset.sum_le_sum fun q hq => (hm q (Finset.mem_filter.mp hq).1).2
      _ = _ := by simp

theorem restriction_total_mass_real (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N) :
    (μ (leafUnion Q C)).toReal = ∑ q ∈ C, (μ (Q.descendant q).carrier).toReal := by
  rw [measure_leafUnion Q hQ μ hC, ENNReal.toReal_sum]
  intro q _; exact measure_ne_top _ _

theorem restriction_total_mass_bounds (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N) {s : ℝ}
    (hm : ∀ q ∈ C, s ≤ (μ (Q.descendant q).carrier).toReal ∧
      (μ (Q.descendant q).carrier).toReal ≤ 2*s) :
    C.card*s ≤ (μ (leafUnion Q C)).toReal ∧
      (μ (leafUnion Q C)).toReal ≤ C.card*(2*s) := by
  rw [restriction_total_mass_real Q hQ μ hC]
  constructor
  · calc
      _ = ∑ _q ∈ C, s := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hm q hq).1
  · calc
      _ ≤ ∑ _q ∈ C, 2*s := Finset.sum_le_sum fun q hq => (hm q hq).2
      _ = _ := by simp

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_RegularizedMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional RegularizedMass for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}

open MeasureTheory Set
open scoped ENNReal

theorem regularization_class_leaf_bounds (Q : DyadicCube d) (μ : Measure (Space d))
    [IsProbabilityMeasure μ] (N B : ℕ) {p : CellPath d}
    (_hp : p ∈ regularizationLeaves Q μ N) :
    let L := regularizationLeaves Q μ N
    let F := regularizationLabel Q μ N B
    let s := leafBinEndpoint d N (leafMassBin d N (μ (Q.descendant p).carrier).toReal)
    0 < s ∧ ∀ q ∈ classLeaves L F (F p),
      s ≤ (μ (Q.descendant q).carrier).toReal ∧ (μ (Q.descendant q).carrier).toReal ≤ 2*s := by
  refine ⟨leafBinEndpoint_pos _ _,?_⟩
  intro q hq
  obtain ⟨hq,hF⟩ := Finset.mem_filter.mp hq
  have hb := retained_leaf_mass_bin_bounds Q μ N hq
  have he := regularization_label_mass_bin Q μ N B hF
  dsimp only at hb ⊢
  rw [he] at hb
  exact ⟨hb.1,hb.2.le⟩

theorem ratio_bounds_of_mass_bounds {x t s u v C : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hC : 0 < C)
    (hx : u*s ≤ x ∧ x ≤ C*u*s) (ht : v*s ≤ t ∧ t ≤ C*v*s) :
    (u/v)/C ≤ x/t ∧ x/t ≤ C*(u/v) := by
  have htpos : 0 < t := (mul_pos hv hs).trans_le ht.1
  have hxn : 0 ≤ x := (mul_pos hu hs).le.trans hx.1
  constructor
  · have hh : (u*s)/(C*v*s) ≤ x/t := div_le_div₀ hxn hx.1 htpos ht.2
    rw [mul_div_mul_right _ _ hs.ne'] at hh
    simpa only [div_div, mul_comm C v] using hh
  · have hh : x/t ≤ (C*u*s)/(v*s) := div_le_div₀ (by positivity) hx.2 (mul_pos hv hs) ht.1
    simpa only [mul_div_mul_right _ _ hs.ne', mul_div_assoc] using hh

theorem regularization_grid_mass_bounds (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N : ℕ) {B : ℕ} (hB : 0 < B)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {i : ℕ} (hi : i ≤ N/B+1) {P : CellPath d}
    (hP : P ∈ (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p)).image (List.take (blockDepth N B i))) :
    let L := regularizationLeaves Q μ N
    let F := regularizationLabel Q μ N B
    let K := N/B+1
    let M := (blockProduct L F N B i p : ℝ) / (blockProduct L F N B K p : ℝ)
    let ρ := normalizedClass Q μ L F (F p)
    M/(2:ℝ)^(K+1) ≤ (ρ (Q.descendant P).carrier).toReal ∧
      (ρ (Q.descendant P).carrier).toReal ≤ (2:ℝ)^(K+1)*M := by
  classical
  let L := regularizationLeaves Q μ N
  let F := regularizationLabel Q μ N B
  let K := N/B+1
  let C := classLeaves L F (F p)
  let s := leafBinEndpoint d N (leafMassBin d N (μ (Q.descendant p).carrier).toReal)
  have hL : L ⊆ cubePaths d N := Finset.filter_subset _ _
  have hC : C ⊆ cubePaths d N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hleaf := regularization_class_leaf_bounds Q μ N B hp
  have hs : 0 < s := hleaf.1
  have hm : ∀ q ∈ C, s ≤ (μ (Q.descendant q).carrier).toReal ∧
      (μ (Q.descendant q).carrier).toReal ≤ 2*s := hleaf.2
  have hlen : P.length = blockDepth N B i := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hqN := (mem_cubePaths _ _ _).mp (hC hq)
    simp [List.length_take,hqN]
  have hc := blockClass_leaf_count hL B (sourceLeafLabel Q μ N) K p hi hP
  have hr := blockClass_root_count hL hB (sourceLeafLabel Q μ N) hp
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i*blockProduct L F N B i p at hc
  change blockProduct L F N B K p ≤ C.card ∧ C.card ≤ 2^K*blockProduct L F N B K p at hr
  have hmass := restriction_prefix_mass_bounds Q hQ μ (Nat.sub_le _ _) hC hlen hm
  have htotal := restriction_total_mass_bounds Q hQ μ hC hm
  have hpow : (2:ℝ)^i ≤ (2:ℝ)^K := by exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hi
  have hu : 0 < (blockProduct L F N B i p : ℝ) := by exact_mod_cast blockProduct_pos L F N B i p
  have hv : 0 < (blockProduct L F N B K p : ℝ) := by exact_mod_cast blockProduct_pos L F N B K p
  have hci : (blockProduct L F N B i p : ℝ) ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ (2:ℝ)^i*(blockProduct L F N B i p : ℝ) := by
    exact_mod_cast hc
  have hcr : (blockProduct L F N B K p : ℝ) ≤ C.card ∧
    (C.card : ℝ) ≤ (2:ℝ)^K*(blockProduct L F N B K p : ℝ) := by exact_mod_cast hr
  have hx : (blockProduct L F N B i p : ℝ)*s ≤
      ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal ∧
      ((μ.restrict (leafUnion Q C)) (Q.descendant P).carrier).toReal ≤
        (2:ℝ)^(K+1)*(blockProduct L F N B i p : ℝ)*s := by
    constructor
    · exact (mul_le_mul_of_nonneg_right hci.1 hs.le).trans hmass.1
    · have hc' := hci.2.trans (mul_le_mul_of_nonneg_right hpow hu.le)
      have hh := hmass.2.trans (mul_le_mul_of_nonneg_right hc' (by positivity : 0 ≤ 2*s))
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh
  have ht : (blockProduct L F N B K p : ℝ)*s ≤ (μ (leafUnion Q C)).toReal ∧
      (μ (leafUnion Q C)).toReal ≤ (2:ℝ)^(K+1)*(blockProduct L F N B K p : ℝ)*s := by
    constructor
    · exact (mul_le_mul_of_nonneg_right hcr.1 hs.le).trans htotal.1
    · have hh := htotal.2.trans (mul_le_mul_of_nonneg_right hcr.2 (by positivity : 0 ≤ 2*s))
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh
  have hh := ratio_bounds_of_mass_bounds hs hu hv (by positivity) hx ht
  dsimp only
  simpa only [normalizedClass, classMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv,
    mul_comm] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalOccupiedClasses
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positivity and occupied original prefixes of a normalized class -/

namespace Falconer.Regularization
variable {d : ℕ}
open MeasureTheory Set
open scoped ENNReal

theorem normalizedClass_real (Q : DyadicCube d) (μ : Measure (Space d))
    (L : Finset (CellPath d)) (F : CellPath d → List ℕ) (T : List ℕ) (S : Set (Space d)) :
    (normalizedClass Q μ L F T S).toReal =
      ((μ.restrict (leafUnion Q (classLeaves L F T))) S).toReal /
        (μ (leafUnion Q (classLeaves L F T))).toReal := by
  simp only [normalizedClass,classMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply_univ,ENNReal.toReal_mul,ENNReal.toReal_inv,div_eq_mul_inv,mul_comm]

theorem normalizedClass_occupied_prefix (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {N n : ℕ} (hn : n ≤ N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ) (T : List ℕ)
    {P : CellPath d} (hP : P.length = n)
    (hp : 0 < (normalizedClass Q μ L F T (Q.descendant P).carrier).toReal) :
    P ∈ (classLeaves L F T).image (List.take n) := by
  classical
  have hC : classLeaves L F T ⊆ cubePaths d N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hne : (prefixFiber (classLeaves L F T) n P).Nonempty := by
    by_contra he
    have hz : prefixFiber (classLeaves L F T) n P = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [normalizedClass_real,restriction_prefix_mass Q hQ μ hn hC hP,hz] at hp
    simp at hp
  obtain ⟨q,hq⟩ := hne
  obtain ⟨hq,he⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_image.mpr ⟨q,hq,he⟩

theorem regularization_class_positive (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N B : ℕ) {p : CellPath d}
    (hp : p ∈ regularizationLeaves Q μ N) :
    0 < (classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p) univ).toReal := by
  classical
  let L := regularizationLeaves Q μ N
  let F := regularizationLabel Q μ N B
  let C := classLeaves L F (F p)
  have hm := regularization_class_leaf_bounds Q μ N B hp
  have hpC : p ∈ C := Finset.mem_filter.mpr ⟨hp, rfl⟩
  have hC : C ⊆ cubePaths d N := fun q hq =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hcount : 0 < (C.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨p,hpC⟩
  have hh := restriction_total_mass_bounds Q hQ μ hC hm.2
  simpa only [classMeasure, Measure.restrict_apply_univ] using (mul_pos hcount hm.1).trans_le hh.1

theorem regularization_class_probability (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N B : ℕ) {p : CellPath d}
    (hp : p ∈ regularizationLeaves Q μ N) :
    IsProbabilityMeasure (normalizedClass Q μ (regularizationLeaves Q μ N)
      (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p)) := by
  apply normalizedClass_probability
  intro he
  have hh := regularization_class_positive Q hQ μ N B hp
  rw [he,ENNReal.toReal_zero] at hh
  exact (lt_irrefl 0) hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileInterpolation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Profiles with the correct all-dimensional slope

The logarithmic child counts are linearly interpolated. Their exact slope
bound is d/N; after rescaling the depth interval to [0,1] it is d.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem intervalRamp_increment {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    0 ≤ intervalRamp a b v - intervalRamp a b u ∧
      intervalRamp a b v - intervalRamp a b u ≤ v-u := by
  unfold intervalRamp
  simp only [min_def]
  split_ifs <;> constructor <;> linarith

theorem finiteRampProfile_continuous (d c : ℕ → ℝ) (K : ℕ) :
    Continuous (finiteRampProfile d c K) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((continuous_id.min continuous_const).sub
    (continuous_id.min continuous_const))

theorem intervalRamp_sum (d : ℕ → ℝ) (K : ℕ) (u : ℝ) :
    (∑ i ∈ Finset.range K, intervalRamp (d (i+1)) (d i) u) = min u (d 0)-min u (d K) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; unfold intervalRamp; ring

theorem finiteRampProfile_zero (d c : ℕ → ℝ) (K : ℕ) (hd : ∀ i, 0 ≤ d i) :
    finiteRampProfile d c K 0 = 0 := by
  simp [finiteRampProfile,intervalRamp, min_eq_left (hd _)]

theorem finiteRampProfile_increment (d c : ℕ → ℝ) (K : ℕ) {N C u v : ℝ}
    (hd : Antitone d) (h0 : d 0 = N) (hK : d K = 0)
    (hc : ∀ i < K, 0 ≤ c i ∧ c i ≤ C)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N) :
    0 ≤ finiteRampProfile d c K v - finiteRampProfile d c K u ∧
      finiteRampProfile d c K v - finiteRampProfile d c K u ≤ C*(v-u) := by
  have he : finiteRampProfile d c K v - finiteRampProfile d c K u =
      ∑ i ∈ Finset.range K, c i * (intervalRamp (d (i+1)) (d i) v -
        intervalRamp (d (i+1)) (d i) u) := by
    simp only [finiteRampProfile, ← Finset.sum_sub_distrib, mul_sub]
  rw [he]
  have hr (i : ℕ) := intervalRamp_increment (hd (Nat.le_succ i)) huv
  constructor
  · exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i (Finset.mem_range.mp hi)).1 (hr i).1
  · calc
      _ ≤ ∑ i ∈ Finset.range K, C * (intervalRamp (d (i+1)) (d i) v -
          intervalRamp (d (i+1)) (d i) u) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
          (hc i (Finset.mem_range.mp hi)).2 (hr i).1
      _ = C*(v-u) := by
        rw [← Finset.mul_sum,Finset.sum_sub_distrib,intervalRamp_sum,intervalRamp_sum,h0,hK]
        rw [min_eq_left hv,min_eq_right (hu.trans huv),min_eq_left (huv.trans hv),min_eq_right hu]
        ring

theorem blockSlope_bounds {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ) (B i : ℕ) (p : CellPath d) :
    0 ≤ blockSlope L F N B i p ∧ blockSlope L F N B i p ≤ (d:ℝ)/(N:ℝ) := by
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hd := blockDepth_antitone N B (Nat.le_succ i)
  have hd' : (blockDepth N B (i+1):ℝ) ≤ (blockDepth N B i:ℝ) := by exact_mod_cast hd
  have hb := child_bin_le hd (Nat.sub_le _ _) hL F p
  have hb' : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
      (blockDepth N B i) p).card:ℝ) ≤ (d:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
    have hbR : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
        (blockDepth N B i) p).card:ℝ) ≤ ((d*(blockDepth N B i-blockDepth N B (i+1)):ℕ):ℝ) := by
      exact_mod_cast hb
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hd] using hbR
  unfold blockSlope
  constructor
  · positivity
  · by_cases he : (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) = 0
    · rw [he,div_zero]; positivity
    · have hp : 0 < (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) := lt_of_le_of_ne (sub_nonneg.mpr hd') (Ne.symm he)
      apply (div_le_iff₀ hp).mpr
      apply (div_le_iff₀ hN').mpr
      have heq : (d:ℝ)/(N:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ))*(N:ℝ) =
          (d:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
        field_simp [hN'.ne']
      rw [heq]
      exact hb'

theorem regularizedProfile_continuous (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B K : ℕ) (p : CellPath d) : Continuous (regularizedProfile L F N B K p) :=
  finiteRampProfile_continuous _ _ _

theorem regularizedProfile_zero (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B K : ℕ) (p : CellPath d) : regularizedProfile L F N B K p 0 = 0 :=
  finiteRampProfile_zero _ _ _ (fun _ => Nat.cast_nonneg _)

theorem regularizedProfile_increment {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ) {B : ℕ} (hB : 0 < B)
    (p : CellPath d) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N) :
    0 ≤ regularizedProfile L F N B (N/B+1) p v - regularizedProfile L F N B (N/B+1) p u ∧
      regularizedProfile L F N B (N/B+1) p v - regularizedProfile L F N B (N/B+1) p u ≤
        (d:ℝ)*(v-u)/(N:ℝ) := by
  have hh := finiteRampProfile_increment (fun i => (blockDepth N B i:ℝ))
    (fun i => blockSlope L F N B i p) (N/B+1)
    (fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)) (by simp [blockDepth])
    (by simp [blockDepth_terminal N hB]) (fun i _ => blockSlope_bounds hN hL F B i p) hu huv hv
  simpa only [regularizedProfile, div_mul_eq_mul_div] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact logarithmic profile values at selected depths -/

namespace Falconer.Regularization
variable {d : ℕ}

theorem intervalRamp_at_upper {a b : ℝ} (hab : a ≤ b) : intervalRamp a b b = b-a := by
  simp [intervalRamp,min_eq_right hab]

theorem intervalRamp_at_lower {a b : ℝ} (hab : a ≤ b) : intervalRamp a b a = 0 := by
  simp [intervalRamp,min_eq_left hab]

theorem intervalRamp_of_le {a b u : ℝ} (hab : a ≤ b) (hu : u ≤ a) : intervalRamp a b u = 0 := by
  simp [intervalRamp,min_eq_left hu,min_eq_left (hu.trans hab)]

theorem intervalRamp_of_ge {a b u : ℝ} (hab : a ≤ b) (hu : b ≤ u) : intervalRamp a b u = b-a := by
  simp [intervalRamp,min_eq_right hu,min_eq_right (hab.trans hu)]

theorem finiteRampProfile_block_difference (d c : ℕ → ℝ) (hd : Antitone d)
    {K i : ℕ} (hi : i < K) :
    finiteRampProfile d c K (d i) - finiteRampProfile d c K (d (i+1)) =
      c i*(d i-d (i+1)) := by
  classical
  simp only [finiteRampProfile, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [intervalRamp_at_upper (hd (Nat.le_succ i)), intervalRamp_at_lower (hd (Nat.le_succ i))]
    ring
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [intervalRamp_of_le (hd (Nat.le_succ j)) (hd (by omega : j+1 ≤ i)),
        intervalRamp_of_le (hd (Nat.le_succ j)) (hd (by omega : j+1 ≤ i+1))]
      ring
    · rw [intervalRamp_of_ge (hd (Nat.le_succ j)) (hd (by omega : i ≤ j)),
        intervalRamp_of_ge (hd (Nat.le_succ j)) (hd (by omega : i+1 ≤ j))]
      ring
  · intro h; exact (h (Finset.mem_range.mpr hi)).elim

theorem finiteRampProfile_knots_telescope (d c : ℕ → ℝ) (hd : Antitone d)
    {K i : ℕ} (hi : i ≤ K) :
    (∑ j ∈ Finset.range i, c j*(d j-d (j+1))) =
      finiteRampProfile d c K (d 0) - finiteRampProfile d c K (d i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ,ih (by omega)]
    rw [← finiteRampProfile_block_difference d c hd (by omega : i < K)]
    ring

theorem blockSlope_mul_gap_grid {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (B i : ℕ) (p : CellPath d) :
    blockSlope L F N B i p * ((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) =
      (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card:ℝ)/(N:ℝ) := by
  have hd := blockDepth_antitone N B (Nat.le_succ i)
  have hb := child_bin_le hd (Nat.sub_le _ _) hL F p
  by_cases he : (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) = 0
  · have he' : blockDepth N B i = blockDepth N B (i+1) := by exact_mod_cast sub_eq_zero.mp he
    have hk : Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card = 0 := by
      exact Nat.eq_zero_of_le_zero (hb.trans_eq (by rw [he',Nat.sub_self,Nat.mul_zero]))
    simp [blockSlope,hk]
  · unfold blockSlope
    exact div_mul_cancel₀ _ he

theorem blockProduct_eq_pow (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : blockProduct L F N B i p = 2 ^ blockLogProduct L F N B i p := by
  unfold blockProduct blockBin blockLogProduct
  rw [← Finset.prod_pow_eq_pow_sum]

theorem regularizedProfile_grid {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) {B : ℕ} (hB : 0 < B) (p : CellPath d)
    {i : ℕ} (hi : i ≤ N/B+1) :
    regularizedProfile L F N B (N/B+1) p (blockDepth N B i) =
      ((blockLogProduct L F N B (N/B+1) p:ℝ)-(blockLogProduct L F N B i p:ℝ))/(N:ℝ) := by
  let d := fun i => (blockDepth N B i:ℝ)
  let c := fun i => blockSlope L F N B i p
  have hd : Antitone d := fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)
  have htel (j : ℕ) (hj : j ≤ N/B+1) := finiteRampProfile_knots_telescope d c hd hj
  have hsum (j : ℕ) : (∑ k ∈ Finset.range j, c k*(d k-d (k+1))) =
      (blockLogProduct L F N B j p:ℝ)/(N:ℝ) := by
    unfold c d
    simp only [blockSlope_mul_gap_grid hL F B _ p, ← Finset.sum_div, blockLogProduct, Nat.cast_sum]
  have hi' := htel i hi
  have hK := htel (N/B+1) le_rfl
  rw [hsum] at hi' hK
  have hz : finiteRampProfile d c (N/B+1) (d (N/B+1)) = 0 := by
    change regularizedProfile L F N B (N/B+1) p _ = 0
    rw [show d (N/B+1) = 0 by simp [d,blockDepth_terminal N hB], regularizedProfile_zero]
  rw [hz] at hK
  change finiteRampProfile d c (N/B+1) (d i) = _
  rw [sub_div]
  linarith

theorem regularizedProfile_reference_grid {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) {B : ℕ} (hB : 0 < B) (p : CellPath d)
    {i : ℕ} (hi : i ≤ N/B+1) :
    ((2:ℝ)^N) ^ (-regularizedProfile L F N B (N/B+1) p (blockDepth N B i)) =
      (blockProduct L F N B i p:ℝ)/(blockProduct L F N B (N/B+1) p:ℝ) := by
  rw [regularizedProfile_grid hL F hB p hi, blockProduct_eq_pow,blockProduct_eq_pow]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [← Real.rpow_natCast (2:ℝ) N, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ) * -(((blockLogProduct L F N B (N/B+1) p:ℝ)-(blockLogProduct L F N B i p:ℝ))/(N:ℝ)) =
      (blockLogProduct L F N B i p:ℝ)-(blockLogProduct L F N B (N/B+1) p:ℝ) := by field_simp; ring
  rw [he,Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_natCast,Real.rpow_natCast]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_IntermediateProfiles
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass-profile comparison at every depth in arbitrary dimension

The interpolation loss is (d+1)*lambda. The block depths satisfy the
same numerical bracketing as in the planar case.
-/

namespace Falconer.Regularization
variable {d : ℕ}
open MeasureTheory
open scoped ENNReal

theorem sourceClass_grid_comparison (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {i : ℕ} (hi : i ≤ N/B+1) {P : CellPath d}
    (hP : P ∈ (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p)).image (List.take (blockDepth N B i))) :
    (((2:ℝ)^N)^(-sourceProfile Q μ N B p (blockDepth N B i)))/(2:ℝ)^(N/B+2) ≤
      (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ∧
    (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ≤
      (2:ℝ)^(N/B+2)*(((2:ℝ)^N)^(-sourceProfile Q μ N B p (blockDepth N B i))) := by
  classical
  rw [sourceProfile,regularizedProfile_reference_grid hN (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) hB p hi]
  exact regularization_grid_mass_bounds Q hQ μ N hB hp hi hP

theorem profile_bracket_mass_bound {R C lam m₀ mₙ m₁ x₀ xₙ x₁ : ℝ}
    (hR : 1 ≤ R) (hC : 0 < C) (hCL : C ≤ R^lam)
    (hml : m₁-mₙ ≤ (d:ℝ)*lam) (hmu : mₙ-m₀ ≤ (d:ℝ)*lam)
    (hlo : R^(-m₁)/C ≤ x₁) (hhi : x₀ ≤ C*R^(-m₀))
    (hxl : x₁ ≤ xₙ) (hxu : xₙ ≤ x₀) :
    R^(-((d:ℝ)+1)*lam)*R^(-mₙ) ≤ xₙ ∧ xₙ ≤ R^(((d:ℝ)+1)*lam)*R^(-mₙ) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  constructor
  · apply le_trans ?_ (hlo.trans hxl)
    apply (le_div_iff₀ hC).mpr
    calc
      R^(-((d:ℝ)+1)*lam)*R^(-mₙ)*C ≤ R^(-((d:ℝ)+1)*lam)*R^(-mₙ)*R^lam :=
        mul_le_mul_of_nonneg_left hCL (by positivity)
      _ = R^(-(d:ℝ)*lam-mₙ) := by rw [← Real.rpow_add hRp,← Real.rpow_add hRp]; congr 1; ring
      _ ≤ R^(-m₁) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  · apply le_trans (hxu.trans hhi)
    calc
      C*R^(-m₀) ≤ R^lam*R^(-m₀) := mul_le_mul_of_nonneg_right hCL (by positivity)
      _ = R^(lam-m₀) := by rw [← Real.rpow_add hRp]; rfl
      _ ≤ R^(((d:ℝ)+1)*lam-mₙ) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
      _ = R^(((d:ℝ)+1)*lam)*R^(-mₙ) := Real.rpow_add hRp _ _

theorem sourceProfile_short_increment (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d) {lam u v : ℝ}
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N)
    (hshort : v-u ≤ B) :
    sourceProfile Q μ N B p v-sourceProfile Q μ N B p u ≤ (d:ℝ)*lam := by
  classical
  have hh := regularizedProfile_increment hN (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) hB p hu huv hv
  apply hh.2.trans
  apply (div_le_iff₀ (by exact_mod_cast hN : 0 < (N:ℝ))).mpr
  have hmul₁ := mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg d)
  have hmul₂ := mul_le_mul_of_nonneg_left hshort (Nat.cast_nonneg d)
  nlinarith

theorem sourceClass_all_depth_comparison (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {n : ℕ} (hn : n ≤ N) {P : CellPath d}
    (hP : P ∈ (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p)).image (List.take n)) :
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) ≤
      (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ∧
    (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) := by
  classical
  let i := (N-n)/B
  have hb := PlanarFalconer.blockDepth_brackets hn hB
  change i < N/B+1 ∧ blockDepth N B (i+1) ≤ n ∧ n ≤ blockDepth N B i ∧
    blockDepth N B i-n ≤ B ∧ n-blockDepth N B (i+1) ≤ B at hb
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  let ρ := sourceClass Q μ N B p
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hQ μ N B hp
  have hgp := sourceClass_grid_comparison Q hQ μ hN hB hp (Nat.le_of_lt hb.1)
    (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hgm := sourceClass_grid_comparison Q hQ μ hN hB hp (by omega : i+1 ≤ N/B+1)
    (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hmono₁ : ρ (Q.descendant (q.take (blockDepth N B i))).carrier ≤
      ρ (Q.descendant (q.take n)).carrier := by
    apply measure_mono
    have hh := descendant_subset_take Q hQ (q.take (blockDepth N B i)) n
    simpa only [List.take_take,Nat.min_eq_left hb.2.2.1] using hh
  have hmono₀ : ρ (Q.descendant (q.take n)).carrier ≤
      ρ (Q.descendant (q.take (blockDepth N B (i+1)))).carrier := by
    apply measure_mono
    have hh := descendant_subset_take Q hQ (q.take n) (blockDepth N B (i+1))
    simpa only [List.take_take,Nat.min_eq_left hb.2.1] using hh
  have hml := sourceProfile_short_increment Q μ hN hB p hwidth
    (Nat.cast_nonneg n) (Nat.cast_le.mpr hb.2.2.1)
    (Nat.cast_le.mpr (Nat.sub_le N (i*B))) (by
      simpa only [Nat.cast_sub hb.2.2.1] using
        (show (((blockDepth N B i-n):ℕ):ℝ) ≤ (B:ℝ) by exact_mod_cast hb.2.2.2.1))
  have hmu := sourceProfile_short_increment Q μ hN hB p hwidth
    (Nat.cast_nonneg (blockDepth N B (i+1))) (Nat.cast_le.mpr hb.2.1) (Nat.cast_le.mpr hn) (by
      simpa only [Nat.cast_sub hb.2.1] using
        (show (((n-blockDepth N B (i+1)):ℕ):ℝ) ≤ (B:ℝ) by exact_mod_cast hb.2.2.2.2))
  exact profile_bracket_mass_bound (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    (by positivity) hlarge hml hmu hgp.1 hgm.2
    (ENNReal.toReal_mono (measure_ne_top ρ _) hmono₁)
    (ENNReal.toReal_mono (measure_ne_top ρ _) hmono₀)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileEnvelopes
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Profile lower bounds from the original mass law

An original s-ball estimate yields the lower profile bound after paying
for class normalization and the dimension-dependent interpolation loss.
-/

namespace Falconer.Regularization
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_occupied_comparison (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {n : ℕ} (hn : n ≤ N) {P : CellPath d} (hP : P.length = n)
    (hpos : 0 < sourceClass Q μ N B p (Q.descendant P).carrier) :
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) ≤
      (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ∧
    (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) := by
  classical
  have : IsProbabilityMeasure (sourceClass Q μ N B p) := regularization_class_probability Q hQ μ N B hp
  apply sourceClass_all_depth_comparison Q hQ μ hN hB hwidth hlarge hp hn
  apply normalizedClass_occupied_prefix Q hQ μ hn
    (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p) hP
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top (sourceClass Q μ N B p) _)

theorem normalizedClass_real_le (Q : DyadicCube d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (L : Finset (CellPath d)) (F : CellPath d → List ℕ) (T : List ℕ) {t : ℝ} (ht : 0 < t)
    (hmass : t ≤ (classMeasure Q μ L F T univ).toReal) (S : Set (Space d)) :
    (normalizedClass Q μ L F T S).toReal ≤ (μ S).toReal/t := by
  rw [normalizedClass_real]
  have hr : ((μ.restrict (leafUnion Q (classLeaves L F T))) S).toReal ≤ (μ S).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
  have hm : t ≤ (μ (leafUnion Q (classLeaves L F T))).toReal := by
    simpa only [classMeasure,Measure.restrict_apply_univ] using hmass
  exact div_le_div₀ ENNReal.toReal_nonneg hr ht hm

theorem sourceProfile_frostman_lower (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    (hmass : ((2:ℝ)^N)^(-lam) ≤
      (classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
        (regularizationLabel Q μ N B p) Set.univ).toReal)
    (hcell : ∀ n ≤ N, ∀ P : CellPath d, P.length = n →
      (μ (Q.descendant P).carrier).toReal ≤
        ((2:ℝ)^N)^lam * ((2:ℝ)^N)^(-s*(n:ℝ)/(N:ℝ)))
    {n : ℕ} (hn : n ≤ N) :
    s*(n:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N B p n := by
  classical
  let R : ℝ := (2:ℝ)^N
  have hR : 1 < R := one_lt_pow₀ (by norm_num : (1:ℝ) < 2) hN.ne'
  have hRp : 0 < R := (zero_lt_one.trans hR)
  have hpN : p.length = N := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
  have hPn : (p.take n).length = n := by simp [List.length_take,hpN,hn]
  have hpC : p ∈ classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p) := Finset.mem_filter.mpr ⟨hp, rfl⟩
  have hcomp := sourceClass_all_depth_comparison Q hQ μ hN hB hwidth hlarge hp hn
    (Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  have hnorm := normalizedClass_real_le Q μ (regularizationLeaves Q μ N)
    (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p)
    (Real.rpow_pos_of_pos hRp (-lam)) hmass (Q.descendant (p.take n)).carrier
  have hu := hnorm.trans (div_le_div_of_nonneg_right (hcell n hn (p.take n) hPn) (by positivity))
  have hpow : R^(-((d:ℝ)+1)*lam-sourceProfile Q μ N B p n) ≤ R^(2*lam-s*(n:ℝ)/(N:ℝ)) := by
    have hh := hcomp.1.trans hu
    change R^(-((d:ℝ)+1)*lam)*R^(-sourceProfile Q μ N B p n) ≤
      (R^lam*R^(-s*(n:ℝ)/(N:ℝ)))/R^(-lam) at hh
    rw [← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have he := (Real.rpow_le_rpow_left_iff hR).mp hpow
  nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FrostmanProfiles
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Frostman lower envelopes for the constructed all-dimensional profiles

The enclosing-ball constant is 2*sqrt d, and the numerical choice of block
length is independent of dimension.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_rpow_scale {N : ℕ} (hN : 0 < N) (j : ℕ) (s : ℝ) :
    ((2:ℝ)^N)^(-s*(j:ℝ)/(N:ℝ)) = (((2:ℝ)^j)^s)⁻¹ := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ)*(-s*(j:ℝ)/(N:ℝ)) = -((j:ℝ)*s) := by field_simp
  rw [he,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]

theorem dyadic_cell_frostman_bound (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {s C : ℝ}
    (hball : ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s))
    (p : CellPath d) :
    μ (Q.descendant p).carrier ≤ ENNReal.ofReal (C*(2*Real.sqrt d*(Q.descendant p).side)^s) := by
  have hside := Q.descendant_side_pos hQ p
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  apply (measure_mono (show (Q.descendant p).carrier ⊆
      ball (Q.descendant p).center (2*Real.sqrt d*(Q.descendant p).side) from ?_)).trans
    (hball _ _ (by positivity))
  intro x hx
  have hh := (Q.descendant p).dist_le hside.le hx ((Q.descendant p).center_mem hside)
  exact mem_ball.mpr (by nlinarith [mul_pos hsqrt hside])

theorem dyadic_cell_frostman_profile_bound (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] {s C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s))
    {N : ℕ} (hN : 0 < N) (p : CellPath d) :
    (μ (Q.descendant p).carrier).toReal ≤
      (C*(2*Real.sqrt d*Q.side)^s)*((2:ℝ)^N)^(-s*(p.length:ℝ)/(N:ℝ)) := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (dyadic_cell_frostman_bound hd Q hQ μ hball p)
  have hside := Q.descendant_side_pos hQ p
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ C*(2*Real.sqrt d*(Q.descendant p).side)^s)] at hh
  apply hh.trans_eq
  rw [Q.descendant_side,dyadic_rpow_scale hN]
  rw [show 2*Real.sqrt d*(Q.side/(2:ℝ)^p.length) =
    (2*Real.sqrt d*Q.side)/(2:ℝ)^p.length by ring,
    Real.div_rpow (by positivity) (by positivity)]
  ring

theorem retained_label_real_mass_lower (Q : DyadicCube d) (μ : Measure (Space d))
    [IsFiniteMeasure μ] {N B : ℕ} {p : CellPath d} {lam : ℝ}
    (hp : regularizationLabel Q μ N B p ∈ regularizationIndex Q μ N B
      (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    ((2:ℝ)^N)^(-lam) ≤ (classMeasure Q μ (regularizationLeaves Q μ N)
      (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p) univ).toReal := by
  have hm := regularizationSet_mass Q μ N B _ hp
  have hh := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simpa only [classMeasure,Measure.restrict_apply_univ,regularizationSet,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2:ℝ)^N)^(-lam))] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UnitProfiles
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The constructed d-Lipschitz profiles on the unit interval

This is the paper's normalization of the finite-tree profile. Its slope
bound is the ambient dimension d, and its values lie between zero and d.
-/

namespace Falconer.Regularization
open Set
variable {d : ℕ}

theorem unitProfile_continuous (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B : ℕ) (p : CellPath d) : Continuous (unitProfile L F N B p) :=
  (regularizedProfile_continuous L F N B (N/B+1) p).comp (continuous_const.mul continuous_id)

theorem unitProfile_zero (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B : ℕ) (p : CellPath d) : unitProfile L F N B p 0 = 0 := by
  simp only [unitProfile,mul_zero,regularizedProfile_zero]

theorem unitProfile_increment {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    0 ≤ unitProfile L F N B p v-unitProfile L F N B p u ∧
      unitProfile L F N B p v-unitProfile L F N B p u ≤ (d : ℝ)*(v-u) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm := regularizedProfile_increment hN hL F hB p
    (mul_nonneg hN0.le hu) (mul_le_mul_of_nonneg_left huv hN0.le)
    (by nlinarith : (N : ℝ)*v ≤ N)
  refine ⟨hm.1,hm.2.trans_eq ?_⟩
  field_simp

theorem unitProfile_monotoneOn {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) :
    MonotoneOn (unitProfile L F N B p) (Icc 0 1) := by
  intro u hu v hv huv
  exact sub_nonneg.mp (unitProfile_increment hN hB hL F p hu.1 huv hv.2).1

theorem unitProfile_lipschitzOn {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) :
    LipschitzOnWith (d : NNReal) (unitProfile L F N B p) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rcases le_total v u with hvu | huv
  · have hi := unitProfile_increment hN hB hL F p hv.1 hvu hu.2
    simpa only [Real.dist_eq,abs_of_nonneg hi.1,abs_of_nonneg (sub_nonneg.mpr hvu),
      NNReal.coe_natCast] using hi.2
  · have hi := unitProfile_increment hN hB hL F p hu.1 huv hv.2
    rw [dist_comm,Real.dist_eq,abs_of_nonneg hi.1,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [NNReal.coe_natCast,neg_sub] using hi.2

theorem unitProfile_range {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (p : CellPath d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    unitProfile L F N B p u ∈ Icc (0 : ℝ) (d : ℝ) := by
  have h := unitProfile_increment hN hB hL F p (u := 0) (v := u) (by rfl) hu.1 hu.2
  rw [unitProfile_zero,sub_zero,sub_zero] at h
  exact ⟨h.1,h.2.trans (mul_le_of_le_one_right (Nat.cast_nonneg d) hu.2)⟩

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationProperties
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit-scale profiles and conditional mass ratios of the original classes -/

namespace Falconer.Regularization
open MeasureTheory Set
variable {d : ℕ}

theorem sourceUnitProfile_at_depth (Q : DyadicCube d) (μ : Measure (Space d))
    {N : ℕ} (hN : 0 < N) (B : ℕ) (p : CellPath d) (j : ℕ) :
    sourceUnitProfile Q μ N B p ((j:ℝ)/N) = sourceProfile Q μ N B p j := by
  unfold sourceUnitProfile unitProfile sourceProfile
  congr 1
  field_simp

theorem sourceUnitProfile_properties (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d) :
    Continuous (sourceUnitProfile Q μ N B p) ∧
    sourceUnitProfile Q μ N B p 0 = 0 ∧
    MonotoneOn (sourceUnitProfile Q μ N B p) (Icc 0 1) ∧
    LipschitzOnWith (d : NNReal) (sourceUnitProfile Q μ N B p) (Icc 0 1) ∧
    ∀ u ∈ Icc (0:ℝ) 1, sourceUnitProfile Q μ N B p u ∈ Icc (0:ℝ) d := by
  have hL : regularizationLeaves Q μ N ⊆ cubePaths d N := Finset.filter_subset _ _
  exact ⟨unitProfile_continuous _ _ _ _ _,unitProfile_zero _ _ _ _ _,
    unitProfile_monotoneOn hN hB hL _ _,unitProfile_lipschitzOn hN hB hL _ _,
    fun _ hu => unitProfile_range hN hB hL _ _ hu⟩

theorem sourceUnitProfile_lower_from_grid (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    {s E : ℝ} (hs : 0 ≤ s)
    (hgrid : ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-E ≤ sourceProfile Q μ N B p j)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    s*u-E-s/N ≤ sourceUnitProfile Q μ N B p u := by
  have hNp : 0 < (N:ℝ) := by exact_mod_cast hN
  let j := Nat.floor ((N:ℝ)*u)
  have hfloor : (j:ℝ) ≤ (N:ℝ)*u := Nat.floor_le (mul_nonneg hNp.le hu.1)
  have hnext : (N:ℝ)*u < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have hj : j ≤ N := by
    exact_mod_cast hfloor.trans (mul_le_of_le_one_right hNp.le hu.2)
  have hju : (j:ℝ)/(N:ℝ) ≤ u := (div_le_iff₀ hNp).mpr (by simpa [mul_comm] using hfloor)
  have hj0 : 0 ≤ (j:ℝ)/(N:ℝ) := by positivity
  have hm := (sourceUnitProfile_properties Q μ hN hB p).2.2.1
    ⟨hj0,hju.trans hu.2⟩ hu hju
  rw [sourceUnitProfile_at_depth Q μ hN B p j] at hm
  have hsj := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ hNp).mpr (by simpa [mul_comm] using hnext.le)) hs
  have he : s*((j:ℝ)+1)/(N:ℝ) = s*(j:ℝ)/(N:ℝ)+s/N := by ring
  rw [← mul_div_assoc,he] at hsj
  linarith [hgrid j hj]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularClasses
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Regular classes of an original Frostman law in arbitrary dimension

This proves the application-level form of Lemma `reg:regularization`.
The classes are unions of the original half-open leaves.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_profile_data (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) {s lam : ℝ} (hs : 0 ≤ s)
    (hsmall : s/(N:ℝ) ≤ lam) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    (hgrid : ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N B p j) :
    RegularizedProfileData Q (sourceClass Q μ N B p) N s lam (sourceUnitProfile Q μ N B p) := by
  obtain ⟨hc,hz,hm,hl,hr⟩ := sourceUnitProfile_properties Q μ hN hB p
  refine ⟨regularization_class_probability Q hQ μ N B hp,hc,hz,hm,hl,hr,?_,?_⟩
  · intro j hj P hP hpos
    simpa only [sourceUnitProfile_at_depth Q μ hN B p j] using
      sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp hj hP hpos
  · intro u hu
    have hh := sourceUnitProfile_lower_from_grid Q μ hN hB p hs hgrid hu
    linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_StartingMeasures
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Starting measures in all dimensions

The published input is Frostman's lemma, Mattila, *Geometry of Sets and
Measures in Euclidean Spaces* (Cambridge, 1995), Theorem 8.8, p. 112.
Only compact sets above the critical half-dimensional threshold are used.
Selecting an exponent strictly between the threshold and the Hausdorff
dimension, and normalizing the nonzero finite measure, gives the exact
specialization below, stated as a hypothesis for the conditional argument.

The separation and restriction arguments are proved here in the original
ambient dimension. They do not use a projection of the distance set.
-/

namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

theorem noAtoms_of_frostman {d : ℕ} (μ : Measure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hb : FrostmanBallBound (μ : Measure (Space d)) s C) : NullSingletonClass μ := by
  constructor
  intro x
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C * r^s)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa only [Real.zero_rpow hs.ne', mul_zero, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb x r hr)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable sphere normalization with a fixed value at zero -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem normalizeToSphere_measurable (w₀ : Sphere d) :
    Measurable (normalizeToSphere w₀) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (by simp)
    measurable_const (measurable_id.norm.inv.smul measurable_id)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialSphereLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sphere-valued original radial laws, with a harmless diagonal value -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem originalRadialSphereLaw_apply (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (B : Set (Sphere d)) (hB : MeasurableSet B) :
    originalRadialSphereLaw w₀ ν G z B =
      ν {x | (z,x) ∈ G ∧ normalizeToSphere w₀ (x-z) ∈ B} := by
  have hm : Measurable (fun x : Space d => normalizeToSphere w₀ (x-z)) :=
    (normalizeToSphere_measurable w₀).comp (measurable_id.sub measurable_const)
  rw [originalRadialSphereLaw,Measure.map_apply hm hB,Measure.restrict_apply (hB.preimage hm)]
  congr 1
  ext x
  exact and_comm

theorem originalRadialSphereLaw_mass_le (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) :
    originalRadialSphereLaw w₀ ν G z Set.univ ≤ ν Set.univ := by
  rw [originalRadialSphereLaw_apply w₀ ν G z Set.univ MeasurableSet.univ]
  exact measure_mono (subset_univ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_EvenStartingCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original-pair starting cap estimate in even dimensions -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace ProjectedStartingPair
variable {d m : ℕ} {ζ : ProbabilityMeasure (Space d)} {s ε : ℝ}

theorem relation_measurable (p : ProjectedStartingPair ζ m s ε) :
    MeasurableSet p.relation :=
  Measure.isClosed_support.measurableSet.prod Measure.isClosed_support.measurableSet

theorem relation_mass (p : ProjectedStartingPair ζ m s ε) :
    ((p.left : Measure (Space d)).prod (p.right : Measure (Space d))) p.relation = 1 := by
  rw [relation,Measure.prod_prod]
  have hμ : (p.left : Measure (Space d)) (p.left : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  have hν : (p.right : Measure (Space d)) (p.right : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  rw [hμ,hν,mul_one]

end ProjectedStartingPair

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NormalizedCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized cap partition and its uniform derivative bounds

The normalization uses the same fixed smooth reciprocal for all radii.
On the sphere the covering bound makes it the exact reciprocal of the
positive bump sum.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) :
    (∀ w : Sphere d, ∑ c ∈ S, normalizedCap δ hδ S c w = 1) ∧
    (∀ c ∈ S, ∀ w : Sphere d, 0 ≤ normalizedCap δ hδ S c w ∧
      normalizedCap δ hδ S c w ≤ 1) ∧
    (∀ c ∈ S, ∀ x : Space d, normalizedCap δ hδ S c x ≠ 0 → ‖x-(c : Space d)‖ ≤ δ) := by
  have hrec (w : Sphere d) : capReciprocal δ hδ S w = (capDenominator δ hδ S w)⁻¹ := by
    have hg : capDenominator δ hδ S w ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w))
    apply mul_left_cancel₀ hg
    rw [capDenominator_mul_reciprocal hδ S hcover w,mul_inv_cancel₀ hg]
  refine ⟨?_,?_,?_⟩
  · intro w
    simpa only [normalizedCap,← Finset.sum_mul,capDenominator] using
      capDenominator_mul_reciprocal hδ S hcover w
  · intro c hc w
    have hb : capBump δ hδ c w ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc
    have hg : 0 < capDenominator δ hδ S w :=
      zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w)
    simp only [normalizedCap,hrec]
    exact ⟨mul_nonneg (capBump δ hδ c).nonneg (inv_nonneg.mpr hg.le),
      (mul_inv_le_iff₀ hg).mpr (by simpa only [one_mul] using hb)⟩
  · intro c _ x hx
    have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hm : x ∈ Metric.ball (c : Space d) δ := by
      change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
      rw [← (capBump δ hδ c).support_eq]
      exact hb
    exact (mem_ball_iff_norm.mp hm).le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NorthRotation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sending the prepared direction to the canonical north pole

An orthogonal reflection handles every equal-norm pair, including opposite
directions. Normalization and all cap distances commute with this fixed
linear isometry, so the original prepared cap can be transported exactly.
-/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem linearIsometryEquiv_normalize {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x : Space d) : normalize (e x) = e (normalize x) := by
  simp only [NormedSpace.normalize,e.norm_map,map_smul]

theorem linearIsometryEquiv_normalize_sub {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x y : Space d) : normalize (e x-e y) = e (normalize (x-y)) := by
  rw [← map_sub,linearIsometryEquiv_normalize]

theorem linearIsometryEquiv_cap_norm {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x y u : Space d) :
    ‖normalize (e x-e y)-e u‖ = ‖normalize (x-y)-u‖ := by
  rw [linearIsometryEquiv_normalize_sub,← map_sub,e.norm_map]

theorem northRotation_cap_norm {n : ℕ} (u : Sphere (n+1)) (x y : Space (n+1)) :
    ‖normalize (northRotation u x-northRotation u y)-
      (gnomonicChart (0 : Space n) : Space (n+1))‖ =
      ‖normalize (x-y)-(u : Space (n+1))‖ := by
  rw [← northRotation_apply u]
  exact linearIsometryEquiv_cap_norm (northRotation u) x y u

theorem reverseNorthRotation_cap_norm {n : ℕ} (u : Sphere (n+1)) (x y : Space (n+1)) :
    ‖normalize (reverseNorthRotation u x-reverseNorthRotation u y)-
      (gnomonicChart (0 : Space n) : Space (n+1))‖ =
      ‖normalize (y-x)-(u : Space (n+1))‖ := by
  change ‖normalize (northRotation u (-x)-northRotation u (-y))-
    (gnomonicChart (0 : Space n) : Space (n+1))‖ = _
  rw [northRotation_cap_norm,show -x- -y = y-x by abel]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereCapCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending finite-scale sphere cap estimates to arbitrary ball centers -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

 theorem sphere_cap_arbitrary_center (ν : Measure (Sphere d))
    {R L s : ℝ} (hR : 1 ≤ R) (hL : 1 ≤ L) (hs : 0 ≤ s) (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ν (ball w r) ≤ ENNReal.ofReal (L*r^s))
    (x : Space d) {r : ℝ} (hr : R⁻¹ ≤ r) (_hr1 : r ≤ 1) :
    ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal ((2:ℝ)^s*L*r^s) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hrp : 0 < r := (inv_pos.mpr hRp).trans_le hr
  have he : L*(2*r)^s = (2:ℝ)^s*L*r^s := by
    rw [Real.mul_rpow (by norm_num) hrp.le]
    ring
  by_cases hsmall : 2*r ≤ 1
  · by_cases hne : {w : Sphere d | dist (w:Space d) x < r}.Nonempty
    · obtain ⟨w,hw⟩ := hne
      have hsub : {u : Sphere d | dist (u:Space d) x < r} ⊆ ball w (2*r) := by
        intro u hu
        apply lt_of_le_of_lt (dist_triangle (u:Space d) x (w:Space d))
        change dist (u:Space d) x+dist x (w:Space d) < 2*r
        rw [dist_comm x]
        change dist (w:Space d) x < r at hw
        change dist (u:Space d) x < r at hu
        linarith
      exact (measure_mono hsub).trans ((hball w (2*r) (by linarith) hsmall).trans_eq (by rw [he]))
    · rw [Set.not_nonempty_iff_eq_empty.mp hne,measure_empty]
      exact zero_le
  · have hpower : 1 ≤ L*(2*r)^s :=
      one_le_mul_of_one_le_of_one_le hL (Real.one_le_rpow (by linarith) hs)
    exact (measure_mono (subset_univ _)).trans (hmass.trans (by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rwa [he] at hpower))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal parallel-test good sets and their directional buffer -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem finiteTubeCount_direction_transfer {d : ℕ} {ι : Type*}
    (S : Finset ι) (v : ι → Space d) {w u : Sphere d}
    {δ M W₀ W₁ : ℝ} (hδ : 0 ≤ δ) (_hM : 0 ≤ M)
    (hclose : dist w u ≤ δ) (hbound : ∀ i ∈ S, ‖v i‖ ≤ M)
    (hwidth : W₁+2*δ*M ≤ W₀) :
    finiteTubeCount S v W₁ u ≤ finiteTubeCount S v W₀ w := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,ht⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  change ‖perpendicularPart (w:Space d) (v i)‖ ≤ W₀
  have herror := perpendicularPart_direction_error (sphere_norm w) (sphere_norm u) (v i)
  have hdist : ‖(w:Space d)-(u:Space d)‖ ≤ δ := by
    simpa only [Subtype.dist_eq,dist_eq_norm] using hclose
  have hb : 2*‖(w:Space d)-(u:Space d)‖*‖v i‖ ≤ 2*δ*M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdist (by norm_num)) (hbound i hi)
      (norm_nonneg _) (mul_nonneg (by norm_num) hδ)
  have htri := norm_sub_le_norm_sub_add_norm_sub (perpendicularPart (w:Space d) (v i))
    (perpendicularPart (u:Space d) (v i)) 0
  simp only [sub_zero] at htri
  change ‖perpendicularPart (u:Space d) (v i)‖ ≤ W₁ at ht
  linarith

namespace Regularization
variable {d : ℕ}

theorem parallelGoodSet_buffer (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) {W₀ W₁ T δ : ℝ} (hδ : 0 ≤ δ)
    (hwidth : W₁+2*δ*(10*((d:ℝ)+1)/(2:ℝ)^g) ≤ W₀)
    {w u : Sphere d} (hw : w ∈ parallelGoodSet Q ρ g p P W₀ T)
    (hclose : dist w u ≤ δ) : u ∈ parallelGoodSet Q ρ g p P W₁ T := by
  classical
  by_cases hocc : 0 < ρ (Q.descendant P).carrier
  · simp only [parallelGoodSet,ite_eq_left hocc,mem_ofPred_eq] at hw ⊢
    have hc := finiteTubeCount_direction_transfer (parallelTestCells Q ρ g p P)
      (fun c => (Q.descendant c).center-(Q.descendant P).center) hδ
      (by positivity : 0 ≤ 10*((d:ℝ)+1)/(2:ℝ)^g) hclose ?_ hwidth
    · exact (Nat.cast_le.mpr hc).trans hw
    · intro c hc
      have h := (mem_ball.mp (Finset.mem_filter.mp hc).2.2).le
      simpa only [dist_eq_norm] using h
  · simp only [parallelGoodSet,ite_eq_right hocc,mem_empty_iff_false] at hw

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothMask
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth angular masks from buffered good sets

A finite subcollection of the normalized cap partition gives a cutoff
supported inside a prescribed set. It equals one wherever a closed ball
of twice the cap radius lies in that set. No regularity of the set is
needed for this finite construction.
-/

namespace Falconer
open Set
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem capCutoffAmbient_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (U : Set (Sphere d)) :
    (∀ w : Sphere d, 0 ≤ capCutoffAmbient δ hδ S U w ∧ capCutoffAmbient δ hδ S U w ≤ 1) ∧
    (∀ w : Sphere d, capCutoffAmbient δ hδ S U w ≠ 0 → w ∈ U) ∧
    (∀ w : Sphere d, (∀ z : Sphere d, dist z w ≤ 2*δ → z ∈ U) →
      capCutoffAmbient δ hδ S U w = 1) := by
  obtain ⟨hpart,hbounds,hsupport⟩ := normalizedCap_properties hδ S hcover
  have hsub : cutoffCapCenters δ S U ⊆ S := Finset.filter_subset _ _
  refine ⟨?_,?_,?_⟩
  · intro w
    constructor
    · exact Finset.sum_nonneg (fun c hc => (hbounds c (hsub hc) w).1)
    · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c hc _ => (hbounds c hc w).1))
      exact (hpart w).le
  · intro w hw
    obtain ⟨c,hc,hcw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    have hsel := (Finset.mem_filter.mp hc).2
    apply hsel w
    exact hsupport c (hsub hc) w hcw
  · intro w hcore
    rw [← hpart w]
    apply Finset.sum_subset hsub
    intro c hc hnot
    by_contra hn
    have hdist : dist w c ≤ δ := hsupport c hc w hn
    apply hnot
    apply Finset.mem_filter.mpr ⟨hc,?_⟩
    intro z hz
    apply hcore z
    calc
      dist z w ≤ dist z c+dist c w := dist_triangle _ _ _
      _ ≤ δ+δ := add_le_add hz (by simpa only [dist_comm] using hdist)
      _ = 2*δ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Angular masks attached to actual dyadic anchor cells

The spatial dependence is a finite Borel choice of the anchor cell.
On every descendant of an anchor cell, its angular mask is exactly
constant in the spatial variable.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem anchoredMask_on_cell {d n : ℕ} (Q : DyadicCube d)
    (F : List (Fin d → Bool) → Sphere d → ℝ) (p : List (Fin d → Bool)) (hp : p.length = n)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d) :
    anchoredMask Q n F x w = F p w := by
  unfold anchoredMask
  rw [Finset.sum_eq_single p]
  · simp [hx]
  · intro q hq hqp
    have hdis := Q.descendants_disjoint ((mem_cubePaths d n q).mp hq |>.trans hp.symm) hqp
    have hn : x ∉ (Q.descendant q).carrier := fun hq => Set.disjoint_left.mp hdis hq hx
    simp [hn]
  · exact fun hn => (hn ((mem_cubePaths d n p).mpr hp)).elim

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AnchoredBufferedMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Buffered masks on the original spatial anchor cells

These masks are jointly measurable, bounded between zero and one, smooth
in every adapted angular chart, and constant in the spatial variable on
all descendants of a reached anchor. Their angular derivative constants
are independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem anchoredBufferedMask_core {d g : ℕ} (Q : DyadicCube d)
    {δ : ℝ} (hδ : 0 < δ) (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2)
    (U : List (Fin d → Bool) → Set (Sphere d))
    (p : List (Fin d → Bool)) (hp : p.length = g) {x : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d)
    (hw : ∀ z : Sphere d, dist z w ≤ 2*δ → z ∈ U p) :
    anchoredBufferedMask Q g δ hδ S U x w = 1 := by
  rw [anchoredBufferedMask,anchoredMask_on_cell Q _ p hp hx]
  exact (capCutoffAmbient_properties hδ S hcover (U p)).2.2 w hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TestWidths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The width and buffer scales of the all-dimensional tests

These are the exponents 500 and 50 in the all-dimensional test family.
-/

namespace Falconer

theorem angularTestWidth_gap (N : ℕ) (σ : ℝ) {J : ℕ} (hJ : 0 < J) (i n : ℕ) :
    angularTestWidth N σ J i n-angularTestWidth N σ J (i+1) n =
      ((2:ℝ)^N)^(500*σ)/((J:ℝ)*(2:ℝ)^n) := by
  have hj : (J:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hJ.ne'
  simp only [angularTestWidth,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem uniform_angularTestWidth_gap {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g n : ℕ, g ≤ n → ∀ i : ℕ,
      angularTestWidth N σ J (i+1) n+
        (C/(2:ℝ)^g)*angularTestRadius N σ (n-g) ≤
      angularTestWidth N σ J i n := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 450*σ) (C*(J:ℝ))
  refine ⟨N₀,?_⟩
  intro N hN g n hgn i
  have hj : 0 < (J:ℝ) := Nat.cast_pos.mpr hJ
  have hR : 0 < (2:ℝ)^N := by positivity
  have hconst := mul_le_mul_of_nonneg_right (hN₀ N hN)
    (by positivity : 0 ≤ ((2:ℝ)^N)^(50*σ))
  have he : ((2:ℝ)^N)^(450*σ)*((2:ℝ)^N)^(50*σ) =
      ((2:ℝ)^N)^(500*σ) := by rw [← Real.rpow_add hR]; congr 1; ring
  rw [he] at hconst
  have hp : (2:ℝ)^g*(2:ℝ)^(n-g) = (2:ℝ)^n := by
    rw [← pow_add,Nat.add_sub_of_le hgn]
  have hb : (C/(2:ℝ)^g)*angularTestRadius N σ (n-g) ≤
      ((2:ℝ)^N)^(500*σ)/((J:ℝ)*(2:ℝ)^n) := by
    calc
      _ ≤ (C/(2:ℝ)^g)*(1/(2:ℝ)^(n-g)*((2:ℝ)^N)^(50*σ)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (C*(J:ℝ)*((2:ℝ)^N)^(50*σ))/((J:ℝ)*(2:ℝ)^n) := by
        rw [← hp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)
  rw [← angularTestWidth_gap N σ hJ i n] at hb
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionBuffer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Directional buffers for the actual full-law projection test -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projectionCollision_direction_transfer (μ : Measure (Space d))
    {D δ W W' : ℝ} (hD : 0 ≤ D) (_hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ z : Space d × Space d ∂μ.prod μ, ‖z.1-z.2‖ ≤ D)
    {v w : Space d} (hvw : ‖v-w‖ ≤ δ) (hwidth : W+D*δ ≤ W') :
    projectionCollision μ v W ≤ projectionCollision μ w W' := by
  apply measure_mono_ae
  filter_upwards [hsupport] with z hz
  intro htest
  have hinner : |inner ℝ (z.1-z.2) (w-v)| ≤ D*δ := by
    have hnorm : ‖w-v‖ ≤ δ := by simpa only [norm_sub_rev] using hvw
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hz hnorm (norm_nonneg _) hD)
  have he : inner ℝ (z.1-z.2) w = inner ℝ (z.1-z.2) v+inner ℝ (z.1-z.2) (w-v) := by
    rw [inner_sub_right]
    ring
  change |inner ℝ (z.1-z.2) v| ≤ W at htest
  change |inner ℝ (z.1-z.2) w| ≤ W'
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add htest hinner).trans hwidth)

theorem projectionGoodSet_buffer (μ : Measure (Space d))
    {D δ W W' T : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ z : Space d × Space d ∂μ.prod μ, ‖z.1-z.2‖ ≤ D)
    {v w : Sphere d} (hvw : dist v w ≤ δ) (hwidth : W+D*δ ≤ W')
    (hw : w ∈ projectionGoodSet μ W' T) : v ∈ projectionGoodSet μ W T := by
  have hd : ‖(v:Space d)-(w:Space d)‖ ≤ δ := by
    simpa only [Subtype.dist_eq,dist_eq_norm] using hvw
  exact (projectionCollision_direction_transfer μ hD hδ hsupport hd hwidth).trans hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionBuffer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection buffers for the full original conditional laws -/

namespace Falconer.Regularization
open Set MeasureTheory
variable {d : ℕ}

theorem conditional_pair_diameter (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) :
    ∀ᵐ z : Space d × Space d ∂
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier).prod
        (ProbabilityTheory.cond ρ (Q.descendant P).carrier),
      ‖z.1-z.2‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^P.length) := by
  have hs : ∀ᵐ z ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
      z ∈ (Q.descendant P).carrier :=
    ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable (fun _ hz => hz)
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hs] with x hx
  filter_upwards [hs] with y hy
  have hh := (Q.descendant P).dist_le (by rw [Q.descendant_side]; positivity) hx hy
  simpa only [dist_eq_norm,Q.descendant_side] using hh

theorem conditional_projection_buffer (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d)
    {δ W W' T : ℝ} (hδ : 0 ≤ δ) {v w : Sphere d} (hvw : dist v w ≤ δ)
    (hwidth : W+(Real.sqrt d/(2:ℝ)^P.length)*δ ≤ W')
    (hw : w ∈ projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W' T) :
    v ∈ projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W T := by
  apply projectionGoodSet_buffer _ (by positivity) hδ _ hvw hwidth hw
  simpa only [hQ,mul_one_div] using conditional_pair_diameter Q (by rw [hQ]; norm_num) ρ P

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionTest
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal occupied-anchor projection tests -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

namespace Regularization

theorem conditionalProjectionGoodSet_buffer (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d)
    {δ W W' T : ℝ} (hδ : 0 ≤ δ) {v w : Sphere d} (hvw : dist v w ≤ δ)
    (hwidth : W+(Real.sqrt d/(2:ℝ)^P.length)*δ ≤ W')
    (hw : w ∈ conditionalProjectionGoodSet Q ρ P W' T) :
    v ∈ conditionalProjectionGoodSet Q ρ P W T := by
  classical
  unfold conditionalProjectionGoodSet at hw ⊢
  split_ifs at hw ⊢ with hocc
  · exact conditional_projection_buffer Q hQ ρ P hδ hvw hwidth hw
  · exact False.elim hw

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorTests
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual all-dimensional tests indexed by policy descriptors

The policy list is scalar. Its tests use original occupied cells and the
full conditional probability of the current ambient-dimensional class.
The tolerance is the manuscript's 500-sigma width at every level.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

variable {d : ℕ}

theorem uniform_descriptor_direction_buffer {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (P : List (Fin d → Bool)), P.length = descriptorAnchor b →
      ∀ (i : ℕ) (w u : Sphere d),
        dist w u ≤ C*angularTestRadius N σ (descriptorLength b) →
        w ∈ descriptorGoodDirections Q ρ m N σ J i P b →
        u ∈ descriptorGoodDirections Q ρ m N σ J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_angularTestWidth_gap hσ hJ
    (20*((d:ℝ)+1)*C) (by positivity)
  obtain ⟨N₂,h₂⟩ := uniform_angularTestWidth_gap hσ hJ
    (Real.sqrt d*C) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ _ m b hb P hP i w u hwu hw
  cases b with
  | parallel g p =>
    apply Regularization.parallelGoodSet_buffer Q ρ g p P
      (mul_nonneg hC (angularTestRadius_pos N σ (p-g)).le) ?_ hw hwu
    convert h₁ N ((le_max_left _ _).trans hN) g p hb.1 i using 1 <;> first | rfl | ring
  | projection p t =>
    apply Regularization.conditionalProjectionGoodSet_buffer Q hQ ρ P
      (mul_nonneg hC (angularTestRadius_pos N σ (t-p)).le)
      (by simpa only [dist_comm, descriptorLength] using hwu) ?_ hw
    have hh := h₂ N ((le_max_right _ _).trans hN) p t hb.1 i
    dsimp only [descriptorAnchor] at hP
    rw [hP]
    convert hh using 1 <;> first | rfl | ring

theorem policy_descriptor_valid (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {b : PolicyDescriptor}
    (hb : b ∈ PlanarFalconer.policyDescriptorList A N q a t) : descriptorValid N b := by
  obtain ⟨s,u,_,hut,_,_,hpos,_,hbound⟩ := PlanarFalconer.policyDescriptor_origin A hq hb
  cases b <;> simp only [descriptorLength,descriptorAnchor,descriptorValid] at hpos hbound ⊢ <;>
    omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

theorem uniform_descriptorMask_core {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (S : Finset (Sphere d)),
      (∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (i : ℕ) (x : Space d), x ∈ Q.carrier → ∀ w : Sphere d,
      (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b →
      descriptorMask Q ρ m N σ J i b S x w = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptor_direction_buffer (d := d) hσ hJ (C := 1) (by norm_num)
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m b hb S hcover i x hx w hw
  obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
  apply anchoredBufferedMask_core Q (descriptorMaskRadius_pos N σ b) S hcover _ p
    ((mem_cubePaths _ _ _).mp hp) hxp w
  intro z hz
  apply h₀ N hN Q hQ ρ m b hb p ((mem_cubePaths _ _ _).mp hp) i w z _ (hw p hp hxp)
  have hr := angularTestRadius_pos N σ (descriptorLength b)
  dsimp only [descriptorMaskRadius] at hz
  rw [dist_comm] at hz
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialSphereBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sphere law has exactly the original directional cap and plate bounds -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem originalRadialSphereLaw_ball (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (w : Sphere d) (r : ℝ) :
    originalRadialSphereLaw w₀ ν G z (Metric.ball w r) =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space d) < r} := by
  rw [originalRadialSphereLaw_apply w₀ ν G z (Metric.ball w r) measurableSet_ball]
  congr 1
  ext x
  by_cases hx : (z,x) ∈ G
  · simp only [mem_ofPred_eq,hx,true_and,Metric.mem_ball,Subtype.dist_eq,
      normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr (hdiag x hx))]
  · simp only [mem_ofPred_eq,hx,false_and]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OriginalFiberCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prepared radial cap bound controls each original sphere law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem eventual_original_fiber_caps {σ s : ℝ} (hσ : 0 < σ) (hs : 0 ≤ s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ μ ν : ProbabilityMeasure (Space d), ∀ G : Set (Space d × Space d),
      (∀ x ∈ (μ : Measure (Space d)).support, ∀ y, (x,y) ∈ G → y ≠ x) →
      (∀ x ∈ (μ : Measure (Space d)).support, ∀ w : Space d, ‖w‖ = 1 →
        ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        (ν : Measure (Space d)) {y | (x,y) ∈ G ∧ dist (radialDirection x y) w < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(σ/2)*r^s)) →
      ∀ w₀ : Sphere d, ∀ x ∈ (μ : Measure (Space d)).support,
      ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^s) := by
  obtain ⟨N₀,h₀⟩ := Regularization.fixed_constant_absorbed (half_pos hσ) ((2:ℝ)^s)
  refine ⟨N₀,?_⟩
  intro N hN μ ν G hdiag hcap w₀ x hx u r hr hr1
  let R : ℝ := (2:ℝ)^N
  let V := originalRadialSphereLaw w₀ ν G x
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hL : 1 ≤ R^(σ/2) := Real.one_le_rpow hR (half_pos hσ).le
  have hmass : V univ ≤ 1 := (originalRadialSphereLaw_mass_le w₀ ν G x).trans (by simp)
  have hball (w : Sphere d) (t : ℝ) (ht : R⁻¹ ≤ t) (ht1 : t ≤ 1) :
      V (Metric.ball w t) ≤ ENNReal.ofReal (R^(σ/2)*t^s) := by
    rw [originalRadialSphereLaw_ball w₀ ν G x (hdiag x hx)]
    simpa only [radialDirection,NormedSpace.normalize] using hcap x hx w (sphere_norm w) t ht ht1
  have hb := sphere_cap_arbitrary_center V hR hL hs hmass hball u
    (by simpa only [R,Real.rpow_neg_one] using hr) hr1
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hc := h₀ N hN
  have he : R^(σ/2)*R^(σ/2) = R^σ := by
    rw [← Real.rpow_add (by dsimp [R]; positivity)]
    congr 1
    ring
  calc
    _ ≤ (R^(σ/2)*R^(σ/2))*r^s := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
        (Real.rpow_nonneg (le_trans (by positivity : 0 ≤ R^(-1:ℝ)) hr) _)
    _ = _ := by rw [he]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OriginalCapRemoval
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prepared cap deletion controls both original sphere laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem original_cap_removal (μ ν : ProbabilityMeasure (Space d))
    (Γ : ℕ → Set (Space d × Space d)) (hcap : CapAvailable μ ν Γ ((d:ℝ)/2))
    (hne : ∀ N, ∀ z ∈ Γ N, z.1 ≠ z.2) {σ : ℝ} (hσ : 0 < σ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ D : Set (Space d × Space d), MeasurableSet D ∧ D ⊆ Γ N ∧
        ((μ : Measure (Space d)).prod (ν : Measure (Space d))) D ≤
          ENNReal.ofReal (C*((2:ℝ)^N)^(-c)) ∧
        ∀ w₀ : Sphere d,
        (∀ᵐ x ∂(μ : Measure (Space d)), ∀ u : Space d, ∀ r : ℝ,
          ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
          originalRadialSphereLaw w₀ ν (Γ N \ D) x {w : Sphere d | dist (w:Space d) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) ∧
        (∀ᵐ y ∂(ν : Measure (Space d)), ∀ u : Space d, ∀ r : ℝ,
          ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
          originalRadialSphereLaw w₀ μ (Prod.swap ⁻¹' (Γ N \ D)) y
            {w : Sphere d | dist (w:Space d) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) := by
  obtain ⟨c,C,hc,hC,N₁,h₁⟩ := hcap (σ/2) (half_pos hσ)
  obtain ⟨N₂,h₂⟩ := eventual_original_fiber_caps (d := d) hσ (show (0:ℝ) ≤ d/2 by positivity)
  refine ⟨c,C,hc,hC,max N₁ N₂,?_⟩
  intro N hN
  obtain ⟨D,hD,hsub,hm,hcaps⟩ := h₁ N ((le_max_left _ _).trans hN)
  refine ⟨D,hD,hsub,hm,?_⟩
  intro w₀
  constructor
  · filter_upwards [(μ : Measure (Space d)).support_mem_ae] with x hx
    exact h₂ N ((le_max_right _ _).trans hN) μ ν (Γ N \ D)
      (fun x _ y hxy => (hne N (x,y) hxy.1).symm) hcaps.1 w₀ x hx
  · filter_upwards [(ν : Measure (Space d)).support_mem_ae] with y hy
    apply h₂ N ((le_max_right _ _).trans hN) ν μ (Prod.swap ⁻¹' (Γ N \ D))
      (fun y _ x hxy => hne N (x,y) hxy.1) ?_ w₀ y hy
    intro y hy u hu r hr hr1
    exact hcaps.2 y hy u hu r hr hr1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ActualOuterMasks
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourceSmoothingLevels_pos {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    0 < sourceSmoothingLevels sig kap := by
  unfold sourceSmoothingLevels
  exact Nat.ceil_pos.mpr (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ValidDescriptors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial finite family containing every descriptor used at a scale -/

namespace Falconer
open PlanarFalconer (PolicyDescriptor)
attribute [local instance] Classical.propDecidable

 theorem mem_validDescriptors (N : ℕ) (b : PolicyDescriptor) :
    b ∈ validDescriptors N ↔ descriptorValid N b := by
  constructor
  · exact fun hb => (Finset.mem_filter.mp hb).2
  · intro hb
    apply Finset.mem_filter.mpr
    refine ⟨?_,hb⟩
    cases b with
    | parallel g p =>
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨(g,p),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by
        change g ≤ p ∧ p ≤ N at hb; omega),Finset.mem_range.mpr (by
        change g ≤ p ∧ p ≤ N at hb; omega)⟩,rfl⟩
    | projection p t =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨(p,t),Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by
        change p ≤ t ∧ t ≤ N at hb; omega),Finset.mem_range.mpr (by
        change p ≤ t ∧ t ≤ N at hb; omega)⟩,rfl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorAmbient
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth ambient extensions of the actual spatially anchored masks

At each spatial point there is at most one active anchor cell. Consequently
the ambient derivative bound has no factor counting anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem descriptorAmbientMask_sphere (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) (x : Space d) (w : Sphere d) :
    descriptorAmbientMask Q ρ m N σ J i b S x w = descriptorMask Q ρ m N σ J i b S x w := rfl

theorem descriptorAmbientMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (S : Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorAmbientMask Q ρ m N σ J i b S)) := by
  apply Finset.measurable_sum
  intro p _
  exact ((capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _).continuous.measurable.comp
    measurable_snd).ite ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DescriptorProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descriptor products and their reached angular factors -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem uniform_descriptorProduct_core {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (B : Finset PolicyDescriptor), (∀ b ∈ B, descriptorValid N b) →
      ∀ (S : PolicyDescriptor → Finset (Sphere d)),
      (∀ b ∈ B, ∀ w : Sphere d,
        ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (i : ℕ) (x : Space d), x ∈ Q.carrier → ∀ w : Sphere d,
      (∀ b ∈ B, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b) →
      descriptorProduct Q ρ m N σ J i B S x w = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorMask_core (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m B hB S hS i x hx w hw
  apply Finset.prod_eq_one
  intro b hb
  exact h₀ N hN Q hQ ρ m b (hB b hb) (S b) (hS b hb) i x hx w (hw b hb)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_AmbientProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient products preserve every original descriptor support -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
variable {d : ℕ}

 theorem descriptorAmbientProduct_sphere (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (x : Space d) (w : Sphere d) :
    descriptorAmbientProduct Q ρ m N σ J i B S x w = descriptorProduct Q ρ m N σ J i B S x w := by
  simp only [descriptorAmbientProduct,descriptorProduct,descriptorAmbientMask_sphere]

 theorem descriptorAmbientProduct_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Measurable (Function.uncurry (descriptorAmbientProduct Q ρ m N σ J i B S)) :=
  Finset.measurable_prod B (fun b _ => descriptorAmbientMask_measurable Q ρ m N σ J i b (S b))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateAntipodal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The incoming stationary pole retains the same descriptor tests -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)
open scoped Topology

 theorem perpendicularPart_neg_direction {d : ℕ} (w v : Space d) :
    perpendicularPart (-w) v = perpendicularPart w v := by
  simp [perpendicularPart,inner_neg_left]

 theorem finiteTubeCount_opposite {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) :
    finiteTubeCount S v W (oppositePole w) = finiteTubeCount S v W w := by
  classical
  unfold finiteTubeCount
  congr 1
  apply Finset.filter_congr
  intro a _
  simp only [angularTubeEvent,Set.mem_ofPred_eq,oppositePole_coe,
    perpendicularPart_neg_direction]

 theorem projectionCollision_neg_direction {d : ℕ} (μ : Measure (Space d))
    (w : Space d) (W : ℝ) : projectionCollision μ (-w) W = projectionCollision μ w W := by
  simp only [projectionCollision,inner_neg_right,abs_neg]

 theorem descriptorGoodDirections_opposite {d : ℕ}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (P : List (Fin d → Bool)) (b : PolicyDescriptor)
    (w : Sphere d) :
    oppositePole w ∈ descriptorGoodDirections Q ρ m N σ J i P b ↔
      w ∈ descriptorGoodDirections Q ρ m N σ J i P b := by
  classical
  cases b with
  | parallel g p =>
    simp only [descriptorGoodDirections,Regularization.parallelGoodSet]
    split_ifs <;> simp only [mem_ofPred_eq,Regularization.parallelTestCount,
      finiteTubeCount_opposite,mem_empty_iff_false]
  | projection p t =>
    simp only [descriptorGoodDirections,Regularization.conditionalProjectionGoodSet]
    split_ifs <;> simp only [projectionGoodSet,mem_ofPred_eq,oppositePole_coe,
      projectionCollision_neg_direction,mem_empty_iff_false]

 theorem descriptorEndpointGood_opposite {d : ℕ}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Space d) (w : Sphere d) :
    (x,oppositePole w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b := by
  simp only [descriptorEndpointGood,mem_ofPred_eq,descriptorGoodDirections_opposite]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllTestsRestoration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One exceptional set restores every policy descriptor at the scale -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
variable {d : ℕ}

 theorem normalizeToSphere_neg (w₀ : Sphere d) {v : Space d} (hv : v ≠ 0) :
    normalizeToSphere w₀ (-v) = oppositePole (normalizeToSphere w₀ v) := by
  apply Subtype.ext
  simp only [normalizeToSphere_coe_of_ne w₀ (neg_ne_zero.mpr hv),oppositePole_coe,
    normalizeToSphere_coe_of_ne w₀ hv,NormedSpace.normalize_neg]

 theorem uniform_all_tests_restoration {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (profile : ℝ → ℝ)
        (F : Finset PolicyDescriptor), F ⊆ validDescriptors N →
      ∀ S : PolicyDescriptor → Finset (Sphere d),
        (∀ b ∈ F, ∀ w : Sphere d, ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)) (x y : Space d),
      x ∈ Q.carrier → x ≠ y → (x,y) ∈ G →
      (x,y) ∉ allDescriptorTestBad w₀ Q ρ profile N σ J G →
      descriptorAmbientProduct Q ρ profile N σ J 0 F S x (NormedSpace.normalize (x-y)) = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorProduct_core (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ profile F hF S hS w₀ G x y hx hxy hG hgood
  have hne : y-x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hneg : normalizeToSphere w₀ (x-y) = oppositePole (normalizeToSphere w₀ (y-x)) := by
    simpa only [neg_sub] using normalizeToSphere_neg w₀ hne
  have hcore := h₀ N hN Q hQ ρ profile F
    (fun b hb => (mem_validDescriptors N b).mp (hF hb)) S hS 0 x hx
    (normalizeToSphere w₀ (x-y)) (by
      intro b hb
      rw [hneg,descriptorEndpointGood_opposite]
      by_contra hn
      apply hgood
      exact mem_iUnion₂.mpr ⟨b,hF hb,hG,hn⟩)
  rw [← descriptorAmbientProduct_sphere] at hcore
  simpa only [normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hxy)] using hcore

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FilteredLimit
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limits of decreasing original-pair filters

For the manuscript application, `ρ` is the original product measure with
the bounded distance weight, and `f` is the original distance map. These
lemmas do not replace distances by those of any auxiliary projection.
-/

namespace Falconer
open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem filteredPushforward_mono (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) {G H : Set X} (hGH : G ⊆ H) :
    filteredPushforward f ρ G ≤ filteredPushforward f ρ H :=
  Measure.map_mono (Measure.restrict_mono hGH le_rfl) hf

theorem filteredPushforward_mass (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) (G : Set X) : filteredPushforward f ρ G univ = ρ G := by
  rw [filteredPushforward, Measure.map_apply hf MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ]

/-- Decreasing filters produce a decreasing sequence of pushforwards. -/
theorem antitone_filteredPushforward (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) {G : ℕ → Set X} (hG : Antitone G) :
    Antitone (fun n => filteredPushforward f ρ (G n)) := by
  intro i j hij
  exact filteredPushforward_mono f hf ρ (hG hij)

/-- Continuity from above gives convergence in the mass of the positive
remaining tail; it supplies no quantitative convergence rate. -/
theorem filteredPushforward_tail_mass_tendsto (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) [IsFiniteMeasure ρ] (G : ℕ → Set X)
    (hG : ∀ n, MeasurableSet (G n)) (hmono : Antitone G) :
    Tendsto (fun n => (filteredPushforward f ρ (G n) -
      filteredPushforward f ρ (⋂ j, G j)).real univ) atTop (𝓝 0) := by
  have hle (n : ℕ) : filteredPushforward f ρ (⋂ j, G j) ≤
      filteredPushforward f ρ (G n) :=
    filteredPushforward_mono f hf ρ (iInter_subset G n)
  have hm := tendsto_measure_iInter_atTop (μ := ρ)
    (fun n => (hG n).nullMeasurableSet) hmono ⟨0, measure_ne_top ρ _⟩
  have hr := ((ENNReal.tendsto_toReal (measure_ne_top ρ _)).comp hm).sub_const
    ((ρ (⋂ j, G j)).toReal)
  simp only [sub_self] at hr
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [Measure.real, Measure.sub_apply MeasurableSet.univ (hle n),
    ENNReal.toReal_sub_of_le (hle n univ) (measure_ne_top _ univ),
    filteredPushforward_mass f hf, filteredPushforward_mass f hf]
  rfl

/-- Positive retained weighted mass remains positive after distance pushforward. -/
theorem filteredPushforward_positive (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) {G : Set X} (hG : 0 < ρ G) :
    0 < filteredPushforward f ρ G univ := by
  rwa [filteredPushforward_mass f hf]

/-- Restriction preserves the carrier of the original pushforward. -/
theorem filteredPushforward_carried (f : X → Y) (hf : Measurable f)
    (ρ : Measure X) (G : Set X) {D : Set Y} (hD : MeasurableSet D)
    (hcarry : ρ (f ⁻¹' Dᶜ) = 0) : filteredPushforward f ρ G Dᶜ = 0 := by
  rw [filteredPushforward, Measure.map_apply hf hD.compl]
  exact le_antisymm ((Measure.restrict_apply_le G _).trans_eq hcarry) bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_MaskLoss
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem removed_pushforward_mass_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) (w m : α → ℝ≥0∞)
    (bad : Set α) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, w x ≤ C)
    (hout : ∀ᵐ x ∂μ, x ∉ bad → m x = 1) :
    (μ.withDensity (fun x => w x*(1-m x))).map f univ ≤ C*μ bad := by
  rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (∫⁻ x, w x*(1-m x) ∂μ) ≤ ∫⁻ x, bad.indicator (fun _ => C) x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound,hout] with x hx houtx
      by_cases hxb : x ∈ bad
      · rw [Set.indicator_of_mem hxb]
        calc
          w x*(1-m x) ≤ w x*1 := mul_le_mul_right tsub_le_self _
          _ ≤ C := by simpa only [mul_one] using hx
      · rw [Set.indicator_of_notMem hxb, houtx hxb, tsub_self, mul_zero]
    _ ≤ C*μ bad := lintegral_indicator_const_le bad C

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_TotalVariation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem totalVariation_sub_of_add {α : Type*} [MeasurableSpace α]
    (τ σ ρ : Measure α) [IsFiniteMeasure τ] [IsFiniteMeasure σ] [IsFiniteMeasure ρ]
    (h : τ = σ+ρ) : (τ.toSignedMeasure-σ.toSignedMeasure).totalVariation = ρ := by
  have heq : τ.toSignedMeasure = σ.toSignedMeasure+ρ.toSignedMeasure := by
    calc
      τ.toSignedMeasure = (σ+ρ).toSignedMeasure := Measure.toSignedMeasure_congr h
      _ = σ.toSignedMeasure+ρ.toSignedMeasure := Measure.toSignedMeasure_add σ ρ
  rw [heq, add_sub_cancel_left, SignedMeasure.totalVariation_eq_variation,
    Measure.variation_toSignedMeasure]

theorem masked_totalVariation_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) (w m : α → ℝ≥0∞)
    (hw : Measurable w) (hm : Measurable m) (hm1 : ∀ x, m x ≤ 1)
    [IsFiniteMeasure (μ.withDensity w)] (bad : Set α) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, w x ≤ C)
    (hout : ∀ᵐ x ∂μ, x ∉ bad → m x = 1) :
    ∃ (σ ρ : Measure β) (_hσ : IsFiniteMeasure σ) (_hρ : IsFiniteMeasure ρ),
      σ = (μ.withDensity (fun x => w x*m x)).map f ∧
      ρ = (μ.withDensity (fun x => w x*(1-m x))).map f ∧
      (((μ.withDensity w).map f).toSignedMeasure-σ.toSignedMeasure).totalVariation univ
        ≤ C*μ bad := by
  let τ := (μ.withDensity w).map f
  let σ := (μ.withDensity (fun x => w x*m x)).map f
  let ρ := (μ.withDensity (fun x => w x*(1-m x))).map f
  have hdec : τ = σ+ρ := masked_pushforward_decomposition μ f hf w m hw hm hm1
  obtain ⟨hσ,hρ⟩ := finite_summands τ σ ρ hdec
  let := hσ
  let := hρ
  refine ⟨σ,ρ,hσ,hρ,rfl,rfl,?_⟩
  rw [totalVariation_sub_of_add τ σ ρ hdec]
  exact removed_pushforward_mass_le μ f hf w m bad C hbound hout

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrunedVariation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact variation cost of deleting original pairs

The full filtered measure is monotone in the coarse filter. Its pruned
approximation differs by precisely the weighted mass of the removed pairs.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem withDensity_positive_of_lower (π : Measure X) (w : X → ℝ≥0∞)
    {c : ℝ≥0∞} (hc : 0 < c) (hbound : ∀ᵐ x ∂π, c ≤ w x)
    (S : Set X) (hS : MeasurableSet S) (hpos : 0 < π S) :
    0 < π.withDensity w S := by
  rw [withDensity_apply w hS]
  have hlow : c * π S ≤ ∫⁻ x in S, w x ∂π := by
    rw [← Measure.restrict_apply_univ (μ := π) (s := S),← lintegral_const]
    exact lintegral_mono_ae (ae_restrict_of_ae hbound)
  exact (ENNReal.mul_pos hc.ne' hpos.ne').trans_le hlow

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FinitePartitionMask
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable masks on a finite disjoint spatial partition -/

namespace Falconer
open Set MeasureTheory
variable {X ι : Type*} [MeasurableSpace X]

 theorem finitePartitionMask_measurable (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ)
    (hC : ∀ i ∈ F, MeasurableSet (C i)) (hw : ∀ i ∈ F, Measurable (w i)) :
    Measurable (finitePartitionMask F C w) :=
  Finset.measurable_sum F (fun i hi => (hw i hi).indicator (hC i hi))

omit [MeasurableSpace X] in
 theorem finitePartitionMask_on (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (C i) (C j))
    {i : ι} (hi : i ∈ F) {x : X} (hx : x ∈ C i) :
    finitePartitionMask F C w x = w i x := by
  classical
  unfold finitePartitionMask
  rw [Finset.sum_eq_single_of_mem i hi]
  · exact indicator_of_mem hx _
  · intro j hj hji
    apply indicator_of_notMem
    intro hjx
    exact Set.disjoint_left.mp (hdis i hi j hj hji.symm) hx hjx

omit [MeasurableSpace X] in
 theorem finitePartitionMask_off (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ)
    {x : X} (hx : x ∉ ⋃ i ∈ F, C i) : finitePartitionMask F C w x = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact indicator_of_notMem (fun hxi => hx (mem_iUnion₂.mpr ⟨i,hi,hxi⟩)) _

omit [MeasurableSpace X] in
 theorem finitePartitionMask_bounds (F : Finset ι) (C : ι → Set X) (w : ι → X → ℝ)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (C i) (C j))
    (hw : ∀ i ∈ F, ∀ x, w i x ∈ Icc (0:ℝ) 1) (x : X) :
    finitePartitionMask F C w x ∈ Icc (0:ℝ) 1 := by
  by_cases hx : x ∈ ⋃ i ∈ F, C i
  · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    rw [finitePartitionMask_on F C w hdis hi hxi]
    exact hw i hi x
  · rw [finitePartitionMask_off F C w hx]
    exact ⟨le_rfl,zero_le_one⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_SmoothShellPartition
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceShellLowpass_tendsto (r : ℝ) :
    Tendsto (fun n => sourceShellLowpass n r) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => r/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have h := sourceShellBump.continuous.continuousAt.tendsto.comp ht
  have hz : sourceShellBump (0:ℝ) = 1 := sourceShellBump.one_of_mem_closedBall (by
    change dist (0:ℝ) 0 ≤ 1
    norm_num)
  simpa only [sourceShellLowpass, hz, Function.comp_def] using h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MeasureKernelConvolution
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform

theorem shellKernelMeasureConvolution_L1 (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    Integrable (kernelMeasureConvolution (sourceShellKernel n) τ) ∧
      (∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) τ x‖) ≤
        τ.real univ * ∫ x, ‖sourceShellKernel 0 x‖ := by
  simpa only [sourceShellKernel_uniform_L1] using kernelMeasureConvolution_L1
    (sourceShellKernel n) (sourceShellKernel_continuous n) (sourceShellKernel_integrable n) τ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellFrequencyTests
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped Topology

theorem sourceShellLowpass_abs_le (n : ℕ) (r : ℝ) : |sourceShellLowpass n r| ≤ 1 := by
  rw [abs_of_nonneg (show 0 ≤ sourceShellLowpass n r from sourceShellBump.nonneg)]
  exact sourceShellBump.le_one

theorem sourceShellLowpass_fourier_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun n => ∫ r, sourceShellLowpass n r • (charFun τ r * f r)) atTop
      (𝓝 (∫ r, charFun τ r * f r)) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun r => sourceShellLowpass n r • (charFun τ r * f r)) volume :=
    (sourceShellLowpass_smooth n).continuous.aestronglyMeasurable.smul
      (continuous_charFun.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  have hb (n : ℕ) : ∀ᵐ r ∂volume,
      ‖sourceShellLowpass n r • (charFun τ r * f r)‖ ≤ τ.real univ * ‖f r‖ := by
    filter_upwards with r
    rw [norm_smul, Real.norm_eq_abs, norm_mul]
    calc
      |sourceShellLowpass n r| * (‖charFun τ r‖ * ‖f r‖) ≤
          1 * (‖charFun τ r‖ * ‖f r‖) :=
        mul_le_mul_of_nonneg_right (sourceShellLowpass_abs_le n r) (by positivity)
      _ ≤ τ.real univ * ‖f r‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (norm_charFun_le r) (norm_nonneg _)
  have hp : ∀ᵐ r ∂volume,
      Tendsto (fun n => sourceShellLowpass n r • (charFun τ r * f r)) atTop
        (𝓝 (charFun τ r * f r)) := by
    filter_upwards with r
    simpa using (sourceShellLowpass_tendsto r).smul (tendsto_const_nhds (x := charFun τ r * f r))
  exact tendsto_integral_of_dominated_convergence (fun r => τ.real univ * ‖f r‖)
    hm (hf.norm.const_mul _) hb hp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SpatialFourierTests
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceInverseKernel_pairing (f : ℝ → ℂ) (hf : Integrable f)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * sourceInverseKernel f x) =
      (2*Real.pi)⁻¹ • ∫ r, f r * 𝓕 φ (r/(2*Real.pi)) := by
  let g : ℝ × ℝ → ℂ := fun z =>
    φ z.1 * (Complex.exp (↑(-z.1*z.2)*Complex.I) * f z.2)
  have hg : AEStronglyMeasurable g (volume.prod volume) :=
    φ.continuous.aestronglyMeasurable.comp_fst.mul
      ((by fun_prop : Continuous (fun z : ℝ × ℝ =>
        Complex.exp (↑(-z.1*z.2)*Complex.I))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable.comp_snd)
  have hi : Integrable g (volume.prod volume) :=
    (φ.integrable.norm.mul_prod hf.norm).mono' hg (by
      filter_upwards with z
      simp [g, Complex.norm_exp, Complex.mul_re])
  simp_rw [sourceInverseKernel_formula, mul_smul_comm, ← integral_const_mul]
  rw [integral_smul, integral_integral_swap hi]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have he : -2*Real.pi*x*(r/(2*Real.pi)) = -x*r := by field_simp
  rw [he, smul_eq_mul]
  ring

 theorem sourceSchwartz_inversion (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (2*Real.pi)⁻¹ • (∫ r, Complex.exp (↑(r*y)*Complex.I) * 𝓕 φ (r/(2*Real.pi))) = φ y := by
  have hs := Measure.integral_comp_div
    (fun u : ℝ => Complex.exp (↑(2*Real.pi*u*y)*Complex.I) * 𝓕 φ u) (2*Real.pi)
  have he (r : ℝ) : 2*Real.pi*(r/(2*Real.pi))*y = r*y := by field_simp
  simp_rw [he] at hs
  rw [hs, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi), smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]
  have h := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ y)
    (show (𝓕⁻ (𝓕 φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = φ from
      FourierTransform.fourierInv_fourier_eq φ)
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', real_inner_eq_re_inner,
    RCLike.inner_apply, conj_trivial, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

 theorem source_characteristic_schwartz_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (φ : 𝓢(ℝ, ℂ)) :
    (2*Real.pi)⁻¹ • (∫ r, charFun τ r * 𝓕 φ (r/(2*Real.pi))) = ∫ y, φ y ∂τ := by
  let f : ℝ → ℂ := fun r => 𝓕 φ (r/(2*Real.pi))
  have hf : Integrable f := (𝓕 φ).integrable.comp_div (by positivity)
  let g : ℝ × ℝ → ℂ := fun z => Complex.exp (↑(z.1*z.2)*Complex.I)*f z.1
  have hp : Integrable g (volume.prod τ) :=
    (hf.norm.comp_fst τ).mono' (by dsimp [g, f]; fun_prop) (by
      filter_upwards with z
      simp [g, Complex.norm_exp, Complex.mul_re])
  simp_rw [charFun_apply_real, ← integral_mul_const]
  have he (r y : ℝ) : Complex.exp ((r:ℂ)*(y:ℂ)*Complex.I) * f r = g (r,y) := by
    simp [g, Complex.ofReal_mul]
  change (2*Real.pi)⁻¹ • (∫ r : ℝ, ∫ y : ℝ, Complex.exp ((r:ℂ)*(y:ℂ)*Complex.I) * f r ∂τ) = _
  simp_rw [he]
  rw [integral_integral_swap hp, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  exact sourceSchwartz_inversion φ y

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_LowFrequencyKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem schwartz_charFun_integrable (f : 𝓢(ℝ, ℂ)) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun r => f r * charFun τ r) := by
  apply (f.integrable.norm.mul_const (τ.real univ)).mono' (by fun_prop)
  filter_upwards with r
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_charFun_le r) (norm_nonneg _)

 theorem schwartzKernelMeasureConvolution_test (f : 𝓢(ℝ, ℂ))
    (τ : Measure ℝ) [IsFiniteMeasure τ] (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * kernelMeasureConvolution (sourceInverseKernel f) τ x) =
      (2*Real.pi)⁻¹ • ∫ r, f r * (charFun τ r * 𝓕 φ (r/(2*Real.pi))) := by
  have he : kernelMeasureConvolution (sourceInverseKernel f) τ =
      sourceInverseKernel (fun r => f r * charFun τ r) :=
    funext (sourceInverseKernel_measure f f.continuous f.integrable τ)
  rw [he, sourceInverseKernel_pairing _ (schwartz_charFun_integrable f τ) φ]
  simp only [mul_assoc]

 theorem schwartz_cutoff_test_integrable (f φ : 𝓢(ℝ, ℂ)) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun r => f r * (charFun τ r * 𝓕 φ (r/(2*Real.pi)))) := by
  have h2 := (schwartz_charFun_integrable f τ)
  have hb : ∃ C : ℝ, ∀ r, ‖𝓕 φ (r/(2*Real.pi))‖ ≤ C := by
    obtain ⟨C,_,hC⟩ := (𝓕 φ).decay 0 0
    exact ⟨C, fun r => by simpa using hC (r/(2*Real.pi))⟩
  obtain ⟨C,hC⟩ := hb
  apply (h2.norm.mul_const C).mono' (by fun_prop)
  filter_upwards with r
  rw [← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC r) (norm_nonneg _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellSummability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

 theorem summable_dyadic_decay {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (2:ℝ)^(-a*(n:ℝ))) := by
  have hq : (2:ℝ)^(-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  convert summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) (-a)) hq using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

 theorem shellL2Term_norm_sq_le (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    ‖shellL2Term τN n‖^2 ≤ (2*Real.pi)⁻¹ * shellEnergy (τN (n+1)) (n+1) := by
  rw [shellL2Term, ← integral_sq_norm_toLp]
  exact (shellKernelMeasureConvolution_L2 (τN (n+1)) n).2

 theorem shellL2Term_norm_summable (τN : ℕ → FiniteMeasure ℝ)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C) (N₀ : ℕ)
    (hb : ∀ N ≥ N₀, shellEnergy (τN N) N ≤ C*(2:ℝ)^(-γ*(N:ℝ))) :
    Summable (fun n => ‖shellL2Term τN n‖) := by
  have hs := (summable_dyadic_decay (half_pos hγ)).mul_left (Real.sqrt ((2*Real.pi)⁻¹*C))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (2*Real.pi)⁻¹ * shellEnergy (τN (n+1)) (n+1) := shellL2Term_norm_sq_le τN n
    _ ≤ (2*Real.pi)⁻¹ * (C*(2:ℝ)^(-γ*((n+1:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (hb _ (by omega)) (by positivity)
    _ ≤ (2*Real.pi)⁻¹ * (C*(2:ℝ)^(-γ*(n:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith
    _ = (Real.sqrt ((2*Real.pi)⁻¹*C) * (2:ℝ)^(-(γ/2)*(n:ℝ)))^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (by norm_num)]
      rw [← mul_assoc]
      congr 2
      push_cast
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellErrorSummability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

 theorem shellL1Error_norm_le (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    ‖shellL1Error τ τN n‖ ≤ (variationDistance τ (τN (n+1))).toReal *
      ∫ x, ‖sourceShellKernel 0 x‖ := by
  have hi := (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).1
  rw [shellL1Error, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  exact (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SchwartzLpTests
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

 theorem schwartzLpTest_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : Lp (α := ℝ) ℂ p volume) : schwartzLpTest p φ f = ∫ x, φ x * f x := by
  exact Lp.toTemperedDistribution_apply f φ

 theorem schwartzLpTest_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : ℝ → ℂ) (hf : MemLp f p volume) :
    schwartzLpTest p φ (hf.toLp f) = ∫ x, φ x * f x := by
  rw [schwartzLpTest_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

 theorem schwartzLpTest_sum_tendsto (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : ℕ → Lp (α := ℝ) ℂ p volume) (hf : Summable f) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, schwartzLpTest p φ (f n)) atTop
      (𝓝 (schwartzLpTest p φ (∑' n, f n))) := by
  simpa only [Function.comp_def, map_sum] using
    ((schwartzLpTest p φ).continuous.tendsto (∑' n, f n)).comp hf.tendsto_sum_tsum_nat

 theorem schwartzLpTest_shell_recombine (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    (φ : 𝓢(ℝ, ℂ)) (n : ℕ) :
    schwartzLpTest 1 φ (shellL1Error τ τN n) + schwartzLpTest 2 φ (shellL2Term τN n) =
      ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
  rw [shellL1Error, shellL2Term, schwartzLpTest_toLp, schwartzLpTest_toLp]
  have ht : Integrable (fun x => φ x * kernelMeasureConvolution (sourceShellKernel n) τ x) :=
    (φ.memLp_top volume).integrable_mul
      (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 τ n).1)
  have hn : Integrable (fun x => φ x *
      kernelMeasureConvolution (sourceShellKernel n) (τN (n+1)) x) :=
    (φ.memLp_top volume).integrable_mul
      (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 (τN (n+1)) n).1)
  simp_rw [mul_sub]
  rw [integral_sub ht hn, sub_add_cancel]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_MonotoneShellVariation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The monotone-variation step in the shell reconstruction

The proof of the manuscript's `asm:monotone-shell` uses summable positive
measure increments ζₙ = αₙ − αₙ₊₁. After interchanging a finite sum of
Fourier bands with these increments, the correction is
`∑' n, (Q (min n M) - Qbase) (ζ n)`. It converges in any Banach
space by the uniform bounds for the low-pass operators.
No rate of convergence of αₙ to α∞ is required.
-/

namespace Falconer
open Filter
open scoped Topology

/-- Positive increments of a decreasing, nonnegative sequence are summable.
For the shell lemma, `m n` is the total mass of `α n`. -/
theorem summable_antitone_mass_increments (m : ℕ → ℝ)
    (hm : Antitone m) (hpos : ∀ n, 0 ≤ m n) :
    Summable (fun n => m n - m (n + 1)) := by
  apply summable_of_sum_range_le (fun n => sub_nonneg.mpr (hm (Nat.le_succ n)))
    (c := m 0)
  intro N
  have he : ∑ n ∈ Finset.range N, (m n - m (n + 1)) = m 0 - m N := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  rw [he]
  exact sub_le_self _ (hpos N)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MonotoneMeasureMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive increments of decreasing finite measures

This is the measure-theoretic telescoping step of `asm:monotone-shell`.
The total variation of each positive decrement is its mass, and those
masses are summable. No quantitative convergence rate is introduced.
-/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- Monotonicity and finite initial mass supply precisely the summability
needed for the variation correction in the shell argument. -/
theorem summable_antitone_measure_decrements (α : ℕ → Measure X)
    [∀ n, IsFiniteMeasure (α n)] (hα : Antitone α) :
    Summable (fun n => (α n - α (n + 1)).real univ) := by
  have hm : Antitone (fun n => (α n).real univ) := by
    intro i j hij
    exact ENNReal.toReal_mono (measure_ne_top (α i) univ) (hα hij univ)
  have hsum := summable_antitone_mass_increments (fun n => (α n).real univ)
    hm (fun _ => measureReal_nonneg)
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [Measure.real, Measure.sub_apply MeasurableSet.univ (hα (Nat.le_succ n)),
    ENNReal.toReal_sub_of_le (hα (Nat.le_succ n) univ) (measure_ne_top (α n) univ)]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_MonotoneLowpass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Low-pass terms for the decreasing-measure shell argument

The Schwartz Fourier cutoffs represent the low-pass terms of shell
reconstruction. The L¹ bound is uniform in the dyadic cutoff index.
-/

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem dyadicLowKernel_dilate (n : ℕ) (x : ℝ) :
    dyadicLowKernel n x = (2 : ℝ)^n • sourceLowKernel ((2 : ℝ)^n * x) := by
  have he : (dyadicLowpassSchwartz n : ℝ → ℂ) =
      fun r => sourceLowpassSchwartz (r / (2 : ℝ)^n) := by
    funext r
    simp only [dyadicLowpassSchwartz_apply, sourceLowpassSchwartz_apply,
      sourceShellLowpass, pow_zero, div_one]
  rw [dyadicLowKernel, he, sourceInverseKernel_dilate _ (by positivity),
    abs_of_pos (by positivity : (0 : ℝ) < 2^n)]
  rfl

theorem dyadicLowKernel_uniform_L1 (n : ℕ) :
    (∫ x, ‖dyadicLowKernel n x‖) = ∫ x, ‖sourceLowKernel x‖ := by
  simp_rw [dyadicLowKernel_dilate n, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2^n)]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun x => ‖sourceLowKernel x‖) ((2 : ℝ)^n), smul_eq_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2^n)⁻¹)]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

theorem dyadicLowTerm_norm_le (n : ℕ) (τ : FiniteMeasure ℝ) :
    ‖dyadicLowTerm n τ‖ ≤ (τ : Measure ℝ).real univ * ∫ x, ‖sourceLowKernel x‖ := by
  have hi := (kernelMeasureConvolution_L1 (dyadicLowKernel n)
    (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) τ).1
  rw [dyadicLowTerm, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  simpa only [dyadicLowKernel_uniform_L1] using
    (kernelMeasureConvolution_L1 (dyadicLowKernel n)
      (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) τ).2

theorem dyadicLowTerm_test (n : ℕ) (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    schwartzLpTest 1 φ (dyadicLowTerm n τ) =
      (2 * Real.pi)⁻¹ • ∫ r, sourceShellLowpass n r •
        (charFun (τ : Measure ℝ) r * 𝓕 φ (r / (2 * Real.pi))) := by
  rw [dyadicLowTerm, schwartzLpTest_toLp]
  simpa only [dyadicLowKernel, dyadicLowpassSchwartz_apply, Complex.real_smul] using
    schwartzKernelMeasureConvolution_test (dyadicLowpassSchwartz n) τ φ

/-- Uniform low-pass bounds make the variation series absolutely convergent.
The increments here are the actual positive differences of finite measures. -/
theorem summable_dyadicLowTerm_decrements (α : ℕ → FiniteMeasure ℝ)
    (hα : Antitone (fun n => (α n : Measure ℝ))) :
    Summable (fun n => ‖dyadicLowTerm (n + 1)
      ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩ -
      dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩‖) := by
  let C := ∫ x, ‖sourceLowKernel x‖
  have hs := (Falconer.summable_antitone_measure_decrements
    (fun n => (α n : Measure ℝ)) hα).mul_left (2 * C)
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  calc
    _ ≤ ‖dyadicLowTerm (n + 1)
        ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩‖ +
        ‖dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩‖ := norm_sub_le _ _
    _ ≤ ((α n : Measure ℝ) - α (n + 1)).real univ * C +
        ((α n : Measure ℝ) - α (n + 1)).real univ * C :=
      add_le_add (dyadicLowTerm_norm_le _ _) (dyadicLowTerm_norm_le _ _)
    _ = _ := by ring

end PlanarFalconer
namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

/-- Convolution preserves sums of finite positive measures in L¹. -/
theorem dyadicLowTerm_add (n : ℕ) (μ ν : FiniteMeasure ℝ) :
    dyadicLowTerm n (μ + ν) = dyadicLowTerm n μ + dyadicLowTerm n ν := by
  apply Lp.ext
  have hsum := (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1
    (dyadicLowKernel n) (dyadicLowKernel_continuous n)
    (dyadicLowKernel_integrable n) (μ + ν)).1).coeFn_toLp
  have hμ := (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1
    (dyadicLowKernel n) (dyadicLowKernel_continuous n)
    (dyadicLowKernel_integrable n) μ).1).coeFn_toLp
  have hν := (memLp_one_iff_integrable.mpr (kernelMeasureConvolution_L1
    (dyadicLowKernel n) (dyadicLowKernel_continuous n)
    (dyadicLowKernel_integrable n) ν).1).coeFn_toLp
  have hiμ := (kernelMeasureConvolution_prod_integrable (dyadicLowKernel n)
    (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) μ).prod_right_ae
  have hiν := (kernelMeasureConvolution_prod_integrable (dyadicLowKernel n)
    (dyadicLowKernel_continuous n) (dyadicLowKernel_integrable n) ν).prod_right_ae
  filter_upwards [hsum, hμ, hν, Lp.coeFn_add (dyadicLowTerm n μ) (dyadicLowTerm n ν),
    hiμ, hiν] with x hxsum hxμ hxν hxadd hxintμ hxintν
  rw [hxadd]
  simp only [Pi.add_apply]
  change _ = _ at hxsum hxμ hxν
  rw [show dyadicLowTerm n (μ + ν) x = kernelMeasureConvolution (dyadicLowKernel n)
    (μ + ν) x from hxsum, show dyadicLowTerm n μ x =
    kernelMeasureConvolution (dyadicLowKernel n) μ x from hxμ,
    show dyadicLowTerm n ν x = kernelMeasureConvolution (dyadicLowKernel n) ν x from hxν]
  exact integral_add_measure hxintμ hxintν

/-- The positive measure difference is sent to the difference of low-pass terms. -/
theorem dyadicLowTerm_sub_of_le (n : ℕ) (μ ν : FiniteMeasure ℝ)
    (h : (ν : Measure ℝ) ≤ μ) :
    dyadicLowTerm n ⟨(μ : Measure ℝ) - ν, inferInstance⟩ =
      dyadicLowTerm n μ - dyadicLowTerm n ν := by
  let ξ : FiniteMeasure ℝ := ⟨(μ : Measure ℝ) - ν, inferInstance⟩
  change dyadicLowTerm n ξ = dyadicLowTerm n μ - dyadicLowTerm n ν
  apply eq_sub_iff_add_eq.mpr
  rw [← dyadicLowTerm_add]
  congr 1
  apply Subtype.ext
  exact Measure.sub_add_cancel_of_le h

/-- Finite summation by parts in the actual L¹ space of low-pass convolutions.
The final term is a single low-pass difference applied to the remaining tail. -/
theorem dyadicLowTerm_summation_by_parts (α : ℕ → FiniteMeasure ℝ)
    (hα : Antitone (fun n => (α n : Measure ℝ))) (M : ℕ) :
    (∑ j ∈ Finset.range M, (dyadicLowTerm (j + 1) (α j) - dyadicLowTerm j (α j))) =
      (∑ n ∈ Finset.range M,
        (dyadicLowTerm (n + 1) ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩ -
        dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n + 1), inferInstance⟩)) +
      (dyadicLowTerm M (α M) - dyadicLowTerm 0 (α M)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
      dyadicLowTerm_sub_of_le _ _ _ (hα (Nat.le_succ M)),
      dyadicLowTerm_sub_of_le _ _ _ (hα (Nat.le_succ M))]
    abel

end PlanarFalconer
namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

/-- The dyadic cutoffs converge to the original measure in Schwartz tests. -/
theorem dyadicLowTerm_test_tendsto (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun n => schwartzLpTest 1 φ (dyadicLowTerm n τ)) atTop
      (𝓝 (∫ x, φ x ∂(τ : Measure ℝ))) := by
  simp_rw [dyadicLowTerm_test]
  have h := (sourceShellLowpass_fourier_test (τ : Measure ℝ)
    (fun r => 𝓕 φ (r / (2 * Real.pi)))
    ((𝓕 φ).integrable.comp_div (by positivity))).const_smul ((2 * Real.pi)⁻¹)
  rw [source_characteristic_schwartz_test] at h
  exact h

/-- The difference of adjacent cutoff tests is exactly the existing shell
kernel test, with no change to the Fourier convention. -/
theorem dyadicLowTerm_band_test (n : ℕ) (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    schwartzLpTest 1 φ (dyadicLowTerm (n + 1) τ - dyadicLowTerm n τ) =
      ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
  rw [map_sub, dyadicLowTerm_test, dyadicLowTerm_test]
  have hi (m : ℕ) : Integrable (fun r => sourceShellLowpass m r •
      (charFun (τ : Measure ℝ) r * 𝓕 φ (r / (2 * Real.pi)))) := by
    simpa only [dyadicLowpassSchwartz_apply, Complex.real_smul] using
      schwartz_cutoff_test_integrable (dyadicLowpassSchwartz m) φ τ
  rw [← smul_sub, ← integral_sub (hi _) (hi _)]
  simp_rw [← sub_smul]
  change (2 * Real.pi)⁻¹ • (∫ r, sourceShellBand n r •
    (charFun (τ : Measure ℝ) r * 𝓕 φ (r / (2 * Real.pi)))) = _
  simpa only [sourceShellKernel, sourceShellSchwartz_apply, Complex.real_smul] using
    (schwartzKernelMeasureConvolution_test (sourceShellSchwartz n) τ φ).symm

/-- A decreasing family's remaining tail vanishes after any varying cutoff,
provided only that its mass tends to zero. -/
theorem dyadicLowTerm_tail_tendsto (α : ℕ → FiniteMeasure ℝ) (τ : FiniteMeasure ℝ)
    (hle : ∀ n, (τ : Measure ℝ) ≤ α n)
    (hmass : Tendsto (fun n => ((α n : Measure ℝ) - τ).real univ) atTop (𝓝 0))
    (k : ℕ → ℕ) :
    Tendsto (fun n => dyadicLowTerm (k n) (α n) - dyadicLowTerm (k n) τ)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun n => ((α n : Measure ℝ) - τ).real univ *
      ∫ x, ‖sourceLowKernel x‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hmass.mul_const (∫ x, ‖sourceLowKernel x‖)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) ht
  rw [← dyadicLowTerm_sub_of_le _ _ _ (hle n)]
  exact dyadicLowTerm_norm_le _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PairExceptional
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two-sided exceptional sets measured on the original pair -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem pairExceptional_outside {A B : Set (Space d)} {D E : Set (Space d × Space d)}
    {z : Space d × Space d} (hz : z ∉ pairExceptional A B D E) :
    z.1 ∈ A ∧ z.2 ∈ B ∧ z ∉ D ∧ z.swap ∉ E := by
  classical
  simp only [pairExceptional,mem_union,not_or,mem_prod,mem_compl_iff,mem_univ,true_and,
    and_true,not_not,mem_preimage] at hz
  exact ⟨hz.1.1.1,hz.1.1.2,hz.1.2,hz.2⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularRoot
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual regularized classes as initial policy states -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor sourcePolicyBlock sourceSmoothingLevels)

 theorem descriptorNets_cover (d N : ℕ) (σ : ℝ) (b : PolicyDescriptor) (w : Sphere d) :
    ∃ c ∈ descriptorNets d N σ b, dist w c ≤ descriptorMaskRadius N σ b/2 :=
  (Classical.choose_spec (finite_separated_cap_net d (descriptorMaskRadius_pos N σ b))).2.1 w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularListRestoration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual entry list is covered by the common restoration event -/

namespace Falconer
open Set

 theorem regularOuterList_subset_valid {d N : ℕ} (profile : ℝ → ℝ) {κ : ℝ}
    (hN : 0 < N) (hκ : 0 < κ) {c : ℕ} (hc : c ≤ N) :
    regularOuterList (d := d) profile N κ c ⊆ validDescriptors N := by
  intro b hb
  apply (mem_validDescriptors N b).mpr
  obtain rfl | hb := Finset.mem_insert.mp hb
  · exact ⟨Nat.zero_le c,hc⟩
  · exact policy_descriptor_valid _ (PlanarFalconer.sourcePolicyBlock_pos hN hκ) le_rfl
      (Finset.mem_filter.mp hb).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularOuterMask
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual outer mask, with both oriented restoration identities -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularOuterMask_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (profile : ℝ → ℝ) (N : ℕ) (σ κ : ℝ) (c : ℕ) :
    Measurable (Function.uncurry (regularOuterMask Q ρ profile N σ κ c)) :=
  descriptorAmbientProduct_measurable ..

theorem regularOuterMask_bounds (Q : DyadicCube d) (ρ : Measure (Space d))
    (profile : ℝ → ℝ) (N : ℕ) (σ κ : ℝ) (c : ℕ) (x w : Space d) :
    regularOuterMask Q ρ profile N σ κ c x w ∈ Icc (0:ℝ) 1 := by
  unfold regularOuterMask descriptorAmbientProduct
  constructor
  · exact Finset.prod_nonneg (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).1)
  · exact Finset.prod_le_one
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).1)
      (fun b _ => (descriptorAmbientMask_global_bounds Q ρ _ N σ _ 0 b _ x w).2)

theorem uniform_regularOuterMask_restoration {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N → ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (profile : ℝ → ℝ),
      ∀ c ≤ N, ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)) (x y : Space d),
      x ∈ Q.carrier → x ≠ y → (x,y) ∈ G →
      (x,y) ∉ allDescriptorTestBad w₀ Q ρ (fun u => profile (u/N)) N σ
        (PlanarFalconer.sourceSmoothingLevels σ κ) G →
      regularOuterMask Q ρ profile N σ κ c x (NormedSpace.normalize (x-y)) = 1 ∧
      regularOuterMask Q ρ profile N σ κ c x (NormedSpace.normalize (y-x)) = 1 := by
  have hJ := PlanarFalconer.sourceSmoothingLevels_pos hσ hκ
  obtain ⟨N₁,h₁⟩ := uniform_all_tests_restoration (d := d) hσ hJ
  obtain ⟨N₂,h₂⟩ := uniform_descriptorProduct_core (d := d) hσ hJ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN hNp Q hQ ρ _ profile c hc w₀ G x y hx hxy hG hgood
  have hvalid := regularOuterList_subset_valid (d := d) profile hNp hκ hc
  constructor
  · exact h₁ N ((le_max_left _ _).trans hN) Q hQ ρ _ _ hvalid _
      (fun b _ => descriptorNets_cover d N σ b) w₀ G x y hx hxy hG hgood
  · have hh := h₂ N ((le_max_right _ _).trans hN) Q hQ ρ _ _
      (fun b hb => (mem_validDescriptors N b).mp (hvalid hb)) _
      (fun b _ => descriptorNets_cover d N σ b) 0 x hx (normalizeToSphere w₀ (y-x)) (by
        intro b hb
        by_contra hn
        exact hgood (mem_iUnion₂.mpr ⟨b,hvalid hb,hG,hn⟩))
    rw [← descriptorAmbientProduct_sphere] at hh
    simpa only [regularOuterMask,normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hxy.symm)] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularSourceClasses
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual regular classes with their source profiles and block scales -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem actual_regular_source_classes (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {s C lam : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) (hC : 0 ≤ C)
    (hlam : 0 < lam)
    (hball : ∀ x : Space d, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves Q μ N
      let F := regularizationLabel Q μ N B
      0 < N ∧ 0 < B ∧ (B:ℝ) ≤ lam*N ∧
      (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam ∧
      (regularizationIndex Q μ N B t).card ≤ N^(4*H+2) ∧
      μ (⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T)ᶜ ≤
        ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^(4*H+2):ℕ)*t ∧
      ∀ T ∈ regularizationIndex Q μ N B t,
        t ≤ classMeasure Q μ L F T univ ∧
        ∃ p ∈ L, F p = T ∧
          RegularizedProfileData Q (sourceClass Q μ N B p) N s lam
            (sourceUnitProfile Q μ N B p) := by
  classical
  obtain ⟨H,N₁,hH,hHb,hscales⟩ := PlanarFalconer.exists_bounded_regularization_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(2*Real.sqrt d*Q.side)^s)
  obtain ⟨N₃,hN₃⟩ := exists_nat_gt ((d:ℝ)/lam)
  refine ⟨H,max (max H (d+3)) (max N₁ (max N₂ N₃)),hH,hHb,?_⟩
  intro N hN
  dsimp only
  have hNH : H ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hdN : d+3 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₃' : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hscale := hscales N hN₁
  have hsmall : s/(N:ℝ) ≤ lam := by
    apply (div_le_iff₀ (by exact_mod_cast hscale.1 : 0 < (N:ℝ))).mpr
    have hh : (d:ℝ)/lam < (N:ℝ) := hN₃.trans_le (by exact_mod_cast hN₃')
    have hh' := (div_lt_iff₀ hlam).mp hh
    nlinarith
  refine ⟨hscale.1,hscale.2.1,hscale.2.2.2.1,hscale.2.2.2.2,
    regularization_count_polynomial Q μ hH hNH hdN _,
    regularization_discarded_global Q hQ μ hcarry hH hNH hdN _,?_⟩
  intro T hT
  refine ⟨(Finset.mem_filter.mp hT).2,?_⟩
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
  refine ⟨p,hp,he,?_⟩
  apply sourceClass_profile_data Q hQ μ hscale.1 hscale.2.1 hs hsmall
    hscale.2.2.2.1 hscale.2.2.2.2 hp
  intro j hj
  apply sourceProfile_frostman_lower Q hQ μ hscale.1 hscale.2.1
    hscale.2.2.2.1 hscale.2.2.2.2 hp
    (retained_label_real_mass_lower Q μ (by rwa [he])) _ hj
  intro k hk P hP
  have hh := dyadic_cell_frostman_profile_bound hd Q hQ μ hC hball hscale.1 P
  rw [hP] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PartitionEndpointDistance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact distance law for class-dependent endpoint masks -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem endpointPairMask_measurable (B C : Space d → Space d → ℝ)
    (hB : Measurable (Function.uncurry B)) (hC : Measurable (Function.uncurry C)) :
    Measurable (endpointPairMask B C) := by
  have hn : Measurable (fun z : Space d × Space d => NormedSpace.normalize (z.1-z.2)) := by
    unfold NormedSpace.normalize
    fun_prop
  exact (hB.comp (measurable_fst.prodMk hn)).mul (hC.comp (measurable_snd.prodMk hn))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ProductPartitionMask
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable mask on a pair of finite disjoint spatial partitions -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ} {ι κ : Type*}

theorem product_regions_disjoint (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (hS : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hT : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (T i) (T j)) :
    ∀ i ∈ F.product G, ∀ j ∈ F.product G, i ≠ j →
      Disjoint (S i.1 ×ˢ T i.2) (S j.1 ×ˢ T j.2) := by
  intro i hi j hj hij
  obtain ⟨hi₁,hi₂⟩ := Finset.mem_product.mp hi
  obtain ⟨hj₁,hj₂⟩ := Finset.mem_product.mp hj
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  by_cases h : i.1 = j.1
  · have hne : i.2 ≠ j.2 := fun h' => hij (Prod.ext h h')
    exact Set.disjoint_left.mp (hT i.2 hi₂ j.2 hj₂ hne) hzi.2 hzj.2
  · exact Set.disjoint_left.mp (hS i.1 hi₁ j.1 hj₁ h) hzi.1 hzj.1

theorem productPartitionMask_measurable (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (B C : ι × κ → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i)) (hT : ∀ i ∈ G, MeasurableSet (T i))
    (hB : ∀ i ∈ F.product G, Measurable (Function.uncurry (B i)))
    (hC : ∀ i ∈ F.product G, Measurable (Function.uncurry (C i))) :
    Measurable (productPartitionMask F G S T B C) :=
  finitePartitionMask_measurable _ _ _
    (fun i hi => (hS i.1 (Finset.mem_product.mp hi).1).prod (hT i.2 (Finset.mem_product.mp hi).2))
    (fun i hi => endpointPairMask_measurable (B i) (C i) (hB i hi) (hC i hi))

theorem productPartitionMask_bounds (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (B C : ι × κ → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hT : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (T i) (T j))
    (hB : ∀ i ∈ F.product G, ∀ x w, B i x w ∈ Icc (0:ℝ) 1)
    (hC : ∀ i ∈ F.product G, ∀ x w, C i x w ∈ Icc (0:ℝ) 1)
    (z : Space d × Space d) : productPartitionMask F G S T B C z ∈ Icc (0:ℝ) 1 := by
  apply finitePartitionMask_bounds _ _ _ (product_regions_disjoint F G S T hS hT)
  intro i hi z
  have hb := hB i hi z.1 (NormedSpace.normalize (z.1-z.2))
  have hc := hC i hi z.2 (NormedSpace.normalize (z.1-z.2))
  exact ⟨mul_nonneg hb.1 hc.1,(mul_le_mul hb.2 hc.2 hc.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem productPartitionMask_eq_one (F : Finset ι) (G : Finset κ)
    (S : ι → Set (Space d)) (T : κ → Set (Space d))
    (B C : ι × κ → Space d → Space d → ℝ)
    (hS : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hT : ∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (T i) (T j))
    {z : Space d × Space d} (hzS : z.1 ∈ ⋃ i ∈ F, S i) (hzT : z.2 ∈ ⋃ i ∈ G, T i)
    (hB : ∀ i ∈ F.product G, z.1 ∈ S i.1 → z.2 ∈ T i.2 →
      B i z.1 (NormedSpace.normalize (z.1-z.2)) = 1)
    (hC : ∀ i ∈ F.product G, z.1 ∈ S i.1 → z.2 ∈ T i.2 →
      C i z.2 (NormedSpace.normalize (z.1-z.2)) = 1) :
    productPartitionMask F G S T B C z = 1 := by
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hzS
  obtain ⟨j,hj,hyj⟩ := mem_iUnion₂.mp hzT
  have hij : (i,j) ∈ F.product G := Finset.mem_product.mpr ⟨hi,hj⟩
  rw [productPartitionMask,finitePartitionMask_on _ _ _
    (product_regions_disjoint F G S T hS hT) hij ⟨hxi,hyj⟩]
  simp only [endpointPairMask,hB (i,j) hij hxi hyj,hC (i,j) hij hxi hyj,mul_one]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationPairMask
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoration of the actual two-class outer mask on the original pair -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_regularizationPairMask_restoration {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N →
      ∀ (Q₁ Q₂ : DyadicCube d), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (p₁ p₂ : List ℕ → CellPath d),
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N) →
      ∀ c : List ℕ × List ℕ → ℕ,
      (∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂), c i ≤ N) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)) (z : Space d × Space d),
      z.1 ≠ z.2 → z ∈ G →
      z ∉ regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ G →
      regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_regularOuterMask_restoration (d := d) hσ hκ
  refine ⟨N₀,?_⟩
  intro N hN hNp Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ B₁ B₂ t₁ t₂ p₁ p₂ hp₁ hp₂ c hc w₀ G z hne hz hout
  have hside₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  obtain ⟨hret₁,hret₂,hbad₁,hbad₂⟩ := pairExceptional_outside hout
  apply productPartitionMask_eq_one _ _ _ _ _ _
    (hS := fun _ _ _ _ hne => regularizationSet_disjoint Q₁ hside₁ μ N B₁ hne)
    (hT := fun _ _ _ _ hne => regularizationSet_disjoint Q₂ hside₂ ν N B₂ hne)
    hret₁ hret₂
  · intro i hi hx hy
    have hi₁ := (Finset.mem_product.mp hi).1
    let : IsProbabilityMeasure (sourceClass Q₁ μ N B₁ (p₁ i.1)) :=
      regularization_class_probability Q₁ hside₁ μ N B₁ (hp₁ i.1 hi₁)
    have hgood : z ∉ allDescriptorTestBad w₀ Q₁ (sourceClass Q₁ μ N B₁ (p₁ i.1))
        (fun u => sourceUnitProfile Q₁ μ N B₁ (p₁ i.1) (u/N)) N σ
          (PlanarFalconer.sourceSmoothingLevels σ κ) G := by
      intro hb
      exact hbad₁ (mem_iUnion₂.mpr ⟨i.1,hi₁,⟨hx,mem_univ _⟩,hb⟩)
    exact (h₀ N hN hNp Q₁ hQ₁ _ _ (c i) (hc i hi) w₀ G z.1 z.2
      (leafUnion_subset Q₁ hside₁ _ hx) hne hz hgood).1
  · intro i hi hx hy
    have hi₂ := (Finset.mem_product.mp hi).2
    let : IsProbabilityMeasure (sourceClass Q₂ ν N B₂ (p₂ i.2)) :=
      regularization_class_probability Q₂ hside₂ ν N B₂ (hp₂ i.2 hi₂)
    have hgood : z.swap ∉ allDescriptorTestBad w₀ Q₂ (sourceClass Q₂ ν N B₂ (p₂ i.2))
        (fun u => sourceUnitProfile Q₂ ν N B₂ (p₂ i.2) (u/N)) N σ
          (PlanarFalconer.sourceSmoothingLevels σ κ) (Prod.swap ⁻¹' G) := by
      intro hb
      exact hbad₂ (mem_iUnion₂.mpr ⟨i.2,hi₂,⟨hy,mem_univ _⟩,hb⟩)
    exact (h₀ N hN hNp Q₂ hQ₂ _ _ (c i) (hc i hi) w₀ (Prod.swap ⁻¹' G) z.2 z.1
      (leafUnion_subset Q₂ hside₂ _ hy) hne.symm hz hgood).2

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationPairBounds
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability, range and original-pair cost of the assembled mask -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularizationPairMask_measurable (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ) :
    Measurable (regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c) :=
  productPartitionMask_measurable _ _ _ _ _ _
    (fun _ _ => regularizationSet_measurable _ _ _ _ _)
    (fun _ _ => regularizationSet_measurable _ _ _ _ _)
    (fun _ _ => regularOuterMask_measurable _ _ _ _ _ _ _)
    (fun _ _ => regularOuterMask_measurable _ _ _ _ _ _ _)

theorem regularizationPairMask_bounds (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ) (z : Space d × Space d) :
    regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z ∈ Icc (0:ℝ) 1 :=
  productPartitionMask_bounds _ _ _ _ _ _
    (fun _ _ _ _ hne => regularizationSet_disjoint Q₁ hQ₁ μ N B₁ hne)
    (fun _ _ _ _ hne => regularizationSet_disjoint Q₂ hQ₂ ν N B₂ hne)
    (fun _ _ => regularOuterMask_bounds _ _ _ _ _ _ _)
    (fun _ _ => regularOuterMask_bounds _ _ _ _ _ _ _) z

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScopedMaskVariation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mask need only be restored inside the coarse filter -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem filtered_masked_variation_on_le (f : X → ℝ) (hf : Measurable f)
    (π : Measure X) (w m : X → ℝ≥0∞) [IsFiniteMeasure (π.withDensity w)]
    (hw : Measurable w) (hm : Measurable m) (hm1 : ∀ x, m x ≤ 1)
    (Γ B : Set X) (hΓ : MeasurableSet Γ) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂π, w x ≤ C)
    (hout : ∀ᵐ x ∂π, x ∈ Γ → x ∉ B → m x = 1) :
    ∃ τ : FiniteMeasure ℝ,
      (τ : Measure ℝ) = ((π.restrict Γ).withDensity (fun x => w x*m x)).map f ∧
      PlanarFalconer.variationDistance
        ⟨filteredPushforward f (π.withDensity w) Γ,(by first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ τ ≤ C*π B := by
  have hfinite : IsFiniteMeasure ((π.restrict Γ).withDensity w) := by
    rw [← restrict_withDensity hΓ w]
    first | exact Measure.isProbabilityMeasure_map (by first | exact hf.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let := hfinite
  have hout' : ∀ᵐ x ∂π.restrict Γ, x ∉ B → m x = 1 := by
    filter_upwards [ae_restrict_of_ae hout,ae_restrict_mem hΓ] with x hx hΓx
    exact hx hΓx
  obtain ⟨σ,ρ,hσ,_hρ,hσeq,_hρeq,hvar⟩ := PlanarFalconer.masked_totalVariation_bound
    (π.restrict Γ) f hf w m hw hm hm1 B C (ae_restrict_of_ae hbound) hout'
  refine ⟨⟨σ,hσ⟩,hσeq,?_⟩
  have heq : filteredPushforward f (π.withDensity w) Γ =
      ((π.restrict Γ).withDensity w).map f := by
    unfold filteredPushforward
    rw [restrict_withDensity hΓ w]
  change ((filteredPushforward f (π.withDensity w) Γ).toSignedMeasure -
    σ.toSignedMeasure).totalVariation univ ≤ C*π B
  rw [Measure.toSignedMeasure_congr heq]
  exact hvar.trans (mul_le_mul' le_rfl (Measure.restrict_apply_le Γ B))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizationVariation
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-law variation cost of the actual regularized mask -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularizationPairDistance_eq_masked (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ)
    (Γ : Set (Space d × Space d)) :
    regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c Γ =
      (((μ.prod ν).restrict Γ).withDensity (fun z => distanceWeight (((d:ℝ)-1)/2) z *
        ENNReal.ofReal (regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z))).map
          (fun z => dist z.1 z.2) := by
  unfold regularizationPairDistance partitionEndpointDistance
  congr 1
  congr 1
  funext z
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg dist_nonneg _)]
  rfl

theorem uniform_regularization_variation {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hd : 1 ≤ d) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N →
      ∀ (Q₁ Q₂ : DyadicCube d), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (p₁ p₂ : List ℕ → CellPath d),
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N) →
      ∀ c : List ℕ × List ℕ → ℕ,
      (∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂), c i ≤ N) →
      ∀ (w₀ : Sphere d) (Γ D : Set (Space d × Space d)), MeasurableSet Γ →
      ∀ (δ : ℝ) (hδ : 0 < δ) (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2),
      ∃ τ : FiniteMeasure ℝ,
        (τ : Measure ℝ) = regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c Γ ∧
        letI := finite_withDensity_of_bounded (μ.prod ν) (distanceWeight (((d:ℝ)-1)/2))
          ENNReal.ofReal_lt_top (distanceWeight_upper hd hδ hsep)
        PlanarFalconer.variationDistance
          ⟨filteredPushforward (fun z : Space d × Space d => dist z.1 z.2)
            ((μ.prod ν).withDensity (distanceWeight (((d:ℝ)-1)/2))) Γ,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ τ ≤
          ENNReal.ofReal (δ^(-(((d:ℝ)-1)/2))) *
            ((μ.prod ν) D + (μ.prod ν)
              (regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ (Γ \ D))) := by
  obtain ⟨N₀,h₀⟩ := uniform_regularizationPairMask_restoration (d := d) hσ hκ
  refine ⟨N₀,?_⟩
  intro N hN hNp Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ B₁ B₂ t₁ t₂ p₁ p₂ hp₁ hp₂ c hc w₀ Γ D hΓ δ hδ hsep
  let w : Space d × Space d → ℝ≥0∞ := distanceWeight (((d:ℝ)-1)/2)
  let mask := regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c
  let E := regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ (Γ \ D)
  have hside₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hbound : ∀ᵐ z ∂μ.prod ν, w z ≤ ENNReal.ofReal (δ^(-(((d:ℝ)-1)/2))) :=
    distanceWeight_upper hd hδ hsep
  let := finite_withDensity_of_bounded (μ.prod ν) w ENNReal.ofReal_lt_top hbound
  have hout : ∀ᵐ z ∂μ.prod ν, z ∈ Γ → z ∉ D ∪ E → ENNReal.ofReal (mask z) = 1 := by
    filter_upwards [hsep] with z hz hΓz hgood
    have hnD : z ∉ D := fun h => hgood (Or.inl h)
    have hnE : z ∉ E := fun h => hgood (Or.inr h)
    have hne : z.1 ≠ z.2 := dist_pos.mp (hδ.trans_le hz)
    change ENNReal.ofReal (regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z) = 1
    rw [h₀ N hN hNp Q₁ Q₂ hQ₁ hQ₂ μ ν B₁ B₂ t₁ t₂ p₁ p₂ hp₁ hp₂ c hc w₀
      (Γ \ D) z hne ⟨hΓz,hnD⟩ hnE]
    simp
  obtain ⟨τ,hτ,hvar⟩ := filtered_masked_variation_on_le
    (fun z : Space d × Space d => dist z.1 z.2) (by fun_prop) (μ.prod ν) w
    (fun z => ENNReal.ofReal (mask z))
    (by unfold w distanceWeight; fun_prop)
    ((regularizationPairMask_measurable Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c).ennreal_ofReal)
    (fun z => (ENNReal.ofReal_le_ofReal (regularizationPairMask_bounds Q₁ Q₂ hside₁ hside₂
      μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z).2).trans_eq (by simp))
    Γ (D ∪ E) hΓ _ hbound hout
  refine ⟨τ,?_,?_⟩
  · rw [regularizationPairDistance_eq_masked]
    exact hτ
  · exact hvar.trans (mul_le_mul' le_rfl (measure_union_le _ _))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_AssemblyLosses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial restoration losses and the coarse product-filter cost -/

namespace Falconer
open Filter

theorem eventual_polynomial_decay {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      C*((N:ℝ)+1)^k*((2:ℝ)^N)^(-a) ≤ ((2:ℝ)^N)^(-a/2) := by
  obtain ⟨N₁,h₁⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < a/4) C
  obtain ⟨N₂,h₂⟩ := PlanarFalconer.fixed_polynomial_subpower k (by positivity : 0 < a/4)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hR : 0 < (2:ℝ)^N := by positivity
  have hp : ((N:ℝ)+1)^k ≤ ((2:ℝ)^N)^(a/4) :=
    (pow_le_pow_left₀ (by positivity)
      (by nlinarith [show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N] : (N:ℝ)+1 ≤ 4*N+1) k).trans
      (h₂ N ((le_max_right _ _).trans hN))
  calc
    _ ≤ (((2:ℝ)^N)^(a/4)*((2:ℝ)^N)^(a/4))*((2:ℝ)^N)^(-a) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (h₁ N ((le_max_left _ _).trans hN)) hp (by positivity) (by positivity)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR]; congr 1; ring

theorem eventual_partition_shell_decay {β θ : ℝ} (hβ : 0 < β) (hθ : 2*θ ≤ β/64) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, (k:ℝ) ≤ ((2:ℝ)^N)^θ →
      2*(k:ℝ)^2*((2:ℝ)^N)^(-β/16) ≤ ((2:ℝ)^N)^(-β/32) := by
  obtain ⟨N₀,h₀⟩ := Regularization.fixed_constant_absorbed (by positivity : 0 < β/64) 2
  refine ⟨N₀,?_⟩
  intro N hN k hk
  have hR : 0 < (2:ℝ)^N := by positivity
  have hR1 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hk2 : (k:ℝ)^2 ≤ ((2:ℝ)^N)^(β/64) := by
    calc
      _ ≤ (((2:ℝ)^N)^θ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hk 2
      _ = ((2:ℝ)^N)^(2*θ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR1 hθ
  calc
    _ ≤ (((2:ℝ)^N)^(β/64)*((2:ℝ)^N)^(β/64))*((2:ℝ)^N)^(-β/16) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (h₀ N hN) hk2 (by positivity) (by positivity)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR]; congr 1; ring

theorem dyadic_scale_power (N : ℕ) (a : ℝ) : ((2:ℝ)^N)^a = (2:ℝ)^(a*(N:ℝ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),mul_comm]

theorem summable_scale_decay {a : ℝ} (ha : 0 < a) :
    Summable (fun N : ℕ => ((2:ℝ)^N)^(-a)) := by
  simp_rw [dyadic_scale_power]
  exact PlanarFalconer.summable_dyadic_decay ha

theorem summable_polynomial_scale_decay {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) :
    Summable (fun N : ℕ => C*((N:ℝ)+1)^k*((2:ℝ)^N)^(-a)) := by
  obtain ⟨N₀,h₀⟩ := eventual_polynomial_decay (half_pos ha) |C| k
  apply (summable_scale_decay (show 0 < a/4 by positivity)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((N:ℝ)+1)^k),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hh := h₀ N hN
  have hR1 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  calc
    _ ≤ |C| *((N:ℝ)+1)^k*((2:ℝ)^N)^(-(a/2)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)) (by positivity)
    _ ≤ _ := by
      have he : -(a/2)/2 = -(a/4) := by ring
      simpa only [he] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RestorationSeries
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summability of the actual cap, class and descriptor deletion costs -/

namespace Falconer
open Filter
open scoped ENNReal Topology

theorem restorationError_nonneg {Cw Ccap : ℝ} (hw : 0 ≤ Cw) (hcap : 0 ≤ Ccap)
    (c lam σ : ℝ) (k₁ k₂ N : ℕ) : 0 ≤ restorationError Cw Ccap c lam σ k₁ k₂ N := by
  unfold restorationError
  positivity

theorem restorationError_summable (Cw Ccap : ℝ) {c lam σ : ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hσ : 0 < σ) (k₁ k₂ : ℕ) :
    Summable (restorationError Cw Ccap c lam σ k₁ k₂) := by
  have hcap := (summable_scale_decay hc).mul_left Ccap
  have hleaf := (summable_scale_decay (by norm_num : (0:ℝ) < 2)).mul_left 2
  have h₁ := summable_polynomial_scale_decay hlam 1 k₁
  have h₂ := summable_polynomial_scale_decay hlam 1 k₂
  have htest := summable_polynomial_scale_decay hσ 4 2
  change Summable (fun N : ℕ => Cw * (Ccap*((2:ℝ)^N)^(-c) + 2*((2:ℝ)^N)^(-2:ℝ) +
    ((N:ℝ)+1)^k₁*((2:ℝ)^N)^(-lam) + ((N:ℝ)+1)^k₂*((2:ℝ)^N)^(-lam) +
    4*((N:ℝ)+1)^2*((2:ℝ)^N)^(-σ)))
  simpa only [one_mul] using ((((hcap.add hleaf).add h₁).add h₂).add htest).mul_left Cw

theorem summable_of_restoration_error {f : ℕ → ℝ≥0∞} {Cw Ccap c lam σ : ℝ}
    (hw : 0 ≤ Cw) (hcap : 0 ≤ Ccap) (hc : 0 < c) (hlam : 0 < lam) (hσ : 0 < σ)
    (k₁ k₂ N₀ : ℕ)
    (hbound : ∀ N ≥ N₀, f N ≤ ENNReal.ofReal (restorationError Cw Ccap c lam σ k₁ k₂ N)) :
    Summable (fun N => (f N).toReal) := by
  apply (restorationError_summable Cw Ccap hc hlam hσ k₁ k₂).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound N hN)
  simpa only [ENNReal.toReal_ofReal (restorationError_nonneg hw hcap c lam σ k₁ k₂ N)] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SourceRepresentatives
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous actual leaf representatives for the retained classes -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem source_representatives (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) (s lam : ℝ)
    (h : ∀ T ∈ regularizationIndex Q μ N B t,
      ∃ p ∈ regularizationLeaves Q μ N, regularizationLabel Q μ N B p = T ∧
        RegularizedProfileData Q (sourceClass Q μ N B p) N s lam (sourceUnitProfile Q μ N B p)) :
    ∃ p : List ℕ → CellPath d,
      (∀ T ∈ regularizationIndex Q μ N B t, p T ∈ regularizationLeaves Q μ N) ∧
      (∀ T ∈ regularizationIndex Q μ N B t, regularizationLabel Q μ N B (p T) = T) ∧
      (∀ T ∈ regularizationIndex Q μ N B t,
        RegularizedProfileData Q (sourceClass Q μ N B (p T)) N s lam (sourceUnitProfile Q μ N B (p T))) := by
  classical
  let p : List ℕ → CellPath d := fun T =>
    if hT : T ∈ regularizationIndex Q μ N B t then (h T hT).choose else []
  refine ⟨p,?_,?_,?_⟩
  · intro T hT
    simpa only [p,dite_eq_left hT] using (h T hT).choose_spec.1
  · intro T hT
    simpa only [p,dite_eq_left hT] using (h T hT).choose_spec.2.1
  · intro T hT
    simpa only [p,dite_eq_left hT] using (h T hT).choose_spec.2.2

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SourceFamily
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the actual source family at every sufficiently large scale -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem eventual_source_family (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {s C lam : ℝ} (hs : 0 ≤ s) (hsd : s ≤ d) (hC : 0 ≤ C) (hlam : 0 < lam)
    (hball : ∀ x : Space d, ∀ r > 0, μ (Metric.ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ H N₀ : ℕ, 0 < H ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      0 < N ∧ 0 < B ∧ (B:ℝ) ≤ lam*N ∧
      (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam ∧
      μ (retainedRegion Q μ N B t)ᶜ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^(4*H+2):ℕ)*t ∧
      ∃ p : List ℕ → CellPath d,
        (∀ T ∈ regularizationIndex Q μ N B t, p T ∈ regularizationLeaves Q μ N) ∧
        (∀ T ∈ regularizationIndex Q μ N B t, regularizationLabel Q μ N B (p T) = T) ∧
        (∀ T ∈ regularizationIndex Q μ N B t,
          RegularizedProfileData Q (sourceClass Q μ N B (p T)) N s lam (sourceUnitProfile Q μ N B (p T))) := by
  obtain ⟨H,N₀,hH,_hHb,h₀⟩ := actual_regular_source_classes hd Q hQ μ hcarry hs hsd hC hlam hball
  refine ⟨H,N₀,hH,?_⟩
  intro N hN
  obtain ⟨hNp,hB,hw,hl,_hcount,hdiscard,hclasses⟩ := h₀ N hN
  refine ⟨hNp,hB,hw,hl,hdiscard,?_⟩
  exact source_representatives Q μ N (N/H) _ s lam (fun T hT => (hclasses T hT).2)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AssemblyCutoff
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed compactly supported scalar cutoff for the assembly -/

namespace Falconer
open Set
open scoped SchwartzMap ContDiff

theorem exists_scalar_assembly_cutoff :
    ∃ (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ), (∀ r, φ r = (Ψ r : ℂ)) ∧
      Measurable Ψ ∧ ContDiff ℝ ∞ Ψ ∧ (∀ r, 0 ≤ Ψ r) ∧
      (∀ r ≤ 0, Ψ r = 0) ∧ (∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) ∧
      (∀ r, Ψ r ≤ 1) ∧ (∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) := by
  let Ψ := PlanarFalconer.assemblyShellBump
  let φ : 𝓢(ℝ,ℂ) :=
    (Ψ.hasCompactSupport.toSchwartzMap Ψ.contDiff).postcompCLM Complex.ofRealCLM
  have hsupp (r : ℝ) (hr : Ψ r ≠ 0) : r ∈ Ioo (1/4:ℝ) 4 := by
    have hh : dist r (5/4:ℝ) < 1 := by
      by_contra hn
      exact hr (Ψ.zero_of_le_dist (not_lt.mp hn))
    rw [Real.dist_eq,abs_lt] at hh
    constructor <;> linarith
  refine ⟨φ,Ψ,fun _ => rfl,Ψ.continuous.measurable,Ψ.contDiff,fun _ => Ψ.nonneg,?_,?_,
    fun _ => Ψ.le_one,hsupp⟩
  · intro r hr
    by_contra hn
    have hh := (hsupp r hn).1
    linarith
  · intro r hr
    have hmem : r ∈ Metric.closedBall (5/4:ℝ) Ψ.rIn := by
      change dist r (5/4:ℝ) ≤ 3/4
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [hr.1,hr.2]
    rw [Ψ.one_of_mem_closedBall hmem]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Put compact projected supports in a fixed unit cube -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem mem_centeredUnitCube_of_norm {x : Space d} (hx : ‖x‖ ≤ 1/4) :
    x ∈ (centeredUnitCube d).carrier := by
  intro i
  have hi : |x i| ≤ 1/4 := (PiLp.norm_apply_le x i).trans hx
  change -(1/2:ℝ) ≤ x i ∧ x i < -(1/2:ℝ)+1
  constructor <;> linarith [abs_le.mp hi]

theorem compact_projection_into_unitCube (E : Set (Space d)) (hE : IsCompact E)
    (P : Space d →L[ℝ] Space m) :
    ∃ a : ℝ, 0 < a ∧ ‖a • P‖ ≤ 1 ∧
      ∀ x ∈ E, (a • P) x ∈ (centeredUnitCube m).carrier := by
  obtain ⟨M,hM,hbound⟩ := (hE.image P.continuous).isBounded.exists_pos_norm_le
  let a := (4*(M+‖P‖+1))⁻¹
  have hden : 0 < 4*(M+‖P‖+1) := by positivity
  have ha : 0 < a := inv_pos.mpr hden
  refine ⟨a,ha,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    change (4*(M+‖P‖+1))⁻¹*‖P‖ ≤ 1
    rw [inv_mul_le_iff₀ hden]
    nlinarith only [hM,norm_nonneg P]
  · intro x hx
    apply mem_centeredUnitCube_of_norm
    rw [smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    calc
      a * ‖P x‖ ≤ a*M := mul_le_mul_of_nonneg_left (hbound _ ⟨x,hx,rfl⟩) ha.le
      _ ≤ 1/4 := by
        change (4*(M+‖P‖+1))⁻¹*M ≤ 1/4
        rw [inv_mul_le_iff₀ hden]
        nlinarith only [norm_nonneg P]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SimilarityGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common similarities for original pairs

Only a common orthogonal map and a positive dilation are used. The direction
map is exactly orthogonal, so the original radial cap constants are unchanged.
-/
namespace Falconer
open Set MeasureTheory NormedSpace

theorem scaledIsometry_dist {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x y : Space d) :
    dist (scaledIsometry e a ha x) (scaledIsometry e a ha y) = a*dist x y := by
  simp only [scaledIsometry_apply,dist_smul₀,Real.norm_eq_abs,abs_of_pos ha,e.dist_map]

theorem scaledIsometry_normalize_sub {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x y : Space d) :
    normalize (scaledIsometry e a ha x-scaledIsometry e a ha y) = e (normalize (x-y)) := by
  rw [scaledIsometry_apply,scaledIsometry_apply,← smul_sub,normalize_smul_of_pos ha]
  exact linearIsometryEquiv_normalize_sub e x y

theorem scaledIsometry_radial {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x y : Space d) :
    radialDirection (scaledIsometry e a ha x) (scaledIsometry e a ha y) = e (radialDirection x y) :=
  scaledIsometry_normalize_sub e a ha y x

theorem scaledIsometry_ball_preimage {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x : Space d) (r : ℝ) :
    scaledIsometry e a ha ⁻¹' Metric.ball x r =
      Metric.ball ((scaledIsometry e a ha).symm x) (r/a) := by
  ext y
  simp only [mem_preimage,Metric.mem_ball]
  have he : dist (scaledIsometry e a ha y) x =
      a*dist y ((scaledIsometry e a ha).symm x) := by
    calc
      _ = dist (scaledIsometry e a ha y)
        (scaledIsometry e a ha ((scaledIsometry e a ha).symm x)) := by
          rw [(scaledIsometry e a ha).apply_symm_apply]
      _ = _ := scaledIsometry_dist e a ha _ _
  rw [he,lt_div_iff₀ ha,mul_comm a]

theorem HasBorelProductPartition.homeomorph {d : ℕ} {G : Set (Space d × Space d)}
    {K : ℝ} (h : HasBorelProductPartition G K) (f : Space d ≃ₜ Space d) :
    HasBorelProductPartition (pairHomeomorph f '' G) K := by
  obtain ⟨n,hn,A,B,hm,hd,rfl⟩ := h
  refine ⟨n,hn,(fun i => f '' A i),(fun i => f '' B i),?_,?_,?_⟩
  · intro i
    exact ⟨f.measurableEmbedding.measurableSet_image.mpr (hm i).1,
      f.measurableEmbedding.measurableSet_image.mpr (hm i).2⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro ⟨x,y⟩ ⟨⟨x₁,hx₁,hx⟩,⟨y₁,hy₁,hy⟩⟩ ⟨⟨x₂,hx₂,hx'⟩,⟨y₂,hy₂,hy'⟩⟩
    have hxx : x₁ = x₂ := f.injective (hx.trans hx'.symm)
    have hyy : y₁ = y₂ := f.injective (hy.trans hy'.symm)
    exact Set.disjoint_left.mp (hd hij)
      (show (x₁,y₁) ∈ A i ×ˢ B i from ⟨hx₁,hy₁⟩)
      (by simpa only [mem_prod,hxx,hyy] using And.intro hx₂ hy₂)
  · ext z
    simp only [mem_image,mem_iUnion,mem_prod,pairHomeomorph_apply]
    constructor
    · rintro ⟨⟨x,y⟩,⟨i,hx,hy⟩,heq⟩
      exact ⟨i,⟨x,hx,congrArg Prod.fst heq⟩,⟨y,hy,congrArg Prod.snd heq⟩⟩
    · rintro ⟨i,⟨x,hx,hx'⟩,⟨y,hy,hy'⟩⟩
      exact ⟨(x,y),⟨i,hx,hy⟩,Prod.ext hx' hy'⟩

theorem scaledIsometry_distanceSet {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (E : Set (Space d)) :
    distanceSet (scaledIsometry e a ha '' E) = (fun r : ℝ => a*r) '' distanceSet E := by
  ext r
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,hr⟩
    exact ⟨dist x y,⟨x,hx,y,hy,rfl⟩,(scaledIsometry_dist e a ha x y).symm.trans hr⟩
  · rintro ⟨_,⟨x,hx,y,hy,rfl⟩,rfl⟩
    exact ⟨_,mem_image_of_mem _ hx,_,mem_image_of_mem _ hy,scaledIsometry_dist e a ha x y⟩

theorem positive_distance_of_scaledIsometry {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (E : Set (Space d))
    (h : 0 < volume (distanceSet (scaledIsometry e a ha '' E))) :
    0 < volume (distanceSet E) := by
  rw [scaledIsometry_distanceSet] at h
  have he : (fun r : ℝ => a*r) '' distanceSet E =
      (fun r : ℝ => a⁻¹*r) ⁻¹' distanceSet E := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩
      simpa only [mem_preimage,inv_mul_cancel_left₀ ha.ne'] using ht
    · intro hr
      exact ⟨a⁻¹*r,hr,mul_inv_cancel_left₀ ha.ne' r⟩
  rw [he,Real.volume_preimage_mul_left (inv_ne_zero ha.ne')] at h
  exact (ENNReal.mul_pos_iff.mp h).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DistributionAbsoluteContinuity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal

 theorem locallyIntegrable_rnDeriv_smul (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (hac : μ ≪ ν) (f : ℝ → ℂ) (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal • f x) ν := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := (integrable_rnDeriv_smul_iff hac).mpr
    ((hf.integrableOn_isCompact hK).integrable_indicator hK.measurableSet)
  apply (integrable_indicator_iff hK.measurableSet).mp
  apply hi.congr
  filter_upwards with x
  by_cases hx : x ∈ K <;> simp [hx]

 theorem absolutelyContinuous_of_smooth_test_density (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : LocallyIntegrable f volume)
    (ht : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      (∫ x, (g x : ℂ) ∂τ) = ∫ x, g x • f x) : τ ≪ volume := by
  let μ : Measure ℝ := τ+volume
  have hτ : τ ≪ μ := Measure.absolutelyContinuous_of_le (by
    apply Measure.le_iff.mpr
    intro s _
    exact le_add_right le_rfl)
  have hv : volume ≪ μ := Measure.absolutelyContinuous_of_le (by
    apply Measure.le_iff.mpr
    intro s _
    exact le_add_left le_rfl)
  let a : ℝ → ℂ := fun x => ((τ.rnDeriv μ x).toReal : ℂ)
  let b : ℝ → ℂ := fun x => (volume.rnDeriv μ x).toReal • f x
  have ha : LocallyIntegrable a μ := by
    simpa only [smul_eq_mul, Complex.real_smul, mul_one] using
      locallyIntegrable_rnDeriv_smul τ μ hτ (fun _ => (1:ℂ))
        (continuous_const.locallyIntegrable)
  have hb : LocallyIntegrable b μ := locallyIntegrable_rnDeriv_smul volume μ hv f hf
  have hab : a =ᵐ[μ] b := by
    apply ae_eq_of_integral_contDiff_smul_eq ha hb
    intro g hg hc
    calc
      _ = ∫ x, (τ.rnDeriv μ x).toReal • (g x : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [a, Complex.real_smul, mul_comm]
      _ = ∫ x, (g x : ℂ) ∂τ := integral_rnDeriv_smul hτ
      _ = ∫ x, g x • f x := ht g hg hc
      _ = ∫ x, (volume.rnDeriv μ x).toReal • (g x • f x) ∂μ :=
        (integral_rnDeriv_smul hv).symm
      _ = _ := by simp only [b, smul_comm (g _) ((volume.rnDeriv μ _).toReal)]
  intro S hS
  have hS' : ∀ᵐ x ∂volume, x ∉ S := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hS
  rw [← Measure.withDensity_rnDeriv_eq volume μ hv] at hS'
  have hz := (ae_withDensity_iff (Measure.measurable_rnDeriv volume μ)).mp hS'
  have hgoal : ∀ᵐ x ∂τ, x ∉ S := by
    rw [← Measure.withDensity_rnDeriv_eq τ μ hτ]
    apply (ae_withDensity_iff (Measure.measurable_rnDeriv τ μ)).mpr
    filter_upwards [hz,hab,Measure.rnDeriv_lt_top τ μ] with x hx he hfin
    intro hax hxS
    have hzero : volume.rnDeriv μ x = 0 := by
      by_contra hn
      exact hx hn hxS
    have hzreal : (τ.rnDeriv μ x).toReal = 0 := by
      have he' : ((τ.rnDeriv μ x).toReal : ℂ) = 0 := by
        simpa only [a,b,hzero,ENNReal.toReal_zero,zero_smul] using he
      exact Complex.ofReal_eq_zero.mp he'
    have heq := ENNReal.ofReal_toReal hfin.ne
    rw [hzreal, ENNReal.ofReal_zero] at heq
    exact hax heq.symm
  simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hgoal

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FrostmanDimension
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Hausdorff-dimension lower bound of the actual Frostman law -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem frostman_set_bound (μ : ProbabilityMeasure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (A : Set (Space d)) :
    (μ : Measure (Space d)) A ≤ ENNReal.ofReal (C*2^s) * (Metric.ediam A)^s := by
  let := noAtoms_of_frostman (μ : Measure (Space d)) hs hfrost
  have hK : 0 < C*2^s := mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)
  by_cases hA : A.Nonempty
  · obtain ⟨x,hx⟩ := hA
    by_cases hzero : Metric.ediam A = 0
    · rw [hzero,ENNReal.zero_rpow_of_pos hs,mul_zero]
      apply le_of_eq
      apply measure_mono_null _ (measure_singleton x)
      intro y hy
      exact Set.mem_singleton_iff.mpr ((Metric.ediam_eq_zero_iff.mp hzero) hy hx)
    by_cases htop : Metric.ediam A = ∞
    · rw [htop,ENNReal.top_rpow_of_pos hs,ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hK)]
      exact le_top
    let r := (Metric.ediam A).toReal
    have hr : 0 < r := ENNReal.toReal_pos hzero htop
    have hsub : A ⊆ ball x (2*r) := by
      intro y hy
      have hd : dist y x ≤ r := by
        have hd := ENNReal.toReal_mono htop (Metric.edist_le_ediam_of_mem hy hx)
        simpa only [edist_dist,ENNReal.toReal_ofReal dist_nonneg] using hd
      exact lt_of_le_of_lt hd (by linarith)
    calc
      (μ : Measure (Space d)) A ≤ ENNReal.ofReal (C*(2*r)^s) :=
        (measure_mono hsub).trans (hfrost x (2*r) (by positivity))
      _ = ENNReal.ofReal (C*2^s) * (Metric.ediam A)^s := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le,← mul_assoc,
          ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_rpow_of_pos hr]
        congr 1
        exact congrArg (fun z : ℝ≥0∞ => z^s) (ENNReal.ofReal_toReal htop)
  · rw [Set.not_nonempty_iff_eq_empty.mp hA,measure_empty]
    exact zero_le

theorem frostman_dimension_lower (μ : ProbabilityMeasure (Space d)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    ENNReal.ofReal s ≤ dimH (μ : Measure (Space d)).support := by
  let K := ENNReal.ofReal (C*2^s)
  have hK : K ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hKtop : K ≠ ∞ := ENNReal.ofReal_ne_top
  have hmeasure : K⁻¹ • (μ : Measure (Space d)) ≤ Measure.hausdorffMeasure s := by
    apply Measure.le_hausdorffMeasure s _ ∞ (by simp)
    intro A _
    rw [Measure.smul_apply,smul_eq_mul]
    calc
      K⁻¹ * (μ : Measure (Space d)) A ≤ K⁻¹ * (K*(Metric.ediam A)^s) :=
        mul_le_mul_right (frostman_set_bound μ hs hC hfrost A) _
      _ = (Metric.ediam A)^s := by rw [← mul_assoc,ENNReal.inv_mul_cancel hK hKtop,one_mul]
  have hsup : (μ : Measure (Space d)) (μ : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  have hpositive : 0 < (K⁻¹ • (μ : Measure (Space d))) (μ : Measure (Space d)).support := by
    rw [Measure.smul_apply,smul_eq_mul,hsup,mul_one]
    exact pos_iff_ne_zero.mpr (ENNReal.inv_ne_zero.mpr hKtop)
  have hnonzero : Measure.hausdorffMeasure s (μ : Measure (Space d)).support ≠ 0 :=
    (hpositive.trans_le (hmeasure _)).ne'
  rw [ENNReal.ofReal_eq_coe_nnreal hs.le]
  exact le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨s,hs.le⟩) hnonzero

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SimilarityMeasures
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original measure and radial-cap transport under a common similarity -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

theorem homeomorph_support_map_subset (f : Space d ≃ₜ Space d)
    (μ : Measure (Space d)) : (μ.map f).support ⊆ f '' μ.support := by
  apply Measure.support_subset_of_isClosed (f.isClosedMap _ Measure.isClosed_support)
  change (μ.map f) (f '' μ.support)ᶜ = 0
  rw [f.measurableEmbedding.map_apply]
  simpa only [preimage_compl,f.injective.preimage_image] using μ.measure_compl_support

@[simp] theorem pairHomeomorph_mem_image (f : Space d ≃ₜ Space d)
    (G : Set (Space d × Space d)) (x y : Space d) :
    (f x,f y) ∈ pairHomeomorph f '' G ↔ (x,y) ∈ G :=
  (pairHomeomorph f).injective.mem_set_image (s := G) (a := (x,y))

theorem homeomorph_pair_measure_image (f : Space d ≃ₜ Space d)
    (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) :
    ((μ.map f).prod (ν.map f)) (pairHomeomorph f '' G) = (μ.prod ν) G := by
  rw [Measure.map_prod_map μ ν f.continuous.measurable f.continuous.measurable]
  change ((μ.prod ν).map (pairHomeomorph f)) (pairHomeomorph f '' G) = _
  rw [(pairHomeomorph f).measurableEmbedding.map_apply,
    (pairHomeomorph f).injective.preimage_image]

theorem scaledIsometry_frostman (e : Space d ≃ₗᵢ[ℝ] Space d) (a : ℝ) (ha : 0 < a)
    (μ : Measure (Space d)) {s C : ℝ} (hf : FrostmanBallBound μ s C) :
    FrostmanBallBound (μ.map (scaledIsometry e a ha)) s (C/a^s) := by
  intro x r hr
  rw [Measure.map_apply (scaledIsometry e a ha).continuous.measurable measurableSet_ball,
    scaledIsometry_ball_preimage]
  apply (hf _ (r/a) (by positivity)).trans_eq
  congr 1
  rw [Real.div_rpow hr.le ha.le]
  ring

theorem scaledIsometry_radial_dist (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) (x y w : Space d) :
    dist (radialDirection (scaledIsometry e a ha x) (scaledIsometry e a ha y)) w =
      dist (radialDirection x y) (e.symm w) := by
  rw [scaledIsometry_radial]
  calc
    _ = dist (e (radialDirection x y)) (e (e.symm w)) := by rw [e.apply_symm_apply]
    _ = _ := e.dist_map _ _

theorem RadialCapBound.scaledIsometry (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) {μ ν : ProbabilityMeasure (Space d)}
    {G : Set (Space d × Space d)} {N : ℕ} {loss q : ℝ}
    (h : RadialCapBound μ ν G N loss q) :
    RadialCapBound (μ.map (f := (scaledIsometry e a ha)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := (scaledIsometry e a ha)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      (pairHomeomorph (scaledIsometry e a ha) '' G) N loss q := by
  let f := Falconer.scaledIsometry e a ha
  constructor
  · intro x hx w hw u hu hu1
    obtain ⟨x,hxs,rfl⟩ := homeomorph_support_map_subset f (μ : Measure _) hx
    change ((ν : Measure _).map f) _ ≤ _
    rw [f.measurableEmbedding.map_apply]
    have he : f ⁻¹' {y | (f x,y) ∈ pairHomeomorph f '' G ∧
        dist (radialDirection (f x) y) w < u} =
        {y | (x,y) ∈ G ∧ dist (radialDirection x y) (e.symm w) < u} := by
      ext y
      simp only [mem_preimage,mem_ofPred_eq,pairHomeomorph_mem_image]
      rw [scaledIsometry_radial_dist]
    rw [he]
    exact h.1 x hxs (e.symm w) (by simpa only [e.symm.norm_map] using hw) u hu hu1
  · intro y hy w hw u hu hu1
    obtain ⟨y,hys,rfl⟩ := homeomorph_support_map_subset f (ν : Measure _) hy
    change ((μ : Measure _).map f) _ ≤ _
    rw [f.measurableEmbedding.map_apply]
    have he : f ⁻¹' {x | (x,f y) ∈ pairHomeomorph f '' G ∧
        dist (radialDirection (f y) x) w < u} =
        {x | (x,y) ∈ G ∧ dist (radialDirection y x) (e.symm w) < u} := by
      ext x
      simp only [mem_preimage,mem_ofPred_eq,pairHomeomorph_mem_image]
      rw [scaledIsometry_radial_dist]
    rw [he]
    exact h.2 y hys (e.symm w) (by simpa only [e.symm.norm_map] using hw) u hu hu1

theorem CapAvailable.scaledIsometry (e : Space d ≃ₗᵢ[ℝ] Space d)
    (a : ℝ) (ha : 0 < a) {μ ν : ProbabilityMeasure (Space d)}
    {Γ : ℕ → Set (Space d × Space d)} {q : ℝ} (h : CapAvailable μ ν Γ q) :
    CapAvailable (μ.map (f := (scaledIsometry e a ha)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) (ν.map (f := (scaledIsometry e a ha)) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
      (fun N => pairHomeomorph (scaledIsometry e a ha) '' Γ N) q := by
  let f := Falconer.scaledIsometry e a ha
  let F := pairHomeomorph f
  intro loss hloss
  obtain ⟨c,C,hc,hC,K,hK⟩ := h loss hloss
  refine ⟨c,C,hc,hC,K,?_⟩
  intro N hN
  obtain ⟨B,hB,hsub,hmass,hcap⟩ := hK N hN
  refine ⟨F '' B,F.measurableEmbedding.measurableSet_image.mpr hB,
    Set.image_mono hsub,?_,?_⟩
  · exact (homeomorph_pair_measure_image f (μ : Measure _) (ν : Measure _) B).le.trans hmass
  · have he : F '' Γ N \ F '' B = F '' (Γ N \ B) := by
      ext z
      obtain ⟨z,rfl⟩ := F.surjective z
      simp only [mem_sdiff,F.injective.mem_set_image]
    rw [he]
    exact hcap.scaledIsometry e a ha

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ClassicalAffineDistance
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The strict classical threshold on a charged affine plane

Coordinates are used isometrically inside the actual affine plane, so the
conclusion concerns original distances.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem frostman_exponent_le_dimension (μ : ProbabilityMeasure (Space n)) {s C : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hfrost : FrostmanBallBound (μ : Measure (Space n)) s C) :
    s ≤ (n:ℝ) := by
  have hu : dimH (univ : Set (Space n)) = (n:ℝ≥0∞) := by
    simp [Real.dimH_univ_eq_finrank,Space]
  have hd := (frostman_dimension_lower μ hs hC hfrost).trans
    ((dimH_mono (subset_univ _)).trans_eq hu)
  have hh := ENNReal.toReal_mono (by simp : (n:ℝ≥0∞) ≠ ∞) hd
  simpa [ENNReal.toReal_ofReal hs.le] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_AssemblyErrorBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Converting the original-pair deletion bound to its summable majorant -/

namespace Falconer
open scoped ENNReal

theorem dyadic_leaf_error (N : ℕ) :
    ((2:ℝ≥0∞)^(2*N))⁻¹ = ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ)) := by
  have hfin : ((2:ℝ≥0∞)^(2*N))⁻¹ ≠ ∞ := by simp
  rw [← ENNReal.ofReal_toReal hfin]
  congr 1
  simp only [ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  rw [Real.rpow_neg (by positivity),Real.rpow_two]
  congr 1
  rw [← pow_mul,Nat.mul_comm N 2]

theorem class_discard_numeric (N k : ℕ) (lam : ℝ) :
    ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^k:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam)) ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ) + ((N:ℝ)+1)^k*((2:ℝ)^N)^(-lam)) := by
  have hp : ((N^k:ℕ):ℝ≥0∞) ≤ ENNReal.ofReal (((N:ℝ)+1)^k) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Nat.cast_pow] using pow_le_pow_left₀ (Nat.cast_nonneg N)
      (show (N:ℝ) ≤ N+1 by linarith) k
  rw [dyadic_leaf_error]
  apply (add_le_add le_rfl (mul_le_mul' hp le_rfl)).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem restoration_numeric_bound (N k₁ k₂ : ℕ) {Cw Ccap c lam σ : ℝ}
    (hw : 0 ≤ Cw) (hcap : 0 ≤ Ccap) {D X₁ X₂ V : ℝ≥0∞}
    (hD : D ≤ ENNReal.ofReal (Ccap*((2:ℝ)^N)^(-c)))
    (h₁ : X₁ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^k₁:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (h₂ : X₂ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹ + (N^k₂:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (hV : V ≤ ENNReal.ofReal Cw * (D + (X₁ + X₂ +
      (4*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ))))) :
    V ≤ ENNReal.ofReal (restorationError Cw Ccap c lam σ k₁ k₂ N) := by
  apply hV.trans
  have ht : (4*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) =
      ENNReal.ofReal (4*((N:ℝ)+1)^2*((2:ℝ)^N)^(-σ)) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [ht,restorationError,ENNReal.ofReal_mul hw]
  apply mul_le_mul' le_rfl
  apply (add_le_add hD (add_le_add (add_le_add (h₁.trans (class_discard_numeric N k₁ lam))
    (h₂.trans (class_discard_numeric N k₂ lam))) le_rfl)).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_MonotoneShellCriterion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Monotone scalar shell reconstruction

This is the analytic reconstruction needed in all dimensions. The measures
remain one-dimensional original-distance pushforwards. Decreasing measures
may approach their limit arbitrarily slowly; only the approximating shell
errors and shell energies are summable.
-/

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

theorem movingShellL1Error_norm_summable (α τ : ℕ → FiniteMeasure ℝ)
    (h : Summable (fun n => (variationDistance (α n) (τ (n+1))).toReal)) :
    Summable (fun n => ‖movingShellL1Error α τ n‖) := by
  exact (h.mul_right (∫ x, ‖sourceShellKernel 0 x‖)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => shellL1Error_norm_le (α n) τ n)

/-- Distributional limit of the shells of the varying monotone measures. -/
theorem monotone_shell_tests_tendsto (α : ℕ → FiniteMeasure ℝ)
    (τ : FiniteMeasure ℝ) (hα : Antitone (fun n => (α n : Measure ℝ)))
    (hle : ∀ n, (τ : Measure ℝ) ≤ α n)
    (hmass : Tendsto (fun n => ((α n : Measure ℝ) - τ).real univ) atTop (𝓝 0))
    (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun M => ∑ j ∈ Finset.range M,
      ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel j) (α j) x) atTop
      (𝓝 (schwartzLpTest 1 φ (∑' n, monotoneVariationTerm α n) +
        ((∫ x, φ x ∂(τ : Measure ℝ)) - schwartzLpTest 1 φ (dyadicLowTerm 0 τ)))) := by
  have hz : Summable (monotoneVariationTerm α) :=
    (summable_dyadicLowTerm_decrements α hα).of_norm
  have hvar := schwartzLpTest_sum_tendsto 1 φ (monotoneVariationTerm α) hz
  have herr := (dyadicLowTerm_tail_tendsto α τ hle hmass id).sub
    (dyadicLowTerm_tail_tendsto α τ hle hmass (fun _ => 0))
  simp only [sub_self] at herr
  have htesterr := (schwartzLpTest 1 φ).continuous.tendsto 0 |>.comp herr
  simp only [map_zero] at htesterr
  have hlast := ((dyadicLowTerm_test_tendsto τ φ).sub_const
    (schwartzLpTest 1 φ (dyadicLowTerm 0 τ))).add htesterr
  simp only [add_zero] at hlast
  have hlast' : Tendsto (fun M => schwartzLpTest 1 φ
      (dyadicLowTerm M (α M) - dyadicLowTerm 0 (α M))) atTop
      (𝓝 ((∫ x, φ x ∂(τ : Measure ℝ)) -
        schwartzLpTest 1 φ (dyadicLowTerm 0 τ))) := by
    convert hlast using 1
    all_goals try with_reducible_and_instances rfl
    funext M
    simp only [Function.comp_apply, map_sub, id_eq]
    abel
  have htotal := hvar.add hlast'
  convert htotal using 1
  all_goals try with_reducible_and_instances rfl
  funext M
  rw [← map_sum, ← map_add]
  change _ = schwartzLpTest 1 φ
    ((∑ n ∈ Finset.range M,
      (dyadicLowTerm (n+1) ⟨(α n : Measure ℝ) - α (n+1), inferInstance⟩ -
      dyadicLowTerm 0 ⟨(α n : Measure ℝ) - α (n+1), inferInstance⟩)) +
      (dyadicLowTerm M (α M) - dyadicLowTerm 0 (α M)))
  rw [← dyadicLowTerm_summation_by_parts α hα M, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (dyadicLowTerm_band_test j (α j) φ).symm

/-- The monotone shell criterion for the positive approximants used in the
manuscript. The hypotheses are summability and mass convergence, with no
rate imposed on the monotone limit. -/
theorem monotone_shell_criterion (α τ : ℕ → FiniteMeasure ℝ)
    (μ : FiniteMeasure ℝ) (hα : Antitone (fun n => (α n : Measure ℝ)))
    (hle : ∀ n, (μ : Measure ℝ) ≤ α n)
    (hmass : Tendsto (fun n => ((α n : Measure ℝ) - μ).real univ) atTop (𝓝 0))
    (herror : Summable (fun n => (variationDistance (α n) (τ (n+1))).toReal))
    (hshell : Summable (fun n => ‖shellL2Term τ n‖)) :
    (μ : Measure ℝ) ≪ volume := by
  have he := (movingShellL1Error_norm_summable α τ herror).of_norm
  have hz := (summable_dyadicLowTerm_decrements α hα).of_norm
  let a : Lp (α := ℝ) ℂ 1 volume :=
    dyadicLowTerm 0 μ + ∑' n, movingShellL1Error α τ n - ∑' n, monotoneVariationTerm α n
  let b : Lp (α := ℝ) ℂ 2 volume := ∑' n, shellL2Term τ n
  have htests (φ : 𝓢(ℝ, ℂ)) :
      schwartzLpTest 1 φ a + schwartzLpTest 2 φ b = ∫ x, φ x ∂(μ : Measure ℝ) := by
    have hsum := (schwartzLpTest_sum_tendsto 1 φ _ he).add
      (schwartzLpTest_sum_tendsto 2 φ _ hshell.of_norm)
    have hsame (M : ℕ) :
        (∑ j ∈ Finset.range M, schwartzLpTest 1 φ (movingShellL1Error α τ j)) +
        (∑ j ∈ Finset.range M, schwartzLpTest 2 φ (shellL2Term τ j)) =
        ∑ j ∈ Finset.range M,
          ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel j) (α j) x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      exact schwartzLpTest_shell_recombine (α j) τ φ j
    simp_rw [hsame] at hsum
    have huniq := tendsto_nhds_unique hsum (monotone_shell_tests_tendsto α μ hα hle hmass φ)
    dsimp [a, b]
    simp only [map_sub, map_add]
    change _ = _ at huniq
    linear_combination huniq
  let f : ℝ → ℂ := fun x => a x + b x
  have hf : LocallyIntegrable f volume :=
    ((Lp.memLp a).locallyIntegrable (by norm_num)).add
      ((Lp.memLp b).locallyIntegrable (by norm_num))
  apply absolutelyContinuous_of_smooth_test_density μ f hf
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  have ht := htests φ
  rw [schwartzLpTest_apply, schwartzLpTest_apply] at ht
  have ha := (φ.memLp_top volume).integrable_mul (Lp.memLp a)
  have hb := (φ.memLp 2 volume).integrable_mul (Lp.memLp b)
  change Integrable (fun x => φ x * a x) at ha
  change Integrable (fun x => φ x * b x) at hb
  change (∫ x, φ x ∂(μ : Measure ℝ)) = ∫ x, g x • f x
  rw [← ht, ← integral_add ha hb]
  apply integral_congr_ae
  filter_upwards with x
  change φ x * a x + φ x * b x = _
  simp only [φ, f, Complex.real_smul, mul_add]
  rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_FilteredShellEndgame
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Final reconstruction for filtered original-distance measures

The two analytic hypotheses below are the restoration estimate and shell
summability. The conclusion uses the positive intersection
of the original pair filters, with no projection of distances.
-/

namespace Falconer
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The endgame of `asm:completion`, in a form permitting the decreasing pair
filters of the all-dimensional manuscript. -/
theorem positive_volume_of_filtered_shells {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (hf : Measurable f) (ρ : Measure X) [IsFiniteMeasure ρ]
    (G : ℕ → Set X) (hG : ∀ n, MeasurableSet (G n)) (hmono : Antitone G)
    (D : Set ℝ) (hD : MeasurableSet D)
    (hcarry : ρ (f ⁻¹' Dᶜ) = 0) (hpositive : 0 < ρ (⋂ n, G n))
    (τ : ℕ → FiniteMeasure ℝ)
    (herror : Summable (fun n =>
      (PlanarFalconer.variationDistance
        ⟨filteredPushforward f ρ (G n), inferInstance⟩ (τ (n+1))).toReal))
    (hshell : Summable (fun n => ‖PlanarFalconer.shellL2Term τ n‖)) :
    0 < volume D := by
  let α : ℕ → FiniteMeasure ℝ := fun n =>
    ⟨filteredPushforward f ρ (G n), inferInstance⟩
  let μ : FiniteMeasure ℝ := ⟨filteredPushforward f ρ (⋂ n, G n), inferInstance⟩
  have hα : Antitone (fun n => (α n : Measure ℝ)) :=
    antitone_filteredPushforward f hf ρ hmono
  have hle : ∀ n, (μ : Measure ℝ) ≤ α n := fun n =>
    filteredPushforward_mono f hf ρ (iInter_subset G n)
  have hac : (μ : Measure ℝ) ≪ volume :=
    PlanarFalconer.monotone_shell_criterion α τ μ hα hle
      (filteredPushforward_tail_mass_tendsto f hf ρ G hG hmono) herror hshell
  exact positive_volume_of_carried_measure D μ
    (filteredPushforward_positive f hf ρ hpositive)
    (filteredPushforward_carried f hf ρ _ hD hcarry) hac

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_DecayEndgame
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The monotone original-law endgame with bounds at the same scale -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

private theorem summable_shift_one {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun n => f (n+1)) := (summable_nat_add_iff 1).mpr hf

theorem positive_volume_of_same_scale_summable {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (hf : Measurable f) (ρ : Measure X) [IsFiniteMeasure ρ]
    (G : ℕ → Set X) (hG : ∀ n, MeasurableSet (G n)) (hmono : Antitone G)
    (D : Set ℝ) (hD : MeasurableSet D) (hcarry : ρ (f ⁻¹' Dᶜ) = 0)
    (hpositive : 0 < ρ (⋂ n, G n)) (τ : ℕ → FiniteMeasure ℝ)
    (herror : Summable (fun N => (PlanarFalconer.variationDistance
      ⟨filteredPushforward f ρ (G N),inferInstance⟩ (τ N)).toReal))
    {γ Cshell : ℝ} (hγ : 0 < γ) (hCshell : 0 < Cshell) (N₀ : ℕ)
    (hshell : ∀ N ≥ N₀, PlanarFalconer.shellEnergy (τ N) N ≤ Cshell*(2:ℝ)^(-γ*(N:ℝ))) :
    0 < volume D := by
  have hpos : 0 < ρ (⋂ n, G (n+1)) := hpositive.trans_le (measure_mono (by
    intro x hx
    exact mem_iInter.mpr (fun n => mem_iInter.mp hx (n+1))))
  apply positive_volume_of_filtered_shells f hf ρ (fun n => G (n+1)) (fun n => hG (n+1))
    (fun n k hnk => hmono (Nat.add_le_add_right hnk 1)) D hD hcarry hpos τ
  · convert summable_shift_one herror using 1
  · exact PlanarFalconer.shellL2Term_norm_summable τ hγ hCshell N₀ hshell

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_UnitPairEndgame
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Completion for an original separated pair in unit cubes -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open Regularization

theorem unit_pair_positive_distance
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {χ : ℝ} (hχ : 0 < χ) (hsd : (m+3:ℕ)/2+χ ≤ (m+3:ℕ))
    (Q₁ Q₂ : DyadicCube (m+3)) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (μ ν : ProbabilityMeasure (Space (m+3)))
    (hcarry₁ : (μ : Measure (Space (m+3))) Q₁.carrierᶜ = 0)
    (hcarry₂ : (ν : Measure (Space (m+3))) Q₂.carrierᶜ = 0)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hball₁ : ∀ x : Space (m+3), ∀ r > 0,
      (μ : Measure (Space (m+3))) (Metric.ball x r) ≤ ENNReal.ofReal (C₁*r^((m+3:ℕ)/2+χ)))
    (hball₂ : ∀ x : Space (m+3), ∀ r > 0,
      (ν : Measure (Space (m+3))) (Metric.ball x r) ≤ ENNReal.ofReal (C₂*r^((m+3:ℕ)/2+χ)))
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (hsep : ∀ᵐ z ∂(μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))),
      δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W)
    (hnear : ∀ᵐ z : Space (m+3) × Space (m+3)
      ∂(μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))),
      ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8)
    (D : Set ℝ) (hD : MeasurableSet D)
    (hcarried : ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))))
      ((fun z => dist z.1 z.2) ⁻¹' Dᶜ) = 0)
    (hfilters : ∀ ω : ℝ, 0 < ω → ω ≤ 1 →
      ∃ Γ : ℕ → Set (Space (m+3) × Space (m+3)),
        (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
        0 < ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3)))) (⋂ N, Γ N) ∧
        (∀ N, ∀ z ∈ Γ N, z.1 ≠ z.2) ∧
        (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*(m+3:ℕ)*ω*(N:ℝ)))) ∧
        CapAvailable μ ν Γ ((m+3:ℕ)/2)) :
    0 < volume D := by
  classical
  obtain ⟨φ,Ψ,hφ,hΨ,hsmooth,hpos,hzero,hone,hΨV,hsupp⟩ := exists_scalar_assembly_cutoff
  obtain ⟨lam,σ,κ,β,hlam,hσ,hlamσ,hκ,hβ,Ns,hNs,hscalar⟩ :=
    exists_regularization_scalar_shell hgnomonic hquadratic m hχ φ Ψ hφ hΨ hsmooth
      hpos hzero hone (by norm_num : (0:ℝ) ≤ 1) hΨV hsupp δ W hδ hW
  have hside₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hs : (0:ℝ) ≤ (m+3:ℕ)/2+χ := by positivity
  obtain ⟨H₁,N₁,_hH₁,hfam₁⟩ := eventual_source_family (by omega) Q₁ hside₁ μ hcarry₁ hs hsd hC₁ hlam hball₁
  obtain ⟨H₂,N₂,_hH₂,hfam₂⟩ := eventual_source_family (by omega) Q₂ hside₂ ν hcarry₂ hs hsd hC₂ hlam hball₂
  let ω : ℝ := min 1 (β/(256*(m+3:ℕ)))
  have hω : 0 < ω := lt_min zero_lt_one (by positivity)
  have hω1 : ω ≤ 1 := min_le_left _ _
  have hθ : 2*(2*(m+3:ℕ)*ω) ≤ β/64 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 256*(m+3:ℕ))).mp (min_le_right 1 (β/(256*(m+3:ℕ))))
    dsimp only [ω]
    nlinarith
  obtain ⟨Γ,hΓ,hmono,hpositive,hne,hparts,hcaps⟩ := hfilters ω hω hω1
  obtain ⟨a,Ccap,ha,hCcap,Ncap,hcap⟩ := original_cap_removal μ ν Γ hcaps hne hσ
  obtain ⟨Nt,htest⟩ := uniform_regularizationPairExceptional_bound (d := m+3) hσ
  obtain ⟨Nv,hvar⟩ := uniform_regularization_variation (d := m+3) hσ hκ (by omega)
  obtain ⟨Np,hpartition⟩ := eventual_partition_shell_decay hβ hθ
  let N₀ := Ns+N₁+N₂+Ncap+Nt+Nv+Np
  let π : Measure (Space (m+3) × Space (m+3)) := (μ : Measure _).prod (ν : Measure _)
  let Cw : ℝ := δ^(-((((m+3:ℕ):ℝ)-1)/2))
  have hCw : 0 < Cw := Real.rpow_pos_of_pos hδ _
  let ρ := π.withDensity (distanceWeight ((((m+3:ℕ):ℝ)-1)/2))
  let : IsFiniteMeasure ρ := finite_withDensity_of_bounded π _ ENNReal.ofReal_lt_top
    (distanceWeight_upper (by omega) hδ (hsep.mono fun _ h => h.1))
  have happ : ∀ N ≥ N₀, ∃ τ : FiniteMeasure ℝ,
      PlanarFalconer.variationDistance
        ⟨filteredPushforward (fun z : Space (m+3) × Space (m+3) => dist z.1 z.2) ρ (Γ N),(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ τ ≤
          ENNReal.ofReal (restorationError Cw Ccap a lam σ (4*H₁+2) (4*H₂+2) N) ∧
      PlanarFalconer.shellEnergy τ N ≤ ((2:ℝ)^N)^(-β/32) := by
    intro N hN
    have hNsN : Ns ≤ N := by dsimp only [N₀] at hN; omega
    have hN₁ : N₁ ≤ N := by dsimp only [N₀] at hN; omega
    have hN₂ : N₂ ≤ N := by dsimp only [N₀] at hN; omega
    have hNcap : Ncap ≤ N := by dsimp only [N₀] at hN; omega
    have hNt : Nt ≤ N := by dsimp only [N₀] at hN; omega
    have hNv : Nv ≤ N := by dsimp only [N₀] at hN; omega
    have hNp : Np ≤ N := by dsimp only [N₀] at hN; omega
    let B₁ := N/H₁
    let B₂ := N/H₂
    let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
    have ht : 0 < t := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨hNpos,hB₁,hw₁,hl₁,hdiscard₁,p₁,hp₁,he₁,hreg₁⟩ := hfam₁ N hN₁
    obtain ⟨_hNpos,hB₂,hw₂,hl₂,hdiscard₂,p₂,hp₂,he₂,hreg₂⟩ := hfam₂ N hN₂
    have hwidth₁ : (B₁:ℝ) ≤ σ*N := hw₁.trans (mul_le_mul_of_nonneg_right hlamσ (Nat.cast_nonneg N))
    have hwidth₂ : (B₂:ℝ) ≤ σ*N := hw₂.trans (mul_le_mul_of_nonneg_right hlamσ (Nat.cast_nonneg N))
    have hR1 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hlarge₁ : (2:ℝ)^(N/B₁+2) ≤ ((2:ℝ)^N)^σ := hl₁.trans (Real.rpow_le_rpow_of_exponent_le hR1 hlamσ)
    have hlarge₂ : (2:ℝ)^(N/B₂+2) ≤ ((2:ℝ)^N)^σ := hl₂.trans (Real.rpow_le_rpow_of_exponent_le hR1 hlamσ)
    obtain ⟨c,hc,hsc⟩ := hscalar N hNsN Q₁ Q₂ hQ₁ hQ₂ μ ν B₁ B₂ t t ht ht p₁ p₂ he₁ he₂ hreg₁ hreg₂ hsep hnear
    obtain ⟨Dcap,hDcap,_hDsub,hDmass,hcaplaw⟩ := hcap N hNcap
    let w₀ : Sphere (m+3) := gnomonicChart (0 : Space (m+2))
    obtain ⟨τ,hτ,htv⟩ := hvar N hNv hNpos Q₁ Q₂ hQ₁ hQ₂ μ ν B₁ B₂ t t p₁ p₂ hp₁ hp₂ c hc w₀ (Γ N) Dcap (hΓ N)
      δ hδ (hsep.mono fun _ h => h.1)
    have hbad := htest N hNt Q₁ Q₂ hQ₁ hQ₂ μ ν B₁ B₂ hB₁ hB₂ hwidth₁ hwidth₂ hlarge₁ hlarge₂
      t t ht ht p₁ p₂ hp₁ hp₂ he₁ he₂ w₀ (Γ N \ Dcap) ((hΓ N).diff hDcap)
      (hcaplaw w₀).1 (hcaplaw w₀).2 κ
    refine ⟨τ,?_,?_⟩
    · apply restoration_numeric_bound N (4*H₁+2) (4*H₂+2) hCw.le hCcap.le hDmass hdiscard₁ hdiscard₂
      exact htv.trans (mul_le_mul' le_rfl (add_le_add le_rfl hbad))
    · obtain ⟨k,hk,A,B,hm,hdis,hΓeq⟩ := hparts N
      have hh := hsc k A B hm hdis
      rw [← hΓeq] at hh
      rw [hτ]
      apply hh.trans (hpartition N hNp k ?_)
      simpa only [dyadic_scale_power] using hk
  let τ : ℕ → FiniteMeasure ℝ := fun N => if hN : N₀ ≤ N then (happ N hN).choose else 0
  have herror : Summable (fun N => (PlanarFalconer.variationDistance
      ⟨filteredPushforward (fun z : Space (m+3) × Space (m+3) => dist z.1 z.2) ρ (Γ N),(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ (τ N)).toReal) := by
    apply summable_of_restoration_error hCw.le hCcap.le ha hlam hσ (4*H₁+2) (4*H₂+2) N₀
    intro N hN
    simpa only [τ,dite_eq_left hN] using (happ N hN).choose_spec.1
  have hshell : ∀ N ≥ N₀, PlanarFalconer.shellEnergy (τ N) N ≤ (1:ℝ)*(2:ℝ)^(-(β/32)*(N:ℝ)) := by
    intro N hN
    simpa only [τ,dite_eq_left hN,dyadic_scale_power,neg_div,one_mul] using (happ N hN).choose_spec.2
  have hρcarried : ρ ((fun z : Space (m+3) × Space (m+3) => dist z.1 z.2) ⁻¹' Dᶜ) = 0 :=
    withDensity_absolutelyContinuous _ _ hcarried
  have hlower : ∀ᵐ z ∂π, ENNReal.ofReal (W^(-((((m+3:ℕ):ℝ)-1)/2))) ≤
      distanceWeight ((((m+3:ℕ):ℝ)-1)/2) z := by
    filter_upwards [hsep] with z hz
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_nonpos (hδ.trans_le hz.1) hz.2
    have hd : (1:ℝ) ≤ (m+3:ℕ) := by exact_mod_cast (show 1 ≤ m+3 by omega)
    linarith
  have hρpositive : 0 < ρ (⋂ N, Γ N) := withDensity_positive_of_lower π _
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hW _)) hlower _ (MeasurableSet.iInter hΓ) hpositive
  exact positive_volume_of_same_scale_summable _ (by fun_prop) ρ Γ hΓ hmono D hD hρcarried
    hρpositive τ herror (by positivity : 0 < β/32) zero_lt_one N₀ hshell

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PreparedEndgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prepared original pair gives positive measure of original distances -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem prepared_pair_positive_distance_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) (E : Set (Space (m+3))) (hE : IsCompact E)
    (p : PreparedOriginalPair E (1/8)) : 0 < volume (distanceSet E) := by
  classical
  let w : Sphere (m+3) := ⟨p.pair.direction,by
    rw [Metric.mem_sphere,dist_zero_right,p.pair.direction_unit]⟩
  let e := reverseNorthRotation w
  obtain ⟨a,ha,_hcontract,hcube⟩ := compact_projection_into_unitCube E hE
    e.toLinearIsometry.toContinuousLinearMap
  let f := scaledIsometry e a ha
  let F := pairHomeomorph f
  let μ := p.pair.left.map f.continuous.aemeasurable
  let ν := p.pair.right.map f.continuous.aemeasurable
  let E' := f '' E
  have hE' : IsCompact E' := hE.image f.continuous
  have hcarr₁ : (μ : Measure (Space (m+3))) (centeredUnitCube (m+3)).carrierᶜ = 0 := by
    change ((p.pair.left : Measure (Space (m+3))).map f) _ = 0
    rw [f.measurableEmbedding.map_apply]
    apply measure_mono_null _ (Measure.measure_compl_support (μ := (p.pair.left : Measure (Space (m+3)))))
    intro x hx hxs
    exact hx (hcube x (p.left_subset hxs))
  have hcarr₂ : (ν : Measure (Space (m+3))) (centeredUnitCube (m+3)).carrierᶜ = 0 := by
    change ((p.pair.right : Measure (Space (m+3))).map f) _ = 0
    rw [f.measurableEmbedding.map_apply]
    apply measure_mono_null _ (Measure.measure_compl_support (μ := (p.pair.right : Measure (Space (m+3)))))
    intro x hx hxs
    exact hx (hcube x (p.right_subset hxs))
  let χ := p.exponent-(m+3:ℕ)/2
  have hχ : 0 < χ := sub_pos.mpr p.exponent_gt
  have hexponent : (m+3:ℕ)/2+χ = p.exponent := by dsimp [χ]; ring
  have hsd : (m+3:ℕ)/2+χ ≤ (m+3:ℕ) := by
    rw [hexponent]
    exact frostman_exponent_le_dimension p.pair.left
      ((by positivity : (0:ℝ) ≤ (m+3:ℕ)/2).trans_lt p.exponent_gt)
      p.pair.constant_pos p.pair.left_frostman
  let C := p.pair.constant/a^p.exponent
  have hC : 0 ≤ C := le_of_lt (div_pos p.pair.constant_pos (Real.rpow_pos_of_pos ha _))
  have hf₁ : FrostmanBallBound (μ : Measure (Space (m+3))) ((m+3:ℕ)/2+χ) C := by
    rw [hexponent]
    exact scaledIsometry_frostman e a ha _ p.pair.left_frostman
  have hf₂ : FrostmanBallBound (ν : Measure (Space (m+3))) ((m+3:ℕ)/2+χ) C := by
    rw [hexponent]
    exact scaledIsometry_frostman e a ha _ p.pair.right_frostman
  have hrelmass : ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3)))) (F '' p.pair.relation) = 1 := by
    exact (homeomorph_pair_measure_image f (p.pair.left : Measure (Space (m+3)))
      (p.pair.right : Measure (Space (m+3))) p.pair.relation).trans p.pair.relation_mass
  have hrelmeas : MeasurableSet (F '' p.pair.relation) :=
    F.measurableEmbedding.measurableSet_image.mpr p.pair.relation_measurable
  have hmem := (mem_ae_iff_prob_eq_one hrelmeas).mpr hrelmass
  have hsep : ∀ᵐ z ∂(μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))),
      a*(p.pair.radius/2) ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ a*(2*p.pair.radius) := by
    filter_upwards [hmem] with z hz
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := hz
    obtain ⟨hl,hu,_⟩ := p.pair.geometry x hxy.1 y hxy.2
    change a*(p.pair.radius/2) ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ a*(2*p.pair.radius)
    rw [scaledIsometry_dist]
    exact ⟨mul_le_mul_of_nonneg_left hl ha.le,mul_le_mul_of_nonneg_left hu ha.le⟩
  have hnear : ∀ᵐ z : Space (m+3) × Space (m+3) ∂(μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))),
      ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 := by
    filter_upwards [hmem] with z hz
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := hz
    have hh := (p.pair.geometry x hxy.1 y hxy.2).2.2.2.2
    change ‖NormedSpace.normalize (f x-f y)-
      (gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8
    rw [scaledIsometry_normalize_sub,← linearIsometryEquiv_normalize_sub]
    change ‖NormedSpace.normalize (reverseNorthRotation w x-reverseNorthRotation w y)-
      (gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8
    rw [reverseNorthRotation_cap_norm]
    exact hh.le
  have hcarried : ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))))
      ((fun z : Space (m+3) × Space (m+3) => dist z.1 z.2) ⁻¹' (distanceSet E')ᶜ) = 0 := by
    have hnull : ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3)))) (F '' p.pair.relation)ᶜ = 0 := hmem
    apply measure_mono_null _ hnull
    rintro z hz ⟨⟨x,y⟩,hxy,rfl⟩
    exact hz ⟨f x,mem_image_of_mem _ (p.left_subset hxy.1),
      f y,mem_image_of_mem _ (p.right_subset hxy.2),rfl⟩
  have hfilters : ∀ ω : ℝ, 0 < ω → ω ≤ 1 →
      ∃ Γ : ℕ → Set (Space (m+3) × Space (m+3)),
        (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
        0 < ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3)))) (⋂ N, Γ N) ∧
        (∀ N, ∀ z ∈ Γ N, z.1 ≠ z.2) ∧
        (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*(m+3:ℕ)*ω*(N:ℝ)))) ∧
        CapAvailable μ ν Γ ((m+3:ℕ)/2) := by
    intro ω hω hω1
    obtain ⟨Γ,hΓ,hm,hpos,hsub,hparts,hcaps⟩ := p.filters ω hω hω1
    refine ⟨fun N => F '' Γ N,fun N => F.measurableEmbedding.measurableSet_image.mpr (hΓ N),
      fun i j hij => Set.image_mono (hm hij),?_,?_,?_,hcaps.scaledIsometry e a ha⟩
    · have he : (⋂ N, F '' Γ N) = F '' (⋂ N, Γ N) := by
        ext z
        obtain ⟨z,rfl⟩ := F.surjective z
        simp only [mem_iInter,F.injective.mem_set_image]
      rw [he]
      exact hpos.trans_le (homeomorph_pair_measure_image f (p.pair.left : Measure (Space (m+3)))
        (p.pair.right : Measure (Space (m+3))) (⋂ N,Γ N)).ge
    · intro N z hz
      obtain ⟨⟨x,y⟩,hxy,rfl⟩ := hz
      change f x ≠ f y
      apply f.injective.ne
      have hh := (p.pair.geometry x (hsub N hxy).1 y (hsub N hxy).2).1
      exact dist_pos.mp ((half_pos p.pair.radius_pos).trans_le hh)
    · intro N
      exact (hparts N).homeomorph f
  apply positive_distance_of_scaledIsometry e a ha E
  exact unit_pair_positive_distance hgnomonic hquadratic m hχ hsd
    (centeredUnitCube _) (centeredUnitCube _) rfl rfl μ ν hcarr₁ hcarr₂ C C hC hC hf₁ hf₂
    (a*(p.pair.radius/2)) (a*(2*p.pair.radius))
    (mul_pos ha (half_pos p.pair.radius_pos))
    (mul_pos ha (mul_pos (by norm_num) p.pair.radius_pos)) hsep hnear
    (distanceSet E') (distanceSet_isCompact hE').measurableSet hcarried hfilters

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.prepared_pair_positive_distance_oai := @OAI.Falconer.prepared_pair_positive_distance_oai
