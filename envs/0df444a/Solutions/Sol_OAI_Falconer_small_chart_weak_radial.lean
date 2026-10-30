-- Prove2me | solution 1 for OAI.Falconer.small_chart_weak_radial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:53:26.746984+00:00
-- url     : https://prove2.me/submissions/4d8749d6-350e-4895-b21a-c9d864f4da51

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

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
-- module Solutions.OAIQ088_FD.Falconer_Incidence_GridCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Candidate grid counts in any ambient dimension

The remaining unknown cell in a retained graph edge is confined to a small
ball. Its integer coordinate labels therefore lie in a product of short
integer intervals. This gives the dimension-dependent degree factor.
-/

namespace Falconer

/-- Euclidean distance bounds every integer coordinate difference. -/
theorem grid_coordinate_bound {d L : ℕ} {s r : ℝ} (hs : 0 < s)
    (hL : r * s ≤ L) {z w : Fin d → ℤ}
    (hz : ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) (i : Fin d) :
    |z i - w i| ≤ (L : ℤ) := by
  have hi := (PiLp.norm_apply_le (scaledGridPoint s z - scaledGridPoint s w) i).trans hz
  change |(z i : ℝ) / s - (w i : ℝ) / s| ≤ r at hi
  rw [← sub_div, abs_div, abs_of_pos hs] at hi
  have hb : |(z i : ℝ) - (w i : ℝ)| ≤ (L : ℝ) :=
    ((div_le_iff₀ hs).mp hi).trans hL
  exact_mod_cast hb

/-- A finite family in a coordinate box has at most `(2L+1)^d` labels. -/
theorem grid_box_card {d L : ℕ} (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ∀ i, |z i - w i| ≤ (L : ℤ)) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  let shift : (Fin d → ℤ) → (Fin d → ℤ) := fun z i => z i - w i
  have hi : Function.Injective shift := by
    intro u v huv
    funext i
    have hi := congrFun huv i
    dsimp [shift] at hi
    omega
  have hsub : S.image shift ⊆
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (abs_le.mp (hS u hu i))
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    S.card = (S.image shift).card := (Finset.card_image_of_injective S hi).symm
    _ ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))).card :=
      Finset.card_le_card hsub
    _ = (2 * L + 1)^d := by simp [Fintype.card_piFinset, hcard]

/-- Ball count at a chosen grid center, with explicit integer radius. -/
theorem grid_ball_card {d L : ℕ} {s r : ℝ} (hs : 0 < s) (hL : r * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) :
    S.card ≤ (2 * L + 1)^d :=
  grid_box_card S w (fun z hz i => grid_coordinate_bound hs hL (hS z hz) i)

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
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidenceMoment
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The natural-number incidence moment used to select transverse pins -/

namespace Falconer
open MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

private theorem rpow_pow_nat (x : ℝ≥0∞) (a : ℝ) (k : ℕ) :
    (x^a)^k = x^(a*k) := by
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]

theorem incidence_moment (μ : Measure X) (F : X → ℝ≥0∞) (hF : AEMeasurable F μ)
    {k : ℕ} (hk : 2 ≤ k) :
    (∫⁻ x, F x ∂μ)^k ≤ (∫⁻ x, (F x)^k ∂μ)*(μ Set.univ)^(k-1) := by
  have hk' : 1 < (k:ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hk0 : (k:ℝ) ≠ 0 := by linarith
  have hkm0 : (k:ℝ)-1 ≠ 0 := by linarith
  have hc : (k:ℝ).HolderConjugate ((k:ℝ)/((k:ℝ)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hk').mpr rfl
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc hF
    (aemeasurable_const : AEMeasurable (fun _ : X => (1:ℝ≥0∞)) μ)
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_one,
    ENNReal.rpow_natCast] at hH
  have hp := pow_le_pow_left' hH k
  apply hp.trans_eq
  rw [mul_pow,rpow_pow_nat,rpow_pow_nat]
  have hfirst : (1/(k:ℝ))*(k:ℝ) = 1 := by field_simp
  have hsecond : (1/((k:ℝ)/((k:ℝ)-1)))*(k:ℝ) = ((k-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k),Nat.cast_one]
    field_simp
  rw [hfirst,hsecond,ENNReal.rpow_one,ENNReal.rpow_natCast]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiberDensityPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Density pruning uses the original fibers in every retained cell -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

theorem fiberDensityBad_measurable (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ι → Set X)
    (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (θ : ℝ≥0∞) :
    MeasurableSet (fiberDensityBad μ G Q I θ) := by
  apply hG.inter
  apply Finset.measurableSet_biUnion I
  intro i hi
  have hS : MeasurableSet ((univ ×ˢ Q i) ∩ G) := (MeasurableSet.univ.prod (hQ i hi)).inter hG
  have hm : Measurable (fun p => μ (Q i ∩ Prod.mk p ⁻¹' G)) := by
    convert measurable_measure_prodMk_left (ν := μ) hS using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    congr 1
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]
  exact (measurableSet_lt hm measurable_const).prod (hQ i hi)

omit [MeasurableSpace P] in
theorem fiberDensityBad_fiber_mass (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (θ : ℝ≥0∞) (p : P) :
    μ (Prod.mk p ⁻¹' fiberDensityBad μ G Q I θ) ≤ θ*μ univ := by
  classical
  let D := I.filter (fun i => μ (Q i ∩ Prod.mk p ⁻¹' G) < θ*μ (Q i))
  have hs : Prod.mk p ⁻¹' fiberDensityBad μ G Q I θ =
      ⋃ i ∈ D, Q i ∩ Prod.mk p ⁻¹' G := by
    ext x
    simp only [fiberDensityBad,mem_preimage,mem_inter_iff,mem_iUnion,mem_prod,
      mem_ofPred_eq,D,Finset.mem_filter]
    aesop
  have hsum : ∑ i ∈ I, μ (Q i) ≤ μ univ := by
    rw [← measure_biUnion_finset hdisj hQ]
    exact measure_mono (subset_univ _)
  rw [hs]
  calc
    _ ≤ ∑ i ∈ D, μ (Q i ∩ Prod.mk p ⁻¹' G) := measure_biUnion_finset_le D _
    _ ≤ ∑ i ∈ D, θ*μ (Q i) := Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2.le)
    _ ≤ ∑ i ∈ I, θ*μ (Q i) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = θ*(∑ i ∈ I, μ (Q i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ θ*μ univ := mul_le_mul' le_rfl hsum

theorem fiberDensityBad_product_mass (ν : Measure P) (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ι → Set X)
    (I : Finset ι) (hQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (θ : ℝ≥0∞) :
    (ν.prod μ) (fiberDensityBad μ G Q I θ) ≤ (θ*μ univ)*ν univ := by
  rw [Measure.prod_apply (fiberDensityBad_measurable μ G hG Q I hQ θ)]
  calc
    _ ≤ ∫⁻ _p, θ*μ univ ∂ν := lintegral_mono (fiberDensityBad_fiber_mass μ G Q I hQ hdisj θ)
    _ = _ := by rw [lintegral_const,mul_comm]

omit [MeasurableSpace P] in
theorem fiberDensity_retained (μ : Measure X) (G : Set (P × X))
    (Q : ι → Set X) (I : Finset ι) (θ : ℝ≥0∞) {p : P} {x : X}
    (hx : (p,x) ∈ G \ fiberDensityBad μ G Q I θ)
    {i : ι} (hi : i ∈ I) (hxi : x ∈ Q i) :
    θ*μ (Q i) ≤ μ (Q i ∩ Prod.mk p ⁻¹' G) := by
  by_contra! hlt
  apply hx.2
  refine ⟨hx.1,mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,?_⟩⟩⟩
  exact ⟨hlt,hxi⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DensityCellCharge
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Charging the full masses of hit children before the final density deletion -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [MeasurableSpace X]

theorem density_hit_children_charge (μ : Measure X) (S P T : Set X)
    (hS : MeasurableSet S) (Q : ι → Set X) (I : Finset ι)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hdisj : (I : Set ι).PairwiseDisjoint Q)
    {θ F : ℝ≥0∞} (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hdensity : ∀ i ∈ I, θ*μ (Q i) ≤ μ (Q i ∩ S))
    (hlocal : ∀ i ∈ I, Q i ∩ S ⊆ P ∩ T)
    (htest : μ (P ∩ T) ≤ F*μ P) :
    (∑ i ∈ I, μ (Q i)) ≤ (θ⁻¹*F)*μ P := by
  have hi : (I : Set ι).PairwiseDisjoint (fun i => Q i ∩ S) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono inter_subset_left inter_subset_left
  have hm : θ*(∑ i ∈ I, μ (Q i)) ≤ F*μ P := by
    calc
      _ = ∑ i ∈ I, θ*μ (Q i) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ I, μ (Q i ∩ S) := Finset.sum_le_sum hdensity
      _ = μ (⋃ i ∈ I, Q i ∩ S) := (measure_biUnion_finset hi (fun i hi => (hQ i hi).inter hS)).symm
      _ ≤ μ (P ∩ T) := measure_mono (iUnion₂_subset hlocal)
      _ ≤ _ := htest
  calc
    _ = θ⁻¹*(θ*(∑ i ∈ I, μ (Q i))) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hθ.ne' hθtop,one_mul]
    _ ≤ θ⁻¹*(F*μ P) := mul_le_mul' le_rfl hm
    _ = _ := (mul_assoc _ _ _).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_MultiscaleDensityPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous density pruning at finitely many endpoint depths -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

theorem multiscaleFiberBad_measurable (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ℕ → ι → Set X)
    (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i)) : MeasurableSet (multiscaleFiberBad μ G Q I θ J) := by
  apply Finset.measurableSet_biUnion
  intro j hj
  exact fiberDensityBad_measurable μ G hG (Q j) (I j) (hQ j (by simpa using hj)) θ

theorem multiscaleFiberBad_mass (ν : Measure P) (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ℕ → ι → Set X)
    (I : ℕ → Finset ι) (J : ℕ)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j)) (θ : ℝ≥0∞) :
    (ν.prod μ) (multiscaleFiberBad μ G Q I θ J) ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J+1), (ν.prod μ) (fiberDensityBad μ G (Q j) (I j) θ) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (J+1), (θ*μ univ)*ν univ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j ≤ J := by simpa using hj
      exact fiberDensityBad_product_mass ν μ G hG (Q j) (I j) (hQ j hjJ) (hdisj j hjJ) θ
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

omit [MeasurableSpace P] in
theorem multiscaleFiber_retained (μ : Measure X) (G : Set (P × X))
    (Q : ℕ → ι → Set X) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    {p : P} {x : X} (hx : (p,x) ∈ G \ multiscaleFiberBad μ G Q I θ J)
    {j : ℕ} (hj : j ≤ J) {i : ι} (hi : i ∈ I j) (hxi : x ∈ Q j i) :
    θ*μ (Q j i) ≤ μ (Q j i ∩ Prod.mk p ⁻¹' G) := by
  apply fiberDensity_retained μ G (Q j) (I j) θ ⟨hx.1,?_⟩ hi hxi
  intro hbad
  apply hx.2
  exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨by simpa using hj,hbad⟩⟩

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual dyadic centers as one translated integer grid

The graph packing estimates apply to centers of descendants of the
original parent cube. Their integer labels and common translation are
identified exactly, in every ambient dimension.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

/-- The translation includes half a child side. Its contribution cancels
in every displacement used by the retained graph. -/
theorem DyadicCube.descendant_center_grid {d n : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (hp : p.length = n) :
    (Q.descendant p).center =
      WithLp.toLp 2 (fun i => Q.origin i + (Q.side / (2 : ℝ)^n)/2) +
        scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) := by
  ext i
  simp only [PiLp.add_apply, scaledGridPoint_apply,
    Q.descendant_center, hp]
  field_simp

theorem DyadicCube.center_sub_eq_grid_sub {d n : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) (hp : p.length = n) (hq : q.length = n) :
    (Q.descendant p).center - (Q.descendant q).center =
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) -
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode q) := by
  rw [Q.descendant_center_grid p hp, Q.descendant_center_grid q hq]
  abel

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicBallCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local counts of actual all-dimensional dyadic ancestors -/

namespace Falconer
open Metric Set

theorem dyadic_center_diameter_count {d n L : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (S : Finset (List (Fin d → Bool))) (hS : ∀ p ∈ S, p.length = n)
    {r : ℝ} (hL : r*((2:ℝ)^n/Q.side) ≤ L)
    (hdiam : ∀ p ∈ S, ∀ q ∈ S, dist (Q.descendant p).center (Q.descendant q).center ≤ r) :
    S.card ≤ (2*L+1)^d := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨q,hq⟩ := hne
    have hi : Set.InjOn dyadicCode (S : Set (List (Fin d → Bool))) := by
      intro p hp t ht he
      exact dyadicCode_injective_at_depth (hS p hp) (hS t ht) he
    rw [← Finset.card_image_of_injOn hi]
    apply grid_ball_card (by positivity) hL (S.image dyadicCode) (dyadicCode q)
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [← Q.center_sub_eq_grid_sub p q (hS p hp) (hS q hq)]
    simpa only [dist_eq_norm] using hdiam p hp q hq
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.zero_le]

theorem DyadicCube.center_distance_ancestor {d n g : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (p : List (Fin d → Bool)) (hp : p.length = n) (hg : g ≤ n) :
    dist (Q.descendant p).center (Q.descendant (p.take g)).center ≤
      Real.sqrt d * (Q.side/(2:ℝ)^g) := by
  have h := (Q.descendant (p.take g)).dist_le (Q.descendant_side_pos hQ _).le
    (Q.center_mem_ancestor hQ p g)
    ((Q.descendant (p.take g)).center_mem (Q.descendant_side_pos hQ _))
  simpa only [Q.descendant_side,List.length_take,hp,min_eq_left hg] using h

theorem dyadic_ancestor_ball_count {d n g : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (S : Finset (List (Fin d → Bool))) (hS : ∀ p ∈ S, p.length = n) (hg : g ≤ n)
    (x : Space d) {r C : ℝ} (_hC : 0 ≤ C) (hr : r ≤ C*(Q.side/(2:ℝ)^g))
    (hball : ∀ p ∈ S, dist (Q.descendant p).center x ≤ r) :
    (S.image (List.take g)).card ≤ (2*Nat.ceil (2*C+2*Real.sqrt d)+1)^d := by
  classical
  let a := Q.side/(2:ℝ)^g
  have ha : 0 < a := by dsimp [a]; positivity
  have hcenter (p : List (Fin d → Bool)) (hp : p ∈ S) :
      dist (Q.descendant (p.take g)).center x ≤ r+Real.sqrt d*a := by
    calc
      _ ≤ dist (Q.descendant (p.take g)).center (Q.descendant p).center +
          dist (Q.descendant p).center x := dist_triangle _ _ _
      _ ≤ Real.sqrt d*a+r := add_le_add
        (by simpa only [dist_comm] using Q.center_distance_ancestor hQ p (hS p hp) hg) (hball p hp)
      _ = _ := add_comm _ _
  apply dyadic_center_diameter_count (n := g) Q hQ (S.image (List.take g))
    (fun p hp => by
      obtain ⟨q,hq',rfl⟩ := Finset.mem_image.mp hp
      simp only [List.length_take,hS q hq',min_eq_left hg])
    (r := 2*r+2*Real.sqrt d*a)
  · have hc : 2*C+2*Real.sqrt d ≤ (Nat.ceil (2*C+2*Real.sqrt d):ℝ) := Nat.le_ceil _
    have hh : 2*r+2*Real.sqrt d*a ≤ (2*C+2*Real.sqrt d)*a := by nlinarith [hr]
    calc
      _ ≤ ((2*C+2*Real.sqrt d)*a)*((2:ℝ)^g/Q.side) :=
        mul_le_mul_of_nonneg_right hh (by positivity)
      _ = 2*C+2*Real.sqrt d := by dsimp [a]; field_simp
      _ ≤ _ := hc
  · intro p hp q hq
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q',hq',rfl⟩ := Finset.mem_image.mp hq
    calc
      _ ≤ dist (Q.descendant (p'.take g)).center x +
          dist x (Q.descendant (q'.take g)).center := dist_triangle _ _ _
      _ ≤ (r+Real.sqrt d*a)+(r+Real.sqrt d*a) :=
        add_le_add (hcenter p' hp') (by simpa only [dist_comm] using hcenter q' hq')
      _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball bounds obtained from actual occupied-cell profile estimates -/

namespace Falconer.Regularization
open MeasureTheory Set Metric
open scoped ENNReal
variable {d : ℕ}

theorem cellsMeetingBall_card (Q : DyadicCube d) (hQ : 0 < Q.side)
    (n : ℕ) (x : Space d) {r C : ℝ} (hC : 0 ≤ C) (hr : r ≤ C*(Q.side/(2:ℝ)^n)) :
    (cellsMeetingBall Q n x r).card ≤ (2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d := by
  classical
  let S := cellsMeetingBall Q n x r
  have hS (p) (hp : p ∈ S) : p.length = n :=
    (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
  have hcenter (p) (hp : p ∈ S) :
      dist (Q.descendant p).center x ≤ (C+Real.sqrt d)*(Q.side/(2:ℝ)^n) := by
    obtain ⟨y,hy,hyb⟩ := (Finset.mem_filter.mp hp).2
    have hc := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le
      ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p)) hy
    rw [Q.descendant_side,hS p hp] at hc
    have hb := (mem_ball.mp hyb).le
    have hh := (dist_triangle (Q.descendant p).center y x).trans (add_le_add hc hb)
    nlinarith
  have hh := dyadic_ancestor_ball_count Q hQ S hS (le_refl n) x
    (C := C+Real.sqrt d) (by positivity) (le_refl _) hcenter
  have he : S.image (List.take n) = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      simpa only [List.take_of_length_le (hS q hq).le] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨p,hp,List.take_of_length_le (hS p hp).le⟩
  rw [he] at hh
  have hc : 2*(C+Real.sqrt d)+2*Real.sqrt d = 2*C+4*Real.sqrt d := by ring
  simpa only [hc] using hh

theorem measure_ball_le_cell_count (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (hcarry : ρ Q.carrierᶜ = 0)
    (n : ℕ) (x : Space d) (r : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hcell : ∀ p ∈ cubePaths d n, 0 < ρ (Q.descendant p).carrier →
      (ρ (Q.descendant p).carrier).toReal ≤ M) :
    (ρ (ball x r)).toReal ≤ (cellsMeetingBall Q n x r).card*M := by
  classical
  let S := cellsMeetingBall Q n x r
  have hcover : ball x r ⊆ leafUnion Q S ∪ Q.carrierᶜ := by
    intro y hy
    by_cases hyQ : y ∈ Q.carrier
    · obtain ⟨p,hp,hyp⟩ := Q.mem_descendant_at_depth n hyQ
      exact Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,y,hyp,hy⟩,hyp⟩)
    · exact Or.inr hyQ
  have hmass : ρ (ball x r) ≤ ρ (leafUnion Q S) := by
    apply (measure_mono hcover).trans
    have hh := measure_union_le (leafUnion Q S) Q.carrierᶜ (μ := ρ)
    rwa [hcarry,add_zero] at hh
  calc
    _ ≤ (ρ (leafUnion Q S)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hmass
    _ = ∑ p ∈ S, (ρ (Q.descendant p).carrier).toReal :=
      restriction_total_mass_real Q hQ ρ (Finset.filter_subset _ _)
    _ ≤ ∑ _p ∈ S, M := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpos : 0 < ρ (Q.descendant p).carrier
      · exact hcell p (Finset.mem_filter.mp hp).1 hpos
      · rw [nonpos_iff_eq_zero.mp (le_of_not_gt hpos),ENNReal.toReal_zero]
        exact hM
    _ = _ := by simp [S]

theorem sourceClass_root_null (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (N B : ℕ) (p : CellPath d) :
    sourceClass Q μ N B p Q.carrierᶜ = 0 := by
  simp only [sourceClass,normalizedClass,classMeasure,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply Q.measurable.compl]
  have he : Q.carrierᶜ ∩ leafUnion Q
      (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
        (regularizationLabel Q μ N B p)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

theorem sourceClass_ball_upper (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {n : ℕ} (hn : n ≤ N) (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    (sourceClass Q μ N B p₀ (ball x (C*(Q.side/(2:ℝ)^n)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*
        (((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p₀ n)) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  have hh := measure_ball_le_cell_count Q hQ (sourceClass Q μ N B p₀)
    (sourceClass_root_null Q hQ μ N B p₀) n x (C*(Q.side/(2:ℝ)^n)) (by positivity)
    (fun p hp hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hn
      ((mem_cubePaths _ _ _).mp hp) hpos).2)
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast cellsMeetingBall_card Q hQ n x hC (le_refl _)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Full conditional class laws, normalized by the actual cell mass

The profile is only a comparison for that mass. The conditional measure
is the original restricted class law divided by its own cell mass.
-/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem conditional_real_le (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (A T : Set (Space d)) :
    (ProbabilityTheory.cond ρ A T).toReal ≤ (ρ T).toReal/(ρ A).toReal := by
  unfold ProbabilityTheory.cond
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have hh : ((ρ.restrict A) T).toReal ≤ (ρ T).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show 0 ≤ (ρ A).toReal from ENNReal.toReal_nonneg))

theorem sourceClass_conditional_probability (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] (N B : ℕ)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N) (P : CellPath d)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier) :
    IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  exact ProbabilityTheory.cond_isProbabilityMeasure hPpos.ne'

theorem sourceClass_conditional_ball_upper (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p n : ℕ} (hpN : p ≤ N) (hn : n ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
      (ball x (C*(Q.side/(2:ℝ)^n)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ n+2*((d:ℝ)+1)*lam) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  let c : ℝ := ((d:ℝ)+1)*lam
  let mp := sourceProfile Q μ N B p₀ p
  let mn := sourceProfile Q μ N B p₀ n
  let D : ℝ := ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)
  have hRp : 0 < R := by dsimp [R]; positivity
  have hb := sourceClass_ball_upper Q hQ μ hN hB hwidth hlarge hp₀ hn x hC
  have hl := (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hpN hP hPpos).1
  have hc := conditional_real_le (sourceClass Q μ N B p₀) (Q.descendant P).carrier
    (ball x (C*(Q.side/(2:ℝ)^n)))
  have hratio := div_le_div₀ (show 0 ≤ D*(R^c*R^(-mn)) by dsimp [D]; positivity)
    hb (show 0 < R^(-c)*R^(-mp) by positivity) (show R^(-c)*R^(-mp) ≤
      (sourceClass Q μ N B p₀ (Q.descendant P).carrier).toReal by
        simpa only [c,mp,R,neg_mul] using hl)
  apply (hc.trans hratio).trans_eq
  change (D*(R^c*R^(-mn)))/(R^(-c)*R^(-mp)) = D*R^(mp-mn+2*((d:ℝ)+1)*lam)
  rw [mul_div_assoc,← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp]
  congr 2
  dsimp [c]
  ring

end Falconer.Regularization

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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialFreezing
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing radial directions in a source cell away from its pin -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalize_distance_scaled {u v : E} {r : ℝ}
    (hu : r ≤ ‖u‖) (hv : v ≠ 0) :
    r*dist (normalize u) (normalize v) ≤ 2*dist u v := by
  have he : ‖u‖ • (normalize u-normalize v) =
      u-v+(‖v‖-‖u‖) • normalize v := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (u-v) ((‖v‖-‖u‖) • normalize v)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hv,mul_one] at hb
  have hn := abs_norm_sub_norm_le v u
  rw [norm_sub_rev v u] at hn
  rw [dist_eq_norm,dist_eq_norm]
  have hh := mul_le_mul_of_nonneg_right hu (norm_nonneg (normalize u-normalize v))
  linarith

theorem perpendicular_normalize_self (v : E) : perpendicularPart (normalize v) v = 0 := by
  by_cases hv : v = 0
  · simp [hv,perpendicularPart,NormedSpace.normalize]
  · have he : v = ‖v‖ • normalize v := (norm_smul_normalize v).symm
    calc
      _ = perpendicularPart (normalize v) (‖v‖ • normalize v) := congrArg _ he
      _ = ‖v‖ • perpendicularPart (normalize v) (normalize v) := perpendicularPart_smul _ _ _
      _ = 0 := by simp [perpendicularPart,norm_normalize hv]

theorem frozen_radial_tube_error (x c z y : E) {r D W : ℝ}
    (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hzx : z ≠ x)
    (hzc : ‖z-c‖ ≤ D) (hyc : ‖y-c‖ ≤ D)
    (htube : ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W) :
    ‖perpendicularPart (normalize (c-x)) (y-z)‖ ≤ W+8*D^2/r := by
  have hc0 : c-x ≠ 0 := norm_pos_iff.mp (hr.trans_le hcx)
  have hz0 : z-x ≠ 0 := sub_ne_zero.mpr hzx
  have hD : 0 ≤ D := (norm_nonneg _).trans hzc
  have hd : ‖normalize (c-x)-normalize (z-x)‖ ≤ 2*D/r := by
    apply (le_div_iff₀ hr).mpr
    have hh := normalize_distance_scaled hcx hz0
    have he : dist (c-x) (z-x) = ‖z-c‖ := by
      rw [dist_eq_norm,sub_sub_sub_cancel_right,norm_sub_rev]
    rw [he,dist_eq_norm] at hh
    nlinarith
  have hyz : ‖y-z‖ ≤ 2*D := by
    have hh := norm_sub_le_norm_sub_add_norm_sub y c z
    rw [norm_sub_rev c z] at hh
    linarith
  have hshift : perpendicularPart (normalize (z-x)) (y-z) =
      perpendicularPart (normalize (z-x)) (y-x) := by
    have he : y-z = (y-x)-(z-x) := by abel
    rw [he,perpendicularPart_sub,perpendicular_normalize_self,sub_zero]
  have herr := perpendicularPart_direction_error (norm_normalize hc0) (norm_normalize hz0) (y-z)
  have hu : ‖perpendicularPart (normalize (c-x)) (y-z) -
      perpendicularPart (normalize (z-x)) (y-z)‖ ≤ 8*D^2/r := by
    apply herr.trans
    calc
      _ ≤ 2*(2*D/r)*(2*D) := by gcongr
      _ = _ := by ring
  calc
    _ = ‖(perpendicularPart (normalize (c-x)) (y-z)-
        perpendicularPart (normalize (z-x)) (y-z))+
          perpendicularPart (normalize (z-x)) (y-z)‖ := by congr 1; abel
    _ ≤ ‖perpendicularPart (normalize (c-x)) (y-z)-
        perpendicularPart (normalize (z-x)) (y-z)‖+
          ‖perpendicularPart (normalize (z-x)) (y-z)‖ := norm_add_le _ _
    _ ≤ 8*D^2/r+W := add_le_add hu (by rw [hshift]; exact htube)
    _ = _ := add_comm _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCapTube
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Final radial caps put entire hit children in a witness's physical tube -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_cap_child_tube (x z q y u : E) {r D B : ℝ}
    (hq : q ≠ x) (hB : ‖z-x‖ ≤ B)
    (hzcap : ‖normalize (z-x)-u‖ ≤ r) (hqcap : ‖normalize (q-x)-u‖ ≤ r)
    (hy : ‖y-z‖ ≤ D) :
    ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r := by
  let v := normalize (z-x)
  let w := normalize (q-x)
  have hw : ‖w‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hr : 0 ≤ r := (norm_nonneg _).trans hzcap
  have hclose : ‖v-w‖ ≤ 2*r := by
    have hh := norm_sub_le_norm_sub_add_norm_sub v u w
    rw [norm_sub_rev u w] at hh
    exact hh.trans (by change _ ≤ 2*r; linarith)
  have hww : perpendicularPart w w = 0 := by simp [perpendicularPart,hw]
  have hv : ‖perpendicularPart w v‖ ≤ 2*r := by
    have hh := norm_perpendicularPart_le hw (v-w)
    rw [perpendicularPart_sub,hww,sub_zero] at hh
    exact hh.trans hclose
  have hzline : ‖perpendicularPart w (z-x)‖ ≤ B*(2*r) := by
    have he : z-x = ‖z-x‖ • v := (norm_smul_normalize (z-x)).symm
    rw [he,perpendicularPart_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul hB hv (norm_nonneg _) hB0
  have he : perpendicularPart w (y-x) = perpendicularPart w (y-z)+perpendicularPart w (z-x) := by
    simp only [perpendicularPart,inner_sub_right,sub_smul]
    abel
  change ‖perpendicularPart w (y-x)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_perpendicularPart_le hw _).trans hy) hzline).trans_eq (by ring))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapDensityCharge
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single retained cap witness charges all hit children of a parent -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem cap_density_children_charge (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (J j : ℕ) (hj : j ≤ J)
    (C : Finset ι) (hCI : C ⊆ I j) (P : Set (Space d)) (x u : Space d)
    {r D B : ℝ} {θ F : ℝ≥0∞} (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ i ∈ C, MeasurableSet (Q j i)) (hdisj : (C : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ i ∈ C, Q j i ⊆ P)
    (hdiam : ∀ i ∈ C, ∀ y ∈ Q j i, ∀ z ∈ Q j i, ‖y-z‖ ≤ D)
    (hhit : ∀ i ∈ C, ∃ z ∈ Q j i,
      (x,z) ∈ G \ multiscaleFiberBad μ G Q I θ J ∧
      z ≠ x ∧ ‖z-x‖ ≤ B ∧ ‖normalize (z-x)-u‖ ≤ r)
    (htest : ∀ q ∈ P, (x,q) ∈ G \ multiscaleFiberBad μ G Q I θ J →
      q ≠ x → ‖normalize (q-x)-u‖ ≤ r →
      μ (P ∩ {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r}) ≤ F*μ P) :
    (∑ i ∈ C, μ (Q j i)) ≤ (θ⁻¹*F)*μ P := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨i,hi⟩ := hC
    obtain ⟨q,hqQ,hq,hqne,_hqB,hqcap⟩ := hhit i hi
    let T : Set (Space d) := {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D+2*B*r}
    apply density_hit_children_charge μ (Prod.mk x ⁻¹' G) P T
      (hG.preimage (by fun_prop)) (Q j) C hQ hdisj hθ hθtop
    · intro i hi
      obtain ⟨z,hzQ,hz,_hzne,_hzB,_hzcap⟩ := hhit i hi
      exact multiscaleFiber_retained μ G Q I θ J hz hj (hCI hi) hzQ
    · intro i hi y hy
      obtain ⟨z,hzQ,_hz,_hzne,hzB,hzcap⟩ := hhit i hi
      exact ⟨hparent i hi hy.1,
        radial_cap_child_tube x z q y u hqne hzB hzcap hqcap (hdiam i hi y hy.1 z hzQ)⟩
    · exact htest q (hparent i hi hqQ) hq hqne hqcap
  · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    simp only [he,Finset.sum_empty,zero_le]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiniteMassMultiplication
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite multiplication of the charged hit-cell masses -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι]

theorem finite_parent_mass_step (P C : Finset ι) (parent : ι → ι)
    (wp wc : ι → ℝ≥0∞) (F : ℝ≥0∞) (hparent : ∀ i ∈ C, parent i ∈ P)
    (hcharge : ∀ p ∈ P, (∑ i ∈ C with parent i = p, wc i) ≤ F*wp p) :
    (∑ i ∈ C, wc i) ≤ F*(∑ p ∈ P, wp p) := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ i ∈ C with parent i = p, wc i :=
      (Finset.sum_fiberwise_of_maps_to hparent wc).symm
    _ ≤ ∑ p ∈ P, F*wp p := Finset.sum_le_sum hcharge
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_mass_multiplication (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (w : ℕ → ι → ℝ≥0∞) (F : ℕ → ℝ≥0∞) (J : ℕ)
    (hparent : ∀ j < J, ∀ i ∈ I (j+1), parent j i ∈ I j)
    (hcharge : ∀ j < J, ∀ p ∈ I j,
      (∑ i ∈ I (j+1) with parent j i = p, w (j+1) i) ≤ F j*w j p) :
    (∑ i ∈ I J, w J i) ≤ (∏ j ∈ Finset.range J, F j)*(∑ i ∈ I 0, w 0 i) := by
  classical
  induction J with
  | zero => simp
  | succ J ih =>
    have hs : (∑ i ∈ I (J+1), w (J+1) i) ≤ F J*(∑ i ∈ I J, w J i) :=
      finite_parent_mass_step (I J) (I (J+1)) (parent J) (w J) (w (J+1)) (F J)
        (hparent J (Nat.lt_succ_self _)) (by
          intro p hp
          exact hcharge J (Nat.lt_succ_self _) p hp)
    have hprev := ih (fun j hj => hparent j (Nat.lt_succ_of_lt hj))
      (fun j hj => hcharge j (Nat.lt_succ_of_lt hj))
    calc
      _ ≤ F J*(∑ i ∈ I J, w J i) := hs
      _ ≤ F J*((∏ j ∈ Finset.range J, F j)*(∑ i ∈ I 0, w 0 i)) := mul_le_mul' le_rfl hprev
      _ = _ := by rw [Finset.prod_range_succ]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_MultiscaleCapMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying actual physical-tube charges for one retained radial cap -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem multiscale_physical_cap_mass (μ : Measure (Space d))
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (Q : ℕ → ι → Set (Space d)) (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (J : ℕ) (x u : Space d) (r B : ℝ) (D : ℕ → ℝ) (θ : ℝ≥0∞) (F : ℕ → ℝ≥0∞)
    (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hparent : ∀ j < J, ∀ i ∈ I (j+1),
      parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ D j)
    (hbound : ∀ z, (x,z) ∈ G → ‖z-x‖ ≤ B)
    (hne : ∀ z, (x,z) ∈ G → z ≠ x)
    (hlocal : ∀ j < J, ∀ p ∈ I j, ∀ q ∈ Q j p, (x,q) ∈ G → q ≠ x →
      μ (Q j p ∩ {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤ D j+2*B*r}) ≤ F j*μ (Q j p))
    (hcover : ∀ z ∈ retainedRadialCap μ G Q I θ J x u r, ∃ i ∈ I J, z ∈ Q J i) :
    μ (retainedRadialCap μ G Q I θ J x u r) ≤
      (∏ j ∈ Finset.range J, θ⁻¹*F j)*μ univ := by
  classical
  let H := radialCapHitCells μ G Q I θ J x u r
  have hHI (j : ℕ) : H j ⊆ I j := Finset.filter_subset _ _
  have hmem {j : ℕ} {i : ι} (hi : i ∈ H j) :
      ∃ z ∈ Q j i, z ∈ retainedRadialCap μ G Q I θ J x u r := (Finset.mem_filter.mp hi).2
  have hparents : ∀ j < J, ∀ i ∈ H (j+1), parent j i ∈ H j := by
    intro j hj i hi
    obtain ⟨z,hz,hcap⟩ := hmem hi
    obtain ⟨hp,hsub⟩ := hparent j hj i (hHI _ hi)
    exact Finset.mem_filter.mpr ⟨hp,z,hsub hz,hcap⟩
  have hcharge : ∀ j < J, ∀ p ∈ H j,
      (∑ i ∈ H (j+1) with parent j i = p, μ (Q (j+1) i)) ≤
        (θ⁻¹*F j)*μ (Q j p) := by
    intro j hj p hp
    let C := (H (j+1)).filter (fun i => parent j i = p)
    have hCI : C ⊆ I (j+1) := fun i hi => hHI _ (Finset.mem_filter.mp hi).1
    have hCQ : ∀ i ∈ C, Q (j+1) i ⊆ Q j p := by
      intro i hi
      have hs := (hparent j hj i (hCI hi)).2
      rwa [(Finset.mem_filter.mp hi).2] at hs
    have hCdisj : (C : Set ι).PairwiseDisjoint (Q (j+1)) := by
      intro i hi k hk hne
      exact hdisj (j+1) (by omega) (hCI hi) (hCI hk) hne
    have hh := cap_density_children_charge μ G hG Q I J (j+1) (by omega)
      C hCI (Q j p) x u hθ hθtop
      (fun i hi => hQ (j+1) (by omega) i (hCI hi)) hCdisj hCQ
      (fun i hi => hdiam j hj i (hCI hi))
      (fun i hi => by
        obtain ⟨z,hz,hcap⟩ := hmem (Finset.mem_filter.mp hi).1
        exact ⟨z,hz,hcap.1,hne z hcap.1.1,hbound z hcap.1.1,hcap.2⟩)
      (fun q hqp hq hqn _ => hlocal j hj p (hHI _ hp) q hqp hq.1 hqn)
    exact hh
  have hmul := finite_mass_multiplication H parent (fun j i => μ (Q j i))
    (fun j => θ⁻¹*F j) J hparents hcharge
  have hsub : retainedRadialCap μ G Q I θ J x u r ⊆ ⋃ i ∈ H J, Q J i := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := hcover z hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hi,z,hzi,hz⟩,hzi⟩⟩
  have hzero : (∑ i ∈ H 0, μ (Q 0 i)) ≤ μ univ := by
    rw [← measure_biUnion_finset (fun i hi k hk hik =>
      hdisj 0 (Nat.zero_le _) (hHI _ hi) (hHI _ hk) hik)
      (fun i hi => hQ 0 (Nat.zero_le _) i (hHI _ hi))]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ μ (⋃ i ∈ H J, Q J i) := measure_mono hsub
    _ ≤ ∑ i ∈ H J, μ (Q J i) := measure_biUnion_finset_le _ _
    _ ≤ (∏ j ∈ Finset.range J, θ⁻¹*F j)*(∑ i ∈ H 0, μ (Q 0 i)) := hmul
    _ ≤ _ := mul_le_mul' le_rfl hzero

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CellwisePairDeletion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining local pair deletions with their original source-cell masses -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem conditional_pair_mass_reconstruct (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (Q : Set X) (hQ : μ Q ≠ 0) (E : Set (X × Y)) :
    μ Q*((ProbabilityTheory.cond μ Q).prod ν) E = ((μ.restrict Q).prod ν) E := by
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,Measure.smul_apply,smul_eq_mul,
    ← mul_assoc,ENNReal.mul_inv_cancel hQ (measure_ne_top μ Q),one_mul]

theorem cellwise_pair_deletion_bound (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set X) (E : ι → Set (X × Y))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hdisj : (I : Set ι).PairwiseDisjoint Q) (t : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ((μ.restrict (Q i)).prod ν) (E i) ≤ t*μ (Q i)) :
    (μ.prod ν) (⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)) ≤ t*μ univ := by
  calc
    _ ≤ ∑ i ∈ I, (μ.prod ν) (E i ∩ (Q i ×ˢ univ)) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ I, ((μ.restrict (Q i)).prod ν) (E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Measure.restrict_prod_eq_prod_univ,Measure.restrict_apply (hE i hi)]
    _ ≤ ∑ i ∈ I, t*μ (Q i) := Finset.sum_le_sum hlocal
    _ = t*(∑ i ∈ I, μ (Q i)) := (Finset.mul_sum _ _ _).symm
    _ = t*μ (⋃ i ∈ I, Q i) := by rw [measure_biUnion_finset hdisj hQ]
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

theorem conditional_cellwise_pair_deletion (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [SFinite ν] (I : Finset ι) (Q : ι → Set X) (E : ι → Set (X × Y))
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hE : ∀ i ∈ I, MeasurableSet (E i))
    (hpos : ∀ i ∈ I, μ (Q i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint Q) (t : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν) (E i) ≤ t) :
    (μ.prod ν) (⋃ i ∈ I, E i ∩ (Q i ×ˢ univ)) ≤ t*μ univ := by
  apply cellwise_pair_deletion_bound μ ν I Q E hQ hE hdisj t
  intro i hi
  rw [← conditional_pair_mass_reconstruct μ ν (Q i) (hpos i hi) (E i),mul_comm t]
  exact mul_le_mul' le_rfl (hlocal i hi)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteOverlap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting heavy members of a finite family with bounded overlap -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X ι : Type*} [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem finite_measure_sum_le_overlap (μ : Measure X) (I : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (L : ℕ)
    (hoverlap : ∀ x, (I.filter (fun i => x ∈ U i)).card ≤ L) :
    ∑ i ∈ I, μ (U i) ≤ (L:ℝ≥0∞)*μ univ := by
  classical
  have hp (x : X) : (∑ i ∈ I, (U i).indicator (fun _ => (1:ℝ≥0∞)) x) =
      ((I.filter (fun i => x ∈ U i)).card:ℝ≥0∞) := by
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp
  calc
    _ = ∑ i ∈ I, ∫⁻ x, (U i).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ :=
      Finset.sum_congr rfl (fun i hi => (lintegral_indicator_one (hU i hi)).symm)
    _ = ∫⁻ x, ∑ i ∈ I, (U i).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_finsetSum' I (fun i hi => (measurable_const.indicator (hU i hi)).aemeasurable)]
    _ ≤ ∫⁻ _x, (L:ℝ≥0∞) ∂μ := lintegral_mono (fun x => by
      rw [hp]
      exact Nat.cast_le.mpr (hoverlap x))
    _ = _ := lintegral_const _

theorem heavy_family_card_bound (μ : Measure X) (I : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (L : ℕ)
    (hoverlap : ∀ x, (I.filter (fun i => x ∈ U i)).card ≤ L)
    (F : ℝ≥0∞) (hheavy : ∀ i ∈ I, F ≤ μ (U i)) :
    (I.card:ℝ≥0∞)*F ≤ (L:ℝ≥0∞)*μ univ := by
  calc
    _ = ∑ _i ∈ I, F := by simp
    _ ≤ ∑ i ∈ I, μ (U i) := Finset.sum_le_sum hheavy
    _ ≤ _ := finite_measure_sum_le_overlap μ I U hU L hoverlap

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MatrixCofactorBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimension-dependent cofactor bounds for the weak-radial transverse frame -/

namespace Falconer
open scoped BigOperators
variable {d : ℕ}

theorem unit_entry_determinant_bound (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) : |M.det| ≤ (d.factorial:ℝ) := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d), |((Equiv.Perm.sign σ : ℤ):ℝ)*∏ i, M (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul,abs_unit_intCast,one_mul,Finset.abs_prod]
      exact (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hM (σ i) i)).trans_eq
        (by simp)
    _ = _ := by simp [Fintype.card_perm]

theorem unit_entry_adjugate_bound (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) (i j : Fin d) : |M.adjugate i j| ≤ (d.factorial:ℝ) := by
  rw [Matrix.adjugate_apply]
  apply unit_entry_determinant_bound
  intro a b
  by_cases ha : a = j
  · subst a
    by_cases hb : b = i <;> simp [Matrix.updateRow_apply,hb]
  · simpa only [Matrix.updateRow_apply,ha,ite_false, if_false] using hM a b

theorem unit_entry_inverse_bound (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) (i j : Fin d) : |M⁻¹ i j| ≤ (d.factorial:ℝ)/|M.det| := by
  rw [Matrix.inv_def,Matrix.smul_apply,Ring.inverse_eq_inv,smul_eq_mul,abs_mul,abs_inv]
  calc
    _ ≤ |M.det|⁻¹*(d.factorial:ℝ) :=
      mul_le_mul_of_nonneg_left (unit_entry_adjugate_bound M hM i j) (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by rw [div_eq_mul_inv,mul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GeneralColumns
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual coordinate isomorphisms for a transverse tuple in arbitrary dimension -/

namespace Falconer
open scoped BigOperators Matrix
variable {d : ℕ}

theorem euclideanColumnEquiv_symm_apply (v : Fin d → Space d)
    (hv : (euclideanColumnMatrix v).det ≠ 0) (x : Space d) :
    (euclideanColumnEquiv v hv).symm x = euclideanDualCoordinates v x := by
  have hh := euclideanDualCoordinates_column v hv ((euclideanColumnEquiv v hv).symm x)
  rw [← euclideanColumnEquiv_apply v hv,ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh.symm

theorem euclideanColumnMatrix_gram (v : Fin d → Space d) :
    Matrix.gram ℝ v = (euclideanColumnMatrix v)ᵀ * euclideanColumnMatrix v := by
  ext i j
  simp only [Matrix.gram_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    Matrix.mul_apply,Matrix.transpose_apply,euclideanColumnMatrix,Matrix.of_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem euclideanColumnMatrix_gram_sqrt (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = |(euclideanColumnMatrix v).det| := by
  rw [euclideanColumnMatrix_gram,Matrix.det_mul,Matrix.det_transpose,← pow_two,Real.sqrt_sq_eq_abs]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GeneralFrameBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative transverse frame for general-dimensional tube counting -/

namespace Falconer
open scoped BigOperators
variable {d : ℕ}

theorem euclideanColumnLinear_norm (v : Fin d → Space d) (hv : ∀ i, ‖v i‖ ≤ 1)
    (x : Space d) : ‖euclideanColumnLinear v x‖ ≤ (d:ℝ)*‖x‖ := by
  change ‖∑ i : Fin d, x i • v i‖ ≤ _
  calc
    _ ≤ ∑ i : Fin d, ‖x i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul (PiLp.norm_apply_le x i) (hv i) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

theorem euclideanDualCoordinates_norm (v : Fin d → Space d) (hv : ∀ i, ‖v i‖ ≤ 1)
    (x : Space d) : ‖euclideanDualCoordinates v x‖ ≤
      ((d:ℝ)^2*(d.factorial:ℝ)/|(euclideanColumnMatrix v).det|)*‖x‖ := by
  let B : ℝ := (d.factorial:ℝ)/|(euclideanColumnMatrix v).det|
  have hB : 0 ≤ B := div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hM (i j : Fin d) : |euclideanColumnMatrix v i j| ≤ 1 :=
    (PiLp.norm_apply_le (v j) i).trans (hv j)
  have hi (i : Fin d) : |euclideanDualCoordinates v x i| ≤ (d:ℝ)*B*‖x‖ := by
    change |∑ j : Fin d, (euclideanColumnMatrix v)⁻¹ i j*x j| ≤ _
    calc
      _ ≤ ∑ j : Fin d, |(euclideanColumnMatrix v)⁻¹ i j*x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, B*‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (unit_entry_inverse_bound _ hM i j) (PiLp.norm_apply_le x j) (abs_nonneg _) hB
      _ = _ := by simp [mul_assoc]
  have hh := coordinate_norm_le_card_mul (euclideanDualCoordinates v x) hi
  apply hh.trans_eq
  dsimp [B]
  ring

theorem exists_general_transverse_frame (v : Fin d → Space d) (hv : ∀ i, ‖v i‖ ≤ 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgram : Δ ≤ Real.sqrt (Matrix.gram ℝ v).det) :
    ∃ e : Space d ≃L[ℝ] Space d,
      (∀ i, e (EuclideanSpace.basisFun (Fin d) ℝ i) = v i) ∧
      (∀ i j, j ≠ i → (e.symm (v i)) j = 0) ∧
      ‖e.toContinuousLinearMap‖ ≤ (d:ℝ) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ (d:ℝ)^2*(d.factorial:ℝ)/Δ := by
  rw [euclideanColumnMatrix_gram_sqrt] at hgram
  have hdet : (euclideanColumnMatrix v).det ≠ 0 := by
    intro hz
    rw [hz,abs_zero] at hgram
    linarith
  let e := euclideanColumnEquiv v hdet
  have he (i : Fin d) : e (EuclideanSpace.basisFun (Fin d) ℝ i) = v i := by
    change (∑ j : Fin d, (EuclideanSpace.basisFun (Fin d) ℝ i) j • v j) = v i
    simp
  refine ⟨e,he,?_,?_,?_⟩
  · intro i j hji
    rw [← he i,e.symm_apply_apply]
    simp [EuclideanSpace.basisFun_apply,hji]
  · apply e.toContinuousLinearMap.opNorm_le_bound (Nat.cast_nonneg _)
    exact euclideanColumnLinear_norm v hv
  · apply e.symm.toContinuousLinearMap.opNorm_le_bound (by positivity)
    intro x
    change ‖e.symm x‖ ≤ _
    rw [euclideanColumnEquiv_symm_apply]
    apply (euclideanDualCoordinates_norm v hv x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact div_le_div_of_nonneg_left (by positivity) hΔ hgram

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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerBox
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product grid boxes for the general-dimensional tube count -/

namespace Falconer
open scoped BigOperators
variable {n : ℕ}

theorem integer_box_card (T : Finset (Fin n → ℤ)) (x : Fin n → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ)) (hT : ∀ z ∈ T, ∀ j, |(z j:ℝ)-x j| ≤ r) :
    T.card ≤ (2*L+1)^n := by
  classical
  let B (j : Fin n) := Finset.Icc (round (x j)-(L:ℤ)) (round (x j)+(L:ℤ))
  have hsub : T ⊆ Fintype.piFinset B := by
    intro z hz
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_Icc.mpr (integer_near_real_bounds (z j) (x j) r L (hT z hz j) hL)
  have hB (j : Fin n) : (B j).card = 2*L+1 := by
    dsimp [B]
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans_eq (by simp only [Fintype.card_piFinset,hB,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin])

theorem integer_box_cover_card {ι : Type*} [DecidableEq ι]
    (T : Finset (Fin n → ℤ)) (A : Finset ι) (x : ι → Fin n → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ))
    (hcover : ∀ z ∈ T, ∃ a ∈ A, ∀ j, |(z j:ℝ)-x a j| ≤ r) :
    T.card ≤ A.card*(2*L+1)^n := by
  classical
  let F : ι → Finset (Fin n → ℤ) := fun a => T.filter (fun z => ∀ j, |(z j:ℝ)-x a j| ≤ r)
  have hs : T ⊆ A.biUnion F := by
    intro z hz
    obtain ⟨a,ha,hza⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_filter.mpr ⟨hz,hza⟩⟩
  calc
    _ ≤ (A.biUnion F).card := Finset.card_le_card hs
    _ ≤ ∑ a ∈ A, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2*L+1)^n := Finset.sum_le_sum (fun a _ =>
      integer_box_card (F a) (x a) r L hL (fun z hz => (Finset.mem_filter.mp hz).2))
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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GeneralTransverseGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # General-dimensional physical grid count from the precise published input -/

namespace Falconer
open scoped BigOperators
variable {n : ℕ}

theorem general_transverse_grid_count (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (e : Space (n+1) ≃L[ℝ] Space (n+1))
    (v : Fin (n+1) → Space (n+1)) (A : Fin (n+1) → Finset (Space (n+1)))
    (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (haxis : ∀ i j : Fin (n+1), j ≠ i → (e.symm (v i)) j = 0)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*C+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin (n+1), ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)‖ ≤ C*δ) :
    S.card^n ≤ (∏ i : Fin (n+1), (A i).card)*(2*L+1)^(n*(n+1)) := by
  classical
  have hp (i : Fin (n+1)) : (S.image (dropGridCoordinate i)).card ≤ (A i).card*(2*L+1)^n := by
    apply integer_box_cover_card _ (A i) (fun a j => (e.symm a) (i.succAbove j)/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover i y hy
    refine ⟨a,ha,?_⟩
    intro j
    have hh := inverse_coordinate_tube_bound e (v i) (e (euclideanIntegerGrid δ y)) a
      (i.succAbove j) (haxis i (i.succAbove j) (Fin.succAbove_ne i j))
    rw [e.symm_apply_apply] at hh
    have hb := hh.trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
    change |(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)/δ| ≤ _
    change |δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)| ≤ _ at hb
    have hd : |(δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j))/δ| ≤
        ‖e.symm.toContinuousLinearMap‖*C := by
      rw [abs_div,abs_of_pos hδ]
      apply (div_le_iff₀ hδ).mpr
      nlinarith
    have he : (δ*(y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j))/δ =
        (y (i.succAbove j):ℝ)-(e.symm a) (i.succAbove j)/δ := by field_simp
    rwa [he] at hd
  calc
    _ ≤ ∏ i : Fin (n+1), (S.image (dropGridCoordinate i)).card := hLW n hn S
    _ ≤ ∏ i : Fin (n+1), (A i).card*(2*L+1)^n := Finset.prod_le_prod' (fun i _ => hp i)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TripleGridRounding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GeneralGridRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded original point sets admit finite transverse lattice approximations -/

namespace Falconer
open Set Metric
variable {n : ℕ}

theorem euclideanRound_distance {δ : ℝ} (hδ : 0 < δ) (x : Space (n+1)) :
    dist x (euclideanIntegerGrid δ (euclideanRound δ x)) ≤ ((n+1:ℕ):ℝ)*δ/2 := by
  rw [dist_eq_norm]
  have hh := coordinate_norm_le_card_mul (x-euclideanIntegerGrid δ (euclideanRound δ x))
    (r := δ/2) (fun i => round_mesh_error hδ (x i))
  nlinarith

theorem euclideanRound_mem_box {δ R : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hL : R/δ+1 ≤ (L:ℝ)) (x : Space (n+1)) (hx : ‖x‖ ≤ R) :
    euclideanRound δ x ∈ integerGridBox n L := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_Icc.mpr (round_bound hδ L hL (x i) ((PiLp.norm_apply_le x i).trans hx))

theorem roundedEuclideanGrid_mem {E : Set (Space (n+1))} {δ R : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ)) (hE : ∀ x ∈ E, ‖x‖ ≤ R)
    {x : Space (n+1)} (hx : x ∈ E) : euclideanRound δ x ∈ roundedEuclideanGrid E δ L := by
  classical
  exact Finset.mem_filter.mpr ⟨euclideanRound_mem_box hδ L hL x (hE x hx),x,hx,rfl⟩

theorem roundedEuclideanGrid_original {E : Set (Space (n+1))} {δ : ℝ} {L : ℕ}
    {z : Fin (n+1) → ℤ} (hz : z ∈ roundedEuclideanGrid E δ L) :
    ∃ x ∈ E, euclideanRound δ x = z := by
  classical
  exact (Finset.mem_filter.mp hz).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_GeneralPhysicalTubeCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # General-dimensional physical tube covers with original point witnesses -/

namespace Falconer
open Set Metric
open scoped BigOperators
variable {n : ℕ}

theorem general_physical_tube_cover (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (e : Space (n+1) ≃L[ℝ] Space (n+1))
    (he : ‖e.toContinuousLinearMap‖ ≤ ((n+1:ℕ):ℝ)) (v : Fin (n+1) → Space (n+1))
    (hv : ∀ i, ‖v i‖ = 1)
    (haxis : ∀ i j : Fin (n+1), j ≠ i → (e.symm (v i)) j = 0)
    (E : Set (Space (n+1))) (A : Fin (n+1) → Finset (Space (n+1))) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*(C+((n+1:ℕ):ℝ)^2)+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin (n+1), ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    ∃ P : Finset (Space (n+1)),
      (∀ x ∈ E, ∃ p ∈ P, dist x p ≤ ((n+1:ℕ):ℝ)^2*δ) ∧
      P.card^n ≤ (∏ i : Fin (n+1), (A i).card)*(2*L+1)^(n*(n+1)) := by
  classical
  let E' := e.symm '' E
  obtain ⟨N,hN⟩ := exists_nat_ge (‖e.symm.toContinuousLinearMap‖*R/δ+1)
  have hE' : ∀ y ∈ E', ‖y‖ ≤ ‖e.symm.toContinuousLinearMap‖*R := by
    rintro y ⟨x,hx,rfl⟩
    exact (e.symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left (hE x hx) (norm_nonneg _))
  let S := roundedEuclideanGrid E' δ N
  have hclose (y : Space (n+1)) :
      dist (e y) (e (euclideanIntegerGrid δ (euclideanRound δ y))) ≤ ((n+1:ℕ):ℝ)^2*δ := by
    calc
      _ = ‖e (y-euclideanIntegerGrid δ (euclideanRound δ y))‖ := by rw [dist_eq_norm,map_sub]
      _ ≤ ‖e.toContinuousLinearMap‖*‖y-euclideanIntegerGrid δ (euclideanRound δ y)‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ ((n+1:ℕ):ℝ)*(((n+1:ℕ):ℝ)*δ/2) := by
        apply mul_le_mul he (by simpa only [dist_eq_norm] using euclideanRound_distance hδ y)
          (norm_nonneg _) (Nat.cast_nonneg _)
      _ ≤ _ := by nlinarith [sq_nonneg ((n+1:ℕ):ℝ)]
  have hgrid : ∀ i : Fin (n+1), ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)‖ ≤ (C+((n+1:ℕ):ℝ)^2)*δ := by
    intro i z hz
    obtain ⟨y,hy,hz'⟩ := roundedEuclideanGrid_original hz
    obtain ⟨x,hx,rfl⟩ := hy
    obtain ⟨a,ha,hta⟩ := hcover i x hx
    have hd := hclose (e.symm x)
    rw [e.apply_symm_apply,hz',dist_comm] at hd
    have herr : ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)-
        perpendicularPart (v i) (x-a)‖ ≤ ((n+1:ℕ):ℝ)^2*δ := by
      rw [← perpendicularPart_sub,sub_sub_sub_cancel_right]
      exact (norm_perpendicularPart_le (hv i) _).trans (by simpa only [dist_eq_norm] using hd)
    refine ⟨a,ha,?_⟩
    calc
      _ = ‖(perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)-
          perpendicularPart (v i) (x-a))+perpendicularPart (v i) (x-a)‖ := by congr 1; abel
      _ ≤ ‖perpendicularPart (v i) (e (euclideanIntegerGrid δ z)-a)-
          perpendicularPart (v i) (x-a)‖+‖perpendicularPart (v i) (x-a)‖ := norm_add_le _ _
      _ ≤ ((n+1:ℕ):ℝ)^2*δ+C*δ := add_le_add herr hta
      _ = _ := by ring
  let P := S.image (fun z => e (euclideanIntegerGrid δ z))
  refine ⟨P,?_,?_⟩
  · intro x hx
    have hy : e.symm x ∈ E' := mem_image_of_mem _ hx
    have hz : euclideanRound δ (e.symm x) ∈ S := roundedEuclideanGrid_mem hδ N hN hE' hy
    refine ⟨e (euclideanIntegerGrid δ (euclideanRound δ (e.symm x))),Finset.mem_image.mpr ⟨_,hz,rfl⟩,?_⟩
    simpa only [e.apply_symm_apply] using hclose (e.symm x)
  · have hcard : P.card ≤ S.card := Finset.card_image_le
    exact (Nat.pow_le_pow_left hcard n).trans (general_transverse_grid_count hLW hn e v A S hδ haxis L hL hgrid)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_GeneralTransverseCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative general-dimensional transverse tube counting -/

namespace Falconer
open Set Metric
open scoped BigOperators
variable {n : ℕ}

theorem general_transverse_tube_cover (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (v : Fin (n+1) → Space (n+1)) (hv : ∀ i, ‖v i‖ = 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (Matrix.gram ℝ v).det)
    (E : Set (Space (n+1))) (A : Fin (n+1) → Finset (Space (n+1))) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcover : ∀ i : Fin (n+1), ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    ∃ P : Finset (Space (n+1)),
      (∀ x ∈ E, ∃ p ∈ P, dist x p ≤ ((n+1:ℕ):ℝ)^2*δ) ∧
      (P.card:ℝ)^n ≤ (∏ i : Fin (n+1), ((A i).card:ℝ))*
        (generalTubeCountConstant (n+1) C/Δ)^(n*(n+1)) := by
  obtain ⟨e,_,haxis,he,hei⟩ := exists_general_transverse_frame v (fun i => (hv i).le) hΔ hgram
  let D : ℝ := ((n+1:ℕ):ℝ)^2*((n+1).factorial:ℝ)
  let L := Nat.ceil (D*(C+((n+1:ℕ):ℝ)^2)/Δ+1/2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCd : 0 ≤ C+((n+1:ℕ):ℝ)^2 := by positivity
  have hL : ‖e.symm.toContinuousLinearMap‖*(C+((n+1:ℕ):ℝ)^2)+1/2 ≤ (L:ℝ) := by
    apply le_trans _ (Nat.le_ceil _)
    have hh := mul_le_mul_of_nonneg_right hei hCd
    calc
      _ ≤ (D/Δ)*(C+((n+1:ℕ):ℝ)^2)+1/2 := add_le_add hh le_rfl
      _ = _ := by ring
  have hsize : 2*(L:ℝ)+1 ≤ generalTubeCountConstant (n+1) C/Δ := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ D*(C+((n+1:ℕ):ℝ)^2)/Δ+1/2 by positivity)
    change (L:ℝ) < D*(C+((n+1:ℕ):ℝ)^2)/Δ+1/2+1 at hc
    have hm := mul_lt_mul_of_pos_right hc hΔ
    have hd : (D*(C+((n+1:ℕ):ℝ)^2)/Δ)*Δ = D*(C+((n+1:ℕ):ℝ)^2) := div_mul_cancel₀ _ hΔ.ne'
    apply (le_div_iff₀ hΔ).mpr
    have hconst : generalTubeCountConstant (n+1) C =
        2*D*(C+((n+1:ℕ):ℝ)^2)+4 := by
      unfold generalTubeCountConstant D
      ring
    rw [hconst]
    nlinarith
  obtain ⟨P,hP,hcard⟩ := general_physical_tube_cover hLW hn e he v hv haxis E A R hE hδ L hL hcover
  have hreal : (P.card:ℝ)^n ≤ (∏ i : Fin (n+1), ((A i).card:ℝ))*(2*(L:ℝ)+1)^(n*(n+1)) := by
    exact_mod_cast hcard
  have hb : 0 ≤ 2*(L:ℝ)+1 := by positivity
  have hp : 0 ≤ ∏ i : Fin (n+1), ((A i).card:ℝ) :=
    Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  exact ⟨P,hP,hreal.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hb hsize _) hp)⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NearPinDeletion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Near-parent pins are removed with their original source-cell weights -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X Y ι : Type*} [MeasurableSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem nearPinPairs_measurable (I : Finset ι) (Q : ι → Set X) (c : ι → Y) (r : ℝ)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) : MeasurableSet (nearPinPairs I Q c r) :=
  Finset.measurableSet_biUnion I (fun i hi => (hQ i hi).prod measurableSet_ball)

omit [BorelSpace Y] in
theorem near_pin_pair_mass (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set X) (c : ι → Y) (r : ℝ)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (K : ℝ≥0∞) (hball : ∀ i ∈ I, ν (ball (c i) r) ≤ K) :
    (μ.prod ν) (nearPinPairs I Q c r) ≤ K*μ univ := by
  calc
    _ ≤ ∑ i ∈ I, (μ.prod ν) (Q i ×ˢ ball (c i) r) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ I, μ (Q i)*ν (ball (c i) r) := by simp only [Measure.prod_prod]
    _ ≤ ∑ i ∈ I, K*μ (Q i) := Finset.sum_le_sum (fun i hi => by
      rw [mul_comm K]
      exact mul_le_mul' le_rfl (hball i hi))
    _ = K*μ (⋃ i ∈ I, Q i) := by rw [← Finset.mul_sum,measure_biUnion_finset hdisj hQ]
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (subset_univ _))

omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem distance_of_not_nearPinPairs (I : Finset ι) (Q : ι → Set X) (c : ι → Y) (r : ℝ)
    {x : X} {p : Y} (hp : (x,p) ∉ nearPinPairs I Q c r) {i : ι} (hi : i ∈ I)
    (hx : x ∈ Q i) : r ≤ dist p (c i) := by
  by_contra! hdist
  exact hp (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx,hdist⟩⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PiCoordinateSections
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product-measure bounds from a single coordinate's sections -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

theorem pi_measure_le_of_coordinate_sections (μ : Measure X) [IsFiniteMeasure μ]
    (i : Fin (n+1)) (E : Set (Fin (n+1) → X)) (hE : MeasurableSet E) (C : ℝ≥0∞)
    (hsec : ∀ y : Fin n → X, μ {x | i.insertNth x y ∈ E} ≤ C) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) E ≤ C*(μ univ)^n := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) i
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
  have he : (Measure.pi (fun _ : Fin (n+1) => μ)) E =
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) (e.symm ⁻¹' E) := by
    rw [← hm.map_eq,Measure.map_apply hm.measurable hE]
  rw [he,Measure.prod_apply_symm (hE.preimage e.symm.measurable)]
  calc
    _ ≤ ∫⁻ _y : Fin n → X, C ∂Measure.pi (fun _ => μ) := by
      apply lintegral_mono
      intro y
      exact hsec y
    _ = _ := by simp only [lintegral_const,Measure.pi_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GramSchmidtMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable Gram--Schmidt residuals with exact prefix dependence -/

namespace Falconer
open Set Submodule InnerProductSpace
variable {d : ℕ}

theorem gramSchmidt_measurable (i : Fin d) :
    Measurable (fun v : Fin d → Space d => gramSchmidt ℝ v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have he : (fun v : Fin d → Space d => gramSchmidt ℝ v i) =
        fun v => v i - ∑ j ∈ Finset.Iio i, (ℝ ∙ gramSchmidt ℝ v j).starProjection (v i) :=
      funext (fun v => gramSchmidt_def ℝ v i)
    rw [he]
    simp_rw [starProjection_singleton]
    apply (measurable_pi_apply i).sub
    apply Finset.measurable_sum
    intro j hj
    have hg := ih j (Finset.mem_Iio.mp hj)
    change Measurable (fun v : Fin d → Space d =>
      (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖^2) • gramSchmidt ℝ v j)
    exact ((hg.inner (measurable_pi_apply i)).div (hg.norm.pow_const 2)).smul hg

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GramSchmidtSlab
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small Gram--Schmidt residual lies in a fixed thin slab -/

namespace Falconer
open Set Submodule InnerProductSpace NormedSpace
open scoped BigOperators
variable {d : ℕ}

theorem inner_gramSchmidt_of_prefix_orthogonal (u : Space d) (v : Fin d → Space d)
    (i : Fin d) (h : ∀ j < i, inner ℝ u (v j) = 0) :
    inner ℝ u (gramSchmidt ℝ v i) = inner ℝ u (v i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [gramSchmidt_def]
    simp only [inner_sub_right, inner_sum, starProjection_singleton, inner_smul_right,
      RCLike.ofReal_real_eq_id, id_eq]
    have hz : (∑ j ∈ Finset.Iio i,
        (inner ℝ (gramSchmidt ℝ v j) (v i) / ‖gramSchmidt ℝ v j‖ ^ 2) *
          inner ℝ u (gramSchmidt ℝ v j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ih j (Finset.mem_Iio.mp hj) (fun k hk => h k (hk.trans (Finset.mem_Iio.mp hj))),
        h j (Finset.mem_Iio.mp hj), mul_zero]
    rw [hz, sub_zero]

theorem exists_unit_prefix_normal (v : Fin d → Space d) (i : Fin d) :
    ∃ u : Space d, ‖u‖ = 1 ∧ ∀ j < i, inner ℝ u (v j) = 0 := by
  let b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) (E := Space d)
    (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v
  exact ⟨b i, b.orthonormal.1 i, fun j hj =>
    gramSchmidtOrthonormalBasis_inv_triangular _ v hj⟩

theorem small_residual_fixed_slab (v : Fin d → Space d) (i : Fin d) :
    ∃ u : Space d, ‖u‖ = 1 ∧ ∀ w : Fin d → Space d,
      (∀ j < i, w j = v j) → |inner ℝ u (w i)| ≤ ‖gramSchmidt ℝ w i‖ := by
  obtain ⟨u,hu,horth⟩ := exists_unit_prefix_normal v i
  refine ⟨u,hu,fun w hw => ?_⟩
  have he := inner_gramSchmidt_of_prefix_orthogonal u w i (fun j hj => by rw [hw j hj]; exact horth j hj)
  rw [← he]
  simpa only [hu,one_mul] using abs_real_inner_le_norm u (gramSchmidt ℝ w i)

theorem normalized_direction_slab (u c x : Space d) {R r : ℝ}
    (hx : ‖c-x‖ ≤ R) (hr : 0 ≤ r)
    (h : |inner ℝ u (normalize (c-x))| ≤ r) :
    |inner ℝ u x-inner ℝ u c| ≤ R*r := by
  have he : inner ℝ u (c-x) = ‖c-x‖*inner ℝ u (normalize (c-x)) := by
    nth_rw 1 [← norm_smul_normalize (c-x)]
    rw [inner_smul_right]
  calc
    _ = |inner ℝ u (c-x)| := by rw [inner_sub_right,abs_sub_comm]
    _ = ‖c-x‖*|inner ℝ u (normalize (c-x))| := by rw [he,abs_mul,abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖c-x‖*r := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ ≤ R*r := mul_le_mul_of_nonneg_right hx hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GramSchmidtVolume
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Gram volume is the product of successive residual lengths -/

namespace Falconer
open InnerProductSpace
open scoped BigOperators Matrix
variable {d : ℕ}

theorem gram_volume_eq_abs_basis_det (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = |b.toBasis.det v| := by
  rw [Matrix.gram_eq_conjTranspose_mul b v, Matrix.det_mul, Matrix.det_conjTranspose]
  change Real.sqrt ((b.toBasis.det v)*(b.toBasis.det v)) = _
  rw [← pow_two, Real.sqrt_sq_eq_abs]

theorem gramSchmidt_basis_diagonal_abs (v : Fin d → Space d) (i : Fin d) :
    |inner ℝ (gramSchmidtOrthonormalBasis
      (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v i) (v i)| =
      ‖gramSchmidt ℝ v i‖ := by
  let w := gramSchmidt ℝ v i
  have he : inner ℝ w (v i) = ‖w‖^2 := by
    have hh := inner_gramSchmidt_of_prefix_orthogonal w v i
      (fun j hj => gramSchmidt_inv_triangular ℝ v hj)
    rw [← hh,real_inner_self_eq_norm_sq]
  by_cases hw : w = 0
  · have hz : gramSchmidtNormed ℝ v i = 0 := by
      simp [gramSchmidtNormed, show gramSchmidt ℝ v i = 0 from hw]
    rw [inner_gramSchmidtOrthonormalBasis_eq_zero _ hz]
    change |(0:ℝ)| = ‖w‖
    simp only [hw,abs_zero,norm_zero]
  · have hz : gramSchmidtNormed ℝ v i ≠ 0 := by
      simp only [gramSchmidtNormed]
      exact smul_ne_zero (inv_ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr hw))) hw
    rw [gramSchmidtOrthonormalBasis_apply _ hz]
    change |inner ℝ (‖w‖⁻¹ • w) (v i)| = ‖w‖
    rw [real_inner_smul_left,he,pow_two,← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw),one_mul,abs_of_nonneg (norm_nonneg w)]

theorem gram_volume_eq_residual_product (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  let b := gramSchmidtOrthonormalBasis
    (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v
  rw [gram_volume_eq_abs_basis_det b v]
  change |(gramSchmidtOrthonormalBasis _ v).toBasis.det v| = _
  rw [gramSchmidtOrthonormalBasis_det,Finset.abs_prod]
  exact Finset.prod_congr rfl (fun i _ => gramSchmidt_basis_diagonal_abs v i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialTupleTransversality
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative radial pin transversality from original-law slab bounds -/

namespace Falconer
open Set MeasureTheory InnerProductSpace NormedSpace
open scoped ENNReal BigOperators
variable {n : ℕ}

theorem radialPinTuple_measurable (c : Space (n+1)) : Measurable (radialPinTuple c) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold radialPinTuple NormedSpace.normalize
  fun_prop

theorem radialResidualBad_measurable (c : Space (n+1)) (r : ℝ) (i : Fin (n+1)) :
    MeasurableSet (radialResidualBad c r i) :=
  measurableSet_lt ((gramSchmidt_measurable i).comp (radialPinTuple_measurable c)).norm
    measurable_const

theorem radial_residual_bad_mass (μ : Measure (Space (n+1))) [IsFiniteMeasure μ]
    (c : Space (n+1)) {r R : ℝ} (hr : 0 ≤ r)
    (hR : ∀ᵐ x ∂μ, ‖c-x‖ ≤ R) (K : ℝ≥0∞)
    (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      μ {x | |inner ℝ u x-inner ℝ u c| ≤ R*r} ≤ K) (i : Fin (n+1)) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (radialResidualBad c r i) ≤ K*(μ univ)^n := by
  apply pi_measure_le_of_coordinate_sections μ i _ (radialResidualBad_measurable c r i) K
  intro y
  let v := radialPinTuple c (i.insertNth 0 y)
  obtain ⟨u,hu,hinner⟩ := small_residual_fixed_slab v i
  apply (measure_mono_ae (t := {x | |inner ℝ u x-inner ℝ u c| ≤ R*r}) ?_).trans (hslab u hu)
  filter_upwards [hR] with x hx
  intro hb
  have hprefix : ∀ j < i, radialPinTuple c (i.insertNth x y) j = v j := by
    intro j hj
    dsimp [radialPinTuple,v]
    rw [Fin.insertNth_apply_below hj,Fin.insertNth_apply_below hj]
  have hi := hinner (radialPinTuple c (i.insertNth x y)) hprefix
  have hb' : ‖gramSchmidt ℝ (radialPinTuple c (i.insertNth x y)) i‖ < r := hb
  have hsmall := hi.trans hb'.le
  simp only [radialPinTuple,Fin.insertNth_apply_same] at hsmall
  exact normalized_direction_slab u c x hx hr hsmall

theorem radialTupleBad_measurable (c : Space (n+1)) (r : ℝ) :
    MeasurableSet (radialTupleBad c r) :=
  MeasurableSet.iUnion (radialResidualBad_measurable c r)

theorem radial_bad_tuple_mass (μ : Measure (Space (n+1))) [IsFiniteMeasure μ]
    (c : Space (n+1)) {r R : ℝ} (hr : 0 ≤ r)
    (hR : ∀ᵐ x ∂μ, ‖c-x‖ ≤ R) (K : ℝ≥0∞)
    (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      μ {x | |inner ℝ u x-inner ℝ u c| ≤ R*r} ≤ K) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (radialTupleBad c r) ≤
      (n+1:ℝ≥0∞)*K*(μ univ)^n := by
  calc
    _ ≤ ∑ i : Fin (n+1),
        (Measure.pi (fun _ : Fin (n+1) => μ)) (radialResidualBad c r i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (n+1), K*(μ univ)^n := Finset.sum_le_sum
      (fun i _ => radial_residual_bad_mass μ c hr hR K hslab i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one,mul_assoc]

theorem radial_good_tuple_gram (c : Space (n+1)) {r : ℝ} (hr : 0 < r)
    (w : Fin (n+1) → Space (n+1)) (hw : w ∉ radialTupleBad c r) :
    (∀ i, ‖radialPinTuple c w i‖ = 1) ∧
      r^(n+1) ≤ Real.sqrt (Matrix.gram ℝ (radialPinTuple c w)).det := by
  have hn (i : Fin (n+1)) : r ≤ ‖gramSchmidt ℝ (radialPinTuple c w) i‖ := by
    by_contra! hi
    exact hw (mem_iUnion.mpr ⟨i,hi⟩)
  constructor
  · intro i
    have hne : c-w i ≠ 0 := by
      intro hz
      have hv : radialPinTuple c w i = 0 := by simp [radialPinTuple,hz]
      have hg : gramSchmidt ℝ (radialPinTuple c w) i = 0 := by
        rw [gramSchmidt_def,hv]
        simp
      have hi := hn i
      rw [hg,norm_zero] at hi
      exact (not_le_of_gt hr) hi
    exact norm_normalize hne
  · rw [gram_volume_eq_residual_product]
    calc
      r^(n+1) = ∏ _i : Fin (n+1), r := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hr.le) (fun i _ => hn i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TroublesomePair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable troublesome pairs use the full original conditional source law -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem measurable_normalized_vector {X : Type*} [MeasurableSpace X]
    {f : X → Space d} (hf : Measurable f) :
    Measurable (fun x => NormedSpace.normalize (f x)) :=
  hf.norm.inv.smul hf

theorem measurable_perpendicular_vectors {X : Type*} [MeasurableSpace X]
    {v z : X → Space d} (hv : Measurable v) (hz : Measurable z) :
    Measurable (fun x => perpendicularPart (v x) (z x)) := by
  have hi : Measurable (fun x => inner ℝ (v x) (z x)) := hv.inner hz
  exact hz.sub (hi.smul hv)

theorem radialTubeMass_measurable (μ : Measure (Space d)) [SFinite μ] (W : ℝ) :
    Measurable (radialTubeMass μ W) := by
  let A : Set ((Space d × Space d) × Space d) :=
    {q | ‖perpendicularPart (normalize (q.1.1-q.1.2)) (q.2-q.1.2)‖ ≤ W}
  have hA : MeasurableSet A := by
    have hv : Measurable (fun q : (Space d × Space d) × Space d =>
        NormedSpace.normalize (q.1.1-q.1.2)) :=
      measurable_normalized_vector (measurable_fst.fst.sub measurable_fst.snd)
    have hy : Measurable (fun q : (Space d × Space d) × Space d => q.2-q.1.2) :=
      measurable_snd.sub measurable_fst.snd
    exact measurableSet_le (measurable_perpendicular_vectors hv hy).norm measurable_const
  exact measurable_measure_prodMk_left hA

theorem troublesomePair_measurable (μ : Measure (Space d)) [SFinite μ]
    (c : Space d) (r D B W : ℝ) (F : ℝ≥0∞) :
    MeasurableSet (troublesomePair μ c r D B W F) := by
  have h₁ : MeasurableSet {p : Space d × Space d | r ≤ ‖c-p.2‖} :=
    measurableSet_le measurable_const (by fun_prop)
  have h₂ : MeasurableSet {p : Space d × Space d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have h₃ : MeasurableSet {p : Space d × Space d | ‖p.1-c‖ ≤ D} :=
    measurableSet_le (by fun_prop) measurable_const
  have h₄ : MeasurableSet {p : Space d × Space d | ‖p.1‖ ≤ B} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h₁.inter (h₂.inter (h₃.inter (h₄.inter
    (measurableSet_lt measurable_const (radialTubeMass_measurable μ W)))))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GridBallOverlap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform overlap of fixed-width lattice cells -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem grid_ball_overlap (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ}
    (hδ : 0 < δ) (L : ℕ) (hL : C+1/2 ≤ (L:ℝ)) (x : Space (n+1)) :
    (S.filter (fun z => ‖x-euclideanIntegerGrid δ z‖ ≤ C*δ)).card ≤ (2*L+1)^(n+1) := by
  apply integer_box_card _ (fun j => x j/δ) C L hL
  intro z hz j
  have hb := (PiLp.norm_apply_le (x-euclideanIntegerGrid δ z) j).trans (Finset.mem_filter.mp hz).2
  change |x j-δ*(z j:ℝ)| ≤ C*δ at hb
  have hd : |(x j-δ*(z j:ℝ))/δ| ≤ C := by
    rw [abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr hb
  have he : (x j-δ*(z j:ℝ))/δ = x j/δ-(z j:ℝ) := by field_simp
  rw [he,abs_sub_comm] at hd
  exact hd

theorem grid_ball_heavy_card (μ : Measure (Space (n+1)))
    (f : Space (n+1) → Space (n+1)) (hf : Measurable f)
    (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : C+1/2 ≤ (L:ℝ)) (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ S, F ≤ μ {x | ‖f x-euclideanIntegerGrid δ z‖ ≤ C*δ}) :
    (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  apply heavy_family_card_bound μ S
    (fun z => {x | ‖f x-euclideanIntegerGrid δ z‖ ≤ C*δ})
    (fun z _ => measurableSet_le (by fun_prop) measurable_const)
    ((2*L+1)^(n+1)) (fun x => grid_ball_overlap S hδ L hL (f x)) F hheavy

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyProjectedCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite cover of sources whose full projected local mass is heavy -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem heavy_projected_grid_cover (μ : Measure (Space (n+1)))
    (f : Space (n+1) → Space (n+1)) (hf : Measurable f)
    (T : Set (Space (n+1))) {R δ C : ℝ} (hδ : 0 < δ)
    (hT : ∀ z ∈ T, ‖f z‖ ≤ R) (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y | ‖f y-f z‖ ≤ C*δ})
    (L : ℕ) (hL : C+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ P : Finset (Space (n+1)),
      (∀ z ∈ T, ∃ p ∈ P, ‖f z-p‖ ≤ ((n+1:ℕ):ℝ)*δ) ∧
      (P.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_ge (R/δ+1)
  let I := integerGridBox n N
  let U (q : Fin (n+1) → ℤ) : Set (Space (n+1)) :=
    {y | ‖f y-euclideanIntegerGrid δ q‖ ≤ (C+((n+1:ℕ):ℝ))*δ}
  let H := I.filter (fun q => F ≤ μ (U q))
  let P := H.image (euclideanIntegerGrid δ)
  have hm := grid_ball_heavy_card μ f hf H hδ L hL F
    (fun q hq => (Finset.mem_filter.mp hq).2)
  refine ⟨P,?_,?_⟩
  · intro z hz
    let q := euclideanRound δ (f z)
    have hqI : q ∈ I := euclideanRound_mem_box hδ N hN (f z) (hT z hz)
    have hclose : ‖f z-euclideanIntegerGrid δ q‖ ≤ ((n+1:ℕ):ℝ)*δ := by
      have he := euclideanRound_distance hδ (f z)
      rw [dist_eq_norm] at he
      have hd : 0 ≤ ((n+1:ℕ):ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
      exact he.trans (by linarith)
    have hsub : {y | ‖f y-f z‖ ≤ C*δ} ⊆ U q := by
      intro y hy
      change ‖f y-euclideanIntegerGrid δ q‖ ≤ _
      calc
        _ ≤ ‖f y-f z‖+‖f z-euclideanIntegerGrid δ q‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C*δ+((n+1:ℕ):ℝ)*δ := add_le_add hy hclose
        _ = _ := by ring
    have hqH : q ∈ H := Finset.mem_filter.mpr ⟨hqI,(hheavy z hz).trans (measure_mono hsub)⟩
    exact ⟨_,Finset.mem_image.mpr ⟨q,hqH,rfl⟩,hclose⟩
  · have hc : (P.card:ℝ≥0∞) ≤ (H.card:ℝ≥0∞) := by exact_mod_cast Finset.card_image_le
    exact (mul_le_mul' hc le_rfl).trans hm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FrozenHeavyCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual parallel tube covers of troublesome original source fibers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem perpendicularPart_idempotent (v z : Space (n+1)) (hv : ‖v‖ = 1) :
    perpendicularPart v (perpendicularPart v z) = perpendicularPart v z := by
  simp [perpendicularPart,inner_sub_right,inner_smul_right,hv]

theorem frozen_heavy_tube_cover (μ : Measure (Space (n+1))) (x c : Space (n+1))
    {r D δ C B : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y |
      ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ C*δ})
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ P : Finset (Space (n+1)),
      (∀ z ∈ T, ∃ p ∈ P,
        ‖perpendicularPart (normalize (c-x)) (z-p)‖ ≤ ((n+1:ℕ):ℝ)*δ) ∧
      (P.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  let v := normalize (c-x)
  have hv : ‖v‖ = 1 := norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))
  let f : Space (n+1) → Space (n+1) := perpendicularPart v
  have hf : Measurable f := by unfold f perpendicularPart; fun_prop
  have hbd : ∀ z ∈ T, ‖f z‖ ≤ B := fun z hz =>
    (norm_perpendicularPart_le hv z).trans (hT z hz).2.2
  have hmass : ∀ z ∈ T, F ≤ μ {y | ‖f y-f z‖ ≤ (C+1)*δ} := by
    intro z hz
    apply (hheavy z hz).trans
    apply measure_mono_ae
    filter_upwards [hsource] with y hy
    intro ht
    have hh := frozen_radial_tube_error x c z y hr hcx (hT z hz).1 (hT z hz).2.1 hy ht
    change ‖perpendicularPart v y-perpendicularPart v z‖ ≤ _
    rw [← perpendicularPart_sub]
    exact hh.trans (by nlinarith)
  obtain ⟨P,hP,hcard⟩ := heavy_projected_grid_cover μ f hf T hδ hbd F hmass L hL
  refine ⟨P,?_,hcard⟩
  intro z hz
  obtain ⟨p,hp,hclose⟩ := hP z hz
  refine ⟨p,hp,?_⟩
  have he : perpendicularPart v (z-p) = perpendicularPart v (f z-p) := by
    rw [perpendicularPart_sub,perpendicularPart_sub]
    dsimp [f]
    rw [perpendicularPart_idempotent v z hv]
  rw [he]
  exact (norm_perpendicularPart_le hv _).trans hclose

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TroublesomeCovers
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Covers of the measurable troublesome-pair relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem troublesome_pair_covers (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ]
    (c : Space (n+1)) {r D δ C B F : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hF : 0 < F)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ A : Space (n+1) → Finset (Space (n+1)),
      (∀ z p, (z,p) ∈ troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F) →
        ∃ a ∈ A p, ‖perpendicularPart (NormedSpace.normalize (c-p)) (z-a)‖ ≤
          ((n+1:ℕ):ℝ)*δ) ∧
      ∀ p, ((A p).card:ℝ) ≤ ((2*L+1)^(n+1):ℕ)/F := by
  classical
  have hall (p : Space (n+1)) : ∃ P : Finset (Space (n+1)),
      (∀ z, (z,p) ∈ troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F) →
        ∃ a ∈ P, ‖perpendicularPart (NormedSpace.normalize (c-p)) (z-a)‖ ≤
          ((n+1:ℕ):ℝ)*δ) ∧ (P.card:ℝ) ≤ ((2*L+1)^(n+1):ℕ)/F := by
    by_cases hp : ∃ z, (z,p) ∈ troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F)
    · obtain ⟨z,hz⟩ := hp
      obtain ⟨P,hP,hcard⟩ := frozen_heavy_tube_cover μ p c hr hz.1 hδ hfreeze hsource
        {z | (z,p) ∈ troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F)}
        (fun z hz => ⟨hz.2.1,hz.2.2.1,hz.2.2.2.1⟩) (ENNReal.ofReal F)
        (fun z hz => hz.2.2.2.2.le) L hL
      refine ⟨P,hP,?_⟩
      apply (le_div_iff₀ hF).mpr
      have hfinite : ((((2*L+1)^(n+1):ℕ):ℝ≥0∞)*μ univ) ≠ ∞ := by
        rw [measure_univ,mul_one]
        exact ENNReal.natCast_ne_top _
      have hc := ENNReal.toReal_mono hfinite hcard
      simpa only [measure_univ,mul_one,ENNReal.toReal_mul,ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal hF.le] using hc
    · refine ⟨∅,fun z hz => False.elim (hp ⟨z,hz⟩),?_⟩
      simp only [Finset.card_empty,Nat.cast_zero]
      exact div_nonneg (Nat.cast_nonneg _) hF.le
  choose A hA using hall
  exact ⟨A,fun z p hz => (hA p).1 z hz,fun p => (hA p).2⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CommonTupleIncidence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common incidence of an arbitrary finite tuple of original pins -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem commonTupleRelation_measurable (k : ℕ) (E : Set (X × W)) (hE : MeasurableSet E) :
    MeasurableSet (commonTupleRelation k E) := by
  simp only [commonTupleRelation, ofPred_forall]
  exact MeasurableSet.iInter (fun i => hE.preimage (by fun_prop))

omit [MeasurableSpace X] in
theorem commonTupleRelation_fiber (k : ℕ) (ν : Measure W) [SigmaFinite ν]
    (E : Set (X × W)) (x : X) :
    (Measure.pi (fun _ : Fin k => ν)) (Prod.mk x ⁻¹' commonTupleRelation k E) =
      (ν (Prod.mk x ⁻¹' E))^k := by
  have he : Prod.mk x ⁻¹' commonTupleRelation k E = Set.pi univ (fun _ => Prod.mk x ⁻¹' E) := by
    ext w
    simp only [commonTupleRelation,mem_preimage,mem_ofPred_eq,mem_pi,mem_univ,true_implies]
  rw [he,Measure.pi_pi]
  simp

theorem common_tuple_incidence_moment (μ : Measure X) (ν : Measure W)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {k : ℕ} (hk : 2 ≤ k)
    (E : Set (X × W)) (hE : MeasurableSet E) :
    ((μ.prod ν) E)^k ≤
      (μ.prod (Measure.pi (fun _ : Fin k => ν))) (commonTupleRelation k E)*(μ univ)^(k-1) := by
  have hf : Measurable (fun x : X => ν (Prod.mk x ⁻¹' E)) := measurable_measure_prodMk_left hE
  have hh := incidence_moment μ (fun x : X => ν (Prod.mk x ⁻¹' E)) hf.aemeasurable hk
  rw [Measure.prod_apply hE,Measure.prod_apply (commonTupleRelation_measurable k E hE)]
  simpa only [commonTupleRelation_fiber] using hh

theorem exists_good_common_tuple (μ : Measure X) (ν : Measure W)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {k : ℕ} (hk : 2 ≤ k)
    (E : Set (X × W)) (hE : MeasurableSet E)
    (B : Set (Fin k → W)) (hB : MeasurableSet B) (t : ℝ≥0∞)
    (hgap : (μ univ)^(k-1)*(t*(ν univ)^k + μ univ*(Measure.pi (fun _ : Fin k => ν)) B) <
      ((μ.prod ν) E)^k) :
    ∃ w ∉ B, t < μ {x | (x,w) ∈ commonTupleRelation k E} := by
  classical
  let ξ := Measure.pi (fun _ : Fin k => ν)
  let F := commonTupleRelation k E ∩ (univ ×ˢ Bᶜ)
  have hF : MeasurableSet F := (commonTupleRelation_measurable k E hE).inter
    (MeasurableSet.univ.prod hB.compl)
  have hξ : ξ univ = (ν univ)^k := by
    have he : (univ : Set (Fin k → W)) = Set.pi univ (fun _ => (univ : Set W)) := by ext; simp
    rw [he,Measure.pi_pi]
    simp
  by_contra! hn
  have hfiber (w : Fin k → W) : μ ((fun x => (x,w)) ⁻¹' F) ≤ t := by
    by_cases hw : w ∈ B
    · have he : (fun x => (x,w)) ⁻¹' F = ∅ := by
        ext x
        simp only [F,mem_preimage,mem_inter_iff,mem_prod,mem_univ,mem_compl_iff,hw,
          not_true_eq_false,and_false,mem_empty_iff_false]
      simp only [he,measure_empty,zero_le]
    · exact (measure_mono (fun _ hx => hx.1)).trans (hn w hw)
  have hgood : (μ.prod ξ) F ≤ t*(ν univ)^k := by
    rw [Measure.prod_apply_symm hF]
    calc
      _ ≤ ∫⁻ _w, t ∂ξ := lintegral_mono hfiber
      _ = _ := by rw [lintegral_const,hξ,mul_comm]
  have hsub : commonTupleRelation k E ⊆ F ∪ (univ ×ˢ B) := by
    intro p hp
    by_cases hb : p.2 ∈ B
    · exact Or.inr ⟨mem_univ _,hb⟩
    · exact Or.inl ⟨hp,mem_univ _,hb⟩
  have hu : (μ.prod ξ) (commonTupleRelation k E) ≤ t*(ν univ)^k+μ univ*ξ B := by
    apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
    exact add_le_add hgood (by rw [Measure.prod_prod])
  have hm := common_tuple_incidence_moment μ ν hk E hE
  have hle := hm.trans (mul_le_mul' hu le_rfl)
  rw [mul_comm] at hle
  exact (not_lt_of_ge hle) hgap

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_GeneralTubeMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A mass bound for an actual intersection of transverse tube families -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
variable {n : ℕ}

theorem general_tube_mass_power (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (μ : Measure (Space (n+1)))
    (v : Fin (n+1) → Space (n+1)) (hv : ∀ i, ‖v i‖ = 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hgram : Δ ≤ Real.sqrt (Matrix.gram ℝ v).det)
    (E : Set (Space (n+1))) (A : Fin (n+1) → Finset (Space (n+1))) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C H : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : ∀ p : Space (n+1), μ (ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) ≤ ENNReal.ofReal H)
    (hcover : ∀ i : Fin (n+1), ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    (μ E).toReal^n ≤ (∏ i : Fin (n+1), ((A i).card:ℝ))*
      (generalTubeCountConstant (n+1) C/Δ)^(n*(n+1))*H^n := by
  obtain ⟨P,hP,hcard⟩ := general_transverse_tube_cover hLW hn v hv hΔ hΔ1 hgram E A R hE hδ hC hcover
  have hm : μ E ≤ ENNReal.ofReal ((P.card:ℝ)*H) := by
    calc
      _ ≤ μ (⋃ p ∈ P, ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) := by
        apply measure_mono
        intro x hx
        obtain ⟨p,hp,hd⟩ := hP x hx
        exact mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,by change dist x p < _; nlinarith⟩⟩
      _ ≤ ∑ p ∈ P, μ (ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) := measure_biUnion_finset_le P _
      _ ≤ ∑ _p ∈ P, ENNReal.ofReal H := Finset.sum_le_sum (fun p _ => hball p)
      _ = (P.card:ℝ≥0∞)*ENNReal.ofReal H := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ = _ := by rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hH)] at hreal
  calc
    _ ≤ ((P.card:ℝ)*H)^n := pow_le_pow_left₀ ENNReal.toReal_nonneg hreal n
    _ = (P.card:ℝ)^n*H^n := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hH n)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RadialIncidenceBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small common transverse tube intersections force small original incidence -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
variable {n : ℕ}

theorem radial_tube_incidence_bound (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : Space (n+1)) {r R : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hR : ∀ᵐ x ∂ν, ‖c-x‖ ≤ R) (K : ℝ≥0∞)
    (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      ν {x | |inner ℝ u x-inner ℝ u c| ≤ R*r} ≤ K)
    (E : Set (Space (n+1) × Space (n+1))) (hE : MeasurableSet E)
    (A : Space (n+1) → Finset (Space (n+1))) (B : ℝ)
    (hbounded : ∀ x w, (x,w) ∈ E → ‖x‖ ≤ B)
    {δ C H M t : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hball : ∀ p : Space (n+1), μ (ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) ≤ ENNReal.ofReal H)
    (hcover : ∀ x w, (x,w) ∈ E → ∃ a ∈ A w,
      ‖perpendicularPart (NormedSpace.normalize (c-w)) (x-a)‖ ≤ C*δ)
    (hcard : ∀ w, ((A w).card:ℝ) ≤ M)
    (hbudget : M^(n+1)*(generalTubeCountConstant (n+1) C/r^(n+1))^(n*(n+1))*H^n ≤ t^n) :
    ((μ.prod ν) E)^(n+1) ≤ ENNReal.ofReal t+(n+1:ℝ≥0∞)*K := by
  by_contra! hlarge
  have hbad := radial_bad_tuple_mass ν c hr.le hR K hslab
  simp only [measure_univ,one_pow,mul_one] at hbad
  have hgap : (μ univ)^((n+1)-1)*
      (ENNReal.ofReal t*(ν univ)^(n+1)+μ univ*
        (Measure.pi (fun _ : Fin (n+1) => ν)) (radialTupleBad c r)) < ((μ.prod ν) E)^(n+1) := by
    simpa only [measure_univ,one_pow,one_mul,mul_one] using
      lt_of_le_of_lt (add_le_add le_rfl hbad) hlarge
  obtain ⟨w,hw,hmass⟩ := exists_good_common_tuple μ ν (by omega) E hE
    (radialTupleBad c r) (radialTupleBad_measurable c r) (ENNReal.ofReal t) hgap
  obtain ⟨hunit,hgram⟩ := radial_good_tuple_gram c hr w hw
  let S : Set (Space (n+1)) := {x | (x,w) ∈ commonTupleRelation (n+1) E}
  have hS (x) (hx : x ∈ S) (i : Fin (n+1)) : (x,w i) ∈ E := hx i
  have hbd : ∀ x ∈ S, ‖x‖ ≤ B := fun x hx => hbounded x (w 0) (hS x hx 0)
  have hm := general_tube_mass_power hLW hn μ (radialPinTuple c w) hunit
    (pow_pos hr _) (pow_le_one₀ hr.le hr1) hgram S (fun i => A (w i)) B hbd
    hδ hC hH hball (fun i x hx => hcover x (w i) (hS x hx i))
  have hc : (∏ i : Fin (n+1), ((A (w i)).card:ℝ)) ≤ M^(n+1) := by
    calc
      _ ≤ ∏ _i : Fin (n+1), M := Finset.prod_le_prod
        (fun i _ => Nat.cast_nonneg _) (fun i _ => hcard (w i))
      _ = _ := by simp
  have hup : (μ S).toReal^n ≤ t^n := by
    have hcount : 0 ≤ generalTubeCountConstant (n+1) C := by
      unfold generalTubeCountConstant
      positivity
    have hp : 0 ≤ (generalTubeCountConstant (n+1) C/r^(n+1))^(n*(n+1)) :=
      pow_nonneg (div_nonneg hcount (pow_nonneg hr.le _)) _
    apply (hm.trans ?_).trans hbudget
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc hp) (pow_nonneg hH _)
  have ht' : t < (μ S).toReal := by
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (measure_ne_top μ S)).mpr hmass
    rwa [ENNReal.toReal_ofReal ht] at hh
  exact (not_lt_of_ge hup) (pow_lt_pow_left₀ ht' ht (by omega))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_TroublesomeIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-law incidence bound for the actual troublesome-pair relation -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem troublesome_pair_incidence_bound (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : Space (n+1)) {r D δ C B F a R H t : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hF : 0 < F) (ha : 0 < a) (ha1 : a ≤ 1)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (hR : ∀ᵐ p ∂ν, ‖c-p‖ ≤ R) (K : ℝ≥0∞)
    (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      ν {p | |inner ℝ u p-inner ℝ u c| ≤ R*a} ≤ K)
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) (hH : 0 ≤ H) (ht : 0 ≤ t)
    (hball : ∀ p : Space (n+1), μ (ball p ((((n+1:ℕ):ℝ)^2+1)*δ)) ≤ ENNReal.ofReal H)
    (hbudget : (((2*L+1)^(n+1):ℕ)/F)^(n+1)*
      (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)/a^(n+1))^(n*(n+1))*H^n ≤ t^n) :
    ((μ.prod ν) (troublesomePair μ c r D B (C*δ) (ENNReal.ofReal F)))^(n+1) ≤
      ENNReal.ofReal t+(n+1:ℝ≥0∞)*K := by
  obtain ⟨A,hcover,hcard⟩ := troublesome_pair_covers μ c hr hδ hF hfreeze hsource L hL
  exact radial_tube_incidence_bound hLW hn μ ν c ha ha1 hR K hslab _
    (troublesomePair_measurable μ c r D B (C*δ) (ENNReal.ofReal F)) A B
    (fun z p hz => hz.2.2.2.1) hδ (Nat.cast_nonneg _) hH ht hball hcover hcard hbudget

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RegularClassRadialIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak radial incidence for the actual conditional regularized class laws -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem regular_class_radial_incidence (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (Q : DyadicCube (n+1)) (hQ : 0 < Q.side)
    (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) {lam : ℝ}
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath (n+1)} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {a b : ℕ} (haN : a ≤ N) (hbN : b ≤ N)
    {p : CellPath (n+1)} (hp : p.length = a)
    (hpos : 0 < sourceClass Q μ N B p₀ (Q.descendant p).carrier)
    {r C Bs F α R t : ℝ} (hr : 0 < r) (hF : 0 < F) (hα : 0 < α) (hα1 : α ≤ 1)
    (hfreeze : 8*(Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a))^2/r ≤ Q.side/(2:ℝ)^b)
    (hR : ∀ᵐ x ∂ν, ‖(Q.descendant p).center-x‖ ≤ R)
    (K : ℝ≥0∞) (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      ν {x | |inner ℝ u x-inner ℝ u (Q.descendant p).center| ≤ R*α} ≤ K)
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) (ht : 0 ≤ t)
    (hbudget : (((2*L+1)^(n+1):ℕ)/F)^(n+1)*
      (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)/α^(n+1))^(n*(n+1))*
        (radialClassBallBound Q μ N B p₀ a b lam)^n ≤ t^n) :
    (((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier).prod ν)
      (troublesomePair (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier)
        (Q.descendant p).center r (Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a)) Bs
          (C*(Q.side/(2:ℝ)^b)) (ENNReal.ofReal F)))^(n+1) ≤
      ENNReal.ofReal t+(n+1:ℝ≥0∞)*K := by
  let ρ := ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier
  have : IsProbabilityMeasure ρ := sourceClass_conditional_probability Q hQ μ N B hp₀ p hpos
  have hδ : 0 < Q.side/(2:ℝ)^b := by positivity
  have hsrc : ∀ᵐ y ∂ρ, ‖y-(Q.descendant p).center‖ ≤
      Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a) := by
    apply ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant p).measurable
    intro y hy
    have hd := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hy
      ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
    simpa only [dist_eq_norm,Q.descendant_side,hp] using hd
  have hH : 0 ≤ radialClassBallBound Q μ N B p₀ a b lam := by
    unfold radialClassBallBound
    positivity
  apply troublesome_pair_incidence_bound hLW hn ρ ν (Q.descendant p).center
    hr hδ hF hα hα1 hfreeze hsrc hR K hslab L hL hH ht _ hbudget
  intro x
  have hb := sourceClass_conditional_ball_upper Q hQ μ hN hB hwidth hlarge hp₀
    haN hbN hp hpos x (C := ((n+1:ℕ):ℝ)^2+1) (by positivity)
  have he : 2*(((n+1:ℕ):ℝ)^2+1)+4*Real.sqrt (n+1:ℕ) =
      2*((n+1:ℕ):ℝ)^2+2+4*Real.sqrt (n+1:ℕ) := by ring
  rw [he] at hb
  change (ρ (ball x ((((n+1:ℕ):ℝ)^2+1)*(Q.side/(2:ℝ)^b)))).toReal ≤
    radialClassBallBound Q μ N B p₀ a b lam at hb
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _)]
  exact ENNReal.ofReal_le_ofReal hb

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialLocalBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Profile cancellation in the weak radial tube-counting budget -/

namespace Falconer
open Real Filter
open scoped Topology

private theorem real_rpow_nat_power {x : ℝ} (hx : 0 < x) (a : ℝ) (j : ℕ) :
    (x^a)^j = x^(a*(j:ℝ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hx.le]

theorem weak_radial_profile_cancel {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (n : ℕ) (K e τ : ℝ) :
    (K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*(δ^(-τ)/D)^n =
      K^(n+1)*δ^((n+1)*e-n*τ) := by
  have hd : (n:ℝ)+1 ≠ 0 := by positivity
  have hroot : (D^((n:ℝ)/(n+1)))^(n+1) = D^n := by
    rw [real_rpow_nat_power hD, Nat.cast_add, Nat.cast_one]
    rw [div_mul_cancel₀ _ hd,Real.rpow_natCast]
  rw [div_div_eq_mul_div,div_pow,mul_pow,div_pow,hroot,
    real_rpow_nat_power hδ,real_rpow_nat_power hδ]
  calc
    _ = K^(n+1)*(δ^(-τ*(n:ℝ))/δ^(-e*((n+1:ℕ):ℝ))) := by
      field_simp [pow_ne_zero n hD.ne']
    _ = _ := by
      rw [← Real.rpow_sub hδ]
      congr 2
      push_cast
      ring

theorem weak_radial_local_count_power {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (n : ℕ) (K G e τ η : ℝ) :
    (K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*
      (G/(δ^η)^(n+1))^(n*(n+1))*(δ^(-τ)/D)^n =
    (K^(n+1)*G^(n*(n+1)))*
      δ^((n+1)*e-n*τ-η*n*(n+1)^2) := by
  calc
    _ = ((K/(δ^(-e)/D^((n:ℝ)/(n+1))))^(n+1)*(δ^(-τ)/D)^n)*
        (G/(δ^η)^(n+1))^(n*(n+1)) := by ring
    _ = (K^(n+1)*δ^((n+1)*e-n*τ))*
        (G^(n*(n+1))/δ^(η*(((n+1)*(n*(n+1)):ℕ):ℝ))) := by
      rw [weak_radial_profile_cancel hδ hD,div_pow,← pow_mul,real_rpow_nat_power hδ]
    _ = (K^(n+1)*G^(n*(n+1)))*
        (δ^((n+1)*e-n*τ)/δ^(η*(((n+1)*(n*(n+1)):ℕ):ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_sub hδ]
      congr 2
      push_cast
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RegularClassRadialBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform profile cancellation in the actual class ball bound -/

namespace Falconer.Regularization
open MeasureTheory
variable {n : ℕ}

theorem radialClassBallBound_le (Q : DyadicCube (n+1)) (μ : Measure (Space (n+1)))
    (N B : ℕ) (p : CellPath (n+1)) (a b : ℕ) (lam τ : ℝ)
    (hC : ((2*Nat.ceil (2*((n+1:ℕ):ℝ)^2+2+4*Real.sqrt (n+1:ℕ))+1)^(n+1):ℕ) ≤
      ((2:ℝ)^N)^(τ-2*(((n+1:ℕ):ℝ)+1)*lam)) :
    radialClassBallBound Q μ N B p a b lam ≤
      ((2:ℝ)^N)^τ / ((2:ℝ)^N)^(sourceProfile Q μ N B p b-sourceProfile Q μ N B p a) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  unfold radialClassBallBound
  calc
    _ ≤ ((2:ℝ)^N)^(τ-2*(((n+1:ℕ):ℝ)+1)*lam) *
        ((2:ℝ)^N)^(sourceProfile Q μ N B p a-sourceProfile Q μ N B p b+
          2*(((n+1:ℕ):ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hR.le _)
    _ = _ := by
      rw [← Real.rpow_add hR,← Real.rpow_sub hR]
      congr 1
      ring

theorem eventually_radialClassBallBound_le (n : ℕ) {lam τ : ℝ}
    (hτ : 2*(((n+1:ℕ):ℝ)+1)*lam < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube (n+1)) (μ : Measure (Space (n+1)))
      (B : ℕ) (p : CellPath (n+1)) (a b : ℕ),
      radialClassBallBound Q μ N B p a b lam ≤
        ((2:ℝ)^N)^τ / ((2:ℝ)^N)^(sourceProfile Q μ N B p b-sourceProfile Q μ N B p a) := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (sub_pos.mpr hτ)
    (((2*Nat.ceil (2*((n+1:ℕ):ℝ)^2+2+4*Real.sqrt (n+1:ℕ))+1)^(n+1):ℕ):ℝ)
  exact ⟨N₀,fun N hN Q μ B p a b => radialClassBallBound_le Q μ N B p a b lam τ (hN₀ N hN)⟩

end Falconer.Regularization

namespace Falconer

theorem weak_radial_reciprocal_count {R D : ℝ} (hR : 0 < R) (hD : 0 < D)
    (n : ℕ) (K G e τ η : ℝ) :
    (K/(R^e/D^((n:ℝ)/(n+1))))^(n+1)*
      (G/(R^(-η))^(n+1))^(n*(n+1))*(R^τ/D)^n =
    (K^(n+1)*G^(n*(n+1)))*R^(-((n+1)*e-n*τ-η*n*(n+1)^2)) := by
  have hh := weak_radial_local_count_power (inv_pos.mpr hR) hD n K G e τ η
  simp only [Real.inv_rpow hR.le,← Real.rpow_neg hR.le,neg_neg] at hh
  exact hh

theorem eventually_weak_radial_reciprocal_budget (n : ℕ) (K G e τ η u : ℝ)
    (hgap : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D > 0,
      (K/(((2:ℝ)^N)^e/D^((n:ℝ)/(n+1))))^(n+1)*
        (G/(((2:ℝ)^N)^(-η))^(n+1))^(n*(n+1))*(((2:ℝ)^N)^τ/D)^n ≤
          (((2:ℝ)^N)^(-u))^n := by
  let A : ℝ := K^(n+1)*G^(n*(n+1))
  let gap : ℝ := (n+1)*e-n*τ-η*n*(n+1)^2-n*u
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hgap A
  refine ⟨N₀,fun N hN D hD => ?_⟩
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [weak_radial_reciprocal_count hR hD]
  calc
    _ ≤ ((2:ℝ)^N)^gap*((2:ℝ)^N)^(-((n+1)*e-n*τ-η*n*(n+1)^2)) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (Real.rpow_nonneg hR.le _)
    _ = _ := by
      rw [← Real.rpow_add hR,← Real.rpow_natCast (((2:ℝ)^N)^(-u)) n,
        ← Real.rpow_mul hR.le]
      congr 1
      dsimp [gap]
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible fixed losses for the local weak radial argument -/

namespace Falconer

theorem weak_radial_bounded_exponents {n : ℕ} (hn : 1 ≤ n) {e ζ : ℝ}
    (he : 0 < e) (hζ : 0 < ζ) :
    ∃ η τ u ε : ℝ, 0 < η ∧ η ≤ 1/2 ∧ 0 < τ ∧ 0 < u ∧ 0 < ε ∧
      0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u ∧ 0 < η*ζ-ε-u := by
  have hN : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : (0:ℝ) < (n:ℝ)+1 := by positivity
  let η₀ : ℝ := e/(8*(n:ℝ)*((n:ℝ)+1))
  let η : ℝ := min η₀ (1/2)
  let τ : ℝ := ((n:ℝ)+1)*e/(8*(n:ℝ))
  let u : ℝ := min τ (η*ζ/8)
  let ε : ℝ := η*ζ/8
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hu : 0 < u := lt_min hτ hε
  refine ⟨η,τ,u,ε,hη,min_le_right _ _,hτ,hu,hε,?_,?_⟩
  · have ht : (n:ℝ)*τ = ((n:ℝ)+1)*e/8 := by dsimp [τ]; field_simp
    have ha : η₀*(n:ℝ)*((n:ℝ)+1)^2 = ((n:ℝ)+1)*e/8 := by
      dsimp [η₀]
      field_simp
    have hηle : η*(n:ℝ)*((n:ℝ)+1)^2 ≤ η₀*(n:ℝ)*((n:ℝ)+1)^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hN.le) (sq_nonneg _)
    have hule : (n:ℝ)*u ≤ (n:ℝ)*τ := mul_le_mul_of_nonneg_left (min_le_left _ _) hN.le
    rw [ht] at hule
    rw [ha] at hηle
    rw [ht]
    nlinarith [mul_pos hD he]
  · have hule : u ≤ ε := min_le_right _ _
    dsimp [ε] at hule ⊢
    nlinarith [mul_pos hη hζ]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialDeletionBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning the two actual local incidence losses into a pair deletion bound -/

namespace Falconer
open scoped ENNReal

theorem weak_radial_two_costs {A B u v c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : c < u) (hv : c < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A*((2:ℝ)^N)^(-u)+B*((2:ℝ)^N)^(-v) ≤ ((2:ℝ)^N)^(-c) := by
  let m := min (u-c) (v-c)
  have hm : 0 < m := lt_min (sub_pos.mpr hu) (sub_pos.mpr hv)
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hm (A+B)
  refine ⟨N₀,fun N hN => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hu' : -u ≤ -c-m := by have := min_le_left (u-c) (v-c); dsimp [m]; linarith
  have hv' : -v ≤ -c-m := by have := min_le_right (u-c) (v-c); dsimp [m]; linarith
  calc
    _ ≤ A*R^(-c-m)+B*R^(-c-m) := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hu') hA)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hv') hB)
    _ = (A+B)*R^(-c-m) := by ring
    _ ≤ R^m*R^(-c-m) := mul_le_mul_of_nonneg_right (hN₀ N hN) (Real.rpow_nonneg hRp.le _)
    _ = R^(-c) := by rw [← Real.rpow_add hRp]; congr 1; ring

theorem weak_radial_local_deletion_budget (d : ℕ) (hd : 0 < d)
    {u v c C : ℝ} (hC : 0 ≤ C) (hu : c*(d:ℝ) < u) (hv : c*(d:ℝ) < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ I : ℝ≥0∞,
      I^d ≤ ENNReal.ofReal (((2:ℝ)^N)^(-u))+
        (d:ℝ≥0∞)*ENNReal.ofReal (C*((2:ℝ)^N)^(-v)) →
      I ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨N₀,hN₀⟩ := weak_radial_two_costs (A := 1) (B := (d:ℝ)*C)
    (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hC) hu hv
  refine ⟨N₀,fun N hN I hI => ?_⟩
  apply (ENNReal.pow_le_pow_left_iff hd.ne').mp
  have hR : 0 < (2:ℝ)^N := by positivity
  have he : (((2:ℝ)^N)^(-c))^d = ((2:ℝ)^N)^(-(c*(d:ℝ))) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hR.le _),he]
  apply hI.trans
  have he' : (d:ℝ≥0∞)*ENNReal.ofReal (C*((2:ℝ)^N)^(-v)) =
      ENNReal.ofReal ((d:ℝ)*C*((2:ℝ)^N)^(-v)) := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [he',← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hN₀ N hN)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularClassSmallTrouble
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform small troublesome-pair mass for the original regularized class -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem regular_class_small_troublesome (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (L : ℕ) {e τ η lam u v c Cp : ℝ}
    (hη : 0 ≤ η) (hCp : 0 ≤ Cp)
    (hτ : 2*(((n+1:ℕ):ℝ)+1)*lam < τ)
    (hgap : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u)
    (hu : c*((n+1:ℕ):ℝ) < u) (hv : c*((n+1:ℕ):ℝ) < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube (n+1)), 0 < Q.side →
      ∀ (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < B →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ a b : ℕ, a ≤ N → b ≤ N →
      ∀ p : CellPath (n+1), p.length = a →
        0 < sourceClass Q μ N B p₀ (Q.descendant p).carrier →
      ∀ r C Bs R : ℝ, 0 < r → C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) →
        8*(Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a))^2/r ≤ Q.side/(2:ℝ)^b →
        (∀ᵐ x ∂ν, ‖(Q.descendant p).center-x‖ ≤ R) →
        (∀ w : Space (n+1), ‖w‖ = 1 →
          ν {x | |inner ℝ w x-inner ℝ w (Q.descendant p).center| ≤ R*((2:ℝ)^N)^(-η)} ≤
            ENNReal.ofReal (Cp*((2:ℝ)^N)^(-v))) →
      ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier).prod ν)
        (troublesomePair (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier)
          (Q.descendant p).center r (Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a)) Bs
            (C*(Q.side/(2:ℝ)^b))
            (ENNReal.ofReal (((2:ℝ)^N)^e /
              (((2:ℝ)^N)^(sourceProfile Q μ N B p₀ b-sourceProfile Q μ N B p₀ a))^((n:ℝ)/(n+1))))) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨N₁,h₁⟩ := eventually_radialClassBallBound_le n hτ
  obtain ⟨N₂,h₂⟩ := eventually_weak_radial_reciprocal_budget n
    (((2*L+1)^(n+1):ℕ):ℝ) (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)) e τ η u hgap
  obtain ⟨N₃,h₃⟩ := weak_radial_local_deletion_budget (n+1) (by omega) hCp hu hv
  refine ⟨max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro N hN Q hQ μ ν _ _ B hB hwidth hlarge p₀ hp₀ a b ha hb p hp hpos r C Bs R hr hL hfreeze hR hslab
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : 0 < 1) ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let R₀ : ℝ := (2:ℝ)^N
  let D : ℝ := R₀^(sourceProfile Q μ N B p₀ b-sourceProfile Q μ N B p₀ a)
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have hD : 0 < D := Real.rpow_pos_of_pos hR₀ _
  have hH := h₁ N hN₁ Q μ B p₀ a b
  have hHpos : 0 ≤ radialClassBallBound Q μ N B p₀ a b lam := by
    unfold radialClassBallBound
    positivity
  have hbudget : (((2*L+1)^(n+1):ℕ)/(R₀^e/D^((n:ℝ)/(n+1))))^(n+1)*
      (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)/(R₀^(-η))^(n+1))^(n*(n+1))*
        (radialClassBallBound Q μ N B p₀ a b lam)^n ≤ (R₀^(-u))^n := by
    have hG : 0 ≤ generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ) := by
      unfold generalTubeCountConstant
      positivity
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHpos hH n) (by positivity)).trans
    exact h₂ N hN₂ D hD
  have hh := regular_class_radial_incidence hLW hn Q hQ μ ν hNpos hB hwidth hlarge hp₀
    ha hb hp hpos (Bs := Bs) hr (show 0 < R₀^e/D^((n:ℝ)/(n+1)) by positivity)
    (Real.rpow_pos_of_pos hR₀ (-η))
    (Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (neg_nonpos.mpr hη))
    hfreeze hR (ENNReal.ofReal (Cp*R₀^(-v))) hslab L hL
    (Real.rpow_nonneg hR₀.le (-u)) hbudget
  apply h₃ N hN₃
  simpa only [R₀,D,Nat.cast_add,Nat.cast_one] using hh

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RetainedTubeTest
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retained pairs control the original full parent-cell tube mass -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem tube_mass_of_not_troublesome (μ : Measure (Space d)) (c z x : Space d)
    (r D B W : ℝ) (F : ℝ≥0∞)
    (hnot : (z,x) ∉ troublesomePair μ c r D B W F)
    (hsep : r ≤ ‖c-x‖) (hne : z ≠ x) (hD : ‖z-c‖ ≤ D) (hB : ‖z‖ ≤ B) :
    radialTubeMass μ W (z,x) ≤ F := by
  by_contra! hmass
  exact hnot ⟨hsep,hne,hD,hB,hmass⟩

theorem original_tube_test_of_not_troublesome (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (Q : Set (Space d)) (hQ : MeasurableSet Q) (c z x : Space d)
    (r D B W : ℝ) (F : ℝ≥0∞)
    (hnot : (z,x) ∉ troublesomePair (ProbabilityTheory.cond μ Q) c r D B W F)
    (hsep : r ≤ ‖c-x‖) (hne : z ≠ x) (hD : ‖z-c‖ ≤ D) (hB : ‖z‖ ≤ B) :
    μ (Q ∩ {y | ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W}) ≤ F*μ Q := by
  have hm := tube_mass_of_not_troublesome (ProbabilityTheory.cond μ Q) c z x r D B W F
    hnot hsep hne hD hB
  rw [← ProbabilityTheory.cond_mul_eq_inter hQ _ μ]
  exact mul_le_mul' hm le_rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicScaleBallBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-scale ball hypothesis supplies all required dyadic cell bounds -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_scale_ball_extension (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (N : ℕ) {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (hball : ∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^s))
    (x : Space d) {r : ℝ} (hr : ((2:ℝ)^N)⁻¹ ≤ r) :
    μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^s) := by
  by_cases hr1 : r ≤ 1
  · exact hball x r hr hr1
  have h1 : 1 ≤ ((2:ℝ)^N)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε
  have h2 : 1 ≤ r^s := Real.one_le_rpow (le_of_not_ge hr1) hs
  calc
    _ ≤ 1 := prob_le_one
    _ = ENNReal.ofReal (1:ℝ) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith)

theorem dyadic_scale_cell_bound (hd : 0 < d) (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (hball : ∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^s))
    {a : ℕ} (ha : a ≤ N) (p : CellPath d) (hp : p.length = a) :
    (μ (Q.descendant p).carrier).toReal ≤
      (2*Real.sqrt d)^s*((2:ℝ)^N)^ε*((2:ℝ)^N)^(-s*(a:ℝ)/(N:ℝ)) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hsqrt : 1 ≤ Real.sqrt (d:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have hlow : ((2:ℝ)^N)⁻¹ ≤ 2*Real.sqrt d*(Q.descendant p).side := by
    rw [Q.descendant_side,hQ,hp]
    have hpow : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^a)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) ha)
    have hc : (1:ℝ) ≤ 2*Real.sqrt d := by linarith
    exact hpow.trans (by simpa only [one_div,one_mul] using
      mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 2^a)))
  have hmeasure : μ (Q.descendant p).carrier ≤
      ENNReal.ofReal (((2:ℝ)^N)^ε*(2*Real.sqrt d*(Q.descendant p).side)^s) := by
    apply (measure_mono ?_).trans
      (dyadic_scale_ball_extension μ N hε hs hball (Q.descendant p).center hlow)
    intro z hz
    have hh := (Q.descendant p).dist_le (Q.descendant_side_pos hside p).le hz
      ((Q.descendant p).center_mem (Q.descendant_side_pos hside p))
    exact mem_ball.mpr (by nlinarith [Q.descendant_side_pos hside p])
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hsidep := Q.descendant_side_pos hside p
  rw [ENNReal.toReal_ofReal (by positivity)] at hh
  apply hh.trans_eq
  rw [Q.descendant_side,hQ,hp,show
    2*Real.sqrt d*(1/(2:ℝ)^a) = (2*Real.sqrt d)/(2:ℝ)^a by ring,
    Real.div_rpow (by positivity) (by positivity),dyadic_rpow_scale hN a s]
  ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SmallChartCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed unit cube for the small gnomonic chart -/

namespace Falconer
open Set Metric MeasureTheory

lemma smallChartCube_side (d : ℕ) : (smallChartCube d).side = 1 := rfl

lemma smallChartCube_center (d : ℕ) : (smallChartCube d).center = 0 := by
  ext i
  change -(1/2:ℝ)+1/2 = 0
  ring

lemma mem_smallChartCube {d : ℕ} {x : Space d} (hx : ‖x‖ ≤ 1/4) :
    x ∈ (smallChartCube d).carrier := by
  intro i
  have hi : |x i| ≤ 1/4 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx
  change -(1/2:ℝ) ≤ x i ∧ x i < -(1/2:ℝ)+1
  constructor <;> linarith [abs_le.mp hi]

lemma smallChartCube_norm {d : ℕ} {x : Space d} (hx : x ∈ (smallChartCube d).carrier) :
    ‖x‖ ≤ Real.sqrt d+1 := by
  have hc := (smallChartCube d).center_mem (by norm_num [smallChartCube])
  have hd := (smallChartCube d).dist_le (by norm_num [smallChartCube]) hx hc
  rw [smallChartCube_center,dist_zero_right,smallChartCube_side,mul_one] at hd
  linarith

lemma smallChartCube_full {d : ℕ} (μ : Measure (Space d))
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) : μ (smallChartCube d).carrierᶜ = 0 := by
  apply measure_mono_null (show (smallChartCube d).carrierᶜ ⊆ {x | ¬ ‖x‖ ≤ 1/4} from ?_)
    (ae_iff.mp hμ)
  intro x hx hb
  exact hx (mem_smallChartCube hb)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RadialBlockDepths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A dyadic block schedule with two initial blocks reserved for freezing -/

namespace Falconer

theorem radialBlockSize_total (N J : ℕ) : (J+2)*radialBlockSize N J ≤ N :=
  Nat.mul_div_le N (J+2)

theorem radialBlockDepth_le (N J : ℕ) {j : ℕ} (hj : j ≤ J) :
    radialBlockDepth N J j ≤ N := by
  have hh := radialBlockSize_total N J
  have hm := Nat.mul_le_mul_right (radialBlockSize N J) hj
  have hJB : J*radialBlockSize N J ≤ N := by nlinarith
  have he := Nat.sub_add_cancel hJB
  unfold radialBlockDepth
  omega

theorem radialBlockDepth_final (N J : ℕ) : radialBlockDepth N J J = N := by
  have hh := radialBlockSize_total N J
  unfold radialBlockDepth
  have hle : J*radialBlockSize N J ≤ N := by nlinarith
  exact Nat.sub_add_cancel hle

theorem radialBlockDepth_step (N J j : ℕ) :
    radialBlockDepth N J (j+1) = radialBlockDepth N J j+radialBlockSize N J := by
  unfold radialBlockDepth
  ring

theorem radialBlockDepth_mono (N J : ℕ) : Monotone (radialBlockDepth N J) := by
  intro i j hij
  unfold radialBlockDepth
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem radialBlockDepth_two_blocks (N J j : ℕ) :
    2*radialBlockSize N J ≤ radialBlockDepth N J j := by
  have hh := radialBlockSize_total N J
  have hJB : J*radialBlockSize N J ≤ N := by nlinarith
  have he := Nat.sub_add_cancel hJB
  unfold radialBlockDepth
  nlinarith

theorem radialBlockDepth_initial_upper {N : ℕ} (hN : 0 < N) (J : ℕ) :
    (radialBlockDepth N J 0:ℝ)/(N:ℝ) ≤ 2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hJ : (0:ℝ) < (J:ℝ)+2 := by positivity
  have ht := Nat.lt_mul_div_succ N (by omega : 0 < J+2)
  have ht' : (N:ℝ) < ((J:ℝ)+2)*((radialBlockSize N J:ℝ)+1) := by
    exact_mod_cast ht
  have htotal := radialBlockSize_total N J
  have hjb : J*radialBlockSize N J ≤ N := by nlinarith
  have he : (radialBlockDepth N J 0:ℝ) = (N:ℝ)-(J:ℝ)*(radialBlockSize N J:ℝ) := by
    simp only [radialBlockDepth,zero_mul,Nat.add_zero,Nat.cast_sub hjb,Nat.cast_mul]
  rw [he]
  apply (div_le_iff₀ hN').mpr
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) J]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialFreezingScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete near-pin radii for the reserved-block dyadic geometry -/

namespace Falconer

theorem reserved_block_freezing {d A q s : ℝ} (hd : 1 ≤ d) (hA : 0 < A)
    (hq : 0 < q) (hq1 : q ≤ 1) (hs : 0 < s) (hscale : s ≤ A*q^2) :
    Real.sqrt d*s < 8*d*A*q ∧
      8*(Real.sqrt d*s)^2/(8*d*A*q) ≤ s*q := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hr : 0 < 8*d*A*q := by positivity
  have hsq : q^2 ≤ q := by nlinarith
  have hb : s ≤ A*q := hscale.trans (mul_le_mul_of_nonneg_left hsq hA.le)
  constructor
  · have hroot : Real.sqrt d ≤ d := by
      nlinarith [Real.sq_sqrt hd0.le,Real.sqrt_nonneg d]
    have he : Real.sqrt d*s ≤ d*A*q := by
      calc
        _ ≤ d*s := mul_le_mul_of_nonneg_right hroot hs.le
        _ ≤ d*(A*q) := mul_le_mul_of_nonneg_left hb hd0.le
        _ = _ := by ring
    have hh : 0 < d*A*q := by positivity
    linarith
  · apply (div_le_iff₀ hr).mpr
    calc
      8*(Real.sqrt d*s)^2 = (8*d*s)*s := by
        rw [mul_pow,Real.sq_sqrt hd0.le]
        ring
      _ ≤ (8*d*s)*(A*q^2) := mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (s*q)*(8*d*A*q) := by ring

theorem dyadic_reserved_block_freezing {d : ℕ} (hd : 0 < d)
    {A : ℝ} (hA : 0 < A) {a b : ℕ} (hab : 2*b ≤ a) :
    Real.sqrt d*(A/(2:ℝ)^a) < 8*(d:ℝ)*A/(2:ℝ)^b ∧
      8*(Real.sqrt d*(A/(2:ℝ)^a))^2/(8*(d:ℝ)*A/(2:ℝ)^b) ≤ A/(2:ℝ)^(a+b) := by
  let q : ℝ := ((2:ℝ)^b)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hscale : A/(2:ℝ)^a ≤ A*q^2 := by
    have hh : A/(2:ℝ)^a ≤ A/(2:ℝ)^(2*b) :=
      div_le_div_of_nonneg_left hA.le (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hab)
    have he : (2:ℝ)^(2*b) = ((2:ℝ)^b)^2 := by rw [Nat.mul_comm 2 b,pow_mul]
    simpa only [q,he,div_eq_mul_inv,inv_pow] using hh
  have hh := reserved_block_freezing (by exact_mod_cast hd : (1:ℝ) ≤ d)
    hA hq hq1 (show 0 < A/(2:ℝ)^a by positivity) hscale
  have he : (A/(2:ℝ)^a)*q = A/(2:ℝ)^(a+b) := by
    simp only [q,pow_add,div_eq_mul_inv,mul_inv_rev]
    ring
  simpa only [q,← div_eq_mul_inv,he] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RadialBlockRadius
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual near-pin radius decays at a fixed reciprocal-scale power -/

namespace Falconer

theorem radial_block_radius_bound {A : ℝ} (hA : 0 ≤ A) (d N J : ℕ) :
    8*(d:ℝ)*A/(2:ℝ)^(radialBlockSize N J) ≤
      16*(d:ℝ)*A*((2:ℝ)^N)^(-1/((J:ℝ)+2)) := by
  have hJ : (0:ℝ) < (J:ℝ)+2 := by positivity
  have hh := Nat.lt_mul_div_succ N (by omega : 0 < J+2)
  have hb : (N:ℝ) < ((J:ℝ)+2)*((radialBlockSize N J:ℝ)+1) := by exact_mod_cast hh
  have hb' : -(radialBlockSize N J:ℝ) ≤ 1-(N:ℝ)/((J:ℝ)+2) := by
    have ht : (N:ℝ)/((J:ℝ)+2) < (radialBlockSize N J:ℝ)+1 :=
      (div_lt_iff₀ hJ).mpr (by simpa only [mul_comm] using hb)
    linarith
  have he : ((2:ℝ)^N)^(-1/((J:ℝ)+2)) = (2:ℝ)^(-(N:ℝ)/((J:ℝ)+2)) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hp : ((2:ℝ)^(radialBlockSize N J))⁻¹ ≤
      2*((2:ℝ)^N)^(-1/((J:ℝ)+2)) := by
    rw [← Real.rpow_natCast,← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    calc
      _ ≤ (2:ℝ)^(1-(N:ℝ)/((J:ℝ)+2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hb'
      _ = _ := by
        rw [he,Real.rpow_sub (by norm_num),Real.rpow_one]
        rw [show -(N:ℝ)/((J:ℝ)+2) = -((N:ℝ)/((J:ℝ)+2)) by ring,
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        rfl
  calc
    _ = (8*(d:ℝ)*A)*((2:ℝ)^(radialBlockSize N J))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (8*(d:ℝ)*A)*(2*((2:ℝ)^N)^(-1/((J:ℝ)+2))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem eventually_radial_block_radius_le_one {A : ℝ} (hA : 0 ≤ A) (d J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 8*(d:ℝ)*A/(2:ℝ)^(radialBlockSize N J) ≤ 1 := by
  have hpow : 0 < (1:ℝ)/((J:ℝ)+2) := by positivity
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hpow (16*(d:ℝ)*A)
  refine ⟨N₀,fun N hN => (radial_block_radius_bound hA d N J).trans ?_⟩
  calc
    _ ≤ (((2:ℝ)^N)^(1/((J:ℝ)+2)))*(((2:ℝ)^N)^(-1/((J:ℝ)+2))) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = 1 := by
      rw [← Real.rpow_add (by positivity),show
        (1/((J:ℝ)+2))+(-1/((J:ℝ)+2)) = 0 by ring,Real.rpow_zero]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_PairCorePruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Core restrictions and density pruning preserve the original pair-cost ledger -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_core_compl_null (ν : Measure X) (μ : Measure Y) [SFinite μ] (P : Set X) (S : Set Y)
    (hP : ν Pᶜ = 0) (hS : μ Sᶜ = 0) : (ν.prod μ) (P ×ˢ S)ᶜ = 0 := by
  apply le_antisymm _ zero_le
  calc
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ ∪ univ ×ˢ Sᶜ) := by
      apply measure_mono
      intro p hp
      by_cases hx : p.1 ∈ P
      · exact Or.inr ⟨mem_univ _,fun hy => hp ⟨hx,hy⟩⟩
      · exact Or.inl ⟨hx,mem_univ _⟩
    _ ≤ (ν.prod μ) (Pᶜ ×ˢ univ)+(ν.prod μ) (univ ×ˢ Sᶜ) := measure_union_le _ _
    _ = 0 := by simp only [Measure.prod_prod,hP,hS,zero_mul,mul_zero,add_zero]

theorem pair_core_restriction_cost (ν : Measure X) (μ : Measure Y) [SFinite μ] (G : Set (X × Y))
    (P : Set X) (S : Set Y) (hP : ν Pᶜ = 0) (hS : μ Sᶜ = 0) :
    (ν.prod μ) (G ∩ (P ×ˢ S))ᶜ ≤ (ν.prod μ) Gᶜ := by
  rw [compl_inter]
  exact (measure_union_le _ _).trans_eq (by rw [product_core_compl_null ν μ P S hP hS,add_zero])

theorem density_pruned_pair_cost (ν : Measure X) (μ : Measure Y) [SFinite μ]
    (G : Set (X × Y)) (hG : MeasurableSet G) (Q : ℕ → ι → Set Y)
    (I : ℕ → Finset ι) (J : ℕ) (θ : ℝ≥0∞)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j)) :
    (ν.prod μ) (G \ multiscaleFiberBad μ G Q I θ J)ᶜ ≤
      (ν.prod μ) Gᶜ+(J+1:ℝ≥0∞)*(θ*μ univ)*ν univ := by
  have he : (G \ multiscaleFiberBad μ G Q I θ J)ᶜ =
      Gᶜ ∪ multiscaleFiberBad μ G Q I θ J := by
    classical
    ext p
    simp only [mem_compl_iff, mem_sdiff, mem_union]
    tauto
  rw [he]
  exact (measure_union_le _ _).trans
    (add_le_add le_rfl (multiscaleFiberBad_mass ν μ G hG Q I J hQ hdisj θ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ClasswiseRadialGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining radial gains with the original source-class weights -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem classwise_radial_gain (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (I : Finset ι) (S : ι → Set (Space d)) (G : ι → Set (Space d × Space d))
    (hS : ∀ i ∈ I, MeasurableSet (S i)) (hG : ∀ i ∈ I, MeasurableSet (G i))
    (hpos : ∀ i ∈ I, μ (S i) ≠ 0) (hdisj : (I : Set ι).PairwiseDisjoint S)
    (t C : ℝ≥0∞) (r : ℝ)
    (hcost : ∀ i ∈ I, (ν.prod (ProbabilityTheory.cond μ (S i))) (G i)ᶜ ≤ t)
    (hcap : ∀ i ∈ I, ∀ x u : Space d,
      ProbabilityTheory.cond μ (S i) {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (ν.prod μ) Hᶜ ≤ μ (⋃ i ∈ I, S i)ᶜ+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let H := ⋃ i ∈ I, G i ∩ (univ ×ˢ S i)
  have hH : MeasurableSet H := Finset.measurableSet_biUnion I
    (fun i hi => (hG i hi).inter (MeasurableSet.univ.prod (hS i hi)))
  have hmass : (∑ i ∈ I, μ (S i)) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj hS]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ)
  have hreconstruct (i : ι) (hi : i ∈ I) (E : Set (Space d × Space d)) :
      μ (S i)*((ν.prod (ProbabilityTheory.cond μ (S i))) E) =
        (ν.prod (μ.restrict (S i))) E := by
    rw [ProbabilityTheory.cond,Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel (hpos i hi) (measure_ne_top μ _),one_mul]
  refine ⟨H,hH,?_,?_⟩
  · have hsub : Hᶜ ⊆ (univ ×ˢ (⋃ i ∈ I, S i)ᶜ) ∪
        ⋃ i ∈ I, (G i)ᶜ ∩ (univ ×ˢ S i) := by
      intro p hp
      by_cases hs : p.2 ∈ ⋃ i ∈ I, S i
      · obtain ⟨i,hi,hsi⟩ := mem_iUnion₂.mp hs
        right
        refine mem_iUnion₂.mpr ⟨i,hi,?_,mem_univ _,hsi⟩
        intro hgi
        exact hp (mem_iUnion₂.mpr ⟨i,hi,hgi,mem_univ _,hsi⟩)
      · exact Or.inl ⟨mem_univ _,hs⟩
    calc
      _ ≤ (ν.prod μ) (univ ×ˢ (⋃ i ∈ I, S i)ᶜ)+
          (ν.prod μ) (⋃ i ∈ I, (G i)ᶜ ∩ (univ ×ˢ S i)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+
          ∑ i ∈ I, (ν.prod μ) ((G i)ᶜ ∩ (univ ×ˢ S i)) := by
        simp only [Measure.prod_prod,measure_univ,one_mul]
        exact add_le_add le_rfl (measure_biUnion_finset_le _ _)
      _ ≤ μ (⋃ i ∈ I, S i)ᶜ+∑ i ∈ I, μ (S i)*t := by
        apply add_le_add le_rfl (Finset.sum_le_sum ?_)
        intro i hi
        rw [← Measure.restrict_apply (hG i hi).compl,← Measure.prod_restrict,
          Measure.restrict_univ,← hreconstruct i hi]
        exact mul_le_mul' le_rfl (hcost i hi)
      _ = μ (⋃ i ∈ I, S i)ᶜ+(∑ i ∈ I, μ (S i))*t := by rw [Finset.sum_mul]
      _ ≤ _ := add_le_add le_rfl ((mul_le_mul' hmass le_rfl).trans_eq (one_mul t))
  · intro x u
    let A := fun i => {z | (x,z) ∈ G i ∧ ‖normalize (z-x)-u‖ ≤ r}
    have hsub : {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ r} ⊆ ⋃ i ∈ I, S i ∩ A i := by
      intro z hz
      obtain ⟨i,hi,hgi,hsi⟩ := mem_iUnion₂.mp hz.1
      exact mem_iUnion₂.mpr ⟨i,hi,hsi.2,hgi,hz.2⟩
    calc
      _ ≤ ∑ i ∈ I, μ (S i ∩ A i) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ = ∑ i ∈ I, μ (S i)*ProbabilityTheory.cond μ (S i) (A i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← ProbabilityTheory.cond_mul_eq_inter (hS i hi) (A i) μ,mul_comm]
      _ ≤ ∑ i ∈ I, μ (S i)*C := Finset.sum_le_sum (fun i hi =>
        mul_le_mul' le_rfl (hcap i hi x u))
      _ = (∑ i ∈ I, μ (S i))*C := (Finset.sum_mul _ _ _).symm
      _ ≤ C := (mul_le_mul' hmass le_rfl).trans_eq (one_mul C)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_LocalRadialPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One level of measurable radial pruning and its original-law cost -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*}

theorem levelRadialBad_measurable (μ : Measure (Space d)) (I : Finset ι)
    (Q : ι → Set (Space d)) (c : ι → Space d) (r D B W : ℝ) (F : ℝ≥0∞)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) :
    MeasurableSet (levelRadialBad μ I Q c r D B W F) := by
  apply (nearPinPairs_measurable I Q c r hQ).union
  apply Finset.measurableSet_biUnion
  intro i hi
  exact (troublesomePair_measurable _ _ _ _ _ _ _).inter ((hQ i hi).prod MeasurableSet.univ)

theorem level_radial_bad_mass (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [SFinite ν]
    (I : Finset ι) (Q : ι → Set (Space d)) (c : ι → Space d)
    (r D B W : ℝ) (F K t : ℝ≥0∞)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) (hpos : ∀ i ∈ I, μ (Q i) ≠ 0)
    (hdisj : (I : Set ι).PairwiseDisjoint Q)
    (hball : ∀ i ∈ I, ν (ball (c i) r) ≤ K)
    (htrouble : ∀ i ∈ I, ((ProbabilityTheory.cond μ (Q i)).prod ν)
      (troublesomePair (ProbabilityTheory.cond μ (Q i)) (c i) r D B W F) ≤ t) :
    (μ.prod ν) (levelRadialBad μ I Q c r D B W F) ≤ (K+t)*μ univ := by
  apply (measure_union_le _ _).trans
  have hn := near_pin_pair_mass μ ν I Q c r hQ hdisj K hball
  have ht := conditional_cellwise_pair_deletion μ ν I Q
    (fun i => troublesomePair (ProbabilityTheory.cond μ (Q i)) (c i) r D B W F)
    hQ (fun i _ => troublesomePair_measurable _ _ _ _ _ _ _) hpos hdisj t htrouble
  exact (add_le_add hn ht).trans_eq (add_mul K t (μ univ)).symm

theorem original_tube_test_of_level_retained (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (I : Finset ι) (Q : ι → Set (Space d)) (c : ι → Space d)
    (r D B W : ℝ) (F : ℝ≥0∞) (hDr : D < r)
    (hQ : ∀ i ∈ I, MeasurableSet (Q i)) {z x : Space d}
    (hgood : (z,x) ∉ levelRadialBad μ I Q c r D B W F) {i : ι} (hi : i ∈ I)
    (hzQ : z ∈ Q i) (hzD : ‖z-c i‖ ≤ D) (hzB : ‖z‖ ≤ B) :
    μ (Q i ∩ {y | ‖perpendicularPart (NormedSpace.normalize (z-x)) (y-x)‖ ≤ W}) ≤ F*μ (Q i) := by
  have hn : (z,x) ∉ nearPinPairs I Q c r := fun h => hgood (Or.inl h)
  have hs := distance_of_not_nearPinPairs I Q c r hn hi hzQ
  have hsep : r ≤ ‖c i-x‖ := by simpa only [dist_eq_norm,norm_sub_rev] using hs
  have hne : z ≠ x := by
    intro he
    subst z
    rw [norm_sub_rev] at hzD
    exact (not_le_of_gt hDr) (hsep.trans hzD)
  have ht : (z,x) ∉ troublesomePair (ProbabilityTheory.cond μ (Q i)) (c i) r D B W F := by
    intro h
    exact hgood (Or.inr (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,h,hzQ,mem_univ _⟩⟩))
  exact original_tube_test_of_not_troublesome μ (Q i) (hQ i hi) (c i) z x r D B W F
    ht hsep hne hzD hzB

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MultilevelRadialPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable surviving pair relation at finitely many radial levels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*}

theorem multilevelRadialBad_measurable (μ : Measure (Space d)) (J : ℕ)
    (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞)
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i)) :
    MeasurableSet (multilevelRadialBad μ J I Q c r D W B F) := by
  apply Finset.measurableSet_biUnion
  intro j hj
  exact levelRadialBad_measurable μ (I j) (Q j) (c j) (r j) (D j) B (W j) (F j)
    (hQ j (Finset.mem_range.mp hj))

theorem radialGoodPairs_measurable (μ : Measure (Space d)) (J : ℕ)
    (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞)
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i)) :
    MeasurableSet (radialGoodPairs μ J I Q c r D W B F) :=
  ((multilevelRadialBad_measurable μ J I Q c r D W B F hQ).preimage measurable_swap).compl

theorem radial_good_pairs_cost (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [SFinite ν]
    (J : ℕ) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F K t : ℕ → ℝ≥0∞)
    (hQ : ∀ j < J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j < J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hball : ∀ j < J, ∀ i ∈ I j, ν (Metric.ball (c j i) (r j)) ≤ K j)
    (htrouble : ∀ j < J, ∀ i ∈ I j,
      ((ProbabilityTheory.cond μ (Q j i)).prod ν)
        (troublesomePair (ProbabilityTheory.cond μ (Q j i)) (c j i) (r j) (D j) B (W j) (F j)) ≤ t j) :
    (ν.prod μ) (radialGoodPairs μ J I Q c r D W B F)ᶜ ≤
      (∑ j ∈ Finset.range J, (K j+t j))*μ univ := by
  have hm := multilevelRadialBad_measurable μ J I Q c r D W B F hQ
  change (ν.prod μ) ((Prod.swap ⁻¹' multilevelRadialBad μ J I Q c r D W B F)ᶜ)ᶜ ≤ _
  rw [compl_compl,← Measure.map_apply measurable_swap hm,Measure.prod_swap]
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        (μ.prod ν) (levelRadialBad μ (I j) (Q j) (c j) (r j) (D j) B (W j) (F j)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range J, (K j+t j)*μ univ := Finset.sum_le_sum (fun j hj =>
      level_radial_bad_mass μ ν (I j) (Q j) (c j) (r j) (D j) B (W j) (F j) (K j) (t j)
        (hQ j (Finset.mem_range.mp hj)) (hpos j (Finset.mem_range.mp hj))
        (hdisj j (Finset.mem_range.mp hj)) (hball j (Finset.mem_range.mp hj))
        (htrouble j (Finset.mem_range.mp hj)))
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem original_tube_test_of_radial_good (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (J : ℕ) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d)) (c : ℕ → ι → Space d)
    (r D W : ℕ → ℝ) (B : ℝ) (F : ℕ → ℝ≥0∞)
    {x z : Space d} (hgood : (x,z) ∈ radialGoodPairs μ J I Q c r D W B F)
    {j : ℕ} (hj : j < J) (hDr : D j < r j) {i : ι} (hi : i ∈ I j)
    (hQ : ∀ i ∈ I j, MeasurableSet (Q j i))
    (hzQ : z ∈ Q j i) (hzD : ‖z-c j i‖ ≤ D j) (hzB : ‖z‖ ≤ B) :
    μ (Q j i ∩ {y | ‖perpendicularPart (NormedSpace.normalize (z-x)) (y-x)‖ ≤ W j}) ≤
      F j*μ (Q j i) := by
  apply original_tube_test_of_level_retained μ (I j) (Q j) (c j) (r j) (D j) B (W j) (F j)
    hDr hQ (i := i) _ hi hzQ hzD hzB
  intro hb
  exact hgood (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨Finset.mem_range.mpr hj,hb⟩⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_FiniteRadialPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite radial pruning from actual parent-cell tests -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ} {ι : Type*} [DecidableEq ι]

theorem finite_radial_pruning (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (J : ℕ) (hJ : 0 < J) (I : ℕ → Finset ι) (Q : ℕ → ι → Set (Space d))
    (parent : ℕ → ι → ι) (c : ℕ → ι → Space d)
    (r D W diam : ℕ → ℝ) (Bs Bp capRadius : ℝ) (F K t : ℕ → ℝ≥0∞)
    (P S : Set (Space d)) (hP : MeasurableSet P) (hS : MeasurableSet S)
    (hPfull : ν Pᶜ = 0) (hSfull : μ Sᶜ = 0)
    (hPb : ∀ x ∈ P, ‖x‖ ≤ Bp) (hSb : ∀ z ∈ S, ‖z‖ ≤ Bs)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hpos : ∀ j < J, ∀ i ∈ I j, μ (Q j i) ≠ 0)
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j))
    (hcover : ∀ j ≤ J, ∀ z ∈ S, ∃ i ∈ I j, z ∈ Q j i)
    (hgeom : ∀ j < J, ∀ i ∈ I j, ∀ z ∈ Q j i, ‖z-c j i‖ ≤ D j ∧ ‖z‖ ≤ Bs)
    (hfar : ∀ j < J, D j < r j)
    (hparent : ∀ j < J, ∀ i ∈ I (j+1), parent j i ∈ I j ∧ Q (j+1) i ⊆ Q j (parent j i))
    (hdiam : ∀ j < J, ∀ i ∈ I (j+1), ∀ y ∈ Q (j+1) i, ∀ z ∈ Q (j+1) i, ‖y-z‖ ≤ diam j)
    (hwidth : ∀ j < J, diam j+2*(Bs+Bp)*capRadius ≤ W j)
    (hball : ∀ j < J, ∀ i ∈ I j, ν (ball (c j i) (r j)) ≤ K j)
    (htrouble : ∀ j < J, ∀ i ∈ I j,
      ((ProbabilityTheory.cond μ (Q j i)).prod ν)
        (troublesomePair (ProbabilityTheory.cond μ (Q j i)) (c j i) (r j) (D j) Bs (W j) (F j)) ≤ t j)
    (θ : ℝ≥0∞) (hθ : 0 < θ) (hθtop : θ ≠ ∞) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (ν.prod μ) Gᶜ ≤ (∑ j ∈ Finset.range J, (K j+t j))+(J+1:ℝ≥0∞)*θ ∧
      ∀ x u : Space d,
        μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ capRadius} ≤
          ∏ j ∈ Finset.range J, θ⁻¹*F j := by
  let G₀ := radialGoodPairs μ J I Q c r D W Bs F ∩ (P ×ˢ S)
  have hG₀ : MeasurableSet G₀ :=
    (radialGoodPairs_measurable μ J I Q c r D W Bs F (fun j hj => hQ j hj.le)).inter (hP.prod hS)
  let G := G₀ \ multiscaleFiberBad μ G₀ Q I θ J
  have hG : MeasurableSet G := hG₀.diff
    (multiscaleFiberBad_measurable μ G₀ hG₀ Q I θ J hQ)
  refine ⟨G,hG,?_,?_⟩
  · have hb := radial_good_pairs_cost μ ν J I Q c r D W Bs F K t
      (fun j hj => hQ j hj.le) hpos (fun j hj => hdisj j hj.le) hball htrouble
    have hc := pair_core_restriction_cost ν μ (radialGoodPairs μ J I Q c r D W Bs F)
      P S hPfull hSfull
    have hd := density_pruned_pair_cost ν μ G₀ hG₀ Q I J θ hQ hdisj
    simp only [measure_univ,mul_one] at hb hd
    exact hd.trans (add_le_add (hc.trans hb) le_rfl)
  · intro x u
    have hbound : ∀ z, (x,z) ∈ G₀ → ‖z-x‖ ≤ Bs+Bp := by
      intro z hz
      exact (norm_sub_le z x).trans (add_le_add (hSb z hz.2.2) (hPb x hz.2.1))
    have hne : ∀ z, (x,z) ∈ G₀ → z ≠ x := by
      intro z hz he
      obtain ⟨i,hi,hzi⟩ := hcover 0 (Nat.zero_le _) z hz.2.2
      have hbad : (z,x) ∉ levelRadialBad μ (I 0) (Q 0) (c 0) (r 0) (D 0) Bs (W 0) (F 0) := by
        intro hh
        exact hz.1 (mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨Finset.mem_range.mpr hJ,hh⟩⟩)
      have hn : (z,x) ∉ nearPinPairs (I 0) (Q 0) (c 0) (r 0) := fun h => hbad (Or.inl h)
      have hs := distance_of_not_nearPinPairs (I 0) (Q 0) (c 0) (r 0) hn hi hzi
      have hh := (hgeom 0 hJ i hi z hzi).1
      rw [he] at hh
      have hs' : r 0 ≤ ‖x-c 0 i‖ := by simpa only [dist_eq_norm] using hs
      exact (not_le_of_gt (hfar 0 hJ)) (hs'.trans hh)
    have hlocal : ∀ j < J, ∀ p ∈ I j, ∀ q ∈ Q j p, (x,q) ∈ G₀ → q ≠ x →
        μ (Q j p ∩ {y | ‖perpendicularPart (normalize (q-x)) (y-x)‖ ≤
          diam j+2*(Bs+Bp)*capRadius}) ≤ F j*μ (Q j p) := by
      intro j hj p hp q hqp hq _
      have ht := original_tube_test_of_radial_good μ J I Q c r D W Bs F hq.1 hj (hfar j hj) hp
        (hQ j hj.le) hqp (hgeom j hj p hp q hqp).1 (hgeom j hj p hp q hqp).2
      apply (measure_mono ?_).trans ht
      intro y hy
      exact ⟨hy.1,hy.2.trans (hwidth j hj)⟩
    have hm := multiscale_physical_cap_mass μ G₀ hG₀ Q I parent J x u capRadius (Bs+Bp) diam θ F
      hθ hθtop hQ hdisj hparent hdiam hbound hne hlocal
      (fun z hz => hcover J le_rfl z hz.1.1.2.2)
    simpa only [retainedRadialCap, G, measure_univ,mul_one] using hm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_OccupiedRadialTree
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Occupied dyadic trees with a common full-measure source core -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem DyadicCube.emptyTreeCells_measurable (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : MeasurableSet (Q.emptyTreeCells μ N) := by
  apply Finset.measurableSet_biUnion
  intro n _
  exact Finset.measurableSet_biUnion _ (fun p _ => (Q.descendant p).measurable)

theorem DyadicCube.emptyTreeCells_null (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : μ (Q.emptyTreeCells μ N) = 0 := by
  apply le_antisymm _ zero_le
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_nonpos
  intro n _
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_nonpos
  intro p hp
  obtain ⟨hp,hno⟩ := Finset.mem_sdiff.mp hp
  have hn : ¬ 0 < μ (Q.descendant p).carrier := by
    intro h
    exact hno (Finset.mem_filter.mpr ⟨hp,h⟩)
  exact le_of_not_gt hn

theorem DyadicCube.occupiedTreeCore_measurable (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) : MeasurableSet (Q.occupiedTreeCore μ N) :=
  Q.measurable.diff (Q.emptyTreeCells_measurable μ N)

theorem DyadicCube.occupiedTreeCore_full (Q : DyadicCube d)
    (μ : Measure (Space d)) (N : ℕ) (hroot : μ Q.carrierᶜ = 0) :
    μ (Q.occupiedTreeCore μ N)ᶜ = 0 := by
  classical
  have he : (Q.occupiedTreeCore μ N)ᶜ = Q.carrierᶜ ∪ Q.emptyTreeCells μ N := by
    ext x
    simp only [occupiedTreeCore,mem_compl_iff,mem_sdiff,mem_union]
    tauto
  rw [he]
  apply le_antisymm _ zero_le
  exact (measure_union_le _ _).trans_eq (by rw [hroot,Q.emptyTreeCells_null,zero_add])

theorem DyadicCube.occupiedTreeCore_cover (Q : DyadicCube d)
    (μ : Measure (Space d)) {N n : ℕ} (hn : n ≤ N)
    {x : Space d} (hx : x ∈ Q.occupiedTreeCore μ N) :
    ∃ p ∈ Q.occupiedPaths μ n, x ∈ (Q.descendant p).carrier := by
  classical
  obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth n hx.1
  refine ⟨p,?_,hxp⟩
  by_contra hno
  exact hx.2 (mem_iUnion₂.mpr ⟨n,Finset.mem_range.mpr (by omega),
    mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hno⟩,hxp⟩⟩)

theorem DyadicCube.occupied_parent (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {a b : ℕ} (hab : a ≤ b)
    {p : List (Fin d → Bool)} (hp : p ∈ Q.occupiedPaths μ b) :
    p.take a ∈ Q.occupiedPaths μ a ∧
      (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  obtain ⟨hp,hpos⟩ := Finset.mem_filter.mp hp
  have hlen := (mem_cubePaths d b p).mp hp
  have hsub := Regularization.descendant_subset_take Q hQ p a
  refine ⟨Finset.mem_filter.mpr ⟨?_,hpos.trans_le (measure_mono hsub)⟩,hsub⟩
  exact (mem_cubePaths d a _).mpr (by simp only [List.length_take,hlen,Nat.min_eq_left hab])

theorem DyadicCube.occupied_center_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {n : ℕ} {p : List (Fin d → Bool)}
    (hp : p ∈ Q.occupiedPaths μ n) {z : Space d} (hz : z ∈ (Q.descendant p).carrier) :
    ‖z-(Q.descendant p).center‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^n) := by
  have hlen := (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1
  have hb := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hz
    ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
  simpa only [dist_eq_norm,Q.descendant_side,hlen] using hb

theorem DyadicCube.occupied_diameter_bound (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) {n : ℕ} {p : List (Fin d → Bool)}
    (hp : p ∈ Q.occupiedPaths μ n) {y z : Space d}
    (hy : y ∈ (Q.descendant p).carrier) (hz : z ∈ (Q.descendant p).carrier) :
    ‖y-z‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^n) := by
  have hlen := (mem_cubePaths d n p).mp (Finset.mem_filter.mp hp).1
  simpa only [dist_eq_norm,Q.descendant_side,hlen] using
    (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hy hz

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_DyadicRadialPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial pruning on actual occupied dyadic descendants -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem dyadic_radial_pruning (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (hQ : 0 < Q.side) (hroot : μ Q.carrierᶜ = 0)
    (N J : ℕ) (hJ : 0 < J) (depth : ℕ → ℕ)
    (hdepth : ∀ j ≤ J, depth j ≤ N) (hmono : ∀ j < J, depth j ≤ depth (j+1))
    (r W : ℕ → ℝ) (Bs Bp capRadius : ℝ) (F K t : ℕ → ℝ≥0∞)
    (P : Set (Space d)) (hP : MeasurableSet P) (hPfull : ν Pᶜ = 0)
    (hPb : ∀ x ∈ P, ‖x‖ ≤ Bp) (hQb : ∀ z ∈ Q.carrier, ‖z‖ ≤ Bs)
    (hfar : ∀ j < J, Real.sqrt d*(Q.side/(2:ℝ)^depth j) < r j)
    (hwidth : ∀ j < J,
      Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1))+2*(Bs+Bp)*capRadius ≤ W j)
    (hball : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      ν (ball (Q.descendant p).center (r j)) ≤ K j)
    (htrouble : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      ((ProbabilityTheory.cond μ (Q.descendant p).carrier).prod ν)
        (troublesomePair (ProbabilityTheory.cond μ (Q.descendant p).carrier)
          (Q.descendant p).center (r j) (Real.sqrt d*(Q.side/(2:ℝ)^depth j))
          Bs (W j) (F j)) ≤ t j)
    (θ : ℝ≥0∞) (hθ : 0 < θ) (hθtop : θ ≠ ∞) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (ν.prod μ) Gᶜ ≤ (∑ j ∈ Finset.range J, (K j+t j))+(J+1:ℝ≥0∞)*θ ∧
      ∀ x u : Space d,
        μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ capRadius} ≤
          ∏ j ∈ Finset.range J, θ⁻¹*F j := by
  apply finite_radial_pruning μ ν J hJ
    (fun j => Q.occupiedPaths μ (depth j)) (fun _ p => (Q.descendant p).carrier)
    (fun j p => p.take (depth j)) (fun _ p => (Q.descendant p).center)
    r (fun j => Real.sqrt d*(Q.side/(2:ℝ)^depth j)) W
    (fun j => Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1))) Bs Bp capRadius F K t
    P (Q.occupiedTreeCore μ N) hP (Q.occupiedTreeCore_measurable μ N)
    hPfull (Q.occupiedTreeCore_full μ N hroot) hPb
    (fun z hz => hQb z hz.1)
    (fun _ _ p _ => (Q.descendant p).measurable)
    (fun _ _ _ hp => (Finset.mem_filter.mp hp).2.ne')
    (fun j _ p hp q hq hpq => Q.descendants_disjoint
      (((mem_cubePaths d (depth j) p).mp (Finset.mem_filter.mp hp).1).trans
        ((mem_cubePaths d (depth j) q).mp (Finset.mem_filter.mp hq).1).symm) hpq)
    (fun j hj z hz => Q.occupiedTreeCore_cover μ (hdepth j hj) hz)
    (fun j _ p hp z hz => ⟨Q.occupied_center_bound hQ μ hp hz,
      hQb z (Q.descendant_subset p hz)⟩)
    hfar
    (fun j hj _ hp => Q.occupied_parent hQ μ (hmono j hj) hp)
    (fun _ _ _ hp _ hy _ hz => Q.occupied_diameter_bound hQ μ hp hy hz)
    hwidth hball htrouble θ hθ hθtop

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialScaleIntersection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Intersecting the actual pair sets at finitely many radial scales -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem finite_radial_scale_intersection (μ ν : Measure (Space d))
    (I : Finset ℕ) (G : ℕ → Set (Space d × Space d))
    (t C : ℕ → ℝ≥0∞) (r : ℕ → ℝ)
    (hG : ∀ j ∈ I, MeasurableSet (G j))
    (hcost : ∀ j ∈ I, (ν.prod μ) (G j)ᶜ ≤ t j)
    (hcap : ∀ j ∈ I, ∀ x u : Space d,
      μ {z | (x,z) ∈ G j ∧ ‖normalize (z-x)-u‖ ≤ r j} ≤ C j) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      (ν.prod μ) Hᶜ ≤ ∑ j ∈ I, t j ∧
      ∀ j ∈ I, ∀ s : ℝ, s ≤ r j → ∀ x u : Space d,
        μ {z | (x,z) ∈ H ∧ ‖normalize (z-x)-u‖ ≤ s} ≤ C j := by
  classical
  let H := ⋂ j ∈ I, G j
  have hm : MeasurableSet H := Finset.measurableSet_biInter I hG
  refine ⟨H,hm,?_,?_⟩
  · have he : Hᶜ = ⋃ j ∈ I, (G j)ᶜ := by
      ext p
      simp only [H,mem_compl_iff,mem_iInter,mem_iUnion]
      push Not
      constructor <;> rintro ⟨j,hj,hp⟩ <;> exact ⟨j,hj,hp⟩
    rw [he]
    exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hcost)
  · intro j hj s hs x u
    apply (measure_mono ?_).trans (hcap j hj x u)
    intro z hz
    exact ⟨mem_iInter₂.mp hz.1 j hj,hz.2.trans hs⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialDyadicBracket
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a retained dyadic scale for an arbitrary cap radius -/

namespace Falconer

theorem radial_dyadic_bracket (N : ℕ) {r : ℝ}
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hr1 : r ≤ 1) :
    ∃ j ≤ N, r ≤ ((2:ℝ)^j)⁻¹ ∧ ((2:ℝ)^j)⁻¹ < 2*r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hr0 hr1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have he : (1/2:ℝ)^j = ((2:ℝ)^j)⁻¹ := by rw [one_div,inv_pow]
  rw [he] at hhi
  have hj : j ≤ N := by
    by_contra h
    have hp : (2:ℝ)^N < (2:ℝ)^j := pow_lt_pow_right₀ (by norm_num) (by omega)
    have hi : ((2:ℝ)^j)⁻¹ < ((2:ℝ)^N)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by positivity)).mpr hp
    exact (not_lt_of_ge hr) (hhi.trans_lt hi)
  refine ⟨j,hj,hhi,?_⟩
  rw [pow_succ,he] at hlo
  linarith

theorem radial_dyadic_bracket_above (N B : ℕ) {r : ℝ}
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hrB : r ≤ ((2:ℝ)^B)⁻¹) :
    ∃ j, B ≤ j ∧ j ≤ N ∧ r ≤ ((2:ℝ)^j)⁻¹ ∧ ((2:ℝ)^j)⁻¹ < 2*r := by
  have hr1 : r ≤ 1 := hrB.trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  obtain ⟨j,hj,hhi,hlo⟩ := radial_dyadic_bracket N hr hr1
  have hBj : B ≤ j := by
    by_contra h
    have hp : (2:ℝ)^(j+1) ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) (by omega)
    have hinv : ((2:ℝ)^B)⁻¹ ≤ ((2:ℝ)^(j+1))⁻¹ := inv_anti₀ (by positivity) hp
    have he : ((2:ℝ)^(j+1))⁻¹ = ((2:ℝ)^j)⁻¹/2 := by rw [pow_succ,mul_inv_rev]; ring
    rw [he] at hinv
    linarith
  exact ⟨j,hBj,hj,hhi,hlo⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialTotalCost
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the actual regularization and radial deletion costs -/

namespace Falconer
open scoped ENNReal

theorem weak_radial_total_real_cost (J k : ℕ) {A lam a b f : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hf : 0 < f) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ)^N)^(-2:ℝ)+(N:ℝ)^k*((2:ℝ)^N)^(-lam)+
        (J:ℝ)*(A*((2:ℝ)^N)^(-a)+((2:ℝ)^N)^(-b))+
        ((J:ℝ)+1)*((2:ℝ)^N)^(-f) ≤ ((2:ℝ)^N)^(-c) := by
  let q := min (lam/2) (min a (min b (min f 2)))
  have hq : 0 < q := lt_min (half_pos hlam) (lt_min ha (lt_min hb (lt_min hf (by norm_num))))
  have hql : q ≤ lam/2 := min_le_left _ _
  have hqa : q ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hqb : q ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hqf : q ≤ f := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hq2 : q ≤ 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let D : ℝ := 2+(J:ℝ)*A+(J:ℝ)+((J:ℝ)+1)
  obtain ⟨N₁,h₁⟩ := PlanarFalconer.fixed_polynomial_subpower k (half_pos hlam)
  obtain ⟨N₂,h₂⟩ := Regularization.fixed_constant_absorbed (half_pos hq) D
  refine ⟨q/2,half_pos hq,max 1 (max N₁ N₂),?_⟩
  intro N hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let R : ℝ := (2:ℝ)^N
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hp : (N:ℝ)^k ≤ R^(lam/2) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith : (N:ℝ) ≤ 4*(N:ℝ)+1) k).trans (h₁ N hN₁)
  have hpoly : (N:ℝ)^k*R^(-lam) ≤ R^(-q) := by
    calc
      _ ≤ R^(lam/2)*R^(-lam) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = R^(-(lam/2)) := by rw [← Real.rpow_add hR]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hbound : R^(-2:ℝ)+(N:ℝ)^k*R^(-lam)+
      (J:ℝ)*(A*R^(-a)+R^(-b))+((J:ℝ)+1)*R^(-f) ≤ D*R^(-q) := by
    have h2 := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hq2)
    have ha' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqa)
    have hb' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqb)
    have hf' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqf)
    calc
      _ ≤ R^(-q)+R^(-q)+(J:ℝ)*(A*R^(-q)+R^(-q))+((J:ℝ)+1)*R^(-q) := by
        gcongr
      _ = _ := by dsimp [D]; ring
  apply hbound.trans
  calc
    _ ≤ R^(q/2)*R^(-q) := mul_le_mul_of_nonneg_right (h₂ N hN₂) (by positivity)
    _ = R^(-(q/2)) := by rw [← Real.rpow_add hR]; congr 1; ring

theorem dyadic_thin_cost (N : ℕ) : ((2:ℝ≥0∞)^(2*N))⁻¹ =
    ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ)) := by
  rw [Real.rpow_neg (by positivity),Real.rpow_two,
    ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat,
    ← pow_mul,Nat.mul_comm 2 N]

theorem weak_radial_total_cost (J k : ℕ) {A lam a b f : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hf : 0 < f) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ≥0∞)^(2*N))⁻¹+(N^k:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        (J:ℝ≥0∞)*(ENNReal.ofReal (A*((2:ℝ)^N)^(-a))+ENNReal.ofReal (((2:ℝ)^N)^(-b)))+
        (J+1:ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-f)) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨c,hc,N₀,hN₀⟩ := weak_radial_total_real_cost J k hA hlam ha hb hf
  refine ⟨c,hc,N₀,fun N hN => ?_⟩
  have hh := ENNReal.ofReal_le_ofReal (hN₀ N hN)
  rw [dyadic_thin_cost]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp (disch := positivity) only [ENNReal.ofReal_add,ENNReal.ofReal_mul,
    ENNReal.ofReal_pow,ENNReal.ofReal_natCast,ENNReal.ofReal_one]
  norm_cast

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialScaleWindow
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative estimates on the retained interval of dyadic scales -/

namespace Falconer
open scoped BigOperators ENNReal

lemma radial_scale_window_half {K N : ℕ} (hK : 0 < K) (hN : 2*K ≤ N) :
    N ≤ 2*K*(N/K) := by
  have hq : 2 ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by omega)
  have hr := Nat.mod_lt N hK
  have he := Nat.div_add_mod N K
  nlinarith

lemma radial_scale_window_loss {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^N)^(a/(2*(K:ℝ))) ≤ ((2:ℝ)^j)^a := by
  have he : (N:ℝ) ≤ 2*(K:ℝ)*(j:ℝ) := by
    exact_mod_cast (radial_scale_window_half hK hN).trans (Nat.mul_le_mul_left (2*K) hj)
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ) < 2*K)).mp
  have hh := mul_le_mul_of_nonneg_right he ha
  calc
    (2*K)*((N:ℝ)*(a/(2*(K:ℝ)))) = (N:ℝ)*a := by field_simp
    _ ≤ (2*(K:ℝ)*(j:ℝ))*a := hh
    _ = (2*K)*((j:ℝ)*a) := by ring

lemma radial_scale_window_decay {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^j)^(-a) ≤ ((2:ℝ)^N)^(-(a/(2*(K:ℝ)))) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact inv_anti₀ (by positivity) (radial_scale_window_loss hK hN hj ha)

theorem radial_scale_window_cost (K : ℕ) (hK : 0 < K) {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∑ j ∈ Finset.Icc (N/K) N, ENNReal.ofReal (((2:ℝ)^j)^(-a))) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  let c : ℝ := a/(4*(K:ℝ))
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Np,hp⟩ := PlanarFalconer.fixed_polynomial_subpower 1 hc
  refine ⟨c,hc,2*K+Np,?_⟩
  intro N hN
  have hhalf : 2*K ≤ N := by omega
  have hpoly : (N:ℝ)+1 ≤ ((2:ℝ)^N)^c := by
    apply le_trans _ (hp N (by omega))
    simp only [pow_one]
    linarith [show (0:ℝ) ≤ N by positivity]
  calc
    _ ≤ ∑ _j ∈ Finset.Icc (N/K) N,
        ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ENNReal.ofReal_le_ofReal (radial_scale_window_decay hK hhalf
        (Finset.mem_Icc.mp hj).1 ha.le)
    _ = ((Finset.Icc (N/K) N).card:ℝ≥0∞)*
        ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by simp
    _ ≤ ((N:ℝ≥0∞)+1)*ENNReal.ofReal (((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      gcongr
      exact_mod_cast (show (Finset.Icc (N/K) N).card ≤ N+1 by simp)
    _ = ENNReal.ofReal (((N:ℝ)+1)*((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (by positivity) (by norm_num)]
      simp
    _ ≤ ENNReal.ofReal (((2:ℝ)^N)^c*((2:ℝ)^N)^(-(a/(2*(K:ℝ))))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpoly (by positivity))
    _ = _ := by
      rw [← Real.rpow_add (by positivity)]
      congr 2
      dsimp [c]
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialAllRadiusBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the retained dyadic scales to every cap radius -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_all_radius_bound (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (G : Set (Space d × Space d)) (N K : ℕ) {e ell ell₁ : ℝ}
    (hell : 0 ≤ ell) (hell₁ : ell ≤ ell₁) (he : 0 ≤ e) (hK : ell ≤ e*K)
    (hconst : (2:ℝ)^ell₁ ≤ ((2:ℝ)^N)^e)
    (hcap : ∀ j ∈ Finset.Icc (N/K) N, ∀ x w : Space d,
      μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^j)⁻¹} ≤
        ENNReal.ofReal (((2:ℝ)^j)^(-ell₁))) :
    ∀ x w : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤
        ENNReal.ofReal (((2:ℝ)^N)^e*r^ell) := by
  intro x w r hr hr1
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hR0 : 0 < (2:ℝ)^N := by positivity
  by_cases hs : r ≤ ((2:ℝ)^(N/K))⁻¹
  · obtain ⟨j,hjB,hjN,hjr,hrj⟩ := radial_dyadic_bracket_above N (N/K) hr hs
    have hbound := hcap j (Finset.mem_Icc.mpr ⟨hjB,hjN⟩) x w
    apply (measure_mono (show {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ⊆
      {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^j)⁻¹} from
      fun z hz => ⟨hz.1,hz.2.trans hjr⟩)).trans
    apply hbound.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      ((2:ℝ)^j)^(-ell₁) = (((2:ℝ)^j)⁻¹)^ell₁ := by rw [Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]
      _ ≤ (2*r)^ell₁ := Real.rpow_le_rpow (by positivity) hrj.le (hell.trans hell₁)
      _ = (2:ℝ)^ell₁*r^ell₁ := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ ((2:ℝ)^N)^e*r^ell := by
        apply mul_le_mul hconst (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hell₁) (by positivity) (by positivity)
  · have hb : ((2:ℝ)^(N/K))⁻¹ ≤ r := (lt_of_not_ge hs).le
    have hexp : (N/K:ℕ)*(ell:ℝ) ≤ (N:ℝ)*e := by
      have hdiv : ((N/K:ℕ):ℝ)*(K:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.div_mul_le_self N K
      calc
        _ ≤ ((N/K:ℕ):ℝ)*(e*K) := mul_le_mul_of_nonneg_left hK (by positivity)
        _ = (((N/K:ℕ):ℝ)*(K:ℝ))*e := by ring
        _ ≤ (N:ℝ)*e := mul_le_mul_of_nonneg_right hdiv he
    have hone : (1:ℝ) ≤ ((2:ℝ)^N)^e*(((2:ℝ)^(N/K))⁻¹)^ell := by
      rw [Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity),
        ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      exact Real.one_le_rpow (by norm_num) (by linarith)
    calc
      _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal (1:ℝ) := by simp
      _ ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^ell) := ENNReal.ofReal_le_ofReal
        (hone.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hell) (by positivity)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCapExtension
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cap estimate at radii above one -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_cap_extension (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (G : Set (Space d × Space d)) {δ K ell : ℝ} (hK : 1 ≤ K) (hell : 0 ≤ ell)
    (hcap : ∀ x w : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤ ENNReal.ofReal (K*r^ell)) :
    ∀ x w : Space d, ∀ r : ℝ, δ ≤ r →
      μ {z | (x,z) ∈ G ∧ dist (normalize (z-x)) w < r} ≤ ENNReal.ofReal (K*r^ell) := by
  intro x w r hr
  by_cases hr1 : r ≤ 1
  · apply (measure_mono ?_).trans (hcap x w r hr hr1)
    intro z hz
    exact ⟨hz.1,by simpa only [dist_eq_norm] using hz.2.le⟩
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hp : 1 ≤ K*r^ell := one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hr1' hell)
    exact (prob_le_one).trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialNearBallBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original pin law controls the concrete near-parent deletion -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_near_ball_bound (hd : 2 ≤ d) (ν : Measure (Space d))
    [IsProbabilityMeasure ν] (N J : ℕ) {ε : ℝ}
    (hball : ∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      ν (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^((d:ℝ)-1)))
    (hr1 : 8*(d:ℝ)/(2:ℝ)^(radialBlockSize N J) ≤ 1) (x : Space d) :
    ν (ball x (8*(d:ℝ)/(2:ℝ)^(radialBlockSize N J))) ≤
      ENNReal.ofReal ((16*(d:ℝ))^((d:ℝ)-1)*
        ((2:ℝ)^N)^(-(((d:ℝ)-1)/((J:ℝ)+2)-ε))) := by
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 ≤ (d:ℝ)-1 := by linarith
  have hR : 0 < (2:ℝ)^N := by positivity
  have hlo : ((2:ℝ)^N)⁻¹ ≤ 8*(d:ℝ)/(2:ℝ)^(radialBlockSize N J) := by
    have hh : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^(radialBlockSize N J))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.div_le_self N (J+2)))
    apply hh.trans
    have hb : (1:ℝ) ≤ 8*(d:ℝ) := by linarith
    simpa only [one_mul,div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 2^(radialBlockSize N J)))
  apply (hball x _ hlo hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hb := radial_block_radius_bound (A := 1) (by norm_num) d N J
  simp only [mul_one] at hb
  calc
    _ ≤ ((2:ℝ)^N)^ε*((16*(d:ℝ))*((2:ℝ)^N)^(-1/((J:ℝ)+2)))^((d:ℝ)-1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hs) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hR.le]
      rw [show ((2:ℝ)^N)^ε*((16*(d:ℝ))^((d:ℝ)-1)*
        ((2:ℝ)^N)^((-1/((J:ℝ)+2))*((d:ℝ)-1))) =
        (16*(d:ℝ))^((d:ℝ)-1)*(((2:ℝ)^N)^ε*
          ((2:ℝ)^N)^((-1/((J:ℝ)+2))*((d:ℝ)-1))) by ring,
        ← Real.rpow_add hR]
      congr 2
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialPinScaleBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Converting original finite-scale pin hypotheses to local radial costs -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_slab_scale_range {D η : ℝ} (hD : 1 ≤ D) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ)^N)⁻¹ ≤ D*((2:ℝ)^N)^(-η) ∧ D*((2:ℝ)^N)^(-η) ≤ 1 := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hη D
  refine ⟨N₀,fun N hN => ?_⟩
  have hR : 0 < (2:ℝ)^N := by positivity
  have hR1 : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  constructor
  · calc
      _ = ((2:ℝ)^N)^(-(1:ℝ)) := (Real.rpow_neg_one _).symm
      _ ≤ ((2:ℝ)^N)^(-η) := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
      _ ≤ D*((2:ℝ)^N)^(-η) := le_mul_of_one_le_left (by positivity) hD
  · calc
      _ ≤ ((2:ℝ)^N)^η*((2:ℝ)^N)^(-η) :=
        mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
      _ = 1 := by rw [← Real.rpow_add hR]; simp

theorem radial_pin_slab_bound (ν : Measure (Space d)) (N : ℕ)
    {ε ζ D η : ℝ} (hD : 0 ≤ D)
    (hlo : ((2:ℝ)^N)⁻¹ ≤ D*((2:ℝ)^N)^(-η))
    (hhi : D*((2:ℝ)^N)^(-η) ≤ 1)
    (hslab : ∀ w : Space d, ‖w‖ = 1 → ∀ a r : ℝ,
      ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) :
    ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ,
      ν {x | |inner ℝ w x-a| ≤ D*((2:ℝ)^N)^(-η)} ≤
        ENNReal.ofReal (D^ζ*((2:ℝ)^N)^(-(η*ζ-ε))) := by
  intro w hw a
  apply (hslab w hw a _ hlo hhi).trans_eq
  congr 1
  rw [Real.mul_rpow hD (by positivity),← Real.rpow_mul (by positivity)]
  rw [show ((2:ℝ)^N)^ε*(D^ζ*((2:ℝ)^N)^(-η*ζ)) =
    D^ζ*(((2:ℝ)^N)^ε*((2:ℝ)^N)^(-η*ζ)) by ring,
    ← Real.rpow_add (by positivity)]
  congr 2
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileTelescoping
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The profile increments telescope without a factor for initial cells -/

namespace Falconer
open scoped ENNReal BigOperators

theorem profile_loss_product_ennreal {R : ℝ} (hR : 0 < R) (m : ℕ → ℝ) (A β : ℝ) (J : ℕ) :
    (∏ j ∈ Finset.range J, ENNReal.ofReal (R^(A-β*(m (j+1)-m j)))) =
      ENNReal.ofReal (R^((J:ℝ)*A-β*(m J-m 0))) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.prod_range_succ,ih,← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
      ← Real.rpow_add hR]
    congr 2
    push_cast
    ring

theorem profile_loss_product_bound {R : ℝ} (hR : 1 ≤ R) (m : ℕ → ℝ)
    {A β s b ℓ : ℝ} (hβ : 0 ≤ β) (J : ℕ)
    (hmJ : s ≤ m J) (hm0 : m 0 ≤ b) (hgap : (J:ℝ)*A-β*(s-b) ≤ -ℓ) :
    (∏ j ∈ Finset.range J, ENNReal.ofReal (R^(A-β*(m (j+1)-m j)))) ≤
      ENNReal.ofReal (R^(-ℓ)) := by
  rw [profile_loss_product_ennreal (lt_of_lt_of_le zero_lt_one hR)]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub hmJ hm0) hβ
  linarith

theorem density_profile_factor {R : ℝ} (hR : 0 < R) (a b β u v : ℝ) :
    (ENNReal.ofReal (R^(-a)))⁻¹*ENNReal.ofReal (R^(b-β*(v-u))) =
      ENNReal.ofReal (R^(a+b-β*(v-u))) := by
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hR _),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg hR.le _)),
    ← Real.rpow_neg hR.le,neg_neg,← Real.rpow_add hR]
  congr 2
  ring

theorem profile_fraction_eq {R : ℝ} (hR : 0 < R) (e β u v : ℝ) :
    R^e/(R^(v-u))^β = R^(e-β*(v-u)) := by
  rw [← Real.rpow_mul hR.le,← Real.rpow_sub hR]
  congr 1
  ring

theorem density_profile_product_bound {R : ℝ} (hR : 1 ≤ R)
    (m : ℕ → ℝ) {a b β s t ℓ : ℝ} (hβ : 0 ≤ β) (J : ℕ)
    (hmJ : s ≤ m J) (hm0 : m 0 ≤ t)
    (hgap : (J:ℝ)*(a+b)-β*(s-t) ≤ -ℓ) :
    (∏ j ∈ Finset.range J,
      (ENNReal.ofReal (R^(-a)))⁻¹*ENNReal.ofReal (R^(b-β*(m (j+1)-m j)))) ≤
      ENNReal.ofReal (R^(-ℓ)) := by
  simp_rw [density_profile_factor (lt_of_lt_of_le zero_lt_one hR)]
  exact profile_loss_product_bound hR m hβ J hmJ hm0 hgap

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialProfileProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative telescoping for the constructed regularization profile -/

namespace Falconer.Regularization
open MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem sourceProfile_depth_upper (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    {a : ℕ} (ha : a ≤ N) : sourceProfile Q μ N B p a ≤ (d:ℝ)*(a:ℝ)/(N:ℝ) := by
  have hh := regularizedProfile_increment hN
    (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) hB p (u := 0) (v := (a:ℝ))
    le_rfl (Nat.cast_nonneg _) (Nat.cast_le.mpr ha)
  simpa only [sourceProfile,regularizedProfile_zero,sub_zero] using hh.2

theorem radial_profile_product_bound (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    (J : ℕ) {e f β s loss ℓ : ℝ} (hβ : 0 ≤ β)
    (hfinal : s-loss ≤ sourceProfile Q μ N B p N)
    (hgap : (J:ℝ)*(e+f)-β*(s-loss-
      (d:ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ))) ≤ -ℓ) :
    (∏ j ∈ Finset.range J,
      (ENNReal.ofReal (((2:ℝ)^N)^(-e)))⁻¹ *
        ENNReal.ofReal (((2:ℝ)^N)^(f-β*(
          sourceProfile Q μ N B p (radialBlockDepth N J (j+1))-
            sourceProfile Q μ N B p (radialBlockDepth N J j))))) ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-ℓ)) := by
  let m := fun j => sourceProfile Q μ N B p (radialBlockDepth N J j)
  apply density_profile_product_bound (one_le_pow₀ (by norm_num)) m hβ J
    (s := s-loss) (t := (d:ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ)))
  · simpa only [m,radialBlockDepth_final] using hfinal
  · have hh := sourceProfile_depth_upper Q μ hN hB p (radialBlockDepth_le N J (Nat.zero_le _))
    have hn := radialBlockDepth_initial_upper hN J
    exact hh.trans (by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _))
  · exact hgap

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialProfileGap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-depth error fits inside the strict weak radial profile gap -/

namespace Falconer

theorem eventually_radial_profile_gap (d J : ℕ) {e f β loss ℓ : ℝ}
    (hgap : (J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-2*(d:ℝ)/((J:ℝ)+2)) < -ℓ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N ∧
      (J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-
        (d:ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ))) ≤ -ℓ := by
  let margin := -ℓ-((J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-2*(d:ℝ)/((J:ℝ)+2)))
  have hm : 0 < margin := sub_pos.mpr hgap
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (max 1 (β*(d:ℝ)*(J:ℝ)/margin))
  refine ⟨N₀,fun N hN => ?_⟩
  have hn : (1:ℝ) < N := (le_max_left _ _).trans_lt (hN₀.trans_le (by exact_mod_cast hN))
  have hn0 : 0 < N := by exact_mod_cast (zero_lt_one.trans hn)
  have hn' : (0:ℝ) < N := zero_lt_one.trans hn
  have hr : β*(d:ℝ)*(J:ℝ)/margin < (N:ℝ) :=
    (le_max_right _ _).trans_lt (hN₀.trans_le (by exact_mod_cast hN))
  have hb : β*(d:ℝ)*(J:ℝ)/(N:ℝ) < margin := by
    apply (div_lt_iff₀ hn').mpr
    have hh := (div_lt_iff₀ hm).mp hr
    nlinarith
  refine ⟨hn0,?_⟩
  have he : (J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-
      (d:ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ))) =
      ((J:ℝ)*(e+f)-β*((d:ℝ)-1-loss-2*(d:ℝ)/((J:ℝ)+2)))+
        β*(d:ℝ)*(J:ℝ)/(N:ℝ) := by ring
  rw [he]
  dsimp [margin] at hb
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialRegularClasses
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual radial regularization classes from the finite-scale ball hypothesis -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem radial_regular_classes (hd : 2 ≤ d) (Q : DyadicCube d) (hQ : Q.side = 1)
    {ε lam : ℝ} (hε : 0 ≤ ε) (hεlam : ε < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧
      (∀ N ≥ N₀, 0 < N ∧ 0 < N/H ∧ ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧
        (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam) ∧ ∀ N ≥ N₀,
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], μ Q.carrierᶜ = 0 →
      (∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^((d:ℝ)-1))) →
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves Q μ N
      let F := regularizationLabel Q μ N B
      (regularizationIndex Q μ N B t).card ≤ N^(4*H+2) ∧
      μ (⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T)ᶜ ≤
        ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*t ∧
      ∀ T ∈ regularizationIndex Q μ N B t,
        t ≤ classMeasure Q μ L F T univ ∧
        ∃ p ∈ regularizationLeaves Q μ N, regularizationLabel Q μ N B p = T ∧
          RegularizedProfileData Q (normalizedClass Q μ L F T)
            N ((d:ℝ)-1) lam (sourceUnitProfile Q μ N B p) := by
  have hlam : 0 < lam := hε.trans_lt hεlam
  have hs : 0 ≤ (d:ℝ)-1 := by
    have hh : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  obtain ⟨H,N₁,hH,hHb,hscales⟩ := PlanarFalconer.exists_bounded_regularization_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed (sub_pos.mpr hεlam) ((2*Real.sqrt d)^((d:ℝ)-1))
  obtain ⟨N₃,hN₃⟩ := exists_nat_gt ((d:ℝ)/lam)
  refine ⟨H,max (max H (d+3)) (max N₁ (max N₂ N₃)),hH,hHb,?_,?_⟩
  · intro N hN
    have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hh := hscales N hN₁
    exact ⟨hh.1,hh.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
  intro N hN μ _ hcarry hball
  dsimp only
  have hNH : H ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hdN : d+3 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN₃' : N₃ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hscale := hscales N hN₁
  have hsmall : ((d:ℝ)-1)/(N:ℝ) ≤ lam := by
    apply (div_le_iff₀ (by exact_mod_cast hscale.1 : 0 < (N:ℝ))).mpr
    have hh : (d:ℝ)/lam < (N:ℝ) := hN₃.trans_le (by exact_mod_cast hN₃')
    have hh' := (div_lt_iff₀ hlam).mp hh
    nlinarith
  have hcell : ∀ j ≤ N, ∀ P : CellPath d, P.length = j →
      (μ (Q.descendant P).carrier).toReal ≤
        ((2:ℝ)^N)^lam*((2:ℝ)^N)^(-((d:ℝ)-1)*(j:ℝ)/(N:ℝ)) := by
    intro j hj P hP
    have hh := dyadic_scale_cell_bound (by omega : 0 < d) Q hQ μ hscale.1 hε hs hball hj P hP
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (((2:ℝ)^N)^(lam-ε))*(((2:ℝ)^N)^ε) :=
        mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  refine ⟨regularization_count_polynomial Q μ hH hNH hdN _,
    regularization_discarded_global Q hside μ hcarry hH hNH hdN _,?_⟩
  intro T hT
  refine ⟨(Finset.mem_filter.mp hT).2,?_⟩
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
  subst T
  refine ⟨p,hp,rfl,?_⟩
  apply sourceClass_profile_data Q hside μ hscale.1 hscale.2.1 hs hsmall
    hscale.2.2.2.1 hscale.2.2.2.2 hp
  intro j hj
  exact sourceProfile_frostman_lower Q hside μ hscale.1 hscale.2.1
    hscale.2.2.2.1 hscale.2.2.2.2 hp (retained_label_real_mass_lower Q μ hT) hcell hj

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialRemoveDiagonal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the diagonal from an actual radial pair set -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_remove_diagonal (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (G : Set (Space d × Space d)) (hG : MeasurableSet G) {r : ℝ} (hr : 0 ≤ r)
    (C : ℝ≥0∞)
    (hcap : ∀ x w : Space d, μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤ C) :
    ∃ H : Set (Space d × Space d), MeasurableSet H ∧ H ⊆ G ∧
      (∀ x : Space d, (x,x) ∉ H) ∧ (μ.prod μ) Hᶜ ≤ (μ.prod μ) Gᶜ+C := by
  let D : Set (Space d × Space d) := {p | p.1 = p.2}
  have hD : MeasurableSet D := measurableSet_eq_fun measurable_fst measurable_snd
  have hbound : (μ.prod μ) (G ∩ D) ≤ C := by
    rw [Measure.prod_apply (hG.inter hD)]
    calc
      _ ≤ ∫⁻ _x, C ∂μ := lintegral_mono (fun x => by
        apply (measure_mono ?_).trans (hcap x 0)
        rintro z ⟨hz,hz'⟩
        have hxz : x = z := hz'
        refine ⟨hz,?_⟩
        rw [← hxz,sub_self,normalize_zero_eq_zero,sub_self,norm_zero]
        exact hr)
      _ = C := by simp
  refine ⟨G \ D,hG.diff hD,sdiff_subset,?_,?_⟩
  · intro x hx
    exact hx.2 rfl
  · have hs : (G \ D)ᶜ ⊆ Gᶜ ∪ (G ∩ D) := by
      intro p hp
      by_cases hg : p ∈ G
      · exact Or.inr ⟨hg,by simpa only [mem_compl_iff,mem_sdiff,hg,true_and,not_not] using hp⟩
      · exact Or.inl hg
    exact (measure_mono hs).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbound))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RegularizationRadialGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recombining the actual radial regularization classes without a class-count loss -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem normalized_regularization_class_eq_cond (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (T : List ℕ) :
    normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T =
      ProbabilityTheory.cond μ (regularizationSet Q μ N B T) := by
  unfold normalizedClass classMeasure ProbabilityTheory.cond regularizationSet
  rw [Measure.restrict_apply_univ]

theorem regularization_radial_gain (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hroot : μ Q.carrierᶜ = 0) {N H : ℕ} (hH : 0 < H) (hNH : H ≤ N) (hdN : d+3 ≤ N)
    {threshold : ℝ≥0∞} (hthreshold : 0 < threshold) (t C : ℝ≥0∞) (r : ℝ)
    (hlocal : ∀ T ∈ regularizationIndex Q μ N (N/H) threshold,
      ∃ G : Set (Space d × Space d), MeasurableSet G ∧
        (ν.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) Gᶜ ≤ t ∧
        ∀ x u : Space d,
          normalizedClass Q μ (regularizationLeaves Q μ N)
            (regularizationLabel Q μ N (N/H)) T
            {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (ν.prod μ) Gᶜ ≤ ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*threshold+t ∧
      ∀ x u : Space d, μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C := by
  classical
  let I := regularizationIndex Q μ N (N/H) threshold
  let S := regularizationSet Q μ N (N/H)
  have hex : ∀ T : List ℕ, ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (T ∈ I → (ν.prod (ProbabilityTheory.cond μ (S T))) Gᶜ ≤ t ∧
        ∀ x u : Space d, ProbabilityTheory.cond μ (S T)
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ r} ≤ C) := by
    intro T
    by_cases hT : T ∈ I
    · obtain ⟨G,hm,hc,hg⟩ := hlocal T hT
      rw [normalized_regularization_class_eq_cond] at hc hg
      exact ⟨G,hm,fun _ => ⟨hc,hg⟩⟩
    · exact ⟨∅,MeasurableSet.empty,fun h => (hT h).elim⟩
  choose G hm hg using hex
  have hpos : ∀ T ∈ I, μ (S T) ≠ 0 := by
    intro T hT
    exact (hthreshold.trans_le (regularizationSet_mass Q μ N (N/H) threshold hT)).ne'
  have hdisj : (I : Set (List ℕ)).PairwiseDisjoint S := by
    intro T _ U _ hTU
    exact regularizationSet_disjoint Q hQ μ N (N/H) hTU
  obtain ⟨G',hG',hc,hcap⟩ := classwise_radial_gain μ ν I S G
    (fun T _ => regularizationSet_measurable Q μ N (N/H) T) (fun T _ => hm T)
    hpos hdisj t C r (fun T hT => (hg T hT).1) (fun T hT => (hg T hT).2)
  refine ⟨G',hG',hc.trans (add_le_add ?_ le_rfl),hcap⟩
  exact regularization_discarded_global Q hQ μ hroot hH hNH hdN threshold

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SingleClassRadialGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-scale radial gain for an actual regularization class -/

namespace Falconer.Regularization
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem single_class_radial_gain (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (Q : DyadicCube (n+1)) (hQ : Q.side = 1)
    (J : ℕ) (hJ : 0 < J) (L : ℕ)
    {e f τ η lam u v c Cp Bs Bp C : ℝ}
    (hη : 0 ≤ η) (hCp : 0 ≤ Cp) (hBs : 0 ≤ Bs) (hBp : 0 ≤ Bp)
    (hτ : 2*(((n+1:ℕ):ℝ)+1)*lam < τ)
    (hcount : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u)
    (hu : c*((n+1:ℕ):ℝ) < u) (hv : c*((n+1:ℕ):ℝ) < v)
    (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (hC : Real.sqrt (n+1:ℕ)+2*(Bs+Bp) ≤ C)
    (P : Set (Space (n+1))) (hP : MeasurableSet P)
    (hPb : ∀ x ∈ P, ‖x‖ ≤ Bp) (hQb : ∀ z ∈ Q.carrier, ‖z‖ ≤ Bs) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ν Pᶜ = 0 → ∀ B : ℕ, 0 < B →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ loss ℓ : ℝ,
      (n:ℝ)-loss ≤ sourceProfile Q μ N B p₀ N →
      (J:ℝ)*(e+f)-((n:ℝ)/(n+1))*((n:ℝ)-loss-
        ((n+1:ℕ):ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ))) ≤ -ℓ →
      ∀ K : ℝ≥0∞,
      (∀ x : Space (n+1), ν (ball x (8*((n+1:ℕ):ℝ)/(2:ℝ)^(radialBlockSize N J))) ≤ K) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a : ℝ,
        ν {x | |inner ℝ w x-a| ≤ (Bs+Bp)*((2:ℝ)^N)^(-η)} ≤
          ENNReal.ofReal (Cp*((2:ℝ)^N)^(-v))) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (ν.prod (sourceClass Q μ N B p₀)) Gᶜ ≤
          (J:ℝ≥0∞)*(K+ENNReal.ofReal (((2:ℝ)^N)^(-c)))+
            (J+1:ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-f)) ∧
        ∀ x w : Space (n+1), sourceClass Q μ N B p₀
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^N)⁻¹} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-ℓ)) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  obtain ⟨N₁,hsmall⟩ := regular_class_small_troublesome hLW hn L hη hCp hτ hcount hu hv
  refine ⟨max 1 N₁,?_⟩
  intro N hN μ ν _ _ hPfull B hB hwidth hlarge p₀ hp₀ loss ℓ hfinal hgap K hball hslab
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : 0 < 1) ((le_max_left _ _).trans hN)
  have hNN : N₁ ≤ N := (le_max_right _ _).trans hN
  let ρ := sourceClass Q μ N B p₀
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hside μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  let depth := radialBlockDepth N J
  let r : ℝ := 8*((n+1:ℕ):ℝ)/(2:ℝ)^(radialBlockSize N J)
  let F := fun j => R^e/(R^(sourceProfile Q μ N B p₀ (depth (j+1))-
    sourceProfile Q μ N B p₀ (depth j)))^((n:ℝ)/(n+1))
  have hgeom (j : ℕ) :
      Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth j) < r ∧
      8*(Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth j))^2/r ≤ Q.side/(2:ℝ)^depth (j+1) := by
    have hh := dyadic_reserved_block_freezing (by omega : 0 < n+1)
      (by norm_num : (0:ℝ) < 1) (radialBlockDepth_two_blocks N J j)
    simpa only [hQ,one_mul,mul_one,depth,r,radialBlockDepth_step] using hh
  have hwidth' (j : ℕ) (hj : j < J) :
      Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth (j+1))+2*(Bs+Bp)*R⁻¹ ≤
        C*(Q.side/(2:ℝ)^depth (j+1)) := by
    have hs : R⁻¹ ≤ Q.side/(2:ℝ)^depth (j+1) := by
      rw [hQ,one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num)
        (radialBlockDepth_le N J (by omega)))
    calc
      _ ≤ Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth (j+1))+
          2*(Bs+Bp)*(Q.side/(2:ℝ)^depth (j+1)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by positivity))
      _ = (Real.sqrt (n+1:ℕ)+2*(Bs+Bp))*(Q.side/(2:ℝ)^depth (j+1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)
  have htrouble : ∀ j < J, ∀ p ∈ Q.occupiedPaths ρ (depth j),
      ((ProbabilityTheory.cond ρ (Q.descendant p).carrier).prod ν)
        (troublesomePair (ProbabilityTheory.cond ρ (Q.descendant p).carrier)
          (Q.descendant p).center r (Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^depth j)) Bs
          (C*(Q.side/(2:ℝ)^depth (j+1))) (ENNReal.ofReal (F j))) ≤ ENNReal.ofReal (R^(-c)) := by
    intro j hj p hp
    have hR : ∀ᵐ x ∂ν, ‖(Q.descendant p).center-x‖ ≤ Bs+Bp := by
      have hpae : ∀ᵐ x ∂ν, x ∈ P := ae_iff.mpr hPfull
      filter_upwards [hpae] with x hx
      exact (norm_sub_le _ _).trans (add_le_add
        (hQb _ (Q.descendant_subset p ((Q.descendant p).center_mem (Q.descendant_side_pos hside p))))
        (hPb x hx))
    have hr : 0 < r := by dsimp [r]; positivity
    exact hsmall N hNN Q hside μ ν B hB hwidth hlarge p₀ hp₀ (depth j) (depth (j+1))
      (radialBlockDepth_le N J hj.le) (radialBlockDepth_le N J (by omega)) p
      ((mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1) (Finset.mem_filter.mp hp).2
      r C Bs (Bs+Bp) hr hL (hgeom j).2 hR (fun w hw => hslab w hw _)
  obtain ⟨G,hG,hcost,hcap⟩ := dyadic_radial_pruning ρ ν Q hside
    (sourceClass_root_null Q hside μ N B p₀) N J hJ depth
    (fun j hj => radialBlockDepth_le N J hj)
    (fun j _ => radialBlockDepth_mono N J (Nat.le_succ j)) (fun _ => r)
    (fun j => C*(Q.side/(2:ℝ)^depth (j+1))) Bs Bp R⁻¹
    (fun j => ENNReal.ofReal (F j)) (fun _ => K) (fun _ => ENNReal.ofReal (R^(-c)))
    P hP hPfull hPb hQb (fun j _ => (hgeom j).1) hwidth'
    (fun _ _ _ _ => hball _) htrouble (ENNReal.ofReal (R^(-f)))
    (by dsimp [R]; positivity) ENNReal.ofReal_ne_top
  refine ⟨G,hG,?_,?_⟩
  · simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,R] using hcost
  · intro x w
    apply (hcap x w).trans
    have hR : 0 < R := by dsimp [R]; positivity
    simp only [F,profile_fraction_eq hR]
    apply radial_profile_product_bound Q μ hNpos hB p₀ J (by positivity) hfinal
    simpa only [add_comm e f] using hgap

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialCapParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed block and density losses below the weak radial exponent -/

namespace Falconer

theorem weak_radial_cap_parameters (d : ℕ) {β ℓ : ℝ}
    (hβ : 0 < β) (hℓ : ℓ < β*((d:ℝ)-1)) :
    ∃ J : ℕ, 0 < J ∧ ∃ e f L : ℝ, 0 < e ∧ 0 < f ∧ 0 < L ∧
      (J:ℝ)*(e+f)-β*((d:ℝ)-1-2*(d:ℝ)/((J:ℝ)+2)-L) < -ℓ := by
  let gap := β*((d:ℝ)-1)-ℓ
  have hg : 0 < gap := sub_pos.mpr hℓ
  obtain ⟨J,hJ⟩ := exists_nat_gt (max 1 (8*β*(d:ℝ)/gap))
  have hJ1 : (1:ℝ) < J := (le_max_left _ _).trans_lt hJ
  have hJpos : 0 < J := by exact_mod_cast (zero_lt_one.trans hJ1)
  have hJden : (0:ℝ) < (J:ℝ)+2 := by positivity
  have hJB : 8*β*(d:ℝ)/gap < (J:ℝ)+2 := by
    have hh := (le_max_right _ _).trans_lt hJ
    linarith
  have hignored : β*(2*(d:ℝ)/((J:ℝ)+2)) < gap/4 := by
    have hh := (div_lt_iff₀ hg).mp hJB
    apply (lt_div_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    rw [show β*(2*(d:ℝ)/((J:ℝ)+2))*4 = (8*β*(d:ℝ))/((J:ℝ)+2) by ring]
    apply (div_lt_iff₀ hJden).mpr
    nlinarith
  let e := gap/(16*((J:ℝ)+1))
  let f := e
  let L := gap/(4*β)
  have he : 0 < e := by dsimp [e]; positivity
  have hf : 0 < f := he
  have hL : 0 < L := by dsimp [L]; positivity
  have hef : ((J:ℝ)+1)*(e+f) = gap/8 := by
    dsimp [e,f]
    field_simp
    ring
  have hsum : (J:ℝ)*(e+f) ≤ gap/4 := by nlinarith
  have hloss : β*L = gap/4 := by dsimp [L]; field_simp
  refine ⟨J,hJpos,e,f,L,he,hf,hL,?_⟩
  dsimp [gap] at hg hignored hsum hloss
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialLosses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous fixed losses for the single-scale weak radial theorem -/

namespace Falconer

theorem exists_weak_radial_losses {n : ℕ} (hn : 1 ≤ n) {ℓ ζ : ℝ}
    (hζ : 0 < ζ) (hℓ : ℓ < ((n:ℝ)/(n+1))*(n:ℝ)) :
    Nonempty (WeakRadialLosses n ℓ ζ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hβ : 0 < (n:ℝ)/(n+1) := div_pos hn0 hd
  obtain ⟨J,hJ,e,f,L,he,hf,hL,hcap⟩ := weak_radial_cap_parameters (n+1) hβ
    (by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hℓ)
  obtain ⟨η,τ,u,ε₀,hη,hηle,hτ,hu,hε₀,hcount,hslab⟩ := weak_radial_bounded_exponents hn he hζ
  let lam : ℝ := min (L/(4*((n:ℝ)+5))) (τ/(4*((n:ℝ)+2)))
  have hlam : 0 < lam := lt_min (by positivity) (by positivity)
  have hlamL : ((n:ℝ)+5)*lam < L := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*((n:ℝ)+5))).mp
      (min_le_left (L/(4*((n:ℝ)+5))) (τ/(4*((n:ℝ)+2))))
    change lam*(4*((n:ℝ)+5)) ≤ L at hh
    nlinarith
  have hlamτ : 2*((n:ℝ)+2)*lam < τ := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*((n:ℝ)+2))).mp
      (min_le_right (L/(4*((n:ℝ)+5))) (τ/(4*((n:ℝ)+2))))
    change lam*(4*((n:ℝ)+2)) ≤ τ at hh
    nlinarith
  let ε : ℝ := min (lam/2) (min ε₀ ((n:ℝ)/(4*((J:ℝ)+2))))
  have hε : 0 < ε := lt_min (by positivity) (lt_min hε₀ (by positivity))
  have hEpsLam : ε < lam := (min_le_left _ _).trans_lt (by linarith : lam/2 < lam)
  have hεold : ε ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hεnear : ε < (n:ℝ)/((J:ℝ)+2) := by
    have hh : ε ≤ (n:ℝ)/(4*((J:ℝ)+2)) := (min_le_right _ _).trans (min_le_right _ _)
    have hq : 0 < (n:ℝ)/((J:ℝ)+2) := by positivity
    have heq : (n:ℝ)/(4*((J:ℝ)+2)) = ((n:ℝ)/((J:ℝ)+2))/4 := by
      field_simp
    rw [heq] at hh
    linarith
  let c : ℝ := u/(2*((n:ℝ)+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcd : c*((n:ℝ)+1) = u/2 := by dsimp [c]; field_simp
  refine ⟨⟨J,e,f,τ,η,lam,u,ε,c,hJ,he,hf,hη,hηle,hlam,hu,hε,hc,hEpsLam,
    hlamτ,hcount,?_,?_,hεnear,?_⟩⟩
  · rw [hcd]
    linarith
  · rw [hcd]
    linarith
  · have hm := mul_lt_mul_of_pos_left hlamL hβ
    norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hcap
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SingleScaleWeakRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-scale weak radial theorem in every dimension -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open Regularization
open scoped ENNReal
variable {n : ℕ}

theorem single_scale_weak_radial (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    {ζ ℓ : ℝ} (hζ : 0 < ζ) (hℓ : ℓ < ((n:ℝ)/(n+1))*(n:ℝ))
    (Q : DyadicCube (n+1)) (hQ : Q.side = 1) {M : ℝ} (hM : 1 ≤ M)
    (hbounded : ∀ x ∈ Q.carrier, ‖x‖ ≤ M) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ], μ Q.carrierᶜ = 0 →
      (∀ x : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^(n:ℝ))) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x w : Space (n+1), μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^N)⁻¹} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-ℓ)) := by
  obtain ⟨p⟩ := exists_weak_radial_losses hn hζ hℓ
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  let C : ℝ := Real.sqrt (n+1:ℕ)+4*M
  let L : ℕ := Nat.ceil (C+1+((n+1:ℕ):ℝ)+1/2)
  have hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) := Nat.le_ceil _
  have hC : Real.sqrt (n+1:ℕ)+2*(M+M) ≤ C := by dsimp [C]; linarith
  have hτ : 2*(((n+1:ℕ):ℝ)+1)*p.lam < p.τ := by
    convert p.regularization_gap using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  have hu : p.c*((n+1:ℕ):ℝ) < p.u := by
    simpa only [Nat.cast_add,Nat.cast_one] using p.incidence_gap
  have hv : p.c*((n+1:ℕ):ℝ) < p.η*ζ-p.ε := by
    simpa only [Nat.cast_add,Nat.cast_one] using p.slab_gap
  obtain ⟨Ns,hgain⟩ := single_class_radial_gain hLW hn Q hQ p.J p.J_pos L
    (e := p.e) (f := p.f) (τ := p.τ) (η := p.η) (lam := p.lam) (u := p.u)
    (v := p.η*ζ-p.ε) (c := p.c) (Cp := (2*M)^ζ) (Bs := M) (Bp := M) (C := C)
    p.η_pos.le (by positivity) hM0 hM0 hτ p.count_gap hu hv hL hC
    Q.carrier Q.measurable hbounded hbounded
  obtain ⟨H,Nr,hH,_,hcontrol,hclasses⟩ := radial_regular_classes (by omega : 2 ≤ n+1)
    Q hQ p.ε_pos.le p.ε_lt_lam
  have hcapgap : (p.J:ℝ)*(p.e+p.f)-((n:ℝ)/(n+1))*
      (((n+1:ℕ):ℝ)-1-((n:ℝ)+5)*p.lam-2*((n+1:ℕ):ℝ)/((p.J:ℝ)+2)) < -ℓ := by
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using p.cap_gap
  obtain ⟨Ng,hgap⟩ := eventually_radial_profile_gap (n+1) p.J hcapgap
  obtain ⟨Nb,hnear⟩ := eventually_radial_block_radius_le_one (A := 1) (by norm_num) (n+1) p.J
  have hD : (1:ℝ) ≤ 2*M := by linarith
  obtain ⟨Nl,hslabrange⟩ := radial_slab_scale_range hD p.η_pos (p.η_le.trans (by norm_num))
  let A : ℝ := (16*((n+1:ℕ):ℝ))^(n:ℝ)
  have ha : 0 < (n:ℝ)/((p.J:ℝ)+2)-p.ε := sub_pos.mpr p.near_gap
  obtain ⟨c,hc,Nc,hcost⟩ := weak_radial_total_cost p.J (4*H+2) (A := A)
    (by dsimp [A]; positivity) p.lam_pos ha p.c_pos p.f_pos
  refine ⟨p.ε,c,p.ε_pos,hc,Ns+Nr+Ng+Nb+Nl+Nc+H+(n+4)+1,?_⟩
  intro N hN μ _ hroot hball hslab
  have hNs : Ns ≤ N := by omega
  have hNr : Nr ≤ N := by omega
  have hNg : Ng ≤ N := by omega
  have hNb : Nb ≤ N := by omega
  have hNl : Nl ≤ N := by omega
  have hNc : Nc ≤ N := by omega
  have hNH : H ≤ N := by omega
  have hdN : (n+1)+3 ≤ N := by omega
  obtain ⟨hNpos,hB,hwidth,hlarge⟩ := hcontrol N hNr
  let R : ℝ := (2:ℝ)^N
  let K : ℝ≥0∞ := ENNReal.ofReal (A*R^(-((n:ℝ)/((p.J:ℝ)+2)-p.ε)))
  let t : ℝ≥0∞ := (p.J:ℝ≥0∞)*(K+ENNReal.ofReal (R^(-p.c)))+
    (p.J+1:ℝ≥0∞)*ENNReal.ofReal (R^(-p.f))
  have hball' : ∀ x : Space (n+1), ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (R^p.ε*r^(((n+1:ℕ):ℝ)-1)) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hball
  have hnear' : ∀ x : Space (n+1),
      μ (ball x (8*((n+1:ℕ):ℝ)/(2:ℝ)^(radialBlockSize N p.J))) ≤ K := by
    intro x
    have hh := radial_near_ball_bound (by omega : 2 ≤ n+1) μ N p.J hball'
      (by simpa only [mul_one] using hnear N hNb) x
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,A,K,R] using hh
  have hslab' : ∀ w : Space (n+1), ‖w‖ = 1 → ∀ a : ℝ,
      μ {x | |inner ℝ w x-a| ≤ (M+M)*R^(-p.η)} ≤
        ENNReal.ofReal ((2*M)^ζ*R^(-(p.η*ζ-p.ε))) := by
    have hh := radial_pin_slab_bound μ N (show 0 ≤ 2*M by positivity)
      (hslabrange N hNl).1 (hslabrange N hNl).2 hslab
    simpa only [two_mul,R] using hh
  have hreg := hclasses N hNr μ hroot hball'
  have hlocal : ∀ T ∈ regularizationIndex Q μ N (N/H) (ENNReal.ofReal (R^(-p.lam))),
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (μ.prod (normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T)) Gᶜ ≤ t ∧
        ∀ x w : Space (n+1), normalizedClass Q μ (regularizationLeaves Q μ N)
          (regularizationLabel Q μ N (N/H)) T
          {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ R⁻¹} ≤ ENNReal.ofReal (R^(-ℓ)) := by
    intro T hT
    obtain ⟨_,p₀,hp₀,he,hprof⟩ := hreg.2.2 T hT
    have hm := hprof.envelope (1:ℝ) (by constructor <;> norm_num)
    have heq := sourceUnitProfile_at_depth Q μ hNpos (N/H) p₀ N
    rw [div_self (by exact_mod_cast hNpos.ne' : (N:ℝ) ≠ 0)] at heq
    rw [heq] at hm
    have hfinal : (n:ℝ)-((n:ℝ)+5)*p.lam ≤ sourceProfile Q μ N (N/H) p₀ N := by
      simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,mul_one] at hm
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hg := (hgap N hNg).2
    obtain ⟨G,hG,hcostG,hcapG⟩ := hgain N hNs μ μ hroot (N/H) hB hwidth hlarge p₀ hp₀
      (((n:ℝ)+5)*p.lam) ℓ hfinal
      (by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hg)
      K hnear' hslab'
    refine ⟨G,hG,?_,?_⟩
    · simpa only [sourceClass,he,t,R] using hcostG
    · simpa only [sourceClass,he,R] using hcapG
  obtain ⟨G,hG,hgc,hgcaps⟩ := regularization_radial_gain Q (by rw [hQ]; norm_num) μ μ
    hroot hH hNH hdN (threshold := ENNReal.ofReal (R^(-p.lam))) (by dsimp [R]; positivity)
    t (ENNReal.ofReal (R^(-ℓ))) R⁻¹ hlocal
  refine ⟨G,hG,hgc.trans ?_,hgcaps⟩
  simpa only [t,K,R,add_assoc] using hcost N hNc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weak radial estimate in every dimension, at finite dyadic scales

This is Lemma `ang:weak-radial` of the manuscript, with the bounded support
specified by a unit dyadic cube. The only published input here is the finite
coordinate form of Loomis--Whitney. All pair deletions use the original law.
-/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem weak_radial (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    {ζ ell e : ℝ} (hζ : 0 < ζ) (hell0 : 0 ≤ ell)
    (hell : ell < ((n:ℝ)/(n+1))*(n:ℝ)) (he : 0 < e)
    (Q : DyadicCube (n+1)) (hQ : Q.side = 1) {M : ℝ} (hM : 1 ≤ M)
    (hbounded : ∀ x ∈ Q.carrier, ‖x‖ ≤ M) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ], μ Q.carrierᶜ = 0 →
      (∀ x : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^(n:ℝ))) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (∀ x : Space (n+1), (x,x) ∉ G) ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x w : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
          μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^e*r^ell) := by
  classical
  obtain ⟨ell₁,hell₁,hupper⟩ := exists_between hell
  have hell₁0 : 0 < ell₁ := lt_of_le_of_lt hell0 hell₁
  obtain ⟨eps,cs,heps,hcs,Ns,hs⟩ := single_scale_weak_radial hLW hn hζ hupper Q hQ hM hbounded
  obtain ⟨K₀,hK₀⟩ := exists_nat_gt (ell/e)
  let K := K₀+1
  have hK : 0 < K := by dsimp [K]; omega
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hKell : ell ≤ e*(K:ℝ) := by
    have hh := (div_lt_iff₀ he).mp hK₀
    dsimp [K]
    push_cast
    nlinarith
  obtain ⟨cw,hcw,Nw,hw⟩ := radial_scale_window_cost K hK hcs
  let c := min cw ell₁/2
  have hc : 0 < c := half_pos (lt_min hcw hell₁0)
  have hccw : c < cw := by dsimp [c]; have := min_le_left cw ell₁; linarith
  have hcell : c < ell₁ := by dsimp [c]; have := min_le_right cw ell₁; linarith
  obtain ⟨Nc,hcost⟩ := weak_radial_two_costs (A := 1) (B := 1)
    (by norm_num) (by norm_num) hccw hcell
  obtain ⟨Nf,hfixed⟩ := Regularization.fixed_constant_absorbed he ((2:ℝ)^ell₁)
  refine ⟨eps/(2*(K:ℝ)),c,by positivity,hc,2*K+K*Ns+Nw+Nc+Nf,?_⟩
  intro N hN μ _ hroot hball hslab
  have hNhalf : 2*K ≤ N := by omega
  have hNs : Ns ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by nlinarith)
  let I := Finset.Icc (N/K) N
  have hex : ∀ j : ℕ, ∃ G : Set (Space (n+1) × Space (n+1)), j ∈ I →
      MeasurableSet G ∧ (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^j)^(-cs)) ∧
      ∀ x w : Space (n+1), μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^j)⁻¹} ≤
        ENNReal.ofReal (((2:ℝ)^j)^(-ell₁)) := by
    intro j
    by_cases hj : j ∈ I
    · obtain ⟨hjB,hjN⟩ := Finset.mem_Icc.mp hj
      have hloss := radial_scale_window_loss hK hNhalf hjB heps.le
      have hradii : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^j)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hjN)
      obtain ⟨G,hG,hcostG,hcapG⟩ := hs j (hNs.trans hjB) μ hroot
        (fun x r hr hr1 => (hball x r (hradii.trans hr) hr1).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
        (fun w hw a r hr hr1 => (hslab w hw a r (hradii.trans hr) hr1).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
      exact ⟨G,fun _ => ⟨hG,hcostG,hcapG⟩⟩
    · exact ⟨∅,fun h => (hj h).elim⟩
  choose G hG using hex
  obtain ⟨H,hH,hcostH,hcapH⟩ := finite_radial_scale_intersection μ μ I G
    (fun j => ENNReal.ofReal (((2:ℝ)^j)^(-cs)))
    (fun j => ENNReal.ofReal (((2:ℝ)^j)^(-ell₁))) (fun j => ((2:ℝ)^j)⁻¹)
    (fun j hj => (hG j hj).1) (fun j hj => (hG j hj).2.1) (fun j hj => (hG j hj).2.2)
  have hNI : N ∈ I := Finset.mem_Icc.mpr ⟨Nat.div_le_self N K,le_rfl⟩
  obtain ⟨H',hH',hsub,hdiag,hcostH'⟩ := radial_remove_diagonal μ H hH (by positivity)
    (ENNReal.ofReal (((2:ℝ)^N)^(-ell₁))) (hcapH N hNI _ le_rfl)
  refine ⟨H',hH',hdiag,hcostH'.trans ?_,?_⟩
  · apply (add_le_add (hcostH.trans (hw N (by omega))) le_rfl).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hcost N (by omega))
  · have hcap' := radial_all_radius_bound μ H N K hell0 hell₁.le he.le hKell
      (hfixed N (by omega)) (fun j hj => hcapH j hj _ le_rfl)
    intro x w r hr hr1
    apply (measure_mono ?_).trans (hcap' x w r hr hr1)
    exact fun z hz => ⟨hsub hz.1,hz.2⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_SmallChartWeakRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak radial pruning on the actual small chart law -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem small_chart_weak_radial_oai (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    {ζ ell e : ℝ} (hζ : 0 < ζ) (hell0 : 0 ≤ ell)
    (hell : ell < ((n:ℝ)/(n+1))*(n:ℝ)) (he : 0 < e) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space (n+1))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space (n+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^(n:ℝ))) →
      (∀ w : Space (n+1), ‖w‖ = 1 → ∀ a r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-a| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space (n+1) × Space (n+1)), MeasurableSet G ∧
        (∀ p z, (p,z) ∈ G → z ≠ p) ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space (n+1),
          μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
            ENNReal.ofReal (((2:ℝ)^N)^e*(3*(1/(2:ℝ)^j))^ell) := by
  obtain ⟨ε,c,hε,hc,N₀,hN₀⟩ := weak_radial hLW hn hζ hell0 hell he
    (smallChartCube (n+1)) (smallChartCube_side _) (M := Real.sqrt (n+1:ℕ)+1)
    (by nlinarith [Real.sqrt_nonneg (n+1:ℕ)]) (fun _ hx => smallChartCube_norm hx)
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN μ _ hμ hball hslab
  obtain ⟨G,hG,hdiag,hcost,hcap⟩ := hN₀ N hN μ (smallChartCube_full μ hμ) hball hslab
  have hext := radial_cap_extension μ G (Real.one_le_rpow (one_le_pow₀ (by norm_num)) he.le) hell0 hcap
  refine ⟨G,hG,?_,hcost,?_⟩
  · intro p z hp hz
    subst z
    exact hdiag p hp
  · intro p j hj u
    apply hext
    have hh : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^j)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hj)
    simpa only [one_div] using hh.trans (show ((2:ℝ)^j)⁻¹ ≤ 3*((2:ℝ)^j)⁻¹ by linarith [show (0:ℝ) ≤ ((2:ℝ)^j)⁻¹ by positivity])

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.small_chart_weak_radial_oai := @OAI.Falconer.small_chart_weak_radial_oai
