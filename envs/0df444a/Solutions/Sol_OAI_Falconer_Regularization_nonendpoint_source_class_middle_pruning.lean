-- Prove2me | solution 1 for OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:57:13.909789+00:00
-- url     : https://prove2.me/submissions/143a2000-3dbc-4619-bcbe-0a8eb7a20a87

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_controlled_dyadic_angular_gain

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_Potential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem finiteMin_le {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteMin s f ≤ f i := by
  rw [finiteMin, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le f hi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_Ledger
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem intervalMin_attained (A : ℕ → ℝ) {a t : ℕ} (hat : a ≤ t) :
    ∃ i, a ≤ i ∧ i ≤ t ∧ intervalMin A a t = A i := by
  have hn : (Finset.Icc a t).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl,hat⟩⟩
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hn A
  exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
    by simpa only [intervalMin, finiteMin, dite_eq_left hn] using he⟩

theorem intervalMin_le (A : ℕ → ℝ) {a t i : ℕ} (hai : a ≤ i) (hit : i ≤ t) :
    intervalMin A a t ≤ A i := finiteMin_le A (Finset.mem_Icc.mpr ⟨hai,hit⟩)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent normalization and branch ledger

The critical slope is `d / 2`. Both copies of a profile are needed for
the cancellation of the spatial normalization. The last-potential bound
uses the last interval with a defined two-depth potential, even when the
final interval itself is shorter.
-/

namespace Falconer
open scoped BigOperators

theorem dyadic_rpow_change_base {N : ℕ} (hN : 0 < N) (x : ℝ) :
    ((2 : ℝ)^N) ^ (x / (N : ℝ)) = (2 : ℝ)^x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AllDimensionalAngularProfileSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Critical-dimensional cancellation in the parallel-test average

Here `s` will be d/2. The interval minimum is over the original integer
depths, and the retained profile is evaluated at those exact depths.
-/

namespace Falconer

theorem dyadic_power_rpow_as_R {N : ℕ} (hN : 0 < N) (n : ℕ) (s : ℝ) :
    ((2:ℝ)^n)^s = ((2:ℝ)^N)^(s*(n:ℝ)/N) := by
  rw [dyadic_rpow_change_base hN,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

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

theorem exists_bounded_anchor_net (D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Space d), (∀ a ∈ S, ‖a‖ ≤ D) ∧
      ∀ x : Space d, ‖x‖ ≤ D → ∃ a ∈ S, ‖x-a‖ ≤ δ := by
  classical
  obtain ⟨T,hT,hfin,hcover⟩ := (isCompact_closedBall (0 : Space d) D).finite_cover_balls hδ
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro a ha
    simpa only [mem_closedBall,dist_zero_right] using hT (hfin.mem_toFinset.mp ha)
  · intro x hx
    have hxc : x ∈ closedBall (0 : Space d) D := by simpa only [mem_closedBall,dist_zero_right] using hx
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hcover hxc)
    refine ⟨a,hfin.mem_toFinset.mpr ha,?_⟩
    simpa only [mem_ball,dist_eq_norm] using hxa.le

theorem perpendicular_anchor_rounding {w x a y b : Space d} (hw : ‖w‖ = 1)
    {ε δ : ℝ} (hx : ‖perpendicularPart w (x-a)‖ ≤ ε)
    (hy : ‖perpendicularPart w (y-a)‖ ≤ ε) (hb : ‖y-b‖ ≤ δ) :
    ‖perpendicularPart w (x-b)‖ ≤ 2*ε+δ := by
  have he : perpendicularPart w (x-b) =
      (perpendicularPart w (x-a)-perpendicularPart w (y-a))+perpendicularPart w (y-b) := by
    simp only [perpendicularPart,inner_sub_right]
    module
  rw [he]
  exact (norm_add_le _ _).trans
    (((add_le_add (norm_sub_le _ _) (norm_perpendicularPart_le hw _)).trans
      (add_le_add (add_le_add hx hy) hb)).trans_eq (by ring))

theorem rounded_tube_cover (w : Sphere d) (E : Set (Space d))
    (S G : Finset (Space d)) {ε δ : ℝ}
    (hnet : ∀ x ∈ E, ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (hcover : ∀ x ∈ E, ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ J : Finset (Space d), J ⊆ G ∧ J.card ≤ S.card ∧
      ∀ x ∈ E, ∃ b ∈ J, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
  classical
  let P := fun a : Space d => ∃ y ∈ E, ‖perpendicularPart (w:Space d) (y-a)‖ ≤ ε
  have hround (a : Space d) (ha : P a) :
      ∃ b ∈ G, ∀ x ∈ E, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε →
        ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
    obtain ⟨y,hy,hya⟩ := ha
    obtain ⟨b,hb,hyb⟩ := hnet y hy
    exact ⟨b,hb,fun _ _ hx => perpendicular_anchor_rounding (sphere_norm w) hx hya hyb⟩
  let b : Space d → Space d := fun a => if ha : P a then (hround a ha).choose else 0
  let J := (S.filter P).image b
  refine ⟨J,?_,(Finset.card_image_le.trans (Finset.card_filter_le _ _)),?_⟩
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hp := (Finset.mem_filter.mp ha).2
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.1
  · intro x hx
    obtain ⟨a,ha,hxa⟩ := hcover x hx
    have hp : P a := ⟨x,hx,hxa⟩
    refine ⟨b a,Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩,rfl⟩,?_⟩
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.2 x hx hxa

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TubeCoverChoice
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable choice of countably listed original-label tube covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W ι : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem tube_cover_uncovered_mass_measurable
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : Finset ι) :
    Measurable (fun w => μ {x | (x,w) ∈ E ∧ ∀ i ∈ C, x ∉ U i w}) := by
  have hC : MeasurableSet {p : W × X | ∀ i ∈ C, p.2 ∉ U i p.1} := by
    simp only [ofPred_forall]
    exact C.measurableSet_biInter (fun i _ => (hU i).compl)
  exact measurable_measure_prodMk_left ((hE.preimage measurable_swap).inter hC)

theorem exists_measurable_tube_cover_choice
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : ℕ → Finset ι)
    (hcover : ∀ w, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ i ∈ C n, x ∉ U i w} = 0) :
    ∃ J : W → Finset ι, (∀ i, MeasurableSet {w | i ∈ J w}) ∧
      (∀ w, μ {x | (x,w) ∈ E ∧ ∀ i ∈ J w, x ∉ U i w} = 0) ∧
      ∀ w, ∃ n, J w = C n := by
  classical
  let j : W → ℕ := fun w => Nat.find (hcover w)
  have hj : Measurable j := measurable_find hcover (fun n =>
    measurableSet_eq_fun (tube_cover_uncovered_mass_measurable μ E hE U hU (C n)) measurable_const)
  refine ⟨fun w => C (j w),?_,?_,?_⟩
  · intro i
    exact hj ((Set.to_countable {n | i ∈ C n}).measurableSet)
  · intro w
    exact Nat.find_spec (hcover w)
  · intro w
    exact ⟨j w,rfl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TubeCoverEnumeration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the admissible finite lists from a bounded anchor net -/

namespace Falconer
open Set
variable {X : Type*}

theorem bounded_finset_enumeration (G : Finset X) (N : ℕ) :
    ∃ C : ℕ → Finset X, (∀ n, C n ⊆ G ∧ (C n).card ≤ N) ∧
      ∀ J : Finset X, J ⊆ G → J.card ≤ N → ∃ n, C n = J := by
  classical
  let S := G.powerset.filter (fun J => J.card ≤ N)
  have hs : (∅ : Finset X) ∈ S := by simp [S]
  have : Nonempty {J : Finset X // J ∈ S} := ⟨⟨∅,hs⟩⟩
  obtain ⟨f,hf⟩ := exists_surjective_nat {J : Finset X // J ∈ S}
  refine ⟨fun n => (f n).val,?_,?_⟩
  · intro n
    have hp := Finset.mem_filter.mp (f n).property
    exact ⟨Finset.mem_powerset.mp hp.1,hp.2⟩
  · intro J hJG hJN
    have hJS : J ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJG,hJN⟩
    obtain ⟨n,hn⟩ := hf ⟨J,hJS⟩
    exact ⟨n,congrArg Subtype.val hn⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MeasurableTubeCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable bounded-grid covers of the original direction fibers -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem original_tube_cover_choice (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset (Space d),
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
        ∀ w, μ {x | (x,w) ∈ E ∧ ∀ a ∈ J w,
          ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} = 0 := by
  classical
  obtain ⟨G,hGb,hGn⟩ := exists_bounded_anchor_net (d := d) D hδ
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  let U : Space d → Sphere d → Set (Space d) := fun a w =>
    {x | ‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ}
  have hU (a : Space d) : MeasurableSet {p : Sphere d × Space d | p.2 ∈ U a p.1} := by
    dsimp [U,perpendicularPart]
    exact measurableSet_le (by fun_prop) measurable_const
  have hc : ∀ w : Sphere d, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ a ∈ C n, x ∉ U a w} = 0 := by
    intro w
    obtain ⟨S,hSN,hS⟩ := hcover w
    obtain ⟨J,hJG,hJS,hJ⟩ := rounded_tube_cover w {x | (x,w) ∈ E} S G
      (fun x hx => hGn x (hbounded (x,w) hx)) hS
    obtain ⟨n,hn⟩ := hCs J hJG (hJS.trans hSN)
    refine ⟨n,?_⟩
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    obtain ⟨a,ha,hxa⟩ := hJ x hx.1
    exact (hx.2 a (hn.symm ▸ ha) hxa).elim
  obtain ⟨J,hJ,hzero,hJC⟩ := exists_measurable_tube_cover_choice μ E hE U hU C hc
  refine ⟨G,hGb,J,hJ,?_,hzero⟩
  intro w
  obtain ⟨n,hn⟩ := hJC w
  simpa only [hn] using hC n

theorem finite_tube_cover_relation_measurable
    (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (hJG : ∀ w, J w ⊆ G) (ε : ℝ) :
    MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
  have hm : MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ G, a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
    have hu : MeasurableSet (⋃ a ∈ G, {t : Space d × Sphere d |
        a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε}) := by
      apply G.measurableSet_biUnion
      intro a _
      have hp : MeasurableSet {t : Space d × Sphere d |
          ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
        dsimp [perpendicularPart]
        exact measurableSet_le (by fun_prop) measurable_const
      exact ((hJ a).preimage measurable_snd).inter hp
    convert hu using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp only [mem_ofPred_eq,mem_iUnion,exists_prop]
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  constructor
  · rintro ⟨a,ha,hp⟩
    exact ⟨a,hJG t.2 ha,ha,hp⟩
  · rintro ⟨a,_,ha,hp⟩
    exact ⟨a,ha,hp⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_BadDirectionEnvelope
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Borel envelope for geometric bad directions

The finite anchor net and the envelope depend only on the point law and the
geometric test, before a direction measure is selected.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem boundedTubeUnion_joint_measurable (D R : ℝ) (J : Finset (Space d)) :
    MeasurableSet {p : Sphere d × Space d | p.2 ∈ boundedTubeUnion D R J p.1} := by
  have hU : MeasurableSet (⋃ a ∈ J, {p : Sphere d × Space d |
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R}) := by
    apply J.measurableSet_biUnion
    intro a _
    unfold perpendicularPart
    exact measurableSet_le (by fun_prop) measurable_const
  have he : {p : Sphere d × Space d | ∃ a ∈ J,
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} =
      ⋃ a ∈ J, {p : Sphere d × Space d | ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} := by
    ext p
    simp only [mem_iUnion,mem_ofPred_eq,exists_prop]
  have hb : MeasurableSet {p : Sphere d × Space d | ‖p.2‖ ≤ D} :=
    measurableSet_le (by fun_prop) measurable_const
  have hU' : MeasurableSet {p : Sphere d × Space d | ∃ a ∈ J,
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} := by
    rw [he]
    exact hU
  change MeasurableSet ({p : Sphere d × Space d | ‖p.2‖ ≤ D} ∩ _)
  exact hb.inter hU'

theorem boundedTubeUnion_mass_measurable (μ : Measure (Space d)) [SFinite μ]
    (D R : ℝ) (J : Finset (Space d)) :
    Measurable (fun w : Sphere d => μ (boundedTubeUnion D R J w)) :=
  measurable_measure_prodMk_left (boundedTubeUnion_joint_measurable D R J)

theorem finiteBadDirections_measurable (μ : Measure (Space d)) [SFinite μ]
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) :
    MeasurableSet (finiteBadDirections μ G N D R a) := by
  classical
  have hU : MeasurableSet (⋃ J ∈ G.powerset,
      {w : Sphere d | J.card ≤ N ∧ a ≤ μ (boundedTubeUnion D R J w)}) := by
    apply G.powerset.measurableSet_biUnion
    intro J _
    exact (MeasurableSet.const _).inter
      (measurableSet_le measurable_const (boundedTubeUnion_mass_measurable μ D R J))
  convert hU using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp only [finiteBadDirections,mem_iUnion,mem_ofPred_eq,exists_prop]

theorem original_bad_direction_mem_envelope (μ : Measure (Space d)) [SFinite μ]
    {D R δ : ℝ} (G : Finset (Space d)) (N : ℕ) (a : ℝ≥0∞)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hnet : ∀ x : Space d, ‖x‖ ≤ D → ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (w : Sphere d) (S : Finset (Space d)) (hS : S.card ≤ N)
    (hmass : a ≤ μ {x | ∃ b ∈ S, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ R}) :
    w ∈ finiteBadDirections μ G N D (2*R+δ) a := by
  classical
  let E := boundedTubeUnion D R S w
  obtain ⟨J,hJG,hJS,hcover⟩ := rounded_tube_cover w E S G
    (fun x hx => hnet x hx.1) (fun _ hx => hx.2)
  refine ⟨J,Finset.mem_powerset.mpr hJG,hJS.trans hS,?_⟩
  have hrestrict : μ {x | ∃ b ∈ S, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ R} ≤ μ E := by
    apply measure_mono_ae
    filter_upwards [hμ] with x hx hm
    exact ⟨hx,hm⟩
  apply (hmass.trans hrestrict).trans
  apply measure_mono
  intro x hx
  exact ⟨hx.1,hcover x hx⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_BadDirectionSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable incidence witnessing every direction in the finite envelope -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem exists_finite_bad_incidence (μ : Measure (Space d)) [SFinite μ]
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) :
    ∃ J : Sphere d → Finset (Space d), ∃ F : Set (Space d × Sphere d),
      MeasurableSet F ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
      (∀ x, MeasurableSet {w | x ∈ J w}) ∧
      (∀ p ∈ F, ‖p.1‖ ≤ D) ∧
      (∀ p ∈ F, ∃ x ∈ J p.2, ‖perpendicularPart (p.2:Space d) (p.1-x)‖ ≤ R) ∧
      ∀ (ν : Measure (Sphere d)) [SFinite ν],
        a*ν (finiteBadDirections μ G N D R a) ≤ (μ.prod ν) F := by
  classical
  let B := finiteBadDirections μ G N D R a
  have hB : MeasurableSet B := finiteBadDirections_measurable μ G N D R a
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  have hfind : ∀ w : Sphere d, ∃ n : ℕ,
      w ∉ B ∨ a ≤ μ (boundedTubeUnion D R (C n) w) := by
    intro w
    by_cases hw : w ∈ B
    · obtain ⟨J,hJG,hJN,hm⟩ := hw
      obtain ⟨n,rfl⟩ := hCs J (Finset.mem_powerset.mp hJG) hJN
      exact ⟨n,Or.inr hm⟩
    · exact ⟨0,Or.inl hw⟩
  let j : Sphere d → ℕ := fun w => Nat.find (hfind w)
  have hj : Measurable j := measurable_find hfind (fun n => hB.compl.union
    (measurableSet_le measurable_const (boundedTubeUnion_mass_measurable μ D R (C n))))
  let J : Sphere d → Finset (Space d) := fun w => C (j w)
  have hJ (x : Space d) : MeasurableSet {w | x ∈ J w} :=
    hj ((Set.to_countable {n | x ∈ C n}).measurableSet)
  let F : Set (Space d × Sphere d) := {p | p.2 ∈ B ∧ p.1 ∈ boundedTubeUnion D R (J p.2) p.2}
  have hF : MeasurableSet F := by
    have ht := finite_tube_cover_relation_measurable G J hJ (fun w => (hC (j w)).1) R
    have hb : MeasurableSet {p : Space d × Sphere d | ‖p.1‖ ≤ D} :=
      measurableSet_le (by fun_prop) measurable_const
    exact (hB.preimage measurable_snd).inter (hb.inter ht)
  refine ⟨J,F,hF,(fun w => hC (j w)),hJ,(fun _ hp => hp.2.1),(fun _ hp => hp.2.2),?_⟩
  intro ν _
  have hbound (w : Sphere d) : B.indicator (fun _ => a) w ≤ μ {x | (x,w) ∈ F} := by
    by_cases hw : w ∈ B
    · rw [indicator_of_mem hw]
      have hm := (Nat.find_spec (hfind w)).resolve_left (not_not.mpr hw)
      have he : {x | (x,w) ∈ F} = boundedTubeUnion D R (J w) w := by
        ext x
        simp only [F,mem_ofPred_eq,hw,true_and]
      rw [he]
      exact hm
    · rw [indicator_of_notMem hw]
      exact bot_le
  rw [Measure.prod_apply_symm hF]
  calc
    _ = ∫⁻ w, B.indicator (fun _ => a) w ∂ν := by
      rw [lintegral_indicator hB,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := lintegral_mono hbound

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-vector Gaussian band estimates for the angular slicing construction -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianBandConstant_pos : 0 < gaussianBandConstant := by
  unfold gaussianBandConstant
  positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPairBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularized two-vector Gaussian band bounds -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianPairBandConstant_pos : 0 < gaussianPairBandConstant := by
  unfold gaussianPairBandConstant
  have := gaussianBandConstant_pos
  positivity

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

theorem leafUnion_subset (Q : DyadicCube d) (_hQ : 0 < Q.side)
    (L : Finset (CellPath d)) : leafUnion Q L ⊆ Q.carrier := by
  intro z hz
  obtain ⟨p,_,hp⟩ := mem_iUnion₂.mp hz
  exact Q.descendant_subset p hp

theorem measure_leafUnion (Q : DyadicCube d) (_hQ : 0 < Q.side) (μ : Measure (Space d))
    {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) :
    μ (leafUnion Q L) = ∑ p ∈ L, μ (Q.descendant p).carrier := by
  apply measure_biUnion_finset
  · intro p hp q hq hne
    exact Q.descendants_disjoint
      (((mem_cubePaths _ _ _).mp (hL hp)).trans ((mem_cubePaths _ _ _).mp (hL hq)).symm)
      hne
  · intro p _; exact (Q.descendant p).measurable

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledConditional
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
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

theorem cellScaleMap_continuous (p : ℕ) (c : Space d) : Continuous (cellScaleMap p c) := by
  change Continuous (fun z : Space d => (2:ℝ)^p • (z-c))
  exact (continuous_id.sub continuous_const).const_smul ((2:ℝ)^p)

theorem cellScaleMap_preimage_ball (p : ℕ) (c x : Space d) (r : ℝ) :
    cellScaleMap p c ⁻¹' ball x r = ball (c+((2:ℝ)^p)⁻¹ • x) (r/(2:ℝ)^p) := by
  ext z
  have hs : 0 < (2:ℝ)^p := by positivity
  have he : (2:ℝ)^p • (z-c)-x = (2:ℝ)^p • (z-(c+((2:ℝ)^p)⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    abel
  simp only [mem_preimage,mem_ball,dist_eq_norm,cellScaleMap]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hs,lt_div_iff₀ hs]
  simp only [mul_comm]

theorem rescaled_conditional_ball_apply (ρ : Measure (Space d)) (p : ℕ) (c : Space d)
    (P : Set (Space d)) (x : Space d) (r : ℝ) :
    (Measure.map (cellScaleMap p c) (ProbabilityTheory.cond ρ P)) (ball x r) =
      ProbabilityTheory.cond ρ P (ball (c+((2:ℝ)^p)⁻¹ • x) (r/(2:ℝ)^p)) := by
  rw [Measure.map_apply (cellScaleMap_continuous p c).measurable measurableSet_ball,
    cellScaleMap_preimage_ball]

theorem sourceClass_rescaled_dyadic_ball (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p n : ℕ} (hpn : p ≤ n) (hn : n ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    ((Measure.map (cellScaleMap p (Q.descendant P).center)
      (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier))
        (ball x (C/(2:ℝ)^(n-p)))).toReal ≤
      ((2*Nat.ceil (2*C+4*Real.sqrt d)+1)^d:ℕ)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ n+2*((d:ℝ)+1)*lam) := by
  rw [rescaled_conditional_ball_apply]
  have hr : (C/(2:ℝ)^(n-p))/(2:ℝ)^p = C*(Q.side/(2:ℝ)^n) := by
    rw [div_div,← pow_add,Nat.sub_add_cancel hpn,hQ]
    ring
  rw [hr]
  exact sourceClass_conditional_ball_upper Q (by rw [hQ]; norm_num) μ hN hB hwidth hlarge hp₀
    (hpn.trans hn) hn hP hPpos _ hC

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
-- module Solutions.OAIQ088_FD.Falconer_Measures_ConditionalFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale Frostman bounds for the full rescaled conditional laws -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem profile_drop_weight (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (s E : ℝ)
    {p n t : ℕ} (hpn : p ≤ n) (hnt : n ≤ t) :
    ((2:ℝ)^N)^(m p-m n+E) ≤
      ((2:ℝ)^N)^(profileDrop m N s p t+E)*(1/(2:ℝ)^(n-p))^s := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hd : (1/(2:ℝ)^(n-p))^s = ((2:ℝ)^N)^(-s*(n-p:ℕ)/N) := by
    rw [one_div,Real.inv_rpow (by positivity),dyadic_power_rpow_as_R hN,
      ← Real.rpow_neg hR.le]
    congr 1
    ring
  rw [hd,← Real.rpow_add hR]
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  have hh := PlanarFalconer.intervalMin_le (fun k : ℕ => m k-s*(k:ℝ)/N) hpn hnt
  dsimp only [profileDrop]
  rw [Nat.cast_sub hpn]
  calc
    m p-m n+E ≤ m p-(PlanarFalconer.intervalMin
      (fun k : ℕ => m k-s*(k:ℝ)/N) p t+s*(n:ℝ)/N)+E := by linarith
    _ = _ := by ring

theorem sourceClass_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^(t-p) ≤ r → r ≤ 1 →
      (Measure.map (cellScaleMap p (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)) (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(profileDrop (sourceProfile Q μ N B p₀) N s p t+2*((d:ℝ)+1)*lam)*r^s) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  let α := Measure.map (cellScaleMap p (Q.descendant P).center)
    (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hPpos
  have : IsFiniteMeasure α := by dsimp [α]; infer_instance
  let m := sourceProfile Q μ N B p₀
  let E := 2*((d:ℝ)+1)*lam
  let D : ℝ := ((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ)
  let R : ℝ := (2:ℝ)^N
  intro x r hr hr₁
  obtain ⟨j,hj,hrj,hjr⟩ := dyadic_radius_bracket hr hr₁
  have hn : p+j ≤ t := by omega
  have hball := sourceClass_rescaled_dyadic_ball Q hQ μ hN hB hwidth hlarge hp₀
    (Nat.le_add_right p j) (hn.trans htN) hP hPpos x (show (0:ℝ) ≤ 1 by norm_num)
  simp only [Nat.add_sub_cancel_left,mul_one] at hball
  have hmono : (α (ball x r)).toReal ≤ (α (ball x (1/(2:ℝ)^j))).toReal :=
    ENNReal.toReal_mono (measure_ne_top α _) (measure_mono (ball_subset_ball hrj))
  have hweight := profile_drop_weight m hN s E (Nat.le_add_right p j) hn
  simp only [Nat.add_sub_cancel_left] at hweight
  have hrpow : (1/(2:ℝ)^j)^s ≤ (2*r)^s :=
    Real.rpow_le_rpow (by positivity) hjr hs
  have hbound : (α (ball x r)).toReal ≤ D*(2:ℝ)^s*R^(profileDrop m N s p t+E)*r^s := by
    calc
      _ ≤ D*R^(m p-m ((p+j:ℕ):ℝ)+E) := hmono.trans hball
      _ ≤ D*(R^(profileDrop m N s p t+E)*(1/(2:ℝ)^j)^s) :=
        mul_le_mul_of_nonneg_left hweight (by dsimp [D]; positivity)
      _ ≤ D*(R^(profileDrop m N s p t+E)*(2*r)^s) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow (by positivity))
          (by dsimp [D]; positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith [hrj,hjr])]; ring
  change α (ball x r) ≤ _
  rw [← ENNReal.ofReal_toReal (measure_ne_top α _)]
  exact ENNReal.ofReal_le_ofReal hbound

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
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FrameEmbedding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear isometry associated with a finite orthonormal frame -/

namespace Falconer
variable {d h : ℕ}

theorem frameLinearMap_orthonormal {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (frameLinearMap v ∘ (EuclideanSpace.basisFun (Fin h) ℝ).toBasis) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  change inner ℝ (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i))
    (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ j)) = _
  simpa only [frameLinearMap_basis] using hv i j

theorem orthonormal_frame_embedding {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    ∃ e : Space h →ₗᵢ[ℝ] Space d,
      ∀ i, e (EuclideanSpace.basisFun (Fin h) ℝ i) = v i := by
  let e : Space h →ₗᵢ[ℝ] Space d := (frameLinearMap v).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin h) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin h) ℝ).orthonormal (frameLinearMap_orthonormal hv)
  refine ⟨e,?_⟩
  intro i
  change frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i) = v i
  exact frameLinearMap_basis v i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLocalBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Band mass inside a fixed neighborhood of a transverse row -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

theorem gaussianLocalBandConstant_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < gaussianLocalBandConstant n ρ := by
  unfold gaussianLocalBandConstant gaussianVolumeNormalization
  positivity

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

theorem exists_transverse_row_frame (hhn : h ≤ n) {w : Space (n+1)} (hw : ‖w‖ = 1) :
    ∃ e : Space h →ₗᵢ[ℝ] Space (n+1),
      ∀ i, inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0 := by
  let u := EuclideanSpace.basisFun (Fin (n+1)) ℝ 0
  let R : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) := (ℝ ∙ (u-w))ᗮ.reflection
  have hR : R u = w := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0).trans hw.symm)
  let f : Fin h → Fin (n+1) := fun i => ⟨i.val+1,by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp [f] at he
    omega
  let v : Fin h → Space (n+1) := fun i => R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))
  have hv : Orthonormal ℝ v := by
    exact ((EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.comp f hf).comp_linearIsometryEquiv R
  obtain ⟨e,he⟩ := orthonormal_frame_embedding hv
  refine ⟨e,fun i => ?_⟩
  rw [he,← hR]
  change inner ℝ (R u) (R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))) = 0
  rw [R.inner_map_map]
  exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.2 (by
    intro heq
    have hz := congrArg Fin.val heq
    dsimp [f] at hz
    omega)

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
-- module Solutions.OAIQ088_FD.Falconer_Radial_ReverseRadialGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reverse radial caps bound collisions of original source directions -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem perpendicularPart_neg_left (u v : Space n) :
    perpendicularPart (-u) v = perpendicularPart u v := by
  simp [perpendicularPart,neg_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_TubeDirectionRobustness
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Robust tube covers under small unoriented changes of direction -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem tube_direction_point_bound {w v z : Space d} {η L r : ℝ}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) (hdir : ‖w-v‖ ≤ η)
    (hz : ‖z‖ ≤ L) (htube : ‖perpendicularPart w z‖ ≤ r) :
    ‖perpendicularPart v z‖ ≤ r+2*η*L := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hdir
  have he := perpendicularPart_direction_error hv hw z
  have htri := norm_sub_le_norm_sub_add_norm_sub (perpendicularPart v z) (perpendicularPart w z) 0
  simp only [sub_zero] at htri
  have hdir' : ‖v-w‖ ≤ η := by simpa only [norm_sub_rev] using hdir
  calc
    _ ≤ ‖perpendicularPart v z-perpendicularPart w z‖+‖perpendicularPart w z‖ := htri
    _ ≤ 2*‖v-w‖*‖z‖+r := add_le_add he htube
    _ ≤ 2*η*L+r := by gcongr
    _ = _ := by ring

theorem unoriented_tube_direction_point_bound {w v z : Space d} {η L r : ℝ}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hdir : ‖w-v‖ ≤ η ∨ ‖w+v‖ ≤ η)
    (hz : ‖z‖ ≤ L) (htube : ‖perpendicularPart w z‖ ≤ r) :
    ‖perpendicularPart v z‖ ≤ r+2*η*L := by
  rcases hdir with hdir | hdir
  · exact tube_direction_point_bound hw hv hdir hz htube
  · have hh := tube_direction_point_bound hw (show ‖-v‖ = 1 by simpa using hv)
      (show ‖w-(-v)‖ ≤ η by simpa only [sub_neg_eq_add] using hdir) hz htube
    simpa only [perpendicularPart_neg_left] using hh

theorem tube_cover_direction_transport (μ : Measure (Space d))
    {w v : Space d} {D B η r : ℝ} (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hdir : ‖w-v‖ ≤ η ∨ ‖w+v‖ ≤ η)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (S : Finset (Space d)) (hS : ∀ a ∈ S, ‖a‖ ≤ B) :
    μ {x | ∃ a ∈ S, ‖perpendicularPart w (x-a)‖ ≤ r} ≤
      μ {x | ∃ a ∈ S, ‖perpendicularPart v (x-a)‖ ≤ r+2*η*(D+B)} := by
  apply measure_mono_ae
  filter_upwards [hμ] with x hx
  rintro ⟨a,ha,htube⟩
  refine ⟨a,ha,unoriented_tube_direction_point_bound hw hv hdir ?_ htube⟩
  exact (norm_sub_le x a).trans (add_le_add hx (hS a ha))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GoodDirectionMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One good witness direction rules out mass in a nearby heavy tube cover -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem mass_lt_of_good_direction_cover (μ : Measure (Space d))
    (Bad : Set (Sphere d)) (v : Sphere d) (hv : v ∉ Bad)
    (w : Space d) (hw : ‖w‖ = 1) {D B η r R : ℝ}
    (hdir : ‖w-(v:Space d)‖ ≤ η ∨ ‖w+(v:Space d)‖ ≤ η)
    (hwidth : r+2*η*(D+B) ≤ R) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (J : Finset (Space d)) (hJ : ∀ a ∈ J, ‖a‖ ≤ B) (N : ℕ) (hcard : J.card ≤ N)
    (a : ℝ≥0∞)
    (henvelope : ∀ S : Finset (Space d), S.card ≤ N →
      a ≤ μ {x | ∃ b ∈ S, ‖perpendicularPart (v:Space d) (x-b)‖ ≤ R} → v ∈ Bad)
    (T : Set (Space d))
    (hcover : ∀ x ∈ T, ∃ b ∈ J, ‖perpendicularPart w (x-b)‖ ≤ r) : μ T < a := by
  by_contra hn
  have hlarge : a ≤ μ T := le_of_not_gt hn
  apply hv
  apply henvelope J hcard
  apply hlarge.trans
  apply (measure_mono hcover).trans
  apply (tube_cover_direction_transport μ hw (sphere_norm v) hdir hμ J hJ).trans
  apply measure_mono
  rintro x ⟨b,hb,hxb⟩
  exact ⟨b,hb,hxb.trans hwidth⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarGainNumerics
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absorbing the explicit losses in the planar measure obstruction

Only fixed constants, logarithms and ceilings are absorbed here. The
underlying incidence estimate has already been proved from the cited
published input.
-/

namespace Falconer
open Real Filter
open scoped Topology

theorem rpow_absorb_constant {δ t u C : ℝ} (hδ : 0 < δ)
    (hC : C ≤ δ^(-(u-t))) : C * δ^(-t) ≤ δ^(-u) := by
  calc
    _ ≤ δ^(-(u-t)) * δ^(-t) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OriginalDirectionChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a small direction chart on the original incidence labels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem sphere_chart_pair_inner_nonnegative (w v c : Sphere d)
    (hw : dist w c ≤ 1/2) (hv : dist v c ≤ 1/2) :
    0 ≤ inner ℝ (w:Space d) (v:Space d) := by
  have hd : dist w v ≤ 1 := (dist_triangle w c v).trans (by rw [dist_comm c v]; linarith)
  have hn : ‖(w:Space d)-(v:Space d)‖ ≤ 1 := by simpa only [Subtype.dist_eq,dist_eq_norm] using hd
  have hsq := norm_sub_sq_real (w:Space d) (v:Space d)
  rw [sphere_norm,sphere_norm] at hsq
  nlinarith [norm_nonneg ((w:Space d)-(v:Space d))]

theorem original_direction_chart_selection
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [SFinite μ] [SFinite ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℝ≥0∞}
    (hmean : ENNReal.ofReal ((2/ρ+1)^d)*a < (μ.prod ν) E) :
    ∃ c : Sphere d, a < (μ.prod (ν.restrict (closedBall c ρ))) E := by
  classical
  obtain ⟨S,_,hcover,hcard,_⟩ := finite_separated_cap_net d (show 0 < 2*ρ by positivity)
  have hcover' (w : Sphere d) : ∃ c ∈ S, dist w c ≤ ρ := by
    have hr : (2*ρ)/2 = ρ := by ring
    simpa only [hr] using hcover w
  let F : Sphere d → Set (Space d × Sphere d) := fun c => E ∩ (univ ×ˢ closedBall c ρ)
  have hsub : E ⊆ ⋃ c ∈ S, F c := by
    intro z hz
    obtain ⟨c,hc,hd⟩ := hcover' z.2
    exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,hz,mem_univ _,hd⟩⟩
  have hmass : (μ.prod ν) E ≤ ∑ c ∈ S, (μ.prod ν) (F c) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le S F)
  have he (c : Sphere d) : (μ.prod ν) (F c) = (μ.prod (ν.restrict (closedBall c ρ))) E := by
    have hprod : μ.prod (ν.restrict (closedBall c ρ)) =
        (μ.prod ν).restrict (univ ×ˢ closedBall c ρ) := by
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := μ) (ν := ν) univ (closedBall c ρ)
    rw [hprod,Measure.restrict_apply hE]
  by_contra! hn
  have hsum : (μ.prod ν) E ≤ (S.card:ℝ≥0∞)*a := hmass.trans (by
    calc
      _ ≤ ∑ _c ∈ S, a := Finset.sum_le_sum (fun c _ => by rw [he]; exact hn c)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul])
  have hcard' : (S.card:ℝ≥0∞) ≤ ENNReal.ofReal ((2/ρ+1)^d) := by
    have hh : (S.card:ℝ) ≤ (2/ρ+1)^d := by
      have hr : 4/(2*ρ)+1 = 2/ρ+1 := by field_simp; ring
      simpa only [hr] using hcard
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hh
  exact (not_le_of_gt hmean) (hsum.trans (mul_le_mul' hcard' le_rfl))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the concrete slice-selection losses into the planar gain -/

namespace Falconer
open Real Filter
open scoped Topology

theorem gaussian_scale_power {δ κ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    (δ^(-κ))^j = δ^(-((j:ℝ)*κ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  congr 1
  ring

theorem eventually_gaussian_scale_losses {η : ℝ} (hη : 0 < η)
    (K₀ V A b : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ K₀ ≤ δ^(-(η/100)) ∧
      4*V*(δ^(-(η/100)))^10 < δ^(-η) ∧
      A*(δ^(-(η/100)))^12*δ^(-b) ≤ δ^(-b-η) := by
  let κ := η/100
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hten : 0 < η-10*κ := by dsimp [κ]; linarith
  have htwelve : 0 < η-12*κ := by dsimp [κ]; linarith
  have hlarge := (tendsto_rpow_neg_nhdsGT_zero (show -κ < 0 by linarith)).eventually
    (eventually_ge_atTop K₀)
  have hnorm := (tendsto_rpow_neg_nhdsGT_zero (show -(η-10*κ) < 0 by linarith)).eventually
    (eventually_gt_atTop (4*V))
  have hcover := (tendsto_rpow_neg_nhdsGT_zero (show -(η-12*κ) < 0 by linarith)).eventually
    (eventually_ge_atTop A)
  filter_upwards [hlarge,hnorm,hcover,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)]
    with δ hlarge hnorm hcover hδone
  have hδ := hδone.1
  refine ⟨hδ,hlarge,?_,?_⟩
  · change 4*V*(δ^(-κ))^10 < δ^(-η)
    rw [gaussian_scale_power hδ]
    calc
      _ < δ^(-(η-10*κ))*δ^(-((10:ℝ)*κ)) :=
        mul_lt_mul_of_pos_right hnorm (Real.rpow_pos_of_pos hδ _)
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  · change A*(δ^(-κ))^12*δ^(-b) ≤ δ^(-b-η)
    rw [gaussian_scale_power hδ]
    calc
      _ = A*δ^(-(12*κ+b)) := by rw [mul_assoc,← Real.rpow_add hδ]; congr 2; ring
      _ ≤ δ^(-(b+η)) := rpow_absorb_constant hδ (by
        rw [show -((b+η)-(12*κ+b)) = -(η-12*κ) by ring]
        exact hcover)
      _ = _ := by congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic number of dyadic tests fits inside the chosen power loss -/

namespace Falconer
open Real Filter
open scoped Topology

theorem dyadic_log_depth (N : ℕ) :
    1-Real.log (1/(2:ℝ)^N)/Real.log 2 = (N:ℝ)+1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [one_div,Real.log_inv,Real.log_pow]
  field_simp
  ring

theorem eventually_dyadic_loss_absorption {ε κ : ℝ} (hεκ : ε < κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ C*(1-Real.log δ/Real.log 2)*δ^(-ε) ≤ δ^(-κ) := by
  have hr : 0 < κ-ε := sub_pos.mpr hεκ
  have hp : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝[>] 0) (𝓝 0) := by
    have hp₀ : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [Real.zero_rpow hr.ne'] using (Real.continuous_rpow_const hr.le).tendsto (0:ℝ)
    exact hp₀.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hr
  have ht : Tendsto (fun δ : ℝ => C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div,sub_zero,mul_zero] using (hp.sub (hl.div_const (Real.log 2))).const_mul C
  have hsmall := ht.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hsmall,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hs hδone
  have hδ := hδone.1
  refine ⟨hδ,?_⟩
  calc
    _ = (C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))*δ^(-κ) := by
      calc
        _ = C*(1-Real.log δ/Real.log 2)*δ^((κ-ε)+(-κ)) := by congr 2; ring
        _ = C*(1-Real.log δ/Real.log 2)*(δ^(κ-ε)*δ^(-κ)) := by rw [Real.rpow_add hδ]
        _ = _ := by ring
    _ ≤ 1*δ^(-κ) := mul_le_mul_of_nonneg_right hs.le (Real.rpow_nonneg hδ.le _)
    _ = _ := one_mul _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarLossBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One scale choice supplies every scalar inequality in the planar slice application -/

namespace Falconer
open Real Filter
open scoped Topology

theorem inverse_power_gap {δ η H : ℝ} (hδ : 0 < δ) (hH : 0 < H)
    (hgap : H < δ^(-η)) : δ^η < 1/H := by
  apply (lt_div_iff₀ hH).mpr
  calc
    δ^η*H < δ^η*δ^(-η) := mul_lt_mul_of_pos_left hgap (Real.rpow_pos_of_pos hδ η)
    _ = 1 := by
      rw [Real.rpow_neg hδ.le]
      exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hδ η))

theorem eventually_gaussian_planar_loss_budget {η : ℝ} (hη : 0 < η)
    {V a : ℝ} (hV : 1 ≤ V) (ha : 1 ≤ a) (f b A K₀ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ K₀ ≤ δ^(-(η/100)) ∧
      1 ≤ 4*(δ^(-(η/100)))^10*V ∧
      (4*(δ^(-(η/100)))^10*V)*(4*a)^f ≤ δ^(-η) ∧
      (4*(δ^(-(η/100)))^10*V)*(8*a)^b ≤ δ^(-η) ∧
      δ^η < 1/(4*(δ^(-(η/100)))^10*V) ∧
      A*(δ^(-(η/100)))^12*δ^(-b) ≤ δ^(-b-η) := by
  let W : ℝ := V*((4*a)^f+(8*a)^b+1)
  have hVpos : 0 < V := by linarith
  have ha0 : 0 < a := by linarith
  have hfpos : 0 < (4*a)^f := Real.rpow_pos_of_pos (by positivity) _
  have hbpos : 0 < (8*a)^b := Real.rpow_pos_of_pos (by positivity) _
  have hVW : V < W := by dsimp [W]; nlinarith
  have hpf : V*(4*a)^f ≤ W := by dsimp [W]; nlinarith
  have hqb : V*(8*a)^b ≤ W := by dsimp [W]; nlinarith
  filter_upwards [eventually_gaussian_scale_losses hη (max K₀ 1) W A b]
    with δ hδ
  rcases hδ with ⟨hδ,hK,hgap,hcover⟩
  have hK₀ : K₀ ≤ δ^(-(η/100)) := (le_max_left _ _).trans hK
  have hK1 : 1 ≤ δ^(-(η/100)) := (le_max_right _ _).trans hK
  have hKpow : 1 ≤ (δ^(-(η/100)))^10 := one_le_pow₀ hK1
  have hH : 0 < 4*(δ^(-(η/100)))^10*V := by positivity
  have hHW : 4*(δ^(-(η/100)))^10*V < δ^(-η) := by
    apply lt_trans _ hgap
    nlinarith [Real.rpow_pos_of_pos hδ (-(η/100))]
  refine ⟨hδ,hK₀,?_,?_,?_,inverse_power_gap hδ hH hHW,hcover⟩
  · nlinarith
  · apply le_trans _ hgap.le
    nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-(η/100))) 10]
  · apply le_trans _ hgap.le
    nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-(η/100))) 10]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ActiveCoverScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original tube count after codimension-h slicing -/

namespace Falconer

theorem gaussian_active_cover_scale {δ ε κ q Nc D : ℝ} (h : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεκ : ε ≤ κ) (hD : 0 ≤ D)
    (hNc : Nc ≤ δ^(-q-ε)) :
    (δ^(-κ))^11*(Nc*(2*(D*δ))^h) ≤
      (2*D)^h*(δ^(-κ))^12*δ^(-(q-(h:ℝ))) := by
  have hε : δ^(-ε) ≤ δ^(-κ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεκ)
  have hpower : δ^(-q-ε)*δ^h = δ^(-ε)*δ^(-(q-(h:ℝ))) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ ≤ (δ^(-κ))^11*(δ^(-q-ε)*(2*(D*δ))^h) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNc (by positivity)) (by positivity)
    _ = (2*D)^h*(δ^(-κ))^11*(δ^(-ε)*δ^(-(q-(h:ℝ)))) := by
      rw [show 2*(D*δ) = (2*D)*δ by ring,mul_pow]
      calc
        _ = (2*D)^h*(δ^(-κ))^11*(δ^(-q-ε)*δ^h) := by ring
        _ = _ := by rw [hpower]
    _ ≤ (2*D)^h*(δ^(-κ))^11*(δ^(-κ)*δ^(-(q-(h:ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hε (Real.rpow_nonneg hδ.le _)) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMomentScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common fixed coefficient for the original finite-scale moment bounds -/

namespace Falconer

theorem exists_gaussian_moment_coefficient (h : ℕ) (t q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (4*gaussianVectorBandConstant)^h*L*gaussianFrostmanFactor h t ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*L*gaussianFrostmanFactor h q ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*(|L*gaussianFrostmanFactor h q|+1) ≤ C*L := by
  let P := (4*gaussianVectorBandConstant)^h*gaussianFrostmanFactor h t
  let Q := (2*gaussianPairBandConstant)^h*gaussianFrostmanFactor h q
  let U := (2*gaussianPairBandConstant)^h*(|gaussianFrostmanFactor h q|+1)
  let C := |P|+|Q|+U+1
  have hG := gaussianPairBandConstant_pos
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hPC : P ≤ C := by dsimp [C]; linarith [le_abs_self P,abs_nonneg Q]
  have hQC : Q ≤ C := by dsimp [C]; linarith [le_abs_self Q,abs_nonneg P]
  have hUC : U ≤ C := by dsimp [C]; linarith [abs_nonneg P,abs_nonneg Q]
  refine ⟨C,hC,?_⟩
  intro L hL
  have hL0 : 0 ≤ L := by linarith
  refine ⟨?_,?_,?_⟩
  · simpa only [P,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hPC hL0
  · simpa only [Q,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hQC hL0
  · calc
      _ = (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+1) := by
        rw [abs_mul,abs_of_nonneg hL0]
      _ ≤ (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+L) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hL _) (by positivity)
      _ = U*L := by dsimp [U]; ring
      _ ≤ C*L := mul_le_mul_of_nonneg_right hUC hL0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NonendpointChartGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform nonendpoint angular decay on a fixed original direction chart -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem nonendpoint_chart_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C ρ : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hstable : (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2)
    (hchart : 4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν).real E ≤ (1/(2:ℝ)^N)^c := by
  classical
  obtain ⟨η,δF,hη,hδF,hgain⟩ := controlled_dyadic_angular_gain hpublished hq hq' hqt ht hC
  obtain ⟨Cm,hCm,hcoeff⟩ := exists_gaussian_moment_coefficient h t q
  let κ₀ := η/100
  let ε := κ₀/2
  let c := κ₀/2
  let M := (h+2:ℝ)*(2*ρ)+1
  let Z := M+1
  let V := (2*Z)^h
  let a₀ := 4+8*(h:ℝ)
  let D := 1+2*(1/4)+C*M
  let B₀ := (2:ℝ)^h*gaussianLocalBandConstant (h+1) ρ^h
  have hκ : 0 < κ₀ := by dsimp [κ₀]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hεκ : ε < κ₀ := by dsimp [ε]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : 1 ≤ V := by
    apply one_le_pow₀
    change 1 ≤ 2*(M+1)
    linarith
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hD : 0 < D := by dsimp [D]; positivity
  have hB₀ : 0 < B₀ := by
    have hb := gaussianLocalBandConstant_pos (n := h+1) hρ
    dsimp [B₀]
    positivity
  have hplan := eventually_gaussian_planar_loss_budget hη hV ha₀ (t-(h:ℝ))
    (q-(h:ℝ)) ((2*D)^h) (4*(1+2*(2:ℝ)^h+1))
  have hdepth := eventually_dyadic_loss_absorption hεκ Cm
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(κ₀-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop (1/B₀))
  obtain ⟨δ₁,hδ₁,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp
      (hplan.and (hdepth.and habs))
  refine ⟨ε,c,min δF (min δ₁ (min ρ 1)),hε,hc,
    lt_min hδF (lt_min hδ₁ (lt_min hρ (by norm_num))),?_⟩
  intro N κ _ _ μ ν _ _ w₀ E J a hδsmall hν hμ hμmass hνmass hμball hνball
    hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let K : ℝ := δ^(-κ₀)
  let L : ℝ := δ^(-ε)
  let Nc : ℝ := δ^(-q-ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ ≤ ρ := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_left _ _)) |>.le
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_right _ _)) |>.le
  obtain ⟨hp,⟨_,hd⟩,ha⟩ := hready ⟨hδ,hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  rcases hp with ⟨_,hlarge,hH,hpcoef,hqcoef,hlow,hcoverScale⟩
  have hL : 1 ≤ L := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -ε ≤ 0 by linarith)
  have hK : 0 < K := Real.rpow_pos_of_pos hδ _
  have hL0 : 0 ≤ L := by linarith
  have hCmL : 0 ≤ Cm*L := mul_nonneg hCm.le hL0
  have hcard : ((N+1:ℕ):ℝ)*(Cm*L) ≤ K := by
    rw [dyadic_log_depth N] at hd
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm] using hd
  have hCK : Cm*L ≤ K := by
    have hN : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (le_mul_of_one_le_left hCmL hN).trans hcard
  have hpair : ∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν,Measure.quasiMeasurePreserving_snd.ae hν]
      with u hu hv
    exact sphere_chart_pair_inner_nonnegative u.1 u.2 w₀ (hu.trans hρhalf) (hv.trans hρhalf)
  obtain ⟨B,hB⟩ := exists_transverse_row_frame (h := h) (n := h+1) (by omega) (sphere_norm w₀)
  have hchartδ : 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
    nlinarith [mul_le_mul_of_nonneg_left hδρ (by positivity : 0 ≤ 4*(h:ℝ))]
  have hbox : (1/4)*((h+2:ℝ)*(2*ρ)+1)+δ ≤ Z := by
    change (1/4)*M+δ ≤ M+1
    nlinarith
  have hactive : K^11*(Nc*(2*(δ+(2*(1/4))*δ+(C*δ)*M))^h) ≤ δ^(-(q-(h:ℝ))-η) := by
    have hh := gaussian_active_cover_scale h hδ hδ1 hεκ.le hD.le (le_refl Nc)
    have hr : δ+(2*(1/4))*δ+(C*δ)*M = D*δ := by dsimp [D]; ring
    rw [hr]
    exact hh.trans hcoverScale
  have hNc : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc := by
    intro w
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hJN w)
  obtain ⟨hCP,hCD,hCM⟩ := hcoeff L hL
  have hg := hgain N κ μ ν w₀ B E J a ρ L L K (Cm*L) Nc Z a₀
    (hδsmall.trans_le (min_le_left _ _)) hρ.le hδρ hB hν hstable hchartδ hμ hμmass hνmass
    hL0 hL0 hμball hνball hpair hK (Real.rpow_pos_of_pos hδ _) hZ hCP hCD hCM
    hcard hCK hlarge hbox ha₀ hH (le_refl a₀) hpcoef hqcoef hlow hactive
    hE hJ hNc hEb hanchors hcover
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
  have hlocal := gaussianLocalBandConstant_pos (n := h+1) hρ
  have hr' : B₀*(μ.prod ν).real E ≤ δ^κ₀ := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2:ℝ)^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ gaussianLocalBandConstant (h+1) ρ^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/K),B₀,Measure.real,one_div,
      K,Real.rpow_neg hδ.le,inv_inv,ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le κ₀),mul_assoc] using hr
  have habs' : (1/B₀)*δ^κ₀ ≤ δ^c := by
    have hh := rpow_absorb_constant (t := -κ₀) (u := -c) hδ (by
      convert ha using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf))
    simpa only [neg_neg] using hh
  have hI : (μ.prod ν).real E ≤ (1/B₀)*δ^κ₀ := by
    calc
      _ = (1/B₀)*(B₀*(μ.prod ν).real E) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)
  exact hI.trans habs'

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SmallGaussianChart
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed direction-chart radius for the controlled Gaussian slice geometry -/

namespace Falconer

theorem exists_small_gaussian_chart_radius (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
      (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 ∧
      4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
  let A : ℝ := 4*(h:ℝ)+1+8*(h:ℝ)*(h+2:ℝ)
  let ρ : ℝ := 1/(8*(A+1))
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : 8*(A+1)*ρ = 1 := by dsimp [ρ]; field_simp
  have hp : A*ρ ≤ 1/8 := by nlinarith
  have hcoef : (h:ℝ)*((h+2:ℝ)*2) ≤ A := by dsimp [A]; nlinarith
  refine ⟨ρ,hρ,?_,?_,?_⟩
  · nlinarith [mul_nonneg hA hρ.le]
  · have hb := mul_le_mul_of_nonneg_right hcoef hρ.le
    nlinarith
  · calc
      _ = A*ρ := by dsimp [A]; ring
      _ ≤ 1/8 := hp
      _ ≤ 1/4 := by norm_num

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NonendpointAngularGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonendpoint angular gain in every ambient dimension h+2 -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem nonendpoint_dyadic_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ρ,hρ,hρhalf,hstable,hchart⟩ := exists_small_gaussian_chart_radius h
  obtain ⟨ε,c₁,δ₁,hε,hc₁,hδ₁,hgain⟩ := nonendpoint_chart_angular_gain hpublished hq hq' hqt ht
    hC hρ hρhalf hstable hchart
  let H : ℝ := (2/ρ+1)^(h+2)
  let c := c₁/2
  have hc : 0 < c := by dsimp [c]; positivity
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(c₁-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop H)
  obtain ⟨δ₂,hδ₂,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp habs
  refine ⟨ε,c,min δ₁ δ₂,hε,hc,lt_min hδ₁ hδ₂,?_⟩
  intro N κ _ _ μ ν _ _ E J a hδsmall hμ hμmass hνmass hμball hνball hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hH : H*δ^c₁ ≤ δ^c := by
    have ha : H ≤ δ^(-(c₁-c)) := hready ⟨hδ,hδsmall.trans_le (min_le_right _ _)⟩
    have hh := rpow_absorb_constant (t := -c₁) (u := -c) hδ (by
      convert ha using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf))
    simpa only [neg_neg] using hh
  by_contra hn
  have hlarge : ENNReal.ofReal H*ENNReal.ofReal (δ^c₁) < (μ.prod ν) E := by
    apply lt_of_le_of_lt _ (lt_of_not_ge hn)
    rw [← ENNReal.ofReal_mul (by dsimp [H]; positivity)]
    exact ENNReal.ofReal_le_ofReal hH
  obtain ⟨w₀,hw₀⟩ := original_direction_chart_selection μ ν E hE hρ hlarge
  let ν' := ν.restrict (Metric.closedBall w₀ ρ)
  have hνsupport : ∀ᵐ w ∂ν', dist w w₀ ≤ ρ := ae_restrict_mem measurableSet_closedBall
  have hν'mass : ν' univ ≤ 1 := (Measure.restrict_le_self _).trans hνmass
  have hν'ball (x : Sphere (h+2)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε)*(1/(2:ℝ)^j)^q) :=
    (Measure.restrict_le_self _).trans (hνball x j hj)
  have hg := hgain N κ μ ν' w₀ E J a (hδsmall.trans_le (min_le_left _ _))
    hνsupport hμ hμmass hν'mass hμball hν'ball hE hJ hJN hEb hanchors hcover
  have hgle : (μ.prod ν') E ≤ ENNReal.ofReal (δ^c₁) := by
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (μ.prod ν') E)] using
      ENNReal.ofReal_le_ofReal hg
  exact (not_lt_of_ge hgle) hw₀

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointPowerAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict power gaps used in endpoint row and triple selection -/

namespace Falconer
open Real Filter
open scoped Topology

theorem eventually_const_mul_rpow_lt {p q : ℝ} (hpq : q < p) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ C*δ^p < δ^q := by
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show q-p < 0 by linarith)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  calc
    _ < δ^(q-p)*δ^p := mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = _ := by rw [← Real.rpow_add hδ.1]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointDyadicScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic cutoff and power conversions for endpoint assembly -/

namespace Falconer
open Filter
open scoped Topology

theorem dyadic_inverse_tendsto :
    Tendsto (fun N : ℕ => 1/(2:ℝ)^N) atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div,inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num : (2:ℝ)⁻¹ < 1))
  · filter_upwards [] with N
    change 0 < 1/(2:ℝ)^N
    positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PowerIncidenceMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning a power-small incidence into a power-small direction mass -/

namespace Falconer
open scoped ENNReal

theorem ennreal_mass_of_power_incidence {δ b c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbc : 2*b ≤ c) (M : ℝ≥0∞)
    (h : ENNReal.ofReal (δ^b)*M ≤ ENNReal.ofReal (δ^c)) : M ≤ ENNReal.ofReal (δ^b) := by
  have h0 : ENNReal.ofReal (δ^b) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ _))
  have hh := mul_le_mul' (le_refl ((ENNReal.ofReal (δ^b))⁻¹)) h
  rw [← mul_assoc,ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top,one_mul] at hh
  apply hh.trans
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hδ _),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_neg hδ.le,← Real.rpow_add hδ]
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteAnchorLabels
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite anchor labels for the measurable original tube lists -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem finiteAnchorLabels_mem (G J : Finset (Space d)) (a : {a // a ∈ G}) :
    a ∈ finiteAnchorLabels G J ↔ a.val ∈ J := by
  classical
  exact Finset.mem_subtype

theorem finiteAnchorLabels_card (G J : Finset (Space d)) (hJG : J ⊆ G) :
    (finiteAnchorLabels G J).card = J.card := by
  classical
  rw [finiteAnchorLabels,Finset.card_subtype]
  congr 1
  exact Finset.filter_eq_self.mpr (fun a ha => hJG ha)

theorem finiteAnchorLabels_measurable (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (a : {a // a ∈ G}) :
    MeasurableSet {w | a ∈ finiteAnchorLabels G (J w)} := by
  simpa only [finiteAnchorLabels_mem] using hJ a.val

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_OriginalCoverRestriction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Null original fiber losses stay null for every retained slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem product_inter_eq_of_null_original_fibers
    (μ α : Measure X) (β : Measure W) [SFinite α] [SFinite β] (hα : α ≪ μ)
    (E F : Set (X × W)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hzero : ∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) :
    (α.prod β) (E ∩ F) = (α.prod β) E := by
  have hz : (α.prod β) (E \ F) = 0 := by
    rw [Measure.prod_apply_symm (hE.diff hF)]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun w => hα (hzero w))
  apply measure_congr
  have hnot : ∀ᵐ t ∂α.prod β, t ∉ E \ F := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hnot] with t ht
  simp only [mem_sdiff] at ht
  apply propext
  change t ∈ E ∩ F ↔ t ∈ E
  simp only [mem_inter_iff]
  tauto

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PreparedTubeRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing a pointwise covered relation without losing original fiber mass -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem prepare_original_tube_relation (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset {a // a ∈ G}, ∃ F : Set (Space d × Sphere d),
        MeasurableSet F ∧ F ⊆ E ∧
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, (J w).card ≤ N) ∧
        (∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) ∧
        ∀ t ∈ F, ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a.val)‖ ≤ 2*ε+δ := by
  classical
  obtain ⟨G,hGb,J,hJ,hJG,hzero⟩ := original_tube_cover_choice μ E hE hδ N hbounded hcover
  let C : Set (Space d × Sphere d) :=
    {t | ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ 2*ε+δ}
  have hC : MeasurableSet C := finite_tube_cover_relation_measurable G J hJ
    (fun w => (hJG w).1) _
  refine ⟨G,hGb,(fun w => finiteAnchorLabels G (J w)),E ∩ C,hE.inter hC,inter_subset_left,
    finiteAnchorLabels_measurable G J hJ,?_,?_,?_⟩
  · intro w
    rw [finiteAnchorLabels_card G (J w) (hJG w).1]
    exact (hJG w).2
  · intro w
    have he : {x | (x,w) ∈ E ∧ (x,w) ∉ E ∩ C} =
        {x | (x,w) ∈ E ∧ ∀ a ∈ J w, ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} := by
      ext x
      constructor
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun a ha hp => hn ⟨hx,?_⟩⟩
        exact ⟨a,ha,hp⟩
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun ht => ?_⟩
        obtain ⟨a,ha,hp⟩ := ht.2
        exact hn a ha hp
    rw [he]
    exact hzero w
  · intro t ht
    obtain ⟨a,ha,hp⟩ := ht.2
    refine ⟨⟨a,(hJG t.2).1 ha⟩,?_,hp⟩
    exact (finiteAnchorLabels_mem G (J t.2) _).mpr ha

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_NonendpointTubeGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonendpoint angular decay for arbitrary original finite fiber covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem nonendpoint_dyadic_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν] (E : Set (Space (h+2) × Sphere (h+2))),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ u ∈ E, ‖u.1‖ ≤ 1/4) →
    (∀ w : Sphere (h+2), ∃ S : Finset (Space (h+2)),
      (S.card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε) ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S,
        ‖perpendicularPart (w:Space (h+2)) (x-a)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ε,c,δ₀,hε,hc,hδ₀,hgain⟩ := nonendpoint_dyadic_angular_gain hpublished hq hq' hqt ht
    (by linarith : 0 ≤ 2*C+1)
  refine ⟨ε,c,δ₀,hε,hc,hδ₀,?_⟩
  intro N μ ν _ _ E hδsmall hμ hμmass hνmass hμball hνball hE hEb hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨G,hG,J,F,hF,hFE,hJ,hcard,hzero,hcoverF⟩ :=
    prepare_original_tube_relation μ E hE hδ (Nat.floor (δ^(-q-ε))) hEb (by
      intro w
      obtain ⟨S,hS,hcoverS⟩ := hcover w
      exact ⟨S,Nat.le_floor hS,hcoverS⟩)
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    have hh := product_inter_eq_of_null_original_fibers μ μ ν Measure.AbsolutelyContinuous.rfl
      E F hE hF hzero
    simpa only [inter_eq_right.mpr hFE] using hh
  rw [← hmass]
  refine hgain N {a // a ∈ G} μ ν F J (fun a => a.val) hδsmall hμ hμmass hνmass
    hμball hνball hF hJ ?_ (fun u hu => hEb u (hFE hu)) (fun _ i _ => hG i.val i.property) ?_
  · intro w
    have hh : ((J w).card : ℝ) ≤ (Nat.floor (δ^(-q-ε)) : ℝ) := by exact_mod_cast hcard w
    exact hh.trans (Nat.floor_le (Real.rpow_nonneg hδ.le _))
  · intro u hu
    obtain ⟨a,ha,hp⟩ := hcoverF u hu
    refine ⟨a,ha,?_⟩
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NonendpointBadDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A universal Borel bad-direction envelope in the nonendpoint regime -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem nonendpoint_bad_direction_envelope (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q C : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ : Measure (Space (h+2))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      ∃ B : Set (Sphere (h+2)), MeasurableSet B ∧
        {w : Sphere (h+2) | ∃ S : Finset (Space (h+2)), (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {x | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+2)) (x-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        ∀ (ν : Measure (Sphere (h+2))) [IsFiniteMeasure ν], ν univ ≤ 1 →
          (∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
          ν B ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  classical
  obtain ⟨ε₀,c,δ₀,hε₀,hc,hδ₀,hgain⟩ := nonendpoint_dyadic_tube_gain hpublished hq hq' hqt ht
    (by linarith : 0 ≤ 2*C+1)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (dyadic_inverse_tendsto.eventually (Ioo_mem_nhdsGT hδ₀))
  let ε : ℝ := ε₀/2
  let b : ℝ := min ε (c/3)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb : 0 < b := lt_min hε (by positivity)
  have hεle : ε ≤ ε₀ := by dsimp [ε]; linarith
  have hble : b ≤ ε₀ := (min_le_left _ _).trans hεle
  have hbc : 2*b ≤ c := by have hh := min_le_right ε (c/3); dsimp [b]; linarith
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ _ hμ hμball
  let δ : ℝ := 1/(2:ℝ)^N
  let count : ℕ := Nat.floor (δ^(-q-b))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hL : δ^(-ε) ≤ δ^(-ε₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεle)
  obtain ⟨G,hG,hnet⟩ := exists_bounded_anchor_net (d := h+2) (1/4) hδ
  let B := finiteBadDirections μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
  refine ⟨B,finiteBadDirections_measurable μ G count _ _ _,?_,?_⟩
  · rintro w ⟨S,hS,hmass⟩
    have hh := original_bad_direction_mem_envelope μ G count (ENNReal.ofReal (δ^b))
      hμ hnet w S (Nat.le_floor hS) hmass
    have he : 2*(C*δ)+δ = (2*C+1)*δ := by ring
    change w ∈ finiteBadDirections μ G count (1/4) (2*(C*δ)+δ) (ENNReal.ofReal (δ^b)) at hh
    rw [he] at hh
    exact hh
  · intro ν _ hνmass hνball
    obtain ⟨J,F,hF,hJ,hJmeas,hFb,hcover,hlower⟩ :=
      exists_finite_bad_incidence μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
    have hcount : (count:ℝ) ≤ δ^(-q-ε₀) :=
      (Nat.floor_le (Real.rpow_nonneg hδ.le _)).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    have hupper := hgain N μ ν F (hN₀ N hN).2 hμ (by simp) hνmass
      (fun x j hj => (hμball x j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) t))))
      (fun w j hj => (hνball w j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) q))))
      hF hFb (by
          intro w
          refine ⟨J w,?_,?_⟩
          · exact (show ((J w).card:ℝ) ≤ count by exact_mod_cast (hJ w).2).trans hcount
          · intro x hx
            exact hcover (x,w) hx)
    exact ennreal_mass_of_power_incidence hδ hδ1 hbc (ν B) ((hlower ν).trans hupper)

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_WitnessDirection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unoriented closeness of a witness direction to the source-cell center -/

namespace Falconer
open NormedSpace
variable {d : ℕ}

theorem cell_center_witness_direction (w₀ : Sphere d) (x c z : Space d)
    {r D : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hzx : z ≠ x)
    (hzc : ‖z-c‖ ≤ D) :
    ‖normalize (c-x)+(normalizeToSphere w₀ (x-z):Space d)‖ ≤ 2*D/r := by
  rw [normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hzx.symm)]
  have hn : normalize (x-z) = -normalize (z-x) := by
    rw [show x-z = -(z-x) by abel,normalize_neg]
  rw [hn,← sub_eq_add_neg]
  apply (le_div_iff₀ hr).mpr
  have hh := normalize_distance_scaled hcx (sub_ne_zero.mpr hzx)
  rw [dist_eq_norm,dist_eq_norm,sub_sub_sub_cancel_right,norm_sub_rev c z] at hh
  nlinarith

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
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCollisionMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable radial collision masses and the original-pin Fubini identity -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialCollisionRelation_measurable (δ : ℝ) :
    MeasurableSet {p : (Space d × Space d) × Space d |
      dist (normalize (p.2-p.1.2)) (normalize (p.1.1-p.1.2)) ≤ δ} := by
  exact measurableSet_le
    ((measurable_normalized_vector (measurable_snd.sub measurable_fst.snd)).dist
      (measurable_normalized_vector (measurable_fst.fst.sub measurable_fst.snd)))
    measurable_const

theorem radialCollisionMass_measurable (μ : Measure (Space d)) [SFinite μ] (δ : ℝ) :
    Measurable (radialCollisionMass μ δ) :=
  measurable_measure_prodMk_left (radialCollisionRelation_measurable δ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoom
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive affine changes of scale preserve original radial directions -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem zoomPairSet_measurable (e : Space d ≃ₜ Space d)
    {G : Set (Space d × Space d)} (hG : MeasurableSet G) : MeasurableSet (zoomPairSet e G) :=
  hG.preimage (e.symm.measurable.prodMap e.symm.measurable)

theorem radial_collision_zoom (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z x : Space d) (θ : ℝ) :
    radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ
      (radialZoom a ha.ne' c z,radialZoom a ha.ne' c x) = radialCollisionMass μ θ (z,x) := by
  let e := radialZoom a ha.ne' c
  unfold radialCollisionMass
  rw [Measure.map_apply e.measurable (by
    apply measurableSet_le _ measurable_const
    exact (measurable_normalized_vector (measurable_id.sub measurable_const)).dist measurable_const)]
  congr 1
  ext y
  dsimp only [e]
  simp only [mem_preimage,mem_ofPred_eq,radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original radial laws and source balls under positive affine rescaling -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_preimage_ball {a : ℝ} (ha : 0 < a) (c x : Space d) (r : ℝ) :
    radialZoom a ha.ne' c ⁻¹' Metric.ball x r = Metric.ball (c+a⁻¹ • x) (r/a) := by
  ext z
  have he : a • (z-c)-x = a • (z-(c+a⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    abel
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,radialZoom_apply]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha,lt_div_iff₀ ha]
  rw [mul_comm a]

theorem radialZoom_ball_apply (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c x : Space d) (r : ℝ) :
    Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) =
      μ (Metric.ball (c+a⁻¹ • x) (r/a)) := by
  rw [Measure.map_apply (radialZoom a ha.ne' c).measurable Metric.isOpen_ball.measurableSet,
    radialZoom_preimage_ball ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded supports and Frostman bounds survive the fixed cell normalization -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_norm {a : ℝ} (ha : 0 < a) (c x : Space d) :
    ‖radialZoom a ha.ne' c x‖ = a*‖x-c‖ := by
  rw [radialZoom_apply,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem radialZoom_frostman_bound (μ : Measure (Space d))
    {a δ K s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hmass : μ univ ≤ 1) (c : Space d)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    ∀ x : Space d, ∀ r : ℝ, 0 < r → δ ≤ r →
      Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) ≤
        ENNReal.ofReal (K*a^(-s)*r^s) := by
  intro x r hr hδ
  rw [radialZoom_ball_apply μ ha]
  have hratio : 0 < r/a := div_pos hr ha
  have hrra : r ≤ r/a := (le_div_iff₀ ha).mpr (mul_le_of_le_one_right hr.le ha1)
  have he : K*(r/a)^s = K*a^(-s)*r^s := by
    rw [Real.div_rpow hr.le ha.le,div_eq_mul_inv,← Real.rpow_neg ha.le]
    ring
  rw [← he]
  by_cases hr1 : r/a ≤ 1
  · exact hball _ _ (hδ.trans hrra) hr1
  · have hp : 1 ≤ (r/a)^s := Real.one_le_rpow (le_of_not_ge hr1) hs
    have hcoeff : 1 ≤ K*(r/a)^s := by nlinarith
    exact ((measure_mono (subset_univ _)).trans hmass).trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hcoeff)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RadialZoomFiniteBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale conditional balls and reverse caps after a fixed contraction -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_ae_iff (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c : Space d) (P : Space d → Prop) :
    (∀ᵐ x ∂Measure.map (radialZoom a ha.ne' c) μ, P x) ↔
      ∀ᵐ x ∂μ, P (radialZoom a ha.ne' c x) := by
  have h := MeasurableEquiv.map_ae (radialZoom a ha.ne' c).toMeasurableEquiv μ
  change Filter.map (radialZoom a ha.ne' c) (ae μ) =
    ae (Measure.map (radialZoom a ha.ne' c) μ) at h
  rw [← h]
  rfl

theorem norm_radialZoom_sub {a : ℝ} (ha : 0 < a) (c x y : Space d) :
    ‖radialZoom a ha.ne' c x-radialZoom a ha.ne' c y‖ = a*‖x-y‖ := by
  rw [radialZoom_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem radialZoom_reverse_cap (ν : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z u : Space d) (r : ℝ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    Measure.map (radialZoom a ha.ne' c) ν
      {x | (radialZoom a ha.ne' c z,x) ∈ zoomPairSet (radialZoom a ha.ne' c) G ∧
        dist (normalize (x-radialZoom a ha.ne' c z)) u < r} =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} := by
  let e := radialZoom a ha.ne' c
  have hm : MeasurableSet {x | (e z,x) ∈ zoomPairSet e G ∧
      dist (normalize (x-e z)) u < r} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (measurableSet_lt ((measurable_normalized_vector
        (measurable_id.sub measurable_const)).dist measurable_const) measurable_const)
  rw [Measure.map_apply e.measurable hm]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
  dsimp only [e]
  rw [radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MiddleRadialTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric data for middle-interval pruning after cell normalization -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_quarter_bound {a : ℝ} (ha : 0 < a) (c z : Space d)
    (hz : ‖z-c‖ ≤ 1/(4*a)) : ‖radialZoom a ha.ne' c z‖ ≤ 1/4 := by
  rw [radialZoom_norm ha]
  calc
    _ ≤ a*(1/(4*a)) := mul_le_mul_of_nonneg_left hz ha.le
    _ = _ := by field_simp

theorem radialZoom_pin_distance {a r : ℝ} (ha : 0 < a) (c x : Space d)
    (hx : r ≤ ‖c-x‖) : a*r ≤ ‖(0:Space d)-radialZoom a ha.ne' c x‖ := by
  rw [zero_sub,norm_neg,radialZoom_norm ha,norm_sub_rev x c]
  exact mul_le_mul_of_nonneg_left hx ha.le

theorem radialZoom_pair_ae_bound (μ : Measure (Space d)) {a H : ℝ}
    (ha : 0 < a) (c x : Space d) (h : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) :
    ∀ᵐ y ∂Measure.map (radialZoom a ha.ne' c) μ,
      ‖y-radialZoom a ha.ne' c x‖ ≤ a*H := by
  rw [radialZoom_ae_iff μ ha]
  filter_upwards [h] with y hy
  rw [norm_radialZoom_sub ha]
  exact mul_le_mul_of_nonneg_left hy ha.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyCoverCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the fixed heavy-cover constant into the angular power margin -/

namespace Falconer
open Filter
open scoped ENNReal Topology

theorem heavy_cover_card_le {m : ℕ} {F K T : ℝ} (hF : 0 < F) (hK : 0 ≤ K)
    (h : (m:ℝ≥0∞)*ENNReal.ofReal F ≤ ENNReal.ofReal K) (hbudget : K ≤ T*F) :
    (m:ℝ) ≤ T := by
  have hm : ENNReal.ofReal ((m:ℝ)*F) ≤ ENNReal.ofReal K := by
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg m),ENNReal.ofReal_natCast] using h
  have hm' := (ENNReal.ofReal_le_ofReal_iff hK).mp hm
  nlinarith

theorem eventually_heavy_cover_card {q b K : ℝ} (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m : ℕ,
      (m:ℝ≥0∞)*ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) ≤ ENNReal.ofReal K →
      (m:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) := by
  have he := eventually_const_mul_rpow_lt (show -b/2 < (0:ℝ) by linarith) K
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (dyadic_inverse_tendsto.eventually he)
  refine ⟨N₀,fun N hN m hm => ?_⟩
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  apply heavy_cover_card_le (Real.rpow_pos_of_pos hδ _) hK hm
  have hbound : K ≤ (1/(2:ℝ)^N)^(-b/2) := by
    have hh := (hN₀ N hN).2
    simpa only [Real.rpow_zero,mul_one] using hh.le
  apply hbound.trans_eq
  rw [← Real.rpow_add hδ]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_RepresentedPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Threshold deletion using one witness only on represented pin fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem represented_threshold_pruning (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (G : Set (X × Y)) (hG : MeasurableSet G)
    (K : X × Y → ℝ≥0∞) (hK : Measurable K) (F a : ℝ≥0∞)
    (hsmall : ∀ y, (∃ x, (x,y) ∈ G) → μ {x | (x,y) ∈ G ∧ F < K (x,y)} ≤ a) :
    ∃ H : Set (X × Y), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ a*ν univ ∧ ∀ p ∈ H, K p ≤ F := by
  let H := G ∩ {p | K p ≤ F}
  have hH : MeasurableSet H := hG.inter (measurableSet_le hK measurable_const)
  refine ⟨H,hH,inter_subset_left,?_,fun p hp => hp.2⟩
  rw [Measure.prod_apply_symm (hG.diff hH)]
  apply (lintegral_mono _).trans_eq (lintegral_const a)
  intro y
  change μ {x | (x,y) ∈ G \ H} ≤ a
  by_cases hy : ∃ x, (x,y) ∈ G
  · apply (measure_mono _).trans (hsmall y hy)
    rintro x ⟨hx,hnot⟩
    exact ⟨hx,lt_of_not_ge (fun hk => hnot (show (x,y) ∈ H from ⟨hx,hk⟩))⟩
  · have he : {x | (x,y) ∈ G \ H} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun x hx => hy ⟨x,hx.1⟩
    rw [he,measure_empty]
    exact zero_le

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
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BoundedFrozenHeavyCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Heavy radial fibers have bounded-anchor frozen tube covers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem bounded_frozen_heavy_tube_cover (μ : Measure (Space (n+1))) (x c : Space (n+1))
    {r D δ C B : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y |
      ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ C*δ})
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ J : Finset (Space (n+1)),
      (∀ a ∈ J, ‖a‖ ≤ B) ∧
      (∀ z ∈ T, ∃ a ∈ J, ‖perpendicularPart (normalize (c-x)) (z-a)‖ ≤
        (2*((n+1:ℕ):ℝ)+1)*δ) ∧
      (J.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  obtain ⟨P,hP,hcard⟩ := frozen_heavy_tube_cover μ x c hr hcx hδ hfreeze hsource T hT F hheavy L hL
  obtain ⟨K,hKb,hKn⟩ := exists_bounded_anchor_net (d := n+1) B hδ
  let w : Sphere (n+1) := ⟨normalize (c-x),by
    rw [Metric.mem_sphere,dist_zero_right]
    exact norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))⟩
  obtain ⟨J,hJK,hJP,hJ⟩ := rounded_tube_cover w T P K
    (fun z hz => hKn z (hT z hz).2.2) hP
  refine ⟨J,fun a ha => hKb a (hJK ha),?_,?_⟩
  · intro z hz
    obtain ⟨a,ha,hza⟩ := hJ z hz
    refine ⟨a,ha,?_⟩
    change ‖perpendicularPart (normalize (c-x)) (z-a)‖ ≤ _ at hza
    convert hza using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hc : (J.card:ℝ≥0∞) ≤ P.card := by exact_mod_cast hJP
    exact (mul_le_mul' hc le_rfl).trans hcard

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MiddleHeavyRadialMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A good witness controls the full conditional heavy radial fiber -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem radial_collision_le_tube_mass (μ : Measure (Space (n+1)))
    (x z : Space (n+1)) (hz : z ≠ x) {H δ W : ℝ}
    (hsource : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) (hwidth : H*δ ≤ W) :
    radialCollisionMass μ δ (z,x) ≤
      μ {y | ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W} := by
  apply measure_mono_ae
  filter_upwards [hsource] with y hy
  intro hclose
  have hv : ‖normalize (z-x)‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hperp : ‖perpendicularPart (normalize (z-x)) (normalize (y-x))‖ ≤ δ := by
    have hh := norm_perpendicularPart_le hv (normalize (y-x)-normalize (z-x))
    rw [perpendicularPart_sub] at hh
    have he : perpendicularPart (normalize (z-x)) (normalize (z-x)) = 0 := by
      simp [perpendicularPart,hv]
    rw [he,sub_zero] at hh
    exact hh.trans hclose
  have he : perpendicularPart (normalize (z-x)) (y-x) =
      ‖y-x‖ • perpendicularPart (normalize (z-x)) (normalize (y-x)) := by
    rw [← perpendicularPart_smul,norm_smul_normalize]
  show ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact (mul_le_mul hy hperp (norm_nonneg _) ((norm_nonneg _).trans hy)).trans hwidth

theorem middle_heavy_radial_mass_lt (μ : Measure (Space (n+1)))
    (x c : Space (n+1)) {r D δ θ C B H η R : ℝ}
    (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ B) (hpin : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H)
    (hwidth : H*θ ≤ C*δ)
    (Bad : Set (Sphere (n+1))) (v : Sphere (n+1)) (hv : v ∉ Bad)
    (hdir : ‖normalize (c-x)-(v:Space (n+1))‖ ≤ η ∨
      ‖normalize (c-x)+(v:Space (n+1))‖ ≤ η)
    (hrobust : (2*((n+1:ℕ):ℝ)+1)*δ+2*η*(B+B) ≤ R)
    (F a : ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (henvelope : ∀ S : Finset (Space (n+1)),
      (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ →
      a ≤ μ {z | ∃ b ∈ S, ‖perpendicularPart (v:Space (n+1)) (z-b)‖ ≤ R} → v ∈ Bad)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B ∧
      F < radialCollisionMass μ θ (z,x)) : μ T < a := by
  obtain ⟨J,hJ,hcover,hcard⟩ := bounded_frozen_heavy_tube_cover μ x c hr hcx hδ
    hfreeze hsource T (fun z hz => ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1⟩)
    F (fun z hz => (hT z hz).2.2.2.le.trans
      (radial_collision_le_tube_mass μ x z (hT z hz).1 hpin hwidth)) L hL
  exact mass_lt_of_good_direction_cover μ Bad v hv _
    (norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))) hdir hrobust hbounded J hJ
    J.card le_rfl a (fun S hS => henvelope S
      ((mul_le_mul' (by exact_mod_cast hS) le_rfl).trans hcard)) T hcover

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialBadWitness
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deleting original pairs whose witness direction is exceptional -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialBadWitness_measurable (w₀ : Sphere d) {G : Set (Space d × Space d)}
    (hG : MeasurableSet G) {B : Set (Sphere d)} (hB : MeasurableSet B) :
    MeasurableSet (radialBadWitness w₀ G B) :=
  hG.inter (hB.preimage ((normalizeToSphere_measurable w₀).comp
    (measurable_snd.sub measurable_fst)))

theorem radial_bad_witness_mass (w₀ : Sphere d) (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (B : Set (Sphere d)) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤ c) :
    (μ.prod ν) (radialBadWitness w₀ G B) ≤ c*μ univ := by
  rw [Measure.prod_apply (radialBadWitness_measurable w₀ hG hB)]
  have he (z : Space d) : ν {x | (z,x) ∈ radialBadWitness w₀ G B} =
      originalRadialSphereLaw w₀ ν G z B := by
    rw [originalRadialSphereLaw_apply w₀ ν G z B hB]
    rfl
  change (∫⁻ z, ν {x | (z,x) ∈ radialBadWitness w₀ G B} ∂μ) ≤ c*μ univ
  simp_rw [he]
  exact (lintegral_mono_ae hsmall).trans_eq (lintegral_const c)

theorem direction_good_of_not_radialBadWitness (w₀ : Sphere d)
    (G : Set (Space d × Space d)) (B : Set (Sphere d)) {z x : Space d}
    (hgood : (z,x) ∈ G \ radialBadWitness w₀ G B) :
    normalizeToSphere w₀ (x-z) ∉ B := by
  intro hb
  exact hgood.2 ⟨hgood.1,hb⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MiddleRadialPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-product middle-interval pruning with no choice of pin witnesses -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem middle_radial_pruning (μ ν : Measure (Space (n+1)))
    [SFinite μ] [SFinite ν] (w₀ : Sphere (n+1))
    (G : Set (Space (n+1) × Space (n+1))) (hG : MeasurableSet G)
    (Bad : Set (Sphere (n+1))) (hBad : MeasurableSet Bad)
    (c : Space (n+1)) {r D δ θ C B H R : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hfreeze : 8*D^2/r ≤ δ)
    (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D) (hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ B)
    (hgeom : ∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (hpin : ∀ x, (∃ z, (z,x) ∈ G) →
      r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H)
    (hwidth : H*θ ≤ C*δ)
    (hrobust : (2*((n+1:ℕ):ℝ)+1)*δ+2*(2*D/r)*(B+B) ≤ R)
    (F a e : ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (henvelope : ∀ v : Sphere (n+1), ∀ S : Finset (Space (n+1)),
      (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ →
      a ≤ μ {z | ∃ b ∈ S, ‖perpendicularPart (v:Space (n+1)) (z-b)‖ ≤ R} → v ∈ Bad)
    (hbadmass : (μ.prod ν) (radialBadWitness w₀ G Bad) ≤ e) :
    ∃ G' : Set (Space (n+1) × Space (n+1)), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ e+a*ν univ ∧
      ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let G₁ := G \ radialBadWitness w₀ G Bad
  have hG₁ : MeasurableSet G₁ := hG.diff (radialBadWitness_measurable w₀ hG hBad)
  have hsub : G₁ ⊆ G := sdiff_subset
  have hsmall (x : Space (n+1)) (hx : ∃ z, (z,x) ∈ G₁) :
      μ {z | (z,x) ∈ G₁ ∧ F < radialCollisionMass μ θ (z,x)} ≤ a := by
    obtain ⟨z,hz⟩ := hx
    have hzx := hgeom z x (hsub hz)
    have hpx := hpin x ⟨z,hsub hz⟩
    let v := normalizeToSphere w₀ (x-z)
    have hv : v ∉ Bad := direction_good_of_not_radialBadWitness w₀ G Bad hz
    apply le_of_lt
    apply middle_heavy_radial_mass_lt μ x c hr hpx.1 hδ hfreeze hsource hbounded
      hpx.2 hwidth Bad v hv (Or.inr (cell_center_witness_direction w₀ x c z hr
        hpx.1 hzx.1 hzx.2.1)) hrobust F a L hL (henvelope v)
    intro y hy
    have hh := hgeom y x (hsub hy.1)
    exact ⟨hh.1,hh.2.1,hh.2.2,hy.2⟩
  obtain ⟨G',hG',hG'sub,hdeleted,hbound⟩ := represented_threshold_pruning μ ν G₁ hG₁
    (radialCollisionMass μ θ) (radialCollisionMass_measurable μ θ) F a hsmall
  refine ⟨G',hG',hG'sub.trans hsub,?_,hbound⟩
  have hcover : G \ G' ⊆ radialBadWitness w₀ G Bad ∪ (G₁ \ G') := by
    intro p hp
    by_cases hb : p ∈ radialBadWitness w₀ G Bad
    · exact Or.inl hb
    · exact Or.inr ⟨⟨hp.1,hb⟩,hp.2⟩
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add hbadmass hdeleted))

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
-- module Solutions.OAIQ088_FD.Falconer_Radial_NonendpointRadialBadDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonendpoint angular gain for the original radial witness pairs -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_radial_bad_directions (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q C : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∃ B : Set (Sphere (h+2)), MeasurableSet B ∧
        {w : Sphere (h+2) | ∃ S : Finset (Space (h+2)),
          (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {z | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+2)) (z-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        (μ.prod ν) (radialBadWitness w₀ G B) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := nonendpoint_bad_direction_envelope hpublished hq hq' hqt ht hC
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hdiag hμ hμball hdata
  obtain ⟨B,hB,hcontains,hbound⟩ := hN₀ N hN μ hμ hμball
  refine ⟨B,hB,hcontains,?_⟩
  have hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤
      ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
    filter_upwards [hdata] with z hz
    apply hbound (originalRadialSphereLaw w₀ ν G z)
      ((originalRadialSphereLaw_mass_le w₀ ν G z).trans hν)
    intro w j hj
    rw [originalRadialSphereLaw_ball w₀ ν G z (hdiag z)]
    exact hz w j hj
  simpa only [measure_univ,mul_one] using radial_bad_witness_mass w₀ μ ν G hG B hB _ hsmall

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_NonendpointMiddleRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative middle-interval improvement from the published planar input -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_middle_radial_pruning (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z‖ ≤ 1/4) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/r ≤ 1/(2:ℝ)^N →
      H*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(0:Space (h+2))-x‖ ∧
        ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) := by
  let C : ℝ := 2*((h+2:ℕ):ℝ)+2
  let L : ℕ := h+5
  let K : ℕ := (2*L+1)^(h+2)
  obtain ⟨ε,b,hε,hb,N₁,hN₁⟩ := nonendpoint_radial_bad_directions hpublished hq hq' hqt ht
    (show 0 ≤ C by dsimp [C]; positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_heavy_cover_card (q := q) (K := (K:ℝ)) hb (by positivity)
  refine ⟨ε,b,hε,hb,max N₁ N₂,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hgeom hμ hballs hcaps r H θ hr hfreeze hwidth hpin
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Bad,hBad,hcontains,hbadmass⟩ := hN₁ N ((le_max_left _ _).trans hN) μ ν hν
    w₀ G hG (fun z x hx => (hgeom z x hx).1.symm) hμ hballs hcaps
  have hL : 1+1+((h+1+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) := by dsimp [L]; push_cast; linarith
  have hrobust : (2*((h+1+1:ℕ):ℝ)+1)*δ+2*(2*(1/4)/r)*(1/4+1/4) ≤ C*δ := by
    have he : 2*(2*(1/4:ℝ)/r)*(1/4+1/4) = 8*(1/4:ℝ)^2/r := by ring
    rw [he]
    dsimp [C]
    change 8*(1/4:ℝ)^2/r ≤ δ at hfreeze
    nlinarith
  have henv (v : Sphere (h+2)) (S : Finset (Space (h+2)))
      (hc : (S.card:ℝ≥0∞)*ENNReal.ofReal (δ^(q+b/2)) ≤
        ((2*L+1)^(h+1+1):ℕ)*μ univ)
      (hm : ENNReal.ofReal (δ^b) ≤
        μ {z | ∃ a ∈ S, ‖perpendicularPart (v:Space (h+2)) (z-a)‖ ≤ C*δ}) : v ∈ Bad := by
    apply hcontains
    refine ⟨S,?_,hm⟩
    apply hN₂ N ((le_max_right _ _).trans hN) S.card
    simpa only [measure_univ,mul_one,ENNReal.ofReal_natCast] using hc
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := middle_radial_pruning (θ := θ) (n := h+1) μ ν w₀ G hG
    Bad hBad 0 hr hδ hfreeze (by simpa only [sub_zero] using hμ) hμ
    (fun z x hx => ⟨(hgeom z x hx).1,by simpa only [sub_zero] using (hgeom z x hx).2,
      (hgeom z x hx).2⟩) hpin (by simpa only [one_mul] using hwidth) hrobust (ENNReal.ofReal (δ^(q+b/2)))
    (ENNReal.ofReal (δ^b)) (ENNReal.ofReal (δ^b)) L hL henv hbadmass
  refine ⟨G',hG',hsub,hdel.trans ?_,hbound⟩
  calc
    _ ≤ ENNReal.ofReal (δ^b)+ENNReal.ofReal (δ^b)*1 :=
      add_le_add le_rfl (mul_le_mul' le_rfl hν)
    _ = 2*ENNReal.ofReal (δ^b) := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling conditional radial pruning back to the unchanged original pair law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_pruning_unzoom (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν]
    {a : ℝ} (ha : 0 < a) (c : Space d)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (H : Set (Space d × Space d)) (hH : MeasurableSet H)
    (hsub : H ⊆ zoomPairSet (radialZoom a ha.ne' c) G)
    (θ : ℝ) (F E : ℝ≥0∞)
    (hdel : ((Measure.map (radialZoom a ha.ne' c) μ).prod
      (Measure.map (radialZoom a ha.ne' c) ν))
      (zoomPairSet (radialZoom a ha.ne' c) G \ H) ≤ E)
    (hbound : ∀ p ∈ H, radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ p ≤ F) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ E ∧ ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let e := radialZoom a ha.ne' c
  let G' := (Prod.map e e) ⁻¹' H
  have hG' : MeasurableSet G' := hH.preimage (e.measurable.prodMap e.measurable)
  refine ⟨G',hG',?_,?_,?_⟩
  · intro p hp
    exact (mem_zoomPairSet e G p.1 p.2).mp (hsub hp)
  · have he : (Prod.map e e) ⁻¹' (zoomPairSet e G \ H) = G \ G' := by
      ext p
      change ((e p.1,e p.2) ∈ zoomPairSet e G ∧ (e p.1,e p.2) ∉ H) ↔
        ((p.1,p.2) ∈ G ∧ (e p.1,e p.2) ∉ H)
      rw [mem_zoomPairSet]
    rw [← he,← Measure.map_apply (e.measurable.prodMap e.measurable)
      ((zoomPairSet_measurable e hG).diff hH),← Measure.map_prod_map μ ν e.measurable e.measurable]
    exact hdel
  · intro p hp
    have hh := hbound (e p.1,e p.2) hp
    rwa [radial_collision_zoom μ ha c p.1 p.2 θ] at hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NonendpointOriginalMiddle
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonendpoint middle-interval pruning in the original source-cell coordinates -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_original_middle_pruning (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+2)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+2)) (c : Space (h+2)) (a : ℝ), 0 < a →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ 1/(4*a)) →
      (∀ᵐ z ∂μ, ‖z-c‖ ≤ 1/(4*a)) →
      (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N → μ (Metric.ball x ((1/(2:ℝ)^j)/a)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/(a*r) ≤ 1/(2:ℝ)^N →
      (a*H)*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := nonendpoint_middle_radial_pruning hpublished hq hq' hqt ht
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ c a ha G hG hgeom hμ hball hcap r H θ hr hfreeze hwidth hpin
  let e := radialZoom a ha.ne' c
  have hν' : Measure.map e ν univ ≤ 1 := by
    simpa only [Measure.map_apply e.measurable MeasurableSet.univ,preimage_univ] using hν
  have hgeom' : ∀ z x, (z,x) ∈ zoomPairSet e G → z ≠ x ∧ ‖z‖ ≤ 1/4 := by
    intro z x hx
    have hh := hgeom (e.symm z) (e.symm x) hx
    refine ⟨fun he => hh.1 (congrArg e.symm he),?_⟩
    have hn := radialZoom_quarter_bound ha c (e.symm z) hh.2
    change ‖e (e.symm z)‖ ≤ 1/4 at hn
    simpa only [e.apply_symm_apply] using hn
  have hμ' : ∀ᵐ z ∂Measure.map e μ, ‖z‖ ≤ 1/4 := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hμ] with z hz
    exact radialZoom_quarter_bound ha c z hz
  have hball' : ∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      Measure.map e μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t) := by
    intro x j hj
    rw [radialZoom_ball_apply μ ha]
    exact hball _ j hj
  have hcap' : ∀ᵐ z ∂Measure.map e μ, ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧
        dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q) := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hcap] with z hz
    intro w j hj
    rw [radialZoom_reverse_cap ν ha c z w _ G hG]
    exact hz w j hj
  have hpin' : ∀ x, (∃ z, (z,x) ∈ zoomPairSet e G) →
      a*r ≤ ‖(0:Space (h+2))-x‖ ∧ ∀ᵐ y ∂Measure.map e μ, ‖y-x‖ ≤ a*H := by
    intro x hx
    obtain ⟨z,hz⟩ := hx
    have hp := hpin (e.symm x) ⟨e.symm z,hz⟩
    have he : e (e.symm x) = x := e.apply_symm_apply x
    refine ⟨?_,?_⟩
    · have hd := radialZoom_pin_distance ha c (e.symm x) hp.1
      change a*r ≤ ‖(0:Space (h+2))-e (e.symm x)‖ at hd
      simpa only [he] using hd
    · have hb := radialZoom_pair_ae_bound μ ha c (e.symm x) hp.2
      change ∀ᵐ y ∂Measure.map e μ, ‖y-e (e.symm x)‖ ≤ a*H at hb
      simpa only [he] using hb
  haveI : IsProbabilityMeasure (Measure.map e μ) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := hN₀ N hN (Measure.map e μ) (Measure.map e ν) hν'
    w₀ (zoomPairSet e G) (zoomPairSet_measurable e hG) hgeom' hμ' hball' hcap'
    (a*r) (a*H) θ (mul_pos ha hr) hfreeze hwidth hpin'
  exact radial_pruning_unzoom μ ν ha c G hG G' hG' hsub θ _ _ hdel hbound

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FiniteScaleBall
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale balls and the support of the actual rescaled laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]

namespace Regularization
variable {d : ℕ}

theorem rescaled_cell_norm_bound (Q : DyadicCube d) (hQ : Q.side = 1)
    (P : CellPath d) {z : Space d} (hz : z ∈ (Q.descendant P).carrier) :
    ‖cellScaleMap P.length (Q.descendant P).center z‖ ≤ Real.sqrt d := by
  have hs : 0 < (Q.descendant P).side := by rw [Q.descendant_side,hQ]; positivity
  have hdist := (Q.descendant P).dist_le hs.le hz ((Q.descendant P).center_mem hs)
  rw [cellScaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^P.length)]
  rw [dist_eq_norm] at hdist
  calc
    _ ≤ (2:ℝ)^P.length*(Real.sqrt d*(Q.descendant P).side) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = Real.sqrt d := by rw [Q.descendant_side,hQ]; field_simp

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileIncrementFrostman
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning a contact-interval profile inequality into actual conditional ball bounds -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem profileDrop_le_of_increment (m : ℝ → ℝ) (N : ℕ) (s E : ℝ)
    {p t : ℕ} (hpt : p ≤ t)
    (hinc : ∀ n, p ≤ n → n ≤ t → s*(n-p:ℕ)/N-E ≤ m n-m p) :
    profileDrop m N s p t ≤ E := by
  obtain ⟨i,hpi,hit,hmin⟩ := PlanarFalconer.intervalMin_attained
    (fun n : ℕ => m n-s*(n:ℝ)/N) hpt
  unfold profileDrop
  rw [hmin]
  have hh := hinc i hpi hit
  rw [Nat.cast_sub hpi] at hh
  have he : s*((i:ℝ)-(p:ℝ))/N = s*(i:ℝ)/N-s*(p:ℝ)/N := by ring
  rw [he] at hh
  linarith

theorem sourceClass_conditional_frostman_of_increment (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E : ℝ} (hs : 0 ≤ s) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 1/(2:ℝ)^(t-p) ≤ r → r ≤ 1 →
      (Measure.map (cellScaleMap p (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)) (ball x r) ≤
      ENNReal.ofReal ((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam)*r^s) := by
  intro x r hr hr1
  apply (sourceClass_conditional_frostman Q hQ μ hN hB hs hwidth hlarge hp₀ hpt htN hP hPpos x r hr hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^(t-p) by positivity).trans hr
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0 s)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  exact add_le_add (profileDrop_le_of_increment _ N s E hpt hinc) le_rfl

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CellNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual cell normalization used by the middle radial interval -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem cell_normalization_map (ρ : Measure (Space d)) (p : ℕ) (c : Space d)
    {b : ℝ} (hb : 0 < b) :
    Measure.map (radialZoom (b*(2:ℝ)^p) (by positivity) c) ρ =
      Measure.map (radialZoom b hb.ne' 0) (Measure.map (cellScaleMap p c) ρ) := by
  rw [Measure.map_map (radialZoom b hb.ne' 0).measurable (cellScaleMap_continuous p c).measurable]
  congr 1
  ext x
  simp only [Function.comp_apply,radialZoom_apply,cellScaleMap,sub_zero,smul_smul]

theorem cell_normalization_quarter_point (Q : DyadicCube d) (hQ : Q.side = 1)
    (P : CellPath d) {b : ℝ} (hb : 0 < b) (hsmall : b*Real.sqrt d ≤ 1/4)
    {z : Space d} (hz : z ∈ (Q.descendant P).carrier) :
    ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^P.length)) := by
  have hh := rescaled_cell_norm_bound Q hQ P hz
  rw [cellScaleMap,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^P.length)] at hh
  have hm := (mul_le_mul_of_nonneg_left hh hb.le).trans hsmall
  apply (le_div_iff₀ (by positivity : 0 < 4*(b*(2:ℝ)^P.length))).mpr
  nlinarith

theorem conditional_frostman_coefficient_ge_one (d N : ℕ) {s E lam : ℝ}
    (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam) :
    1 ≤ (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) := by
  have hdim : (1:ℝ) ≤ (((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ) := by
    exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ 2*Nat.ceil (2+4*Real.sqrt d)+1) :
      1 ≤ (2*Nat.ceil (2+4*Real.sqrt d)+1)^d)
  have htwo : 1 ≤ (2:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have hR : 1 ≤ ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hdim htwo) hR

theorem sourceClass_normalized_conditional_frostman (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t : ℕ} (hpt : p ≤ t) (htN : t ≤ N) {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) :
    ∀ x : Space d, ∀ r : ℝ, 0 < r → 1/(2:ℝ)^(t-p) ≤ r →
      Measure.map (radialZoom (b*(2:ℝ)^p) (by positivity) (Q.descendant P).center)
        (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
        (Metric.ball x r) ≤
      ENNReal.ofReal (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
        ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)*r^s) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hPpos
  intro x r hr hδ
  rw [cell_normalization_map _ _ _ hb]
  apply radialZoom_frostman_bound _ hb hb1
    (conditional_frostman_coefficient_ge_one d N hs hE hlam) hs (by
      haveI := Measure.isProbabilityMeasure_map (μ := ProbabilityTheory.cond (sourceClass Q μ N B p₀)
        (Q.descendant P).carrier) (cellScaleMap_continuous p (Q.descendant P).center).aemeasurable
      exact prob_le_one) 0
    (sourceClass_conditional_frostman_of_increment Q hQ μ hN hB hs hwidth hlarge
      hp₀ hpt htN hP hPpos hinc) x r hr hδ

theorem sourceClass_scaled_dyadic_ball (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b K : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t M : ℕ} (hpt : p ≤ t) (htN : t ≤ N) (hM : M ≤ t-p)
    {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)) ≤ K) :
    ∀ x : Space d, ∀ j : ℕ, j ≤ M →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
        (Metric.ball x ((1/(2:ℝ)^j)/(b*(2:ℝ)^p))) ≤
          ENNReal.ofReal (K*(1/(2:ℝ)^j)^s) := by
  intro x j hj
  have ha : 0 < b*(2:ℝ)^p := by positivity
  have hr : 1/(2:ℝ)^(t-p) ≤ 1/(2:ℝ)^j :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (hj.trans hM))
  have hh := sourceClass_normalized_conditional_frostman Q hQ μ hN hB hs hE hlam hb hb1
    hwidth hlarge hp₀ hpt htN hP hPpos hinc
    (radialZoom (b*(2:ℝ)^p) ha.ne' (Q.descendant P).center x)
    (1/(2:ℝ)^j) (by positivity) hr
  rw [radialZoom_ball_apply _ ha] at hh
  have hc : (Q.descendant P).center+(b*(2:ℝ)^p)⁻¹ •
      radialZoom (b*(2:ℝ)^p) ha.ne' (Q.descendant P).center x = x := by
    simp only [radialZoom_apply,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    abel
  rw [hc] at hh
  apply hh.trans
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef (by positivity))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SourceClassMiddleData
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual conditional source data for either middle-interval angular theorem -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem source_class_middle_data (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s E b K : ℝ} (hs : 0 ≤ s) (hE : 0 ≤ E) (hlam : 0 ≤ lam)
    (hb : 0 < b) (hb1 : b ≤ 1) (hsmall : b*Real.sqrt d ≤ 1/4)
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {p t M : ℕ} (hpt : p ≤ t) (htN : t ≤ N) (hM : M ≤ t-p)
    {P : CellPath d} (hP : P.length = p)
    (hPpos : 0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier)
    (hinc : ∀ n, p ≤ n → n ≤ t →
      s*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p)
    (hcoef : (((((2*Nat.ceil (2+4*Real.sqrt d)+1)^d:ℕ):ℝ)*(2:ℝ)^s*
      ((2:ℝ)^N)^(E+2*((d:ℝ)+1)*lam))*b^(-s)) ≤ K) :
    (∀ z ∈ (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p))) ∧
    (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p))) ∧
    (∀ x : Space d, ∀ j : ℕ, j ≤ M →
      ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier
        (Metric.ball x ((1/(2:ℝ)^j)/(b*(2:ℝ)^p))) ≤
          ENNReal.ofReal (K*(1/(2:ℝ)^j)^s)) := by
  have hpoint : ∀ z ∈ (Q.descendant P).carrier,
      ‖z-(Q.descendant P).center‖ ≤ 1/(4*(b*(2:ℝ)^p)) := by
    intro z hz
    simpa only [hP] using cell_normalization_quarter_point Q hQ P hb hsmall hz
  refine ⟨hpoint,ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable hpoint,?_⟩
  exact sourceClass_scaled_dyadic_ball Q hQ μ hN hB hs hE hlam hb hb1 hwidth hlarge
    hp₀ hpt htN hM hP hPpos hinc hcoef

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_NonendpointSourceMiddle
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonendpoint middle estimate for an actual regularized source cell -/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_source_class_middle_pruning_oai (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ∀ (Q : DyadicCube (h+2)), Q.side = 1 →
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
      ν univ ≤ 1 → ∀ N B : ℕ, 0 < N → 0 < B →
      ∀ lam E σ : ℝ, 0 ≤ E → 0 ≤ lam → 0 < σ → σ ≤ 1 → σ*Real.sqrt (h+2:ℕ) ≤ 1/4 →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ p v : ℕ, p ≤ v → v ≤ N → M ≤ v-p →
      ∀ P : CellPath (h+2), P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      (∀ n, p ≤ n → n ≤ v →
        t*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) →
      (((((2*Nat.ceil (2+4*Real.sqrt (h+2:ℕ))+1)^(h+2):ℕ):ℝ)*(2:ℝ)^t*
        ((2:ℝ)^N)^(E+2*(((h+2:ℕ):ℝ)+1)*lam))*σ^(-t)) ≤ (1/(2:ℝ)^M)^(-ε) →
      ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ z ∈ (Q.descendant P).carrier) →
      (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
        ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ M →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^M)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M →
      ((σ*(2:ℝ)^p)*H)*θ ≤ 1/(2:ℝ)^M →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(Q.descendant P).center-x‖ ∧
        ∀ᵐ y ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
          (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^M)^b) ∧
        ∀ z ∈ G', radialCollisionMass
          (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) θ z ≤
            ENNReal.ofReal ((1/(2:ℝ)^M)^(q+b/2)) := by
  obtain ⟨ε,b,hε,hb,M₀,hM₀⟩ := nonendpoint_original_middle_pruning hpublished hq hq' hqt ht
  refine ⟨ε,b,hε,hb,M₀,?_⟩
  intro M hM Q hQ μ ν _ _ hν N B hN hB lam E σ hE hlam hσ hσ1 hsmall hwidth hlarge
    p₀ hp₀ p v hpv hvN hMv P hP hpos hinc hcoef w₀ G hG hgeom hcap r H θ hr hfreeze hwidth' hpin
  have ht0 : 0 ≤ t := by have hh : (0:ℝ) ≤ h := Nat.cast_nonneg h; linarith
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have : IsProbabilityMeasure (ProbabilityTheory.cond (sourceClass Q μ N B p₀)
      (Q.descendant P).carrier) := sourceClass_conditional_probability Q hside μ N B hp₀ P hpos
  have hdata := source_class_middle_data Q hQ μ hN hB ht0 hE hlam hσ hσ1 hsmall hwidth hlarge
    hp₀ hpv hvN hMv hP hpos hinc hcoef
  exact hM₀ M hM _ ν hν w₀ (Q.descendant P).center (σ*(2:ℝ)^p) (by positivity) G hG
    (fun z x hz => ⟨(hgeom z x hz).1,hdata.1 z (hgeom z x hz).2⟩)
    hdata.2.1 hdata.2.2 hcap r H θ hr hfreeze hwidth' hpin

end Falconer.Regularization

end OAI
end

theorem solution : type_of% @OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning_oai := @OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning_oai
