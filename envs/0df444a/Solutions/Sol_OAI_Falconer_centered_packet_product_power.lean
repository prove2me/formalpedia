-- Prove2me | solution 1 for OAI.Falconer.centered_packet_product_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:04:17.974224+00:00
-- url     : https://prove2.me/submissions/cd255cab-7877-421a-b73f-36f644be017a

import Mathlib
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_coordinate_graph_obstruction

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TubeSecondMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite incidence identities before the geometric common-tube bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_tube_membership (U S : Finset (Space 2)) (hS : S ⊆ U) :
    (∑ l ∈ U, if l ∈ S then (1 : ℝ) else 0) = S.card := by
  rw [← Finset.sum_filter]
  have he : U.filter (fun l => l ∈ S) = S := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hl => hS hl)
  rw [he]
  simp

theorem sum_tubeDegree (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, tubeDegree P T l) = ∑ x ∈ P, ((T x).card : ℝ) := by
  unfold tubeDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_tube_membership _ _ (Finset.subset_biUnion_of_mem T hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoPointTubeGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point localization of actual bounded-chart tube parameters.
This is the elementary incidence kernel used in the multiscale Furstenberg proof. -/
namespace Falconer
open Set

theorem planar_dist_le_coordinate_sum (x y : Space 2) :
    dist x y ≤ |x 0-y 0| + |x 1-y 1| := by
  have he := EuclideanSpace.dist_sq_eq x y
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at he
  nlinarith [dist_nonneg (x := x) (y := y), abs_nonneg (x 0-y 0),
    abs_nonneg (x 1-y 1), sq_abs (x 0-y 0), sq_abs (x 1-y 1),
    mul_nonneg (abs_nonneg (x 0-y 0)) (abs_nonneg (x 1-y 1))]

theorem tube_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l : Space 2}
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) :
    |x 1-l 0*x 0-l 1| ≤ 2*δ := by
  have hs : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1+(l 0)^2) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    have hsq := (sq_le_sq₀ (abs_nonneg (l 0)) zero_le_one).mpr hl
    nlinarith [sq_abs (l 0)]
  exact ((div_le_iff₀ hs).mp hi).trans (by nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The row geometry in Orponen--Shmerkin, Appendix A.7, expressed in the
original line chart. A line is incident to only a bounded number of points
on a separated row. Its parameter projection stays close to that row point. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem rowPoint_dist (y x z : ℝ) : dist (rowPoint y x) (rowPoint y z) = |x-z| := by
  have he := EuclideanSpace.dist_sq_eq (rowPoint y x) (rowPoint y z)
  simp only [Fin.sum_univ_two,rowPoint_zero,rowPoint_one,Real.dist_eq,sq_abs] at he
  nlinarith [dist_nonneg (x := rowPoint y x) (y := rowPoint y z),abs_nonneg (x-z),sq_abs (x-z)]

theorem lineParameterProjection_dist {y : ℝ} (hy : |y| ≤ 1) (l m : Space 2) :
    |lineParameterProjection y l-lineParameterProjection y m| ≤ 2*dist l m := by
  have h0 : |l 0-m 0| ≤ dist l m := by
    simpa only [dist_eq_norm,Real.norm_eq_abs,PiLp.sub_apply] using (PiLp.norm_apply_le (l-m) 0)
  have h1 : |l 1-m 1| ≤ dist l m := by
    simpa only [dist_eq_norm,Real.norm_eq_abs,PiLp.sub_apply] using (PiLp.norm_apply_le (l-m) 1)
  calc
    _ = |y*(l 0-m 0)+(l 1-m 1)| := by unfold lineParameterProjection; congr 1; ring
    _ ≤ |y| * |l 0-m 0|+|l 1-m 1| := by simpa only [abs_mul] using abs_add_le (y*(l 0-m 0)) (l 1-m 1)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hy (abs_nonneg (l 0-m 0))]

theorem tube_projection_near {δ : ℝ} (hδ : 0 ≤ δ) {x l : Space 2}
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) :
    |x 1-lineParameterProjection (x 0) l| ≤ 2*δ := by
  simpa only [lineParameterProjection,mul_comm,sub_add_eq_sub_sub] using tube_residual_le hδ hl hi

theorem row_dist_projection {x : Space 2} {y : ℝ} (hy : x 0 = y) (v : ℝ) :
    dist x (rowPoint y v) = |x 1-v| := by
  have hx : x = rowPoint y (x 1) := by
    ext i
    fin_cases i
    · exact hy
    · rfl
  rw [hx,rowPoint_dist]
  rfl

theorem separated_row_tube_count {δ y : ℝ} (hδ : 0 < δ)
    {P : Finset (Space 2)} (hP : FiniteSeparatedAt δ P)
    (hrow : ∀ x ∈ P, x 0 = y) {l : Space 2} (hl : |l 0| ≤ 1) :
    ((P.filter fun x => TubeIncident δ x l).card : ℝ) ≤ 25 := by
  classical
  have hb := separated_ball_card (P.filter fun x => TubeIncident δ x l)
    (rowPoint y (lineParameterProjection y l)) hδ (r := 2*δ) (by positivity)
    (fun x hx z hz hne => hP x (Finset.mem_filter.mp hx).1 z (Finset.mem_filter.mp hz).1 hne)
    (fun x hx => ?_)
  · have he : 2*(2*δ)/δ+1 = (5 : ℝ) := by field_simp; ring
    norm_num only [he] at hb
    exact hb
  · obtain ⟨hxP,hxi⟩ := Finset.mem_filter.mp hx
    rw [row_dist_projection (hrow x hxP)]
    have hh := tube_projection_near hδ.le hl hxi
    rwa [hrow x hxP] at hh

theorem row_tube_union_count {δ y : ℝ} (hδ : 0 < δ)
    {P : Finset (Space 2)} (hP : FiniteSeparatedAt δ P)
    (hrow : ∀ x ∈ P, x 0 = y) (T : Space 2 → Finset (Space 2))
    (hchart : ∀ x ∈ P, InBoundedLineChart (T x))
    (hinc : ∀ x ∈ P, ∀ l ∈ T x, TubeIncident δ x l) :
    (∑ x ∈ P, ((T x).card : ℝ)) ≤ 25*((P.biUnion T).card : ℝ) := by
  classical
  rw [← sum_tubeDegree]
  calc
    _ ≤ ∑ _l ∈ P.biUnion T, (25 : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      obtain ⟨x,hx,hxl⟩ := Finset.mem_biUnion.mp hl
      have hls := (hchart x hx l hxl).1
      have hsub : P.filter (fun x => l ∈ T x) ⊆ P.filter (fun x => TubeIncident δ x l) := by
        intro z hz
        obtain ⟨hz,hzl⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hz,hinc z hz l hzl⟩
      have he : tubeDegree P T l = ((P.filter fun x => l ∈ T x).card : ℝ) := by
        unfold tubeDegree
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
      rw [he]
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (separated_row_tube_count hδ hP hrow hls)
    _ = _ := by simp; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCells
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scale-delta covering cells for parameter projections. For a
family through a row, at most seven cells per row point are needed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem floor_div_near {δ u v : ℝ} (hδ : 0 < δ) (huv : |u-v| ≤ 2*δ) :
    |⌊u/δ⌋-⌊v/δ⌋| ≤ (3 : ℤ) := by
  have hd : |u/δ-v/δ| ≤ 2 := by
    rw [← sub_div,abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).2 huv
  have hu0 := Int.floor_le (u/δ)
  have hu1 := Int.lt_floor_add_one (u/δ)
  have hv0 := Int.floor_le (v/δ)
  have hv1 := Int.lt_floor_add_one (v/δ)
  have he : |(⌊u/δ⌋ : ℝ)-(⌊v/δ⌋ : ℝ)| ≤ 3 := by
    rw [abs_le] at hd ⊢
    constructor <;> linarith
  exact_mod_cast he

theorem projectionCells_mono (δ y : ℝ) {T U : Finset (Space 2)} (hTU : T ⊆ U) :
    projectionCells δ y T ⊆ projectionCells δ y U := Finset.image_subset_image hTU

theorem projectionCells_row_count {δ y : ℝ} (hδ : 0 < δ) {P : Finset (Space 2)}
    (hrow : ∀ x ∈ P, x 0 = y) (T : Space 2 → Finset (Space 2))
    (hchart : ∀ x ∈ P, InBoundedLineChart (T x))
    (hinc : ∀ x ∈ P, ∀ l ∈ T x, TubeIncident δ x l) :
    (projectionCells δ y (P.biUnion T)).card ≤ 7*P.card := by
  classical
  let S := fun x : Space 2 => Finset.Icc (⌊x 1/δ⌋-3) (⌊x 1/δ⌋+3)
  have hsub : projectionCells δ y (P.biUnion T) ⊆ P.biUnion S := by
    intro k hk
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨x,hx,hxl⟩ := Finset.mem_biUnion.mp hl
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    have he := tube_projection_near hδ.le (hchart x hx l hxl).1 (hinc x hx l hxl)
    rw [hrow x hx] at he
    have hb := floor_div_near hδ he
    rw [abs_le] at hb
    apply Finset.mem_Icc.mpr
    dsimp [S]
    omega
  have hcard (x : Space 2) : (S x).card = 7 := by
    dsimp [S]
    rw [Int.card_Icc]
    have he : ⌊x 1/δ⌋+3+1-(⌊x 1/δ⌋-3) = (7 : ℤ) := by omega
    rw [he]
    rfl
  calc
    _ ≤ (P.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P, (S x).card := Finset.card_biUnion_le
    _ = 7*P.card := by simp [hcard,Nat.mul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FinitePopularity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative popular-parameter selection in the finite incidence
argument. No asymptotic notation or hidden logarithmic losses are used. -/
namespace Falconer

/-- Deleting points below a fixed degree threshold loses at most the
threshold times the size of the whole set. -/
theorem finite_popular_mass {α : Type*} (S : Finset α) (w : α → ℝ)
    {I θ L : ℝ} (hθ : 0 ≤ θ) (htotal : I ≤ ∑ x ∈ S, w x)
    (hsmall : θ*(S.card : ℝ) ≤ I/2) (hupper : ∀ x ∈ S, w x ≤ L) :
    let G := S.filter fun x => θ ≤ w x
    I/2 ≤ ∑ x ∈ G, w x ∧ I/2 ≤ L*(G.card : ℝ) := by
  let G := S.filter fun x => θ ≤ w x
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun x => θ ≤ w x) w
  have hbad : (∑ x ∈ S.filter (fun x => ¬θ ≤ w x), w x) ≤ θ*(S.card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x => ¬θ ≤ w x), θ :=
        Finset.sum_le_sum fun x hx => (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ = θ*((S.filter (fun x => ¬θ ≤ w x)).card : ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_filter_le _ _)) hθ
  have hmass : I/2 ≤ ∑ x ∈ G, w x := by
    dsimp [G]
    linarith
  refine ⟨hmass,hmass.trans ?_⟩
  calc
    _ ≤ ∑ _x ∈ G, L := Finset.sum_le_sum fun x hx => hupper x (Finset.mem_filter.mp hx).1
    _ = _ := by simp [G,mul_comm]

theorem familyDegree_sum {α β : Type*} [DecidableEq β]
    (J : Finset α) (A : α → Finset β) :
    (∑ x ∈ J.biUnion A, familyDegree J A x) = ∑ j ∈ J, ((A j).card : ℝ) := by
  have hd := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := J) (t := J.biUnion A) (fun j x => x ∈ A j)
  have hf (j) (hj : j ∈ J) : (J.biUnion A).bipartiteAbove (fun j x => x ∈ A j) j = A j := by
    ext x
    simp only [Finset.mem_bipartiteAbove]
    exact and_iff_right_of_imp (fun hx => Finset.mem_biUnion.mpr ⟨j,hj,hx⟩)
  have hsum : (∑ j ∈ J, ((J.biUnion A).bipartiteAbove (fun j x => x ∈ A j) j).card) =
      ∑ j ∈ J, (A j).card := Finset.sum_congr rfl (fun j hj => by rw [hf j hj])
  rw [hsum] at hd
  unfold familyDegree
  have he : (∑ x ∈ J.biUnion A, (J.filter fun j => x ∈ A j).card) =
      ∑ j ∈ J, (A j).card := hd.symm
  exact_mod_cast he

theorem family_popular_selection {α β : Type*} [DecidableEq β]
    (J : Finset α) (A : α → Finset β) (hJ : J.Nonempty) {m : ℝ} (hm : 0 < m)
    (hsize : ∀ j ∈ J, m ≤ ((A j).card : ℝ)) :
    let U := J.biUnion A
    let θ := m*(J.card : ℝ)/(2*(U.card : ℝ))
    ∃ G ⊆ U, m/2 ≤ (G.card : ℝ) ∧
      m*(J.card : ℝ)/2 ≤ ∑ x ∈ G, familyDegree J A x ∧
      ∀ x ∈ G, θ ≤ familyDegree J A x := by
  let U := J.biUnion A
  have hJpos : 0 < (J.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
  have hUpos : 0 < (U.card : ℝ) := by
    obtain ⟨j,hj⟩ := hJ
    have hjpos : 0 < (A j).card := by exact_mod_cast hm.trans_le (hsize j hj)
    exact Nat.cast_pos.mpr (lt_of_lt_of_le hjpos (Finset.card_le_card (Finset.subset_biUnion_of_mem A hj)))
  let θ := m*(J.card : ℝ)/(2*(U.card : ℝ))
  have htotal : m*(J.card : ℝ) ≤ ∑ x ∈ U, familyDegree J A x := by
    rw [familyDegree_sum]
    calc
      _ = ∑ _j ∈ J, m := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hsize
  have hsmall : θ*(U.card : ℝ) ≤ m*(J.card : ℝ)/2 := by
    dsimp [θ]
    have he : m*(J.card : ℝ)/(2*(U.card : ℝ))*(U.card : ℝ) = m*(J.card : ℝ)/2 := by field_simp
    exact he.le
  have hupper (x : β) (_hx : x ∈ U) : familyDegree J A x ≤ (J.card : ℝ) := by
    unfold familyDegree
    exact_mod_cast Finset.card_filter_le J (fun j => x ∈ A j)
  have hb := finite_popular_mass U (familyDegree J A) (by dsimp [θ]; positivity)
    htotal hsmall hupper
  refine ⟨U.filter (fun x => θ ≤ familyDegree J A x),Finset.filter_subset _ _,?_,hb.1,?_⟩
  · nlinarith [hb.2]
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarEnergyRefinement
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the integer additive-energy refinement to separated real
sets, preserving the original points and the quantized difference bound. -/
namespace Falconer
open scoped Pointwise

theorem same_scalar_cell_dist_lt {δ x y : ℝ} (hδ : 0 < δ) (hcell : ⌊x/δ⌋ = ⌊y/δ⌋) :
    |x-y| < δ := by
  have hx0 := Int.floor_le (x/δ)
  have hx1 := Int.lt_floor_add_one (x/δ)
  have hy0 := Int.floor_le (y/δ)
  have hy1 := Int.lt_floor_add_one (y/δ)
  rw [hcell] at hx0 hx1
  have hh : |x/δ-y/δ| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_div,abs_div,abs_of_pos hδ] at hh
  exact (div_lt_one hδ).1 hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ScalarCoverCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting cells covered by finitely many translated scalar sets. -/
namespace Falconer
open scoped Pointwise

theorem floor_div_near_nat {δ u v : ℝ} (hδ : 0 < δ) (k : ℕ)
    (huv : |u-v| ≤ k*δ) : |⌊u/δ⌋-⌊v/δ⌋| ≤ (k : ℤ)+1 := by
  have hd : |u/δ-v/δ| ≤ (k : ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).2 huv
  have hu0 := Int.floor_le (u/δ)
  have hu1 := Int.lt_floor_add_one (u/δ)
  have hv0 := Int.floor_le (v/δ)
  have hv1 := Int.lt_floor_add_one (v/δ)
  have he : |(⌊u/δ⌋ : ℝ)-(⌊v/δ⌋ : ℝ)| ≤ (k : ℝ)+1 := by
    rw [abs_le] at hd ⊢
    constructor <;> linarith
  exact_mod_cast he

theorem scalarCells_near_card_nat {δ : ℝ} (hδ : 0 < δ) (A B : Finset ℝ)
    (k : ℕ) (hcover : ∀ a ∈ A, ∃ b ∈ B, |a-b| ≤ k*δ) :
    (scalarCells δ A).card ≤ (2*k+3)*(scalarCells δ B).card := by
  classical
  let I := fun z : ℤ => Finset.Icc (z-((k : ℤ)+1)) (z+((k : ℤ)+1))
  have hsub : scalarCells δ A ⊆ (scalarCells δ B).biUnion I := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b,hb,hab⟩ := hcover a ha
    apply Finset.mem_biUnion.mpr
    refine ⟨⌊b/δ⌋,Finset.mem_image.mpr ⟨b,hb,rfl⟩,?_⟩
    have hh := floor_div_near_nat hδ k hab
    rw [abs_le] at hh
    apply Finset.mem_Icc.mpr
    omega
  have hI (z : ℤ) : (I z).card = 2*k+3 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((scalarCells δ B).biUnion I).card := Finset.card_le_card hsub
    _ ≤ ∑ z ∈ scalarCells δ B, (I z).card := Finset.card_biUnion_le
    _ = _ := by simp [hI,Nat.mul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarDilationBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar dilation changes a fixed-resolution covering number by at
most a linear factor in the dilation bound. -/
namespace Falconer
open scoped Pointwise

theorem scalar_dilation_cells {δ c : ℝ} (hδ : 0 < δ) (A : Finset ℝ)
    (M : ℕ) (hc : |c| ≤ M) :
    (scalarCells δ (A.image fun x => c*x)).card ≤ (2*M+3)*(scalarCells δ A).card := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let g := Function.invFunOn q (A : Set ℝ)
  let F := (scalarCells δ A).image g
  have hF : F.card ≤ (scalarCells δ A).card := Finset.card_image_le
  have hcover : ∀ x ∈ A.image (fun x => c*x),
      ∃ y ∈ F.image (fun x => c*x), |x-y| ≤ (M : ℝ)*δ := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    have hq := Function.invFunOn_pos (f := q) (s := (A : Set ℝ)) ⟨x,hx,rfl⟩
    have hxg : |x-g (q x)| ≤ δ := (same_scalar_cell_dist_lt hδ hq.2.symm).le
    have hgf : g (q x) ∈ F := Finset.mem_image.mpr
      ⟨q x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,rfl⟩
    refine ⟨c*g (q x),Finset.mem_image.mpr ⟨g (q x),hgf,rfl⟩,?_⟩
    rw [← mul_sub,abs_mul]
    exact mul_le_mul hc hxg (abs_nonneg _) (Nat.cast_nonneg M)
  have hn := scalarCells_near_card_nat hδ (A.image fun x => c*x) (F.image fun x => c*x) M hcover
  have hsmall : (scalarCells δ (F.image fun x => c*x)).card ≤ (scalarCells δ A).card :=
    Finset.card_image_le.trans (Finset.card_image_le.trans hF)
  exact hn.trans (Nat.mul_le_mul_left _ hsmall)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarProductBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fine-scale ball bounds for a Cartesian product of separated scalar
sets, with its actual Euclidean embedding. -/
namespace Falconer

theorem rowPoint_pair_injective : Function.Injective (fun p : ℝ × ℝ => rowPoint p.1 p.2) := by
  intro p q h
  have h0 := congrArg (fun v : Space 2 => v 0) h
  have h1 := congrArg (fun v : Space 2 => v 1) h
  exact Prod.ext h0 h1

theorem scalarProductPoints_card (X Y : Finset ℝ) :
    (scalarProductPoints X Y).card = X.card*Y.card := by
  rw [scalarProductPoints,Finset.card_image_of_injective _ rowPoint_pair_injective,Finset.card_product]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarRatioFamily
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting and ball regularity for the actual ratio coefficients retained
by the common-rectangle selection. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_ball_bound_all_radii {δ s K : ℝ} (hK : 1 ≤ K) (hs : 0 ≤ s)
    (E : Finset ℝ)
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass E u r ≤ K*r^s*(E.card:ℝ))
    (u r : ℝ) (hr : δ ≤ r) : scalarBallMass E u r ≤ K*r^s*(E.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hball u r hr hr1
  · have hp : 1 ≤ r^s := Real.one_le_rpow (le_of_not_ge hr1) hs
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hc : scalarBallMass E u r ≤ (E.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hf : 1 ≤ K*r^s := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) E.card])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteBallBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and nonemptiness consequences for the normalized finite sets
appearing in the published planar incidence statement. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem normalized_finite_ball_bound_subset {δ s K C : ℝ}
    {P S : Finset (Space 2)} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hS : S ⊆ P) (hsize : (P.card : ℝ) ≤ C*(S.card : ℝ))
    (hball : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound δ s (K*C) S := by
  intro z r hdr hr1
  have hsub : S.filter (fun x => dist x z ≤ r) ⊆ P.filter (fun x => dist x z ≤ r) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  calc
    _ ≤ ((P.filter (fun x => dist x z ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K*r^s*(P.card : ℝ) := hball z r hdr hr1
    _ ≤ K*r^s*(C*(S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg (hδ.trans hdr) _))
    _ = _ := by ring

theorem finiteSeparatedAt_subset {δ : ℝ} {P S : Finset (Space 2)}
    (hS : S ⊆ P) (hP : FiniteSeparatedAt δ P) : FiniteSeparatedAt δ S :=
  fun x hx y hy hxy => hP x (hS hx) y (hS hy) hxy

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PointSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Separated point sets from samples with repeated coordinates

A maximal separated subfamily covers the sampled coordinates. The bound
on the multiplicity in a small ball then controls the loss in cardinality.
This is the point-selection step of `ang:planar-measures`.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

/-- Covering the original labels by the selected point balls gives the
lower cardinality bound, with all repeated labels counted. -/
theorem selected_points_card_lower {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    {δ L : ℝ} (hcover : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ)
    (hcount : ∀ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) ≤ L) :
    (D.card : ℝ) ≤ (P.card : ℝ) * L := by
  classical
  have hsub : D ⊆ P.biUnion (fun x => D.filter (fun i => dist (p i) x ≤ δ)) := by
    intro i hi
    obtain ⟨x, hx, hdist⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hi, hdist⟩⟩
  calc
    (D.card : ℝ) ≤ ((P.biUnion (fun x => D.filter
        (fun i => dist (p i) x ≤ δ))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ P, L := Finset.sum_le_sum hcount
    _ = (P.card : ℝ) * L := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketCentering
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Center a genuine coarse line packet by an affine shear. Translation in
line-parameter space preserves all pencil counts and ball bounds exactly;
the point-line residual is unchanged. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem packetCenterPoint_inverse (c b : ℝ) (p : Space 2) :
    packetCenterPoint (-c) (-b) (packetCenterPoint c b p) = p := by
  ext i
  fin_cases i
  · rfl
  · change p 1+c*p 0-b+(-c)*p 0-(-b) = p 1
    ring

theorem packetCenterLine_inverse (c b : ℝ) (l : Space 2) :
    packetCenterLine (-c) (-b) (packetCenterLine c b l) = l := by
  ext i
  fin_cases i
  · change l 0+c+(-c) = l 0
    ring
  · change l 1-b-(-b) = l 1
    ring

theorem packetCenterLine_injective (c b : ℝ) :
    Function.Injective (packetCenterLine c b) :=
  Function.LeftInverse.injective (packetCenterLine_inverse c b)

theorem packetCenterLine_dist (c b : ℝ) (l m : Space 2) :
    dist (packetCenterLine c b l) (packetCenterLine c b m) = dist l m := by
  have he (l : Space 2) : packetCenterLine c b l = l+rowPoint c (-b) := by
    ext i
    fin_cases i
    · rfl
    · change l 1-b = l 1+(-b)
      ring
  rw [he l,he m,dist_add_right]

theorem packetCenterLine_card (c b : ℝ) (T : Finset (Space 2)) :
    (T.image (packetCenterLine c b)).card = T.card :=
  Finset.card_image_of_injective _ (packetCenterLine_injective c b)

theorem packetCenterLine_separated {δ c b : ℝ} (T : Finset (Space 2))
    (hT : FiniteSeparatedAt δ T) : FiniteSeparatedAt δ (T.image (packetCenterLine c b)) := by
  intro l hl m hm hne
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hm
  rw [packetCenterLine_dist]
  exact hT p hp q hq (fun h => hne (congrArg _ h))

theorem packetCenterLine_regular {δ s K c b : ℝ} (T : Finset (Space 2))
    (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound δ s K (T.image (packetCenterLine c b)) := by
  intro z r hr hr1
  let w := packetCenterLine (-c) (-b) z
  have hw : packetCenterLine c b w = z := by
    simpa only [neg_neg] using packetCenterLine_inverse (-c) (-b) z
  have hsub : (T.image (packetCenterLine c b)).filter (fun l => dist l z ≤ r) ⊆
      (T.filter (fun l => dist l w ≤ r)).image (packetCenterLine c b) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr ⟨hm,?_⟩,rfl⟩
    rwa [← hw,packetCenterLine_dist] at hlr
  rw [packetCenterLine_card]
  exact (Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)).trans
    (hT w r hr hr1)

theorem packetCenter_residual (c b : ℝ) (p l : Space 2) :
    packetCenterPoint c b p 1-packetCenterLine c b l 0*packetCenterPoint c b p 0-
      packetCenterLine c b l 1 = p 1-l 0*p 0-l 1 := by
  change p 1+c*p 0-b-(l 0+c)*p 0-(l 1-b) = _
  ring

theorem packetCenter_residual_le {δ c b : ℝ} (hδ : 0 ≤ δ)
    (p l : Space 2) (hslope : |l 0| ≤ 1) (hi : TubeIncident δ p l) :
    |packetCenterPoint c b p 1-packetCenterLine c b l 0*packetCenterPoint c b p 0-
      packetCenterLine c b l 1| ≤ 2*δ := by
  rw [packetCenter_residual]
  exact tube_residual_le hδ hslope hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TubePacketDilation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dilation of a coarse line packet and the error from moving
its incident points to a common row. Used in the product extraction step
of the planar regular-set argument (Orponen--Shmerkin, Appendix A.6). -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem packetLineDilate_apply (Δ : ℝ) (l : Space 2) (i : Fin 2) :
    packetLineDilate Δ l i = l i/Δ := by
  change Δ⁻¹*l i = l i/Δ
  rw [div_eq_mul_inv,mul_comm]

theorem packetLineDilate_dist {Δ : ℝ} (hΔ : 0 < Δ) (l m : Space 2) :
    dist (packetLineDilate Δ l) (packetLineDilate Δ m) = dist l m/Δ := by
  rw [packetLineDilate,packetLineDilate,dist_smul₀,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hΔ),div_eq_mul_inv,mul_comm]

theorem packetLineDilate_inverse {Δ : ℝ} (hΔ : 0 < Δ) (z : Space 2) :
    packetLineDilate Δ (Δ • z) = z := by
  simp only [packetLineDilate,smul_smul,inv_mul_cancel₀ hΔ.ne',one_smul]

theorem packetLineDilate_injective {Δ : ℝ} (hΔ : 0 < Δ) :
    Function.Injective (packetLineDilate Δ) := by
  intro l m h
  have hd : dist l m/Δ = 0 := by rw [← packetLineDilate_dist hΔ,h,dist_self]
  exact dist_eq_zero.mp ((div_eq_zero_iff.mp hd).resolve_right hΔ.ne')

theorem packetLineDilate_card {Δ : ℝ} (hΔ : 0 < Δ) (S : Finset (Space 2)) :
    (S.image (packetLineDilate Δ)).card = S.card :=
  Finset.card_image_of_injective _ (packetLineDilate_injective hΔ)

theorem packetLineDilate_separated {δ Δ : ℝ} (hΔ : 0 < Δ)
    (S : Finset (Space 2)) (hsep : FiniteSeparatedAt δ S) :
    FiniteSeparatedAt (δ/Δ) (S.image (packetLineDilate Δ)) := by
  intro l hl m hm hlm
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hm
  rw [packetLineDilate_dist hΔ]
  exact div_le_div_of_nonneg_right
    (hsep x hx y hy (fun h => hlm (congrArg _ h))) hΔ.le

theorem packetLineDilate_chart {Δ : ℝ} (hΔ : 0 < Δ) (S : Finset (Space 2))
    (hS : ∀ l ∈ S, |l 0| ≤ Δ ∧ |l 1| ≤ Δ) :
    InBoundedLineChart (S.image (packetLineDilate Δ)) := by
  intro l hl
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
  constructor
  · rw [packetLineDilate_apply,abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hS m hm).1
  · rw [packetLineDilate_apply,abs_div,abs_of_pos hΔ]
    exact (div_le_one hΔ).2 (hS m hm).2

theorem packetLineDilate_regular {δ Δ s K : ℝ} (hδ : 0 < δ)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (S : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ s K S) :
    NormalizedFiniteBallBound (δ/Δ) s (K*Δ^s) (S.image (packetLineDilate Δ)) := by
  intro z r hr hr1
  have hr0 : 0 < r := (div_pos hδ hΔ).trans_le hr
  have hδr : δ ≤ Δ*r := by nlinarith only [(div_le_iff₀ hΔ).1 hr]
  have hΔr : Δ*r ≤ 1 := (mul_le_mul hΔ1 hr1 hr0.le (by norm_num)).trans_eq (by norm_num)
  have hsub : (S.image (packetLineDilate Δ)).filter (fun l => dist l z ≤ r) ⊆
      (S.filter (fun l => dist l (Δ • z) ≤ Δ*r)).image (packetLineDilate Δ) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr ⟨hm,?_⟩,rfl⟩
    have he := packetLineDilate_dist hΔ m (Δ • z)
    rw [packetLineDilate_inverse hΔ] at he
    rw [he] at hlr
    nlinarith only [(div_le_iff₀ hΔ).1 hlr]
  have hc : (((S.image (packetLineDilate Δ)).filter (fun l => dist l z ≤ r)).card:ℝ) ≤
      ((S.filter (fun l => dist l (Δ • z) ≤ Δ*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [packetLineDilate_card hΔ]
  calc
    _ ≤ ((S.filter (fun l => dist l (Δ • z) ≤ Δ*r)).card:ℝ) := hc
    _ ≤ K*(Δ*r)^s*(S.card:ℝ) := hreg _ _ hδr hΔr
    _ = _ := by rw [Real.mul_rpow hΔ.le hr0.le]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PacketResidualRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raw residual form of the packet row lift. This is stable under the
actual affine centering, whose residual identity is exact. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem packet_raw_common_row {Δ y : ℝ} (hΔ : 0 < Δ)
    (p l : Space 2) (hslope : |l 0| ≤ Δ) (hrow : |p 0-y| ≤ Δ)
    (hres : |p 1-l 0*p 0-l 1| ≤ 2*Δ^2) :
    TubeIncident (3*Δ) (rowPoint y (p 1/Δ)) (packetLineDilate Δ l) := by
  have hprod : |l 0*(p 0-y)| ≤ Δ^2 := by
    rw [abs_mul]
    have hh := mul_le_mul hslope hrow (abs_nonneg _) hΔ.le
    nlinarith only [hh]
  have hnum : |p 1-l 0*y-l 1| ≤ 3*Δ^2 := by
    have he : p 1-l 0*y-l 1 = (p 1-l 0*p 0-l 1)+l 0*(p 0-y) := by ring
    rw [he]
    have hh := (abs_add_le (p 1-l 0*p 0-l 1) (l 0*(p 0-y))).trans (add_le_add hres hprod)
    nlinarith only [hh]
  have he : rowPoint y (p 1/Δ) 1-packetLineDilate Δ l 0*rowPoint y (p 1/Δ) 0-
      packetLineDilate Δ l 1 = (p 1-l 0*y-l 1)/Δ := by
    simp only [rowPoint_zero,rowPoint_one,packetLineDilate_apply]
    ring
  have hden : 1 ≤ Real.sqrt (1+(packetLineDilate Δ l 0)^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith only [sq_nonneg (packetLineDilate Δ l 0)]
  have hdiv : |p 1-l 0*y-l 1|/Δ ≤ 3*Δ :=
    (div_le_iff₀ hΔ).2 (by nlinarith only [hnum])
  unfold TubeIncident
  rw [he,abs_div,abs_of_pos hΔ]
  apply (div_le_iff₀ (zero_lt_one.trans_le hden)).2
  exact hdiv.trans (le_mul_of_one_le_right (by positivity) hden)

theorem packet_row_pencil_lift_residual {Δ s K m M : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (P S : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hrep : ∀ x ∈ P, ∃ p ∈ S, p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ)
    (hT : ∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
      NormalizedFiniteBallBound (Δ^2) s K (T p) ∧
      m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      ∀ l ∈ T p, |l 0| ≤ Δ ∧ |l 1| ≤ Δ ∧ |p 1-l 0*p 0-l 1| ≤ 2*Δ^2) :
    ∃ U : Space 2 → Finset (Space 2),
      P.biUnion U ⊆ (S.biUnion T).image (packetLineDilate Δ) ∧
      ((P.biUnion U).card:ℝ) ≤ ((S.biUnion T).card:ℝ) ∧
      ∀ x ∈ P, InBoundedLineChart (U x) ∧ FiniteSeparatedAt Δ (U x) ∧
        NormalizedFiniteBallBound Δ s (K*Δ^s) (U x) ∧
        m ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
        ∀ l ∈ U x, TubeIncident (3*Δ) x l := by
  let rep : {x // x ∈ P} → Space 2 := fun x => Classical.choose (hrep x.val x.property)
  have hrep' (x : Space 2) (hx : x ∈ P) :
      rep ⟨x,hx⟩ ∈ S ∧ (rep ⟨x,hx⟩) 1 = Δ*x 1 ∧
        |(rep ⟨x,hx⟩) 0-x 0| ≤ Δ := Classical.choose_spec (hrep x hx)
  let U : Space 2 → Finset (Space 2) := fun x =>
    if hx : x ∈ P then (T (rep ⟨x,hx⟩)).image (packetLineDilate Δ) else ∅
  have hU (x : Space 2) (hx : x ∈ P) :
      U x = (T (rep ⟨x,hx⟩)).image (packetLineDilate Δ) := dite_eq_left hx
  have hsub : P.biUnion U ⊆ (S.biUnion T).image (packetLineDilate Δ) := by
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    rw [hU x hx] at hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image.mpr ⟨a,
      Finset.mem_biUnion.mpr ⟨rep ⟨x,hx⟩,(hrep' x hx).1,ha⟩,rfl⟩
  refine ⟨U,hsub,?_,?_⟩
  · have hc := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
    rwa [packetLineDilate_card hΔ] at hc
  · intro x hx
    let p := rep ⟨x,hx⟩
    have hp := hrep' x hx
    obtain ⟨hsep,hreg,hlo,hup,hgeom⟩ := hT p hp.1
    have hscale : Δ^2/Δ = Δ := by field_simp
    have hxrow : rowPoint (x 0) (p 1/Δ) = x := by
      ext i
      fin_cases i
      · rfl
      · change p 1/Δ = x 1
        rw [hp.2.1]
        field_simp
    rw [hU x hx]
    refine ⟨packetLineDilate_chart hΔ (T p) (fun l hl =>
      ⟨(hgeom l hl).1,(hgeom l hl).2.1⟩),?_,?_,?_,?_,?_⟩
    · simpa only [hscale] using packetLineDilate_separated hΔ (T p) hsep
    · simpa only [hscale] using packetLineDilate_regular (sq_pos_of_pos hΔ)
        hΔ hΔ1 (T p) hreg
    · simpa only [packetLineDilate_card hΔ] using hlo
    · simpa only [packetLineDilate_card hΔ] using hup
    · intro l hl
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      have hh := packet_raw_common_row hΔ p a (hgeom a ha).1 hp.2.2 (hgeom a ha).2.2
      rwa [hxrow] at hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CenteredPacketPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lift projected rows directly from an arbitrary original coarse packet.
Affine centering and dilation preserve the original union cardinality. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_pencil_lift {Δ s K m M c b : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (P S : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hrep : ∀ x ∈ P, ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-x 0| ≤ Δ)
    (hT : ∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
      NormalizedFiniteBallBound (Δ^2) s K (T p) ∧
      m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      ∀ l ∈ T p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) :
    ∃ U : Space 2 → Finset (Space 2),
      ((P.biUnion U).card:ℝ) ≤ ((S.biUnion T).card:ℝ) ∧
      ∀ x ∈ P, InBoundedLineChart (U x) ∧ FiniteSeparatedAt Δ (U x) ∧
        NormalizedFiniteBallBound Δ s (K*Δ^s) (U x) ∧
        m ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
        ∀ l ∈ U x, TubeIncident (3*Δ) x l := by
  let S' := S.image (packetCenterPoint c b)
  let T' := fun p => (T (packetCenterPoint (-c) (-b) p)).image (packetCenterLine c b)
  have hrep' : ∀ x ∈ P, ∃ p ∈ S', p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
    intro x hx
    obtain ⟨p,hp,h1,h0⟩ := hrep x hx
    exact ⟨packetCenterPoint c b p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,h1,h0⟩
  have hT' : ∀ p ∈ S', FiniteSeparatedAt (Δ^2) (T' p) ∧
      NormalizedFiniteBallBound (Δ^2) s K (T' p) ∧
      m ≤ ((T' p).card:ℝ) ∧ ((T' p).card:ℝ) ≤ M ∧
      ∀ l ∈ T' p, |l 0| ≤ Δ ∧ |l 1| ≤ Δ ∧ |p 1-l 0*p 0-l 1| ≤ 2*Δ^2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hsep,hreg,hlo,hup,hgeom⟩ := hT q hq
    simp only [T',packetCenterPoint_inverse]
    refine ⟨packetCenterLine_separated (T q) hsep,
      packetCenterLine_regular (T q) hreg,?_,?_,?_⟩
    · simpa only [packetCenterLine_card] using hlo
    · simpa only [packetCenterLine_card] using hup
    · intro l hl
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨(hgeom k hk).2.1,(hgeom k hk).2.2.1,
        packetCenter_residual_le (sq_nonneg Δ) q k (hgeom k hk).1 (hgeom k hk).2.2.2⟩
  obtain ⟨U,_,hcard,hU⟩ := packet_row_pencil_lift_residual hΔ hΔ1 P S' T' hrep' hT'
  have hunion : S'.biUnion T' = (S.biUnion T).image (packetCenterLine c b) := by
    simp only [S',T',Finset.image_biUnion,packetCenterPoint_inverse,Finset.biUnion_image]
  rw [hunion,packetCenterLine_card] at hcard
  exact ⟨U,hcard,hU⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphBallCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual graph edges in a narrow Cartesian strip are covered by planar
balls. The count retains every neighbor, rather than only one witness. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem normalized_ball_bound_all_radii {δ t K : ℝ} {G : Finset (Space 2)}
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hG : NormalizedFiniteBallBound δ t K G)
    (z : Space 2) (r : ℝ) (hr : δ ≤ r) :
    ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ K*r^t*(G.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hG z r hr hr1
  · have hrpos : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    have hp : 1 ≤ r^t := Real.one_le_rpow hrpos ht
    have hc : ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ (G.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hk : 1 ≤ K*r^t := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) G.card])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarScalarGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual scalar grid coordinates for a planar finite set. Rounding is
injective below the separation scale and coordinate counts are exactly the
original scalar cell counts. -/
namespace Falconer

 theorem scalarGridFloor_error {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    |x-scalarGridFloor δ x| ≤ δ := by
  have h0 := (le_div_iff₀ hδ).1 (Int.floor_le (x/δ))
  have h1 := (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one (x/δ))
  unfold scalarGridFloor
  rw [abs_of_nonneg (by nlinarith : 0 ≤ x-δ*(⌊x/δ⌋:ℝ))]
  nlinarith

 theorem scalarGridFloor_injective {δ : ℝ} (hδ : δ ≠ 0) :
    Function.Injective (fun k : ℤ => δ*(k:ℝ)) := by
  intro k l h
  exact Int.cast_injective (mul_left_cancel₀ hδ h)

 theorem scalarGridFloor_card {δ : ℝ} (hδ : 0 < δ) (X : Finset ℝ) :
    (X.image (scalarGridFloor δ)).card = (scalarCells δ X).card := by
  have he : X.image (scalarGridFloor δ) = (scalarCells δ X).image (fun k : ℤ => δ*(k:ℝ)) := by
    change X.image (fun x => δ*(⌊x/δ⌋:ℝ)) = _
    simp only [scalarCells,Finset.image_image,Function.comp_def]
  rw [he,Finset.card_image_of_injective _ (scalarGridFloor_injective hδ.ne')]

 theorem scalarGridFloor_separated {δ : ℝ} (hδ : 0 < δ) (X : Finset ℝ) :
    ∀ x ∈ X.image (scalarGridFloor δ), ∀ y ∈ X.image (scalarGridFloor δ),
      x ≠ y → δ ≤ |x-y| := by
  intro x hx y hy hne
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  have hfloor : ⌊a/δ⌋ ≠ ⌊b/δ⌋ := by
    intro h
    exact hne (by simp only [scalarGridFloor,h])
  have hInt : (1:ℤ) ≤ |⌊a/δ⌋-⌊b/δ⌋| := by
    have hh : (0:ℤ) < |⌊a/δ⌋-⌊b/δ⌋| := abs_pos.mpr (sub_ne_zero.mpr hfloor)
    omega
  have hR : (1:ℝ) ≤ |(⌊a/δ⌋:ℝ)-(⌊b/δ⌋:ℝ)| := by exact_mod_cast hInt
  unfold scalarGridFloor
  rw [← mul_sub,abs_mul,abs_of_pos hδ]
  nlinarith

 theorem planarGridFloor_apply (δ : ℝ) (x : Space 2) (i : Fin 2) :
    planarGridFloor δ x i = scalarGridFloor δ (x i) := by
  fin_cases i <;> rfl

 theorem planarGridFloor_error {δ : ℝ} (hδ : 0 < δ) (x : Space 2) :
    dist x (planarGridFloor δ x) ≤ 2*δ := by
  have hh := planar_dist_le_coordinate_sum x (planarGridFloor δ x)
  change dist x (planarGridFloor δ x) ≤
    |x 0-scalarGridFloor δ (x 0)|+|x 1-scalarGridFloor δ (x 1)| at hh
  linarith [scalarGridFloor_error hδ (x 0),scalarGridFloor_error hδ (x 1)]

 theorem planarGridFloor_injOn {δ σ : ℝ} (hσ : 0 < σ) (hsmall : 4*σ < δ)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    Set.InjOn (planarGridFloor σ) (G:Set (Space 2)) := by
  intro x hx y hy he
  by_contra hne
  have hh := dist_triangle x (planarGridFloor σ x) y
  rw [he,dist_comm (planarGridFloor σ y) y] at hh
  have hxerr := planarGridFloor_error hσ x
  have hyerr := planarGridFloor_error hσ y
  rw [he] at hxerr
  have hdist : dist x y ≤ 4*σ := by
    linarith
  exact (not_lt_of_ge (hsep x hx y hy hne)) (hdist.trans_lt hsmall)

 theorem planarGridFloor_coordinate_card {δ : ℝ} (hδ : 0 < δ)
    (G : Finset (Space 2)) (i : Fin 2) :
    ((G.image (planarGridFloor δ)).image (fun x => x i)).card =
      (scalarCells δ (G.image (fun x => x i))).card := by
  have he : (G.image (planarGridFloor δ)).image (fun x => x i) =
      (G.image (fun x => x i)).image (scalarGridFloor δ) := by
    simp only [Finset.image_image,Function.comp_def,planarGridFloor_apply]
  rw [he,scalarGridFloor_card hδ]

 theorem planarGridFloor_coordinate_separated {δ : ℝ} (hδ : 0 < δ)
    (G : Finset (Space 2)) (i : Fin 2) :
    ∀ x ∈ (G.image (planarGridFloor δ)).image (fun p => p i),
      ∀ y ∈ (G.image (planarGridFloor δ)).image (fun p => p i), x ≠ y → δ ≤ |x-y| := by
  have he : (G.image (planarGridFloor δ)).image (fun x => x i) =
      (G.image (fun x => x i)).image (scalarGridFloor δ) := by
    simp only [Finset.image_image,Function.comp_def,planarGridFloor_apply]
  rw [he]
  exact scalarGridFloor_separated hδ _

 theorem planarGridFloor_separated {δ : ℝ} (hδ : 0 < δ) (G : Finset (Space 2)) :
    FiniteSeparatedAt δ (G.image (planarGridFloor δ)) := by
  intro x hx y hy hne
  by_contra hn
  have hd : dist x y < δ := lt_of_not_ge hn
  apply hne
  ext i
  have hx' : x i ∈ (G.image (planarGridFloor δ)).image (fun p => p i) := Finset.mem_image_of_mem _ hx
  have hy' : y i ∈ (G.image (planarGridFloor δ)).image (fun p => p i) := Finset.mem_image_of_mem _ hy
  by_contra hneq
  have hs := planarGridFloor_coordinate_separated hδ G i _ hx' _ hy' hneq
  have hh : |x i-y i| ≤ dist x y := by simpa only [Real.dist_eq] using PiLp.dist_apply_le x y i
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteNearbyImages
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed finite losses for the nearby grid images of the tube packet.
The factor 361 is the planar packing bound in a ball of radius nine mesh
lengths. Both directions of the cardinality comparison will be needed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem separated_near_cover_card {δ : ℝ} (hδ : 0 < δ)
    (S V : Finset (Space 2)) (hsep : FiniteSeparatedAt δ S)
    (hcover : ∀ x ∈ S, ∃ y ∈ V, dist x y ≤ 9*δ) :
    (S.card:ℝ) ≤ 361*(V.card:ℝ) := by
  have hcount (y : Space 2) (_hy : y ∈ V) :
      ((S.filter fun x => dist x y ≤ 9*δ).card:ℝ) ≤ 361 := by
    have hh := separated_ball_card (S.filter fun x => dist x y ≤ 9*δ) y hδ
      (show 0 ≤ 9*δ by positivity)
      (fun x hx z hz hne => hsep x (Finset.mem_filter.mp hx).1 z
        (Finset.mem_filter.mp hz).1 hne)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have he : 2*(9*δ)/δ+1 = (19:ℝ) := by field_simp; ring
    norm_num only [he, Nat.cast_ofNat, Nat.reducePow] at hh
    exact hh
  have hh := selected_points_card_lower S id V hcover hcount
  simpa only [id_eq,mul_comm] using hh

theorem nearby_image_card {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Space 2)) (f : Space 2 → Space 2)
    (hsep : FiniteSeparatedAt δ S) (hnear : ∀ x ∈ S, dist x (f x) ≤ 9*δ) :
    (S.card:ℝ) ≤ 361*((S.image f).card:ℝ) :=
  separated_near_cover_card hδ S (S.image f) hsep
    (fun x hx => ⟨f x,Finset.mem_image_of_mem f hx,hnear x hx⟩)

theorem nearby_image_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (S : Finset (Space 2)) (f : Space 2 → Space 2)
    (hsep : FiniteSeparatedAt δ S) (hnear : ∀ x ∈ S, dist x (f x) ≤ 9*δ)
    (hreg : NormalizedFiniteBallBound δ s K S) :
    NormalizedFiniteBallBound δ s (361*K*(10:ℝ)^s) (S.image f) := by
  intro z r hr _
  have hr0 : 0 < r := hδ.trans_le hr
  have hsub : (S.image f).filter (fun y => dist y z ≤ r) ⊆
      (S.filter (fun x => dist x z ≤ 10*r)).image f := by
    intro y hy
    obtain ⟨hy,hyr⟩ := Finset.mem_filter.mp hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := (dist_triangle x (f x) z).trans (add_le_add (hnear x hx) hyr)
    linarith only [hh,hr]
  have hsize := nearby_image_card hδ S f hsep hnear
  calc
    _ ≤ ((S.filter fun x => dist x z ≤ 10*r).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(10*r)^s*(S.card:ℝ) :=
      normalized_ball_bound_all_radii hs hK hreg z (10*r) (by linarith only [hr,hδ])
    _ ≤ K*(10*r)^s*(361*((S.image f).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 10) hr0.le]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarProjectionCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinates supplied by two distinct planar projection directions.
These are the actual coordinates used by the dense scalar graph reduction. -/
namespace Falconer

 theorem planar_projection_slope {a b : ℝ} (hab : b ≠ a) (l : Space 2) :
    l 0 = (lineParameterProjection b l-lineParameterProjection a l)/(b-a) := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr hab
  unfold lineParameterProjection
  field_simp
  ring

 theorem planar_projection_intercept {a b : ℝ} (hab : b ≠ a) (l : Space 2) :
    l 1 = (b*lineParameterProjection a l-a*lineParameterProjection b l)/(b-a) := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr hab
  unfold lineParameterProjection
  field_simp
  ring

 theorem planarProjectionCoordinates_injective {a b : ℝ} (hab : b ≠ a) :
    Function.Injective (planarProjectionCoordinates a b) := by
  intro l m he
  have h0 := congrArg (fun v : Space 2 => v 0) he
  have h1 := congrArg (fun v : Space 2 => v 1) he
  change lineParameterProjection a l = lineParameterProjection a m at h0
  change lineParameterProjection b l = lineParameterProjection b m at h1
  ext i
  fin_cases i
  · change l 0 = m 0
    rw [planar_projection_slope hab l,planar_projection_slope hab m,h0,h1]
  · change l 1 = m 1
    rw [planar_projection_intercept hab l,planar_projection_intercept hab m,h0,h1]

 theorem planar_projection_normalized {a b y : ℝ} (hab : b ≠ a) (hyb : y ≠ b) (l : Space 2) :
    lineParameterProjection a l+((y-a)/(b-y))*lineParameterProjection b l =
      ((b-a)/(b-y))*lineParameterProjection y l := by
  have hby : b-y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyb)
  have hba : b-a ≠ 0 := sub_ne_zero.mpr hab
  unfold lineParameterProjection
  field_simp
  ring

 theorem planar_projection_ratio_bound {a b y r : ℝ} (hr : 0 < r)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hy : |y| ≤ 1)
    (hya : r ≤ |y-a|) (hby : r ≤ |b-y|) :
    (y-a)/(b-y) ≠ 0 ∧ |(y-a)/(b-y)| ≤ 2/r ∧ |((y-a)/(b-y))⁻¹| ≤ 2/r := by
  have hya0 : 0 < |y-a| := hr.trans_le hya
  have hby0 : 0 < |b-y| := hr.trans_le hby
  have hya' : y-a ≠ 0 := abs_pos.mp hya0
  have hby' : b-y ≠ 0 := abs_pos.mp hby0
  have hya2 : |y-a| ≤ 2 := (abs_sub y a).trans (by linarith)
  have hby2 : |b-y| ≤ 2 := (abs_sub b y).trans (by linarith)
  refine ⟨div_ne_zero hya' hby',?_,?_⟩
  · rw [abs_div]
    exact div_le_div₀ (by positivity) hya2 hr hby
  · rw [inv_div,abs_div]
    exact div_le_div₀ (by positivity) hby2 hr hya

 theorem planarProjectionCoordinates_dist_lower {a b : ℝ} (hab : b ≠ a)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (l m : Space 2) :
    dist l m ≤ (4/|b-a|)*dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) := by
  let u := lineParameterProjection a l-lineParameterProjection a m
  let v := lineParameterProjection b l-lineParameterProjection b m
  have hd : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have h0 : |l 0-m 0| ≤ (|u|+|v|)/|b-a| := by
    rw [planar_projection_slope hab l,planar_projection_slope hab m,← sub_div,abs_div]
    apply div_le_div_of_nonneg_right _ hd.le
    have he : (lineParameterProjection b l-lineParameterProjection a l)-
        (lineParameterProjection b m-lineParameterProjection a m) = v-u := by dsimp [u,v]; ring
    rw [he]
    exact (abs_sub v u).trans_eq (by ring)
  have h1 : |l 1-m 1| ≤ (|u|+|v|)/|b-a| := by
    rw [planar_projection_intercept hab l,planar_projection_intercept hab m,← sub_div,abs_div]
    apply div_le_div_of_nonneg_right _ hd.le
    have he : (b*lineParameterProjection a l-a*lineParameterProjection b l)-
        (b*lineParameterProjection a m-a*lineParameterProjection b m) = b*u-a*v := by dsimp [u,v]; ring
    rw [he]
    have hh := abs_sub (b*u) (a*v)
    rw [abs_mul,abs_mul] at hh
    have hbu := mul_le_mul_of_nonneg_right hb (abs_nonneg u)
    have hav := mul_le_mul_of_nonneg_right ha (abs_nonneg v)
    nlinarith
  have hu : |u| ≤ dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) := by
    simpa only [planarProjectionCoordinates,rowPoint_zero,Real.dist_eq] using
      PiLp.dist_apply_le (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) 0
  have hv : |v| ≤ dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) := by
    simpa only [planarProjectionCoordinates,rowPoint_one,Real.dist_eq] using
      PiLp.dist_apply_le (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) 1
  have hh := planar_dist_le_coordinate_sum l m
  have h0' := (le_div_iff₀ hd).1 h0
  have h1' := (le_div_iff₀ hd).1 h1
  have hh' := mul_le_mul_of_nonneg_right hh hd.le
  have he : (4/|b-a|)*dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m) =
      (4*dist (planarProjectionCoordinates a b l) (planarProjectionCoordinates a b m))/|b-a| := by ring
  rw [he]
  apply (le_div_iff₀ hd).2
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionCoordinateBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact inverse coordinates and ball-count transport for the two
separated projections selected from the original planar configuration. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem planarProjectionCoordinates_right_inverse {a b : ℝ} (hab : b ≠ a) (z : Space 2) :
    planarProjectionCoordinates a b (planarProjectionInverse a b z) = z := by
  have hd : b-a ≠ 0 := sub_ne_zero.mpr hab
  ext i
  fin_cases i
  · change a*((z 1-z 0)/(b-a))+(b*z 0-a*z 1)/(b-a) = z 0
    field_simp
    ring
  · change b*((z 1-z 0)/(b-a))+(b*z 0-a*z 1)/(b-a) = z 1
    field_simp
    ring

 theorem planarProjectionCoordinates_separated {δ a b : ℝ} (_hδ : 0 < δ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt (δ/(4/|b-a|)) (G.image (planarProjectionCoordinates a b)) := by
  intro x hx y hy hne
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hy
  have hlm : l ≠ m := fun h => hne (congrArg (planarProjectionCoordinates a b) h)
  have hL : 0 < 4/|b-a| := div_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hab))
  apply (div_le_iff₀ hL).2
  exact (hsep l hl m hm hlm).trans (by
    simpa only [mul_comm] using planarProjectionCoordinates_dist_lower hab ha hb l m)

 theorem planarProjectionCoordinates_regular {δ t K a b : ℝ} (hδ : 0 < δ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound (δ/(4/|b-a|)) t (K*(4/|b-a|)^t)
      (G.image (planarProjectionCoordinates a b)) := by
  classical
  let f := planarProjectionCoordinates a b
  let L := 4/|b-a|
  have hL : 0 < L := div_pos (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hab))
  have hcard : (G.image f).card = G.card :=
    Finset.card_image_of_injective G (planarProjectionCoordinates_injective hab)
  intro z r hr _
  have hr0 : 0 < r := (div_pos hδ hL).trans_le hr
  have hdr : δ ≤ L*r := by
    have hh := (div_le_iff₀ hL).1 hr
    nlinarith
  let u := planarProjectionInverse a b z
  have hfu : f u = z := planarProjectionCoordinates_right_inverse hab z
  have hsub : (G.image f).filter (fun p => dist p z ≤ r) ⊆
      (G.filter (fun l => dist l u ≤ L*r)).image f := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,?_⟩,rfl⟩
    have hh := planarProjectionCoordinates_dist_lower hab ha hb l u
    change dist l u ≤ L*dist (f l) (f u) at hh
    rw [hfu] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hpr hL.le)
  have hc : (((G.image f).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((G.filter (fun l => dist l u ≤ L*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hball := normalized_ball_bound_all_radii ht hK hreg u (L*r) hdr
  rw [Real.mul_rpow hL.le hr0.le] at hball
  change (((G.image f).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
    K*L^t*r^t*((G.image f).card:ℝ)
  rw [hcard]
  exact hc.trans (by nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarQuarter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed contraction puts the actual two projection coordinates inside
one bounded square without changing their finite combinatorics. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem planarQuarter_apply (p : Space 2) (i : Fin 2) : planarQuarter p i = p i / 4 := by
  change (1/4:ℝ) * p i = p i / 4
  ring

 theorem planarQuarter_dist (p q : Space 2) :
    dist (planarQuarter p) (planarQuarter q) = dist p q / 4 := by
  rw [planarQuarter,planarQuarter,dist_smul₀]
  norm_num
  ring

 theorem planarQuarter_injective : Function.Injective planarQuarter := by
  intro p q h
  have hh : dist p q / 4 = 0 := by rw [← planarQuarter_dist,h,dist_self]
  exact dist_eq_zero.mp (by linarith)

 theorem planarQuarter_right_inverse (z : Space 2) : planarQuarter ((4:ℝ) • z) = z := by
  ext i
  rw [planarQuarter_apply]
  change 4 * z i / 4 = z i
  ring

 theorem planarQuarter_separated {δ : ℝ} (G : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt (δ/4) (G.image planarQuarter) := by
  intro p hp q hq hpq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  rw [planarQuarter_dist]
  exact div_le_div_of_nonneg_right (hsep x hx y hy (fun h => hpq (congrArg _ h))) (by norm_num)

 theorem planarQuarter_regular {δ t K : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound (δ/4) t (K*4^t) (G.image planarQuarter) := by
  classical
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  have hsub : (G.image planarQuarter).filter (fun p => dist p z ≤ r) ⊆
      (G.filter (fun p => dist p ((4:ℝ) • z) ≤ 4*r)).image planarQuarter := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := planarQuarter_dist x ((4:ℝ) • z)
    rw [planarQuarter_right_inverse] at hh
    linarith
  have hc : (((G.image planarQuarter).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((G.filter (fun p => dist p ((4:ℝ) • z) ≤ 4*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hb := normalized_ball_bound_all_radii ht hK hreg ((4:ℝ) • z) (4*r) (by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le] at hb
  rw [Finset.card_image_of_injective _ planarQuarter_injective]
  exact hc.trans (by nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RoundedRowPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turn the width-three incidences produced by a coarse packet into exact
mesh-scale incidences. The output slope and intercept lie on the mesh, and
every output line remains within nine mesh lengths of its original line. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem rowAdjustedLine_residual {δ : ℝ} (hδ : 0 < δ) (p l : Space 2) :
    |p 1-rowAdjustedLine δ p l 0*p 0-rowAdjustedLine δ p l 1| ≤ δ := by
  simpa only [rowAdjustedLine_zero,rowAdjustedLine_one] using
    scalarGridFloor_error hδ (p 1-scalarGridFloor δ (l 0)*p 0)

theorem rowAdjustedLine_coordinate_error {δ : ℝ} (hδ : 0 < δ) (p l : Space 2)
    (hp : |p 0| ≤ 1) (hl : |l 0| ≤ 1) (hi : TubeIncident (3*δ) p l) :
    |l 0-rowAdjustedLine δ p l 0| ≤ δ ∧ |l 1-rowAdjustedLine δ p l 1| ≤ 8*δ := by
  have ha := scalarGridFloor_error hδ (l 0)
  have hb := scalarGridFloor_error hδ (p 1-scalarGridFloor δ (l 0)*p 0)
  have hres : |p 1-l 0*p 0-l 1| ≤ 6*δ := by
    have hh := tube_residual_le (show 0 ≤ 3*δ by positivity) hl hi
    linarith only [hh]
  have hmul : |(l 0-scalarGridFloor δ (l 0))*p 0| ≤ δ := by
    rw [abs_mul]
    exact (mul_le_mul ha hp (abs_nonneg _) hδ.le).trans_eq (mul_one δ)
  have hu : |p 1-scalarGridFloor δ (l 0)*p 0-l 1| ≤ 7*δ := by
    have he : p 1-scalarGridFloor δ (l 0)*p 0-l 1 =
        (p 1-l 0*p 0-l 1)+(l 0-scalarGridFloor δ (l 0))*p 0 := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hres,hmul])
  refine ⟨ha,?_⟩
  rw [rowAdjustedLine_one]
  have hh := abs_sub_le (l 1) (p 1-scalarGridFloor δ (l 0)*p 0)
    (scalarGridFloor δ (p 1-scalarGridFloor δ (l 0)*p 0))
  rw [abs_sub_comm (l 1) (p 1-scalarGridFloor δ (l 0)*p 0)] at hh
  exact hh.trans (by linarith only [hb,hu])

theorem rowAdjustedLine_near {δ : ℝ} (hδ : 0 < δ) (p l : Space 2)
    (hp : |p 0| ≤ 1) (hl : |l 0| ≤ 1) (hi : TubeIncident (3*δ) p l) :
    dist l (rowAdjustedLine δ p l) ≤ 9*δ := by
  obtain ⟨h0,h1⟩ := rowAdjustedLine_coordinate_error hδ p l hp hl hi
  exact (planar_dist_le_coordinate_sum _ _).trans (by linarith only [h0,h1])

theorem rowAdjustedLine_family_separated {δ : ℝ} (hδ : 0 < δ)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    FiniteSeparatedAt δ (P.biUnion fun p => (T p).image (rowAdjustedLine δ p)) := by
  let U := P.biUnion fun p => (T p).image (rowAdjustedRaw δ p)
  have he : P.biUnion (fun p => (T p).image (rowAdjustedLine δ p)) =
      U.image (planarGridFloor δ) := by
    simp only [U,Finset.biUnion_image,Finset.image_image,Function.comp_def]
    rfl
  rw [he]
  exact planarGridFloor_separated hδ U

theorem rowAdjustedLine_family_card {δ : ℝ} (hδ : 0 < δ)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hp : ∀ p ∈ P, |p 0| ≤ 1)
    (hT : ∀ p ∈ P, ∀ l ∈ T p, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l) :
    ((P.biUnion fun p => (T p).image (rowAdjustedLine δ p)).card:ℝ) ≤
      361*((P.biUnion T).card:ℝ) := by
  apply separated_near_cover_card hδ _ _ (rowAdjustedLine_family_separated hδ P T)
  intro q hq
  obtain ⟨p,hpP,hq⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hq
  refine ⟨l,Finset.mem_biUnion.mpr ⟨p,hpP,hl⟩,?_⟩
  rw [dist_comm]
  exact rowAdjustedLine_near hδ p l (hp p hpP) (hT p hpP l hl).1 (hT p hpP l hl).2

theorem rowAdjustedLine_pencil_card {δ : ℝ} (hδ : 0 < δ)
    (p : Space 2) (T : Finset (Space 2)) (hp : |p 0| ≤ 1)
    (hsep : FiniteSeparatedAt δ T)
    (hT : ∀ l ∈ T, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l) :
    (T.card:ℝ) ≤ 361*((T.image (rowAdjustedLine δ p)).card:ℝ) :=
  nearby_image_card hδ T _ hsep
    (fun l hl => rowAdjustedLine_near hδ p l hp (hT l hl).1 (hT l hl).2)

theorem rowAdjustedLine_pencil_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (p : Space 2) (T : Finset (Space 2))
    (hp : |p 0| ≤ 1) (hsep : FiniteSeparatedAt δ T)
    (hT : ∀ l ∈ T, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l)
    (hreg : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound δ s (361*K*(10:ℝ)^s) (T.image (rowAdjustedLine δ p)) :=
  nearby_image_regular hδ hs hK T _ hsep
    (fun l hl => rowAdjustedLine_near hδ p l hp (hT l hl).1 (hT l hl).2) hreg

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_CommonRowNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the rounded product rows into the bounded line chart without
changing their first coordinate. All size losses are explicit. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem verticalFour_verticalQuarter (p : Space 2) : verticalFour (verticalQuarter p) = p := by
  ext i
  fin_cases i
  · rfl
  · change 4*(p 1/4) = p 1
    ring

theorem verticalQuarter_injective : Function.Injective verticalQuarter :=
  Function.LeftInverse.injective verticalFour_verticalQuarter

theorem verticalQuarter_row_distance {p q : Space 2} (h : p 0 = q 0) :
    dist (verticalQuarter p) (verticalQuarter q) = dist p q/4 := by
  have hp : p = rowPoint (p 0) (p 1) := by ext i; fin_cases i <;> rfl
  have hq : q = rowPoint (p 0) (q 1) := by
    ext i
    fin_cases i
    · exact h.symm
    · rfl
  conv_rhs => rw [hp,hq,rowPoint_dist]
  change dist (rowPoint (p 0) (p 1/4)) (rowPoint (q 0) (q 1/4)) = _
  rw [← h,rowPoint_dist,← sub_div,abs_div]
  norm_num

theorem verticalQuarter_row_separated {δ y : ℝ} (P : Finset (Space 2))
    (hrow : ∀ p ∈ P, p 0 = y) (hsep : FiniteSeparatedAt δ P) :
    FiniteSeparatedAt (δ/4) (P.image verticalQuarter) := by
  intro p hp q hq hpq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
  rw [verticalQuarter_row_distance ((hrow x hx).trans (hrow z hz).symm)]
  exact div_le_div_of_nonneg_right
    (hsep x hx z hz (fun h => hpq (congrArg _ h))) (by norm_num)

theorem verticalQuarter_row_regular {δ s K y : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (P : Finset (Space 2))
    (hrow : ∀ p ∈ P, p 0 = y) (hreg : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound (δ/4) s (K*(4:ℝ)^s) (P.image verticalQuarter) := by
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  have hsub : (P.image verticalQuarter).filter (fun p => dist p z ≤ r) ⊆
      (P.filter (fun p => dist p (rowPoint y (4*z 1)) ≤ 4*r)).image verticalQuarter := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    rw [row_dist_projection (hrow x hx)]
    have hh : |x 1/4-z 1| ≤ r :=
      (show |x 1/4-z 1| ≤ dist (verticalQuarter x) z by
        simpa only [Real.dist_eq,verticalQuarter_one] using PiLp.dist_apply_le (verticalQuarter x) z 1).trans hpr
    have he : |x 1-4*z 1| = 4*|x 1/4-z 1| := by
      rw [← abs_of_pos (by norm_num : (0:ℝ) < 4),← abs_mul]
      congr 1
      ring
    rw [he]
    linarith only [hh]
  have hc : (((P.image verticalQuarter).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((P.filter (fun p => dist p (rowPoint y (4*z 1)) ≤ 4*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_image_of_injective _ verticalQuarter_injective]
  calc
    _ ≤ ((P.filter (fun p => dist p (rowPoint y (4*z 1)) ≤ 4*r)).card:ℝ) := hc
    _ ≤ K*(4*r)^s*(P.card:ℝ) :=
      normalized_ball_bound_all_radii hs hK hreg _ _ (by linarith only [hr])
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring

theorem quarter_adjusted_incident {δ : ℝ} (hδ : 0 < δ) (p l : Space 2) :
    TubeIncident (δ/4) (verticalQuarter p) (planarQuarter (rowAdjustedLine δ p l)) := by
  have hd : 1 ≤ Real.sqrt (1+(planarQuarter (rowAdjustedLine δ p l) 0)^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith only [sq_nonneg (planarQuarter (rowAdjustedLine δ p l) 0)]
  have he : verticalQuarter p 1-planarQuarter (rowAdjustedLine δ p l) 0*verticalQuarter p 0-
      planarQuarter (rowAdjustedLine δ p l) 1 =
      (p 1-rowAdjustedLine δ p l 0*p 0-rowAdjustedLine δ p l 1)/4 := by
    simp only [verticalQuarter_zero,verticalQuarter_one,planarQuarter_apply]
    ring
  unfold TubeIncident
  rw [he,abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
  apply (div_le_iff₀ (zero_lt_one.trans_le hd)).2
  exact (div_le_div_of_nonneg_right (rowAdjustedLine_residual hδ p l) (by norm_num)).trans
    (le_mul_of_one_le_right (by positivity) hd)

theorem quarter_adjusted_chart {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/8)
    (p l : Space 2) (hp : |p 0| ≤ 1) (hl : |l 0| ≤ 1 ∧ |l 1| ≤ 1)
    (hi : TubeIncident (3*δ) p l) :
    |planarQuarter (rowAdjustedLine δ p l) 0| ≤ 1 ∧
    |planarQuarter (rowAdjustedLine δ p l) 1| ≤ 1 := by
  obtain ⟨h0,h1⟩ := rowAdjustedLine_coordinate_error hδ p l hp hl.1 hi
  have h0' : |rowAdjustedLine δ p l 0| ≤ |l 0|+δ := by
    have hh := abs_sub_le (rowAdjustedLine δ p l 0) (l 0) 0
    simp only [sub_zero] at hh
    rw [abs_sub_comm (rowAdjustedLine δ p l 0) (l 0)] at hh
    linarith only [hh,h0]
  have h1' : |rowAdjustedLine δ p l 1| ≤ |l 1|+8*δ := by
    have hh := abs_sub_le (rowAdjustedLine δ p l 1) (l 1) 0
    simp only [sub_zero] at hh
    rw [abs_sub_comm (rowAdjustedLine δ p l 1) (l 1)] at hh
    linarith only [hh,h1]
  simp only [planarQuarter_apply,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 4)]
  constructor <;> linarith only [h0',h1',hl.1,hl.2,hδsmall]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_NormalizedProductPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the common-row rounding into actual pencil families. The
pencil cardinality drops by at most 361, and the complete union grows by
at most 361. No separation assumption is needed on the original union. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem normalizedPencil_card_upper (δ : ℝ) (p : Space 2) (S : Finset (Space 2)) :
    (normalizedPencil δ p S).card ≤ S.card :=
  Finset.card_image_le.trans Finset.card_image_le

theorem normalizedPencil_card_lower {δ : ℝ} (hδ : 0 < δ)
    (p : Space 2) (S : Finset (Space 2)) (hp : |p 0| ≤ 1)
    (hsep : FiniteSeparatedAt δ S)
    (hS : ∀ l ∈ S, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l) :
    (S.card:ℝ) ≤ 361*((normalizedPencil δ p S).card:ℝ) := by
  unfold normalizedPencil
  rw [Finset.card_image_of_injective _ planarQuarter_injective]
  exact rowAdjustedLine_pencil_card hδ p S hp hsep hS

theorem normalizedPencil_incident {δ : ℝ} (hδ : 0 < δ)
    (p : Space 2) (S : Finset (Space 2)) :
    ∀ l ∈ normalizedPencil δ p S, TubeIncident (δ/4) (verticalQuarter p) l := by
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp ha
  exact quarter_adjusted_incident hδ p m

theorem normalizedPencil_chart {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/8)
    (p : Space 2) (S : Finset (Space 2)) (hp : |p 0| ≤ 1)
    (hchart : InBoundedLineChart S) (hi : ∀ l ∈ S, TubeIncident (3*δ) p l) :
    InBoundedLineChart (normalizedPencil δ p S) := by
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp ha
  exact quarter_adjusted_chart hδ hδsmall p m hp (hchart m hm) (hi m hm)

theorem normalizedPencil_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (p : Space 2) (S : Finset (Space 2))
    (hp : |p 0| ≤ 1) (hsep : FiniteSeparatedAt δ S)
    (hchart : InBoundedLineChart S) (hi : ∀ l ∈ S, TubeIncident (3*δ) p l)
    (hreg : NormalizedFiniteBallBound δ s K S) :
    NormalizedFiniteBallBound (δ/4) s ((361*K*(10:ℝ)^s)*(4:ℝ)^s)
      (normalizedPencil δ p S) := by
  have hpow : 1 ≤ (10:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have hcost : 1 ≤ 361*K*(10:ℝ)^s := by
    have hh := mul_le_mul hK hpow (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
    nlinarith only [hh]
  apply planarQuarter_regular hδ hs hcost
  exact rowAdjustedLine_pencil_regular hδ hs hK p S hp hsep
    (fun l hl => ⟨(hchart l hl).1,hi l hl⟩) hreg

theorem normalizedRowPencils_union (δ : ℝ) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) :
    (P.image verticalQuarter).biUnion (normalizedRowPencils δ T) =
      (P.biUnion fun p => (T p).image (rowAdjustedLine δ p)).image planarQuarter := by
  simp only [Finset.image_biUnion,normalizedRowPencils,verticalFour_verticalQuarter,
    normalizedPencil,Finset.biUnion_image]

theorem normalizedRowPencils_union_separated {δ : ℝ} (hδ : 0 < δ)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    FiniteSeparatedAt (δ/4) ((P.image verticalQuarter).biUnion (normalizedRowPencils δ T)) := by
  rw [normalizedRowPencils_union]
  exact planarQuarter_separated _ (rowAdjustedLine_family_separated hδ P T)

theorem normalizedRowPencils_union_card {δ : ℝ} (hδ : 0 < δ)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hp : ∀ p ∈ P, |p 0| ≤ 1)
    (hT : ∀ p ∈ P, ∀ l ∈ T p, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l) :
    (((P.image verticalQuarter).biUnion (normalizedRowPencils δ T)).card:ℝ) ≤
      361*((P.biUnion T).card:ℝ) := by
  rw [normalizedRowPencils_union,Finset.card_image_of_injective _ planarQuarter_injective]
  exact rowAdjustedLine_family_card hδ P T hp hT

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ScalarSubsetMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative ball bounds and projection covers under the actual scalar
 pruning. The sole cost is the ratio of the numbers of retained leaves. -/
namespace Falconer
open scoped Pointwise

 theorem scalarBallMass_mono {A B : Finset ℝ} (h : A ⊆ B) (u r : ℝ) :
    scalarBallMass A u r ≤ scalarBallMass B u r := by
  unfold scalarBallMass
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ h)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarResolution
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparing scalar covering and ball counts at two nearby resolutions. -/
namespace Falconer

 theorem scalar_cells_resolution {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (m : ℕ) (hscale : ρ ≤ (m:ℝ)*δ) (X : Finset ℝ) :
    (scalarCells δ X).card ≤ (2*m+3)*(scalarCells ρ X).card := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/ρ⌋
  let g := Function.invFunOn q (X : Set ℝ)
  let F := (scalarCells ρ X).image g
  have hnear : ∀ x ∈ X, ∃ y ∈ F, |x-y| ≤ (m:ℝ)*δ := by
    intro x hx
    have hrep := Function.invFunOn_pos (f := q) (s := (X : Set ℝ)) ⟨x,hx,rfl⟩
    have hd : |x-g (q x)| < ρ := same_scalar_cell_dist_lt hρ hrep.2.symm
    exact ⟨g (q x),Finset.mem_image.mpr ⟨q x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,rfl⟩,
      hd.le.trans hscale⟩
  have hh := scalarCells_near_card_nat hδ X F m hnear
  have hc : (scalarCells δ F).card ≤ (scalarCells ρ X).card :=
    Finset.card_image_le.trans Finset.card_image_le
  exact hh.trans (Nat.mul_le_mul_left _ hc)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GridProjectionTransfer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted projection counts through actual coordinate changes and
rounding, with all losses given by finite covering factors. -/
namespace Falconer

 theorem cartesianProjection_grid_error {σ : ℝ} (hσ : 0 < σ) (c : ℝ) (p : Space 2) :
    |cartesianProjection c (planarGridFloor σ p)-cartesianProjection c p| ≤ (1+|c|)*σ := by
  have h0 : |scalarGridFloor σ (p 0)-p 0| ≤ σ := by
    simpa only [abs_sub_comm] using scalarGridFloor_error hσ (p 0)
  have h1 : |scalarGridFloor σ (p 1)-p 1| ≤ σ := by
    simpa only [abs_sub_comm] using scalarGridFloor_error hσ (p 1)
  have he : cartesianProjection c (planarGridFloor σ p)-cartesianProjection c p =
      (scalarGridFloor σ (p 0)-p 0)+c*(scalarGridFloor σ (p 1)-p 1) := by
    unfold cartesianProjection planarGridFloor
    simp only [rowPoint_zero,rowPoint_one]
    ring
  rw [he]
  have hh := abs_add_le (scalarGridFloor σ (p 0)-p 0) (c*(scalarGridFloor σ (p 1)-p 1))
  rw [abs_mul] at hh
  have hm := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
  nlinarith

 theorem cartesianProjection_grid_cells {δ σ : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (c : ℝ) (G : Finset (Space 2)) (k : ℕ) (hk : (1+|c|)*σ ≤ (k:ℝ)*δ) :
    (scalarCells δ ((G.image (planarGridFloor σ)).image (cartesianProjection c))).card ≤
      (2*k+3)*(scalarCells δ (G.image (cartesianProjection c))).card := by
  apply scalarCells_near_card_nat hδ _ _ k
  intro a ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  exact ⟨cartesianProjection c x,Finset.mem_image_of_mem _ hx,
    (cartesianProjection_grid_error hσ c x).trans hk⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BoundedProjectionCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded actual projection coordinates, with exact finite cell-count
comparison to the original planar projections. -/
namespace Falconer

 theorem boundedProjectionCoordinates_zero (a b : ℝ) (p : Space 2) :
    boundedProjectionCoordinates a b p 0 = lineParameterProjection a p / 4 := by
  rw [boundedProjectionCoordinates,planarQuarter_apply]
  rfl

 theorem boundedProjectionCoordinates_one (a b : ℝ) (p : Space 2) :
    boundedProjectionCoordinates a b p 1 = lineParameterProjection b p / 4 := by
  rw [boundedProjectionCoordinates,planarQuarter_apply]
  rfl

 theorem boundedProjectionCoordinates_injective {a b : ℝ} (hab : b ≠ a) :
    Function.Injective (boundedProjectionCoordinates a b) :=
  planarQuarter_injective.comp (planarProjectionCoordinates_injective hab)

 theorem boundedProjectionCoordinates_image (a b : ℝ) (G : Finset (Space 2)) :
    G.image (boundedProjectionCoordinates a b) =
      (G.image (planarProjectionCoordinates a b)).image planarQuarter := by
  rw [Finset.image_image]
  rfl

 theorem boundedProjectionCoordinates_separated {δ a b : ℝ} (hδ : 0 < δ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt ((δ/(4/|b-a|))/4) (G.image (boundedProjectionCoordinates a b)) := by
  rw [boundedProjectionCoordinates_image]
  exact planarQuarter_separated _ (planarProjectionCoordinates_separated hδ hab ha hb G hsep)

 theorem boundedProjectionCoordinates_regular {δ t K a b : ℝ} (hδ : 0 < δ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound ((δ/(4/|b-a|))/4) t (K*(4/|b-a|)^t*4^t)
      (G.image (boundedProjectionCoordinates a b)) := by
  have hba : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith)
  have hd : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hL : 1 ≤ 4/|b-a| := (le_div_iff₀ hd).2 (by linarith)
  have hpow : 1 ≤ (4/|b-a|)^t := Real.one_le_rpow hL ht
  have hKK : 1 ≤ K*(4/|b-a|)^t := by nlinarith
  rw [boundedProjectionCoordinates_image]
  exact planarQuarter_regular (by positivity) ht hKK _
    (planarProjectionCoordinates_regular hδ hab ha hb ht hK G hreg)

 theorem boundedProjectionCoordinates_bound {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (p : Space 2) (hp : ∀ i, |p i| ≤ 1) (i : Fin 2) :
    |boundedProjectionCoordinates a b p i| ≤ 1/2 := by
  have hproj (y : ℝ) (hy : |y| ≤ 1) : |lineParameterProjection y p| ≤ 2 := by
    have hh := abs_add_le (y*p 0) (p 1)
    rw [abs_mul] at hh
    have hm := mul_le_mul hy (hp 0) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    change |y*p 0+p 1| ≤ 2
    linarith [hp 1]
  fin_cases i
  · change |boundedProjectionCoordinates a b p 0| ≤ 1/2
    rw [boundedProjectionCoordinates_zero,abs_div]
    norm_num
    linarith [hproj a ha]
  · change |boundedProjectionCoordinates a b p 1| ≤ 1/2
    rw [boundedProjectionCoordinates_one,abs_div]
    norm_num
    linarith [hproj b hb]

 theorem boundedProjectionCoordinates_coordinate_cells {σ δ a b : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (G : Finset (Space 2)) (m : ℕ) (hm : δ ≤ (m:ℝ)*σ)
    (i : Fin 2) :
    (scalarCells σ ((G.image (boundedProjectionCoordinates a b)).image (fun p => p i))).card ≤
      5*(2*m+3)*(projectionCells δ (if i = 0 then a else b) G).card := by
  have he : (G.image (boundedProjectionCoordinates a b)).image (fun p => p i) =
      (G.image (lineParameterProjection (if i = 0 then a else b))).image (fun v => (1/4:ℝ)*v) := by
    simp only [Finset.image_image,Function.comp_def]
    apply Finset.image_congr
    intro p _
    fin_cases i
    · change boundedProjectionCoordinates a b p 0 = (1/4:ℝ)*lineParameterProjection a p
      rw [boundedProjectionCoordinates_zero]
      ring
    · change boundedProjectionCoordinates a b p 1 = (1/4:ℝ)*lineParameterProjection b p
      rw [boundedProjectionCoordinates_one]
      ring
  rw [he]
  have hd := scalar_dilation_cells (c := (1/4:ℝ)) hσ
    (G.image (lineParameterProjection (if i = 0 then a else b))) 1 (by norm_num)
  have hr := scalar_cells_resolution hσ hδ m hm
    (G.image (lineParameterProjection (if i = 0 then a else b)))
  have hc : scalarCells δ (G.image (lineParameterProjection (if i = 0 then a else b))) =
      projectionCells δ (if i = 0 then a else b) G := by
    simp only [scalarCells,projectionCells,Finset.image_image,Function.comp_def]
  rw [hc] at hr
  exact hd.trans ((Nat.mul_le_mul_left 5 hr).trans_eq (by ring))

 theorem boundedProjectionCoordinates_projection_image {a b y : ℝ} (hab : b ≠ a)
    (hy : y ≠ b) (G : Finset (Space 2)) :
    (G.image (boundedProjectionCoordinates a b)).image (cartesianProjection ((y-a)/(b-y))) =
      (G.image (lineParameterProjection y)).image (fun v => (((b-a)/(b-y))/4)*v) := by
  simp only [Finset.image_image,Function.comp_def]
  apply Finset.image_congr
  intro p _
  have hh := planar_projection_normalized hab hy p
  change (boundedProjectionCoordinates a b p 0)+((y-a)/(b-y))*(boundedProjectionCoordinates a b p 1) = _
  rw [boundedProjectionCoordinates_zero,boundedProjectionCoordinates_one]
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarGridRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original normalized planar ball bound survives injective grid
rounding, with the exact scale and radius losses exposed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem planarGridFloor_regular {δ σ α C t K : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    (hC : 1 ≤ C) (hscale : δ ≤ C*α) (herror : 2*σ ≤ (C-1)*α)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (G : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t K G)
    (hinj : Set.InjOn (planarGridFloor σ) (G:Set (Space 2))) :
    NormalizedFiniteBallBound α t (K*C^t) (G.image (planarGridFloor σ)) := by
  classical
  have hcard : (G.image (planarGridFloor σ)).card = G.card := Finset.card_image_of_injOn hinj
  intro z r hr _
  have hr0 : 0 < r := hα.trans_le hr
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCr : δ ≤ C*r := hscale.trans (mul_le_mul_of_nonneg_left hr hC0)
  have herr : r+2*σ ≤ C*r := by
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ C-1 by linarith)
    nlinarith
  have hsub : (G.image (planarGridFloor σ)).filter (fun p => dist p z ≤ r) ⊆
      (G.filter (fun p => dist p z ≤ C*r)).image (planarGridFloor σ) := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := dist_triangle x (planarGridFloor σ x) z
    have he := planarGridFloor_error hσ x
    linarith
  have hc : (((G.image (planarGridFloor σ)).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((G.filter (fun p => dist p z ≤ C*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hb := normalized_ball_bound_all_radii ht hK hreg z (C*r) hCr
  rw [Real.mul_rpow hC0 hr0.le] at hb
  rw [hcard]
  exact hc.trans (by nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_CoordinateGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite planar set is exactly the edge set of its two coordinate
projections. This keeps original point counts in the dense graph reduction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem rowPoint_coordinates (x : Space 2) : rowPoint (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> rfl

 theorem coordinate_graph_card_le (X Y : Finset ℝ) (H : Finset (Space 2))
    (hcoord : ∀ p ∈ H, p 0 ∈ X ∧ p 1 ∈ Y) : H.card ≤ X.card*Y.card := by
  have hsub : H ⊆ scalarProductPoints X Y := by
    intro p hp
    exact Finset.mem_image.mpr ⟨(p 0,p 1),Finset.mem_product.mpr (hcoord p hp),rowPoint_coordinates p⟩
  exact (Finset.card_le_card hsub).trans_eq (scalarProductPoints_card X Y)

 theorem coordinate_graph_comparable {X Y G N K : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hK : 0 ≤ K)
    (hXN : X ≤ N) (hYN : Y ≤ N) (hG : G ≤ X*Y) (hlarge : N^2 ≤ K*G) :
    X ≤ K*Y ∧ Y ≤ K*X := by
  have hN : 0 ≤ N := hX.le.trans hXN
  have hX2 := pow_le_pow_left₀ hX.le hXN 2
  have hY2 := pow_le_pow_left₀ hY.le hYN 2
  have hKG := mul_le_mul_of_nonneg_left hG hK
  constructor
  · apply (mul_le_mul_iff_right₀ hX).1
    nlinarith
  · apply (mul_le_mul_iff_right₀ hY).1
    nlinarith

 theorem coordinate_graph_density {ρ K G H X Y : ℝ}
    (hρ : 0 ≤ ρ) (hK : 0 < K) (hlarge : X*Y ≤ K*G) (hH : ρ*G ≤ H) :
    (ρ/K)*X*Y ≤ H := by
  have hh := mul_le_mul_of_nonneg_left hlarge (div_nonneg hρ hK.le)
  have he : (ρ/K)*(K*G) = ρ*G := by field_simp
  rw [he] at hh
  convert hh.trans hH using 1 <;> first | rfl | ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RoundedProjectionCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite coordinate graph used in the planar projection application:
actual points, a fixed contraction, and an injective fine-grid rounding. -/
namespace Falconer

 theorem roundedProjectionCoordinates_image (σ a b : ℝ) (G : Finset (Space 2)) :
    G.image (roundedProjectionCoordinates σ a b) =
      (G.image (boundedProjectionCoordinates a b)).image (planarGridFloor σ) := by
  rw [Finset.image_image]
  rfl

 theorem roundedProjectionCoordinates_injOn {δ σ a b : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    Set.InjOn (roundedProjectionCoordinates σ a b) (G:Set (Space 2)) := by
  have hi := planarGridFloor_injOn hσ hsmall _
    (boundedProjectionCoordinates_separated hδ hab ha hb G hsep)
  intro x hx y hy he
  exact boundedProjectionCoordinates_injective hab (hi
    (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy) he)

 theorem roundedProjectionCoordinates_card {δ σ a b : ℝ} (hδ : 0 < δ) (hσ : 0 < σ)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (G : Finset (Space 2)) (hsep : FiniteSeparatedAt δ G) :
    (G.image (roundedProjectionCoordinates σ a b)).card = G.card :=
  Finset.card_image_of_injOn (roundedProjectionCoordinates_injOn hδ hσ hab ha hb hsmall G hsep)

 theorem roundedProjectionCoordinates_coordinate_separated {σ a b : ℝ} (hσ : 0 < σ)
    (G : Finset (Space 2)) (i : Fin 2) :
    ∀ x ∈ (G.image (roundedProjectionCoordinates σ a b)).image (fun p => p i),
      ∀ y ∈ (G.image (roundedProjectionCoordinates σ a b)).image (fun p => p i),
        x ≠ y → σ ≤ |x-y| := by
  rw [roundedProjectionCoordinates_image]
  exact planarGridFloor_coordinate_separated hσ _ i

 theorem roundedProjectionCoordinates_bound {σ a b : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1/2)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (p : Space 2) (hp : ∀ i, |p i| ≤ 1) (i : Fin 2) :
    |roundedProjectionCoordinates σ a b p i| ≤ 1 := by
  have herr := scalarGridFloor_error hσ (boundedProjectionCoordinates a b p i)
  have hbound := boundedProjectionCoordinates_bound ha hb p hp i
  have ht := abs_add_le (boundedProjectionCoordinates a b p i)
    (scalarGridFloor σ (boundedProjectionCoordinates a b p i)-boundedProjectionCoordinates a b p i)
  rw [abs_sub_comm] at ht
  have he : boundedProjectionCoordinates a b p i+
      (scalarGridFloor σ (boundedProjectionCoordinates a b p i)-boundedProjectionCoordinates a b p i) =
      scalarGridFloor σ (boundedProjectionCoordinates a b p i) := by ring
  rw [he] at ht
  change |planarGridFloor σ (boundedProjectionCoordinates a b p) i| ≤ 1
  rw [planarGridFloor_apply]
  linarith

 theorem roundedProjectionCoordinates_coordinate_card {σ δ a b : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) (G : Finset (Space 2)) (m : ℕ) (hm : δ ≤ (m:ℝ)*σ) (i : Fin 2) :
    ((G.image (roundedProjectionCoordinates σ a b)).image (fun p => p i)).card ≤
      5*(2*m+3)*(projectionCells δ (if i = 0 then a else b) G).card := by
  rw [roundedProjectionCoordinates_image,planarGridFloor_coordinate_card hσ]
  exact boundedProjectionCoordinates_coordinate_cells hσ hδ G m hm i

 theorem roundedProjectionCoordinates_regular {δ σ α C t K a b : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hα : 0 < α) (hC : 1 ≤ C)
    (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hscale : (δ/(4/|b-a|))/4 ≤ C*α) (herror : 2*σ ≤ (C-1)*α)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (G : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ G) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound α t ((K*(4/|b-a|)^t*4^t)*C^t)
      (G.image (roundedProjectionCoordinates σ a b)) := by
  have hd : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hba : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith)
  have hL : 1 ≤ 4/|b-a| := (le_div_iff₀ hd).2 (by linarith)
  have hp : 1 ≤ (4/|b-a|)^t := Real.one_le_rpow hL ht
  have hp4 : 1 ≤ (4:ℝ)^t := Real.one_le_rpow (by norm_num) ht
  have hKK0 : 1 ≤ K*(4/|b-a|)^t := by nlinarith
  have hKK : 1 ≤ K*(4/|b-a|)^t*4^t := by nlinarith
  rw [roundedProjectionCoordinates_image]
  exact planarGridFloor_regular hσ hα hC hscale herror ht hKK _
    (boundedProjectionCoordinates_regular hδ hab ha hb ht hK G hreg)
    (planarGridFloor_injOn hσ hsmall _
      (boundedProjectionCoordinates_separated hδ hab ha hb G hsep))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarGridScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compatible original, grid and analysis scales for a weakly separated
pair of projection bases. All costs are polynomial in the inverse separation. -/
namespace Falconer

 theorem planar_grid_scale_bounds {δ M a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 1 ≤ M) (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hgap : 4/M ≤ |b-a|) :
    let σ := δ/(64*M)
    let α := δ/(64*M^2)
    let C := 128*M^2
    0 < σ ∧ σ ≤ 1/2 ∧ 0 < α ∧ σ = M*α ∧ δ = (64*M)*σ ∧ δ = (64*M^2)*α ∧
      1 ≤ C ∧ 4*σ < (δ/(4/|b-a|))/4 ∧
      (δ/(4/|b-a|))/4 ≤ C*α ∧ 2*σ ≤ (C-1)*α := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hd : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hd2 : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith)
  let σ := δ/(64*M)
  let α := δ/(64*M^2)
  let C := 128*M^2
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hs : σ = M*α := by dsimp [σ,α]; field_simp
  have hdσ : δ = (64*M)*σ := by dsimp [σ]; field_simp
  have hdα : δ = (64*M^2)*α := by dsimp [α]; field_simp
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  have hcoord : (δ/(4/|b-a|))/4 = δ*|b-a|/16 := by field_simp; ring
  have hgap' : 4 ≤ M*|b-a| := by
    have hh := (div_le_iff₀ hM0).1 hgap
    nlinarith
  have hσ1 : σ ≤ 1/2 := by nlinarith [hdσ]
  have hsmall : 4*σ < (δ/(4/|b-a|))/4 := by
    rw [hcoord,hdσ]
    have hh := mul_le_mul_of_nonneg_right hgap' hσ.le
    nlinarith
  have hscale : (δ/(4/|b-a|))/4 ≤ C*α := by
    rw [hcoord]
    have hh := mul_le_mul_of_nonneg_left hd2 hδ.le
    change δ*|b-a|/16 ≤ (128*M^2)*α
    nlinarith [hdα]
  have herr : 2*σ ≤ (C-1)*α := by
    rw [hs]
    have hh : 2*M ≤ C-1 := by dsimp [C]; nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh hα.le
  exact ⟨hσ,hσ1,hα,hs,hdσ,hdα,hC,hsmall,hscale,herr⟩

 theorem planar_analysis_dyadic (n l : ℕ) :
    (1/2:ℝ)^n/(64*((2:ℝ)^(l+2))^2) = (1/2:ℝ)^(n+2*l+10) := by
  have hp : ((2:ℝ)^l)^2 = (4:ℝ)^l := by
    rw [← pow_mul,Nat.mul_comm l 2,pow_mul]
    norm_num
  simp only [div_pow,one_pow,pow_add,pow_mul]
  norm_num
  field_simp
  rw [hp]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarGridCosts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit fixed polynomial costs for the original-to-rounded graph
construction. These are absorbed only after the geometric application. -/
namespace Falconer

 theorem planar_grid_polynomial_costs {M L K t A : ℝ}
    (hM : 1 ≤ M) (hL : 0 ≤ L) (hK : 0 ≤ K) (hA : 1 ≤ A) (hAM : A ≤ M)
    (_ht : 0 ≤ t) (ht2 : t ≤ 2) :
    let F := 5*(2*(64*M)+3)
    let B := (2*(2*M^2)+3)*(2*M+3)*(2*(64*M^2)+3)
    F ≤ 655*M ∧ L*F^2 ≤ 429025*L*M^2 ∧
      B*L*F ≤ 3003175*L*M^6 ∧
      (K*A^t*4^t)*(128*M^2)^t ≤ 262144*K*M^6 := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hM2 : 1 ≤ M^2 := by nlinarith
  let F := 5*(2*(64*M)+3)
  let B := (2*(2*M^2)+3)*(2*M+3)*(2*(64*M^2)+3)
  have hF : F ≤ 655*M := by dsimp [F]; linarith
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hB : B ≤ 4585*M^5 := by
    have h0 : 2*(2*M^2)+3 ≤ 7*M^2 := by nlinarith
    have h1 : 2*M+3 ≤ 5*M := by linarith
    have h2 : 2*(64*M^2)+3 ≤ 131*M^2 := by nlinarith
    calc
      B ≤ (7*M^2)*(5*M)*(131*M^2) :=
        mul_le_mul (mul_le_mul h0 h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)
      _ = 4585*M^5 := by ring
  have hQ : L*F^2 ≤ 429025*L*M^2 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hF0 hF 2) hL
    convert hh using 1 <;> first | rfl | ring
  have hBP : B*L*F ≤ 3003175*L*M^6 := by
    calc
      _ ≤ (4585*M^5)*L*(655*M) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hB hL) hF hF0 (by positivity)
      _ = _ := by ring
  have hAp : A^t ≤ M^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hA ht2
    rw [Real.rpow_two] at hh
    exact hh.trans (pow_le_pow_left₀ (zero_le_one.trans hA) hAM 2)
  have h4 : (4:ℝ)^t ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) ht2
    simpa only [Real.rpow_two,show (4:ℝ)^2 = 16 by norm_num] using hh
  have hC : (128*M^2)^t ≤ (128*M^2)^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by nlinarith : 1 ≤ 128*M^2) ht2
    simpa only [Real.rpow_two] using hh
  have hR : (K*A^t*4^t)*(128*M^2)^t ≤ 262144*K*M^6 := by
    calc
      _ ≤ (K*M^2*16)*(128*M^2)^2 :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hAp hK) h4
          (Real.rpow_nonneg (by norm_num) t) (by positivity)) hC
          (Real.rpow_nonneg (by positivity) t) (by positivity)
      _ = _ := by ring
  exact ⟨hF,hQ,hBP,hR⟩

 theorem planar_direction_polynomial_cost {M A K u : ℝ}
    (hM : 1 ≤ M) (hA : 0 ≤ A) (hK : 0 ≤ K) (hu : u ≤ 2) :
    (A*K)*(64*M^2)^u ≤ 4096*A*K*M^4 := by
  have hC : 1 ≤ 64*M^2 := by nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le hC hu
  rw [Real.rpow_two] at hp
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hA hK)
  convert hm using 1 <;> first | rfl | ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarCommonBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One fixed polynomial majorizes the separate rounding, regularity,
density and directional losses in the planar graph application. -/
namespace Falconer

 theorem planar_common_budget {W M : ℝ} (hW : 1 ≤ W) (hM : 1 ≤ M) :
    let B := 4000000*W^5*M^6
    M ≤ B ∧ 429025*W*M^2 ≤ B ∧ 3003175*W*M^6 ≤ B ∧
      262144*W*M^6 ≤ B ∧ 4096*W^2*M^4 ≤ B ∧ 429025*W^2*M^2 ≤ B := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hW5 : 1 ≤ W^5 := one_le_pow₀ hW
  have hM6 : 1 ≤ M^6 := one_le_pow₀ hM
  have hWW : W ≤ W^5 := by simpa only [pow_one] using pow_le_pow_right₀ hW (show 1 ≤ (5:ℕ) by omega)
  have hW2 : W^2 ≤ W^5 := pow_le_pow_right₀ hW (by omega)
  have hMM : M ≤ M^6 := by simpa only [pow_one] using pow_le_pow_right₀ hM (show 1 ≤ (6:ℕ) by omega)
  have hM2 : M^2 ≤ M^6 := pow_le_pow_right₀ hM (by omega)
  have hM4 : M^4 ≤ M^6 := pow_le_pow_right₀ hM (by omega)
  have hprod : 0 ≤ W^5*M^6 := by positivity
  have hcoeff (c : ℝ) (hc : 0 ≤ c) (hcB : c ≤ 4000000) (x y : ℝ)
      (hx : 0 ≤ x) (hy : 0 ≤ y) (hxW : x ≤ W^5) (hyM : y ≤ M^6) :
      c*x*y ≤ 4000000*W^5*M^6 := by
    calc
      _ = c*(x*y) := by ring
      _ ≤ c*(W^5*M^6) := mul_le_mul_of_nonneg_left (mul_le_mul hxW hyM hy (by positivity)) hc
      _ ≤ 4000000*(W^5*M^6) := mul_le_mul_of_nonneg_right hcB hprod
      _ = _ := by ring
  refine ⟨?_,hcoeff 429025 (by norm_num) (by norm_num) W (M^2) hW0 (by positivity) hWW hM2,
    hcoeff 3003175 (by norm_num) (by norm_num) W (M^6) hW0 (by positivity) hWW le_rfl,
    hcoeff 262144 (by norm_num) (by norm_num) W (M^6) hW0 (by positivity) hWW le_rfl,
    hcoeff 4096 (by norm_num) (by norm_num) (W^2) (M^4) (by positivity) (by positivity) hW2 hM4,
    hcoeff 429025 (by norm_num) (by norm_num) (W^2) (M^2) (by positivity) (by positivity) hW2 hM2⟩
  have hh := hcoeff 1 (by norm_num) (by norm_num) 1 M (by norm_num) hM0 hW5 hMM
  simpa only [one_mul] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PlanarWeakDepth
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small auxiliary dyadic depth simultaneously separates the base
projections and pays the fixed polynomial cost of the coordinate graph. -/
namespace Falconer

 theorem planar_weak_coefficients {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧ τ ≤ 1/2 ∧ τ ≤ κ ∧
      30*ε+6*τ ≤ γ/4 ∧ 7*ε ≤ κ*τ/4 := by
  let τ := min (γ/100) (min (κ/100) (1/100))
  let ε := κ*τ/100
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have htγ : τ ≤ γ/100 := min_le_left _ _
  have htκ : τ ≤ κ/100 := (min_le_right _ _).trans (min_le_left _ _)
  have ht1 : τ ≤ 1/100 := (min_le_right _ _).trans (min_le_right _ _)
  have he : 0 < ε := by dsimp [ε]; positivity
  have heτ : ε ≤ τ/100 := by
    have hh := mul_le_mul_of_nonneg_right hκ1 hτ.le
    dsimp [ε]
    nlinarith
  refine ⟨τ,ε,hτ,he,by linarith,by linarith,by linarith,?_⟩
  dsimp [ε]
  nlinarith [mul_pos hκ hτ]

 theorem planar_weak_depth {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (Nmin : ℕ) :
    ∃ ε : ℝ, ∃ n0 : ℕ, 0 < ε ∧ 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ l : ℕ, l ≤ n ∧ Nmin ≤ n+2*l+10 ∧
        Real.log 128+7*ε*(n:ℝ)*Real.log 2 ≤ 2*κ*(l:ℝ)*Real.log 2 ∧
        Real.log (4000000*(64:ℝ)^5)+30*ε*(n:ℝ)*Real.log 2+
          6*((l:ℝ)+2)*Real.log 2 ≤ γ*((n+2*l+10:ℕ):ℝ)*Real.log 2 ∧
        Real.log 655+((l:ℝ)+2)*Real.log 2+(1-4*κ)*(n:ℝ)*Real.log 2 ≤
          (1-κ)*((n+2*l+10:ℕ):ℝ)*Real.log 2 := by
  obtain ⟨τ,ε,hτ,hε,ht1,htκ,heγ,heκ⟩ := planar_weak_coefficients hγ hκ hκ1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := 2/τ
  let B := 4*Real.log 128/(κ*τ*Real.log 2)
  let C := 2*(Real.log (4000000*(64:ℝ)^5)+12*Real.log 2)/(γ*Real.log 2)
  let D := (Real.log 655+2*Real.log 2)/(κ*Real.log 2)
  obtain ⟨n0,hn0⟩ := exists_nat_gt (max (max 1 (Nmin:ℝ)) (max (max A B) (max C D)))
  have hlarge : ∀ n : ℕ, n0 ≤ n →
      (1:ℝ) < n ∧ (Nmin:ℝ) ≤ n ∧ A ≤ n ∧ B ≤ n ∧ C ≤ n ∧ D ≤ n := by
    intro n hn
    have hnR : (n0:ℝ) ≤ n := Nat.cast_le.mpr hn
    have h0 := le_max_left (max 1 (Nmin:ℝ)) (max (max A B) (max C D))
    have h1 := le_max_right (max 1 (Nmin:ℝ)) (max (max A B) (max C D))
    have h2 := le_max_left (1:ℝ) (Nmin:ℝ)
    have h3 := le_max_right (1:ℝ) (Nmin:ℝ)
    have h4 := le_max_left (max A B) (max C D)
    have h5 := le_max_right (max A B) (max C D)
    have h6 := le_max_left A B
    have h7 := le_max_right A B
    have h8 := le_max_left C D
    have h9 := le_max_right C D
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  have hn0pos : 0 < n0 := by
    have hh := (hlarge n0 le_rfl).1
    exact_mod_cast (show (0:ℝ) < n0 by linarith)
  refine ⟨ε,n0,hε,hn0pos,?_⟩
  intro n hn
  obtain ⟨hn1,hN,hA,hB,hC,hD⟩ := hlarge n hn
  let l := ⌊τ*(n:ℝ)⌋₊
  have hfloor : (l:ℝ) ≤ τ*(n:ℝ) := Nat.floor_le (by positivity)
  have hceil : τ*(n:ℝ) < (l:ℝ)+1 := Nat.lt_floor_add_one _
  have hτn : 2 ≤ τ*(n:ℝ) := by
    have hh := (div_le_iff₀ hτ).1 hA
    nlinarith
  have hlower : τ*(n:ℝ)/2 ≤ (l:ℝ) := by linarith
  have hln : l ≤ n := by
    have hh : (l:ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  have hsepconst : Real.log 128 ≤ κ*τ*(n:ℝ)*Real.log 2/4 := by
    have hh := (div_le_iff₀ (by positivity : 0 < κ*τ*Real.log 2)).1 hB
    nlinarith
  have hbudgetconst : Real.log (4000000*(64:ℝ)^5)+12*Real.log 2 ≤
      γ*(n:ℝ)*Real.log 2/2 := by
    have hh := (div_le_iff₀ (mul_pos hγ hlog)).1 hC
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).2
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hlogconst : Real.log 655+2*Real.log 2 ≤ κ*(n:ℝ)*Real.log 2 := by
    have hh := (div_le_iff₀ (mul_pos hκ hlog)).1 hD
    nlinarith
  have hxn : 0 ≤ (n:ℝ)*Real.log 2 := by positivity
  have hNnat : Nmin ≤ n := by exact_mod_cast hN
  refine ⟨l,hln,by omega,?_,?_,?_⟩
  · have he := mul_le_mul_of_nonneg_right heκ hxn
    have hl := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 2*κ*Real.log 2 by positivity)
    nlinarith
  · have he := mul_le_mul_of_nonneg_right heγ hxn
    have hl := mul_le_mul_of_nonneg_left hfloor (show 0 ≤ 6*Real.log 2 by positivity)
    have hnR : ((n+2*l+10:ℕ):ℝ) = (n:ℝ)+2*(l:ℝ)+10 := by norm_cast
    rw [hnR]
    have hmore : 0 ≤ γ*(2*(l:ℝ)+10)*Real.log 2 := by positivity
    have hgn : 0 ≤ γ*(n:ℝ)*Real.log 2 := by positivity
    have hsum : 30*ε*(n:ℝ)*Real.log 2+6*(l:ℝ)*Real.log 2 ≤
        (γ/4)*((n:ℝ)*Real.log 2) := by
      calc
        _ ≤ 30*ε*(n:ℝ)*Real.log 2+6*τ*(n:ℝ)*Real.log 2 := by nlinarith only [hl]
        _ = (30*ε+6*τ)*((n:ℝ)*Real.log 2) := by ring
        _ ≤ _ := he
    calc
      _ = (Real.log (4000000*(64:ℝ)^5)+12*Real.log 2)+
          (30*ε*(n:ℝ)*Real.log 2+6*(l:ℝ)*Real.log 2) := by ring
      _ ≤ γ*(n:ℝ)*Real.log 2/2+(γ/4)*((n:ℝ)*Real.log 2) := add_le_add hbudgetconst hsum
      _ ≤ γ*(n:ℝ)*Real.log 2 := by nlinarith only [hgn]
      _ ≤ γ*((n:ℝ)+2*(l:ℝ)+10)*Real.log 2 := by nlinarith only [hmore]
  · have hl := mul_le_mul_of_nonneg_left hfloor hlog.le
    have ht := mul_le_mul_of_nonneg_right htκ hxn
    have hnR : ((n+2*l+10:ℕ):ℝ) = (n:ℝ)+2*(l:ℝ)+10 := by norm_cast
    rw [hnR]
    have hκ0 : 0 ≤ 1-κ := by linarith
    have hmore : 0 ≤ (1-κ)*(2*(l:ℝ)+10)*Real.log 2 := by positivity
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarWeakParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The linear auxiliary-depth inequalities imply the exact multiplicative
budgets needed by the original planar graph obstruction. -/
namespace Falconer

 theorem planar_weak_parameters {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (Nmin : ℕ) :
    ∃ ε : ℝ, ∃ n0 : ℕ, 0 < ε ∧ 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ l : ℕ, l ≤ n ∧ Nmin ≤ n+2*l+10 ∧
      let W := Real.exp (ε*(n:ℝ)*Real.log 2)
      let M := (2:ℝ)^(l+2)
      let r := (1/2:ℝ)^l
      let S := Real.exp (γ*((n+2*l+10:ℕ):ℝ)*Real.log 2)
      1 ≤ W ∧ 1 ≤ M ∧ 0 < r ∧ r ≤ 1 ∧ (1/2:ℝ)^n ≤ r ∧
        W*r^(2*κ) ≤ (W⁻¹)^6/128 ∧ 4000000*(64*W^6)^5*M^6 ≤ S ∧
        ∀ P : ℝ, 0 < P → Real.log P ≤ (1-4*κ)*(n:ℝ)*Real.log 2 →
          Real.log (655*M*P) ≤ (1-κ)*((n+2*l+10:ℕ):ℝ)*Real.log 2 := by
  obtain ⟨ε,n0,hε,hn0,hdepth⟩ := planar_weak_depth hγ hκ hκ1 Nmin
  refine ⟨ε,n0,hε,hn0,?_⟩
  intro n hn
  obtain ⟨l,hln,hN,hsep,hbudget,hlog⟩ := hdepth n hn
  let W := Real.exp (ε*(n:ℝ)*Real.log 2)
  let M := (2:ℝ)^(l+2)
  let r := (1/2:ℝ)^l
  let S := Real.exp (γ*((n+2*l+10:ℕ):ℝ)*Real.log 2)
  have hW : 0 < W := Real.exp_pos _
  have hM : 0 < M := by dsimp [M]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hWlog : Real.log W = ε*(n:ℝ)*Real.log 2 := Real.log_exp _
  have hMlog : Real.log M = ((l:ℝ)+2)*Real.log 2 := by
    dsimp [M]
    rw [Real.log_pow]
    push_cast
    rfl
  have hrlog : Real.log r = -(l:ℝ)*Real.log 2 := by
    dsimp [r]
    rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one]
    ring
  have hW1 : 1 ≤ W := Real.one_le_exp_iff.mpr (by positivity)
  have hM1 : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hr1 : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hscale : (1/2:ℝ)^n ≤ r := pow_le_pow_of_le_one (by norm_num) (by norm_num) hln
  refine ⟨l,hln,hN,hW1,hM1,hr,hr1,hscale,?_,?_,?_⟩
  · apply (Real.log_le_log_iff (mul_pos hW (Real.rpow_pos_of_pos hr _)) (by positivity)).1
    change Real.log (W*r^(2*κ)) ≤ Real.log ((W⁻¹)^6/128)
    have hleft : Real.log (W*r^(2*κ)) = Real.log W+2*κ*Real.log r := by
      rw [Real.log_mul hW.ne' (Real.rpow_pos_of_pos hr _).ne',Real.log_rpow hr]
    have hright : Real.log ((W⁻¹)^6/128) = -6*Real.log W-Real.log 128 := by
      rw [Real.log_div (by positivity) (by norm_num),Real.log_pow,Real.log_inv]
      norm_num
    rw [hleft,hright,hWlog,hrlog]
    nlinarith only [hsep]
  · apply (Real.log_le_log_iff (by positivity) (Real.exp_pos _)).1
    change Real.log (4000000*(64*W^6)^5*M^6) ≤ _
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_pow,Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow,
      hWlog,hMlog,Real.log_exp]
    have hc : Real.log (4000000*(64:ℝ)^5) = Real.log 4000000+5*Real.log 64 := by
      rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
      norm_num
    rw [hc] at hbudget
    convert hbudget using 1 <;> first | rfl | ring
  · intro P hP hPlog
    rw [Real.log_mul (mul_ne_zero (by norm_num) hM.ne') hP.ne',
      Real.log_mul (by norm_num) hM.ne',hMlog]
    linarith only [hlog,hPlog]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteFamilyOverlap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common row with many large intersections, for the two-sided
additive-energy refinements. -/
namespace Falconer

 theorem finite_membership_sum {β : Type*} [DecidableEq β]
    (U S : Finset β) (hS : S ⊆ U) :
    (∑ x ∈ U, if x ∈ S then (1 : ℝ) else 0) = S.card := by
  have he : U.filter (fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hx => hS hx)
  rw [Finset.sum_boole,he]

 theorem finite_family_overlap_moment {α β : Type*} [DecidableEq β]
    (I : Finset α) (U : Finset β) (A : α → Finset β)
    (hsub : ∀ i ∈ I, A i ⊆ U) :
    (∑ i ∈ I, ((A i).card : ℝ))^2 ≤
      (U.card : ℝ)*(∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ)) := by
  classical
  let d := fun x => ∑ i ∈ I, if x ∈ A i then (1 : ℝ) else 0
  have htotal : ∑ x ∈ U, d x = ∑ i ∈ I, ((A i).card : ℝ) := by
    dsimp [d]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i hi => finite_membership_sum U (A i) (hsub i hi)
  have hsquare : (∑ x ∈ U, (d x)^2) =
      ∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ) := by
    calc
      _ = ∑ x ∈ U, ∑ i ∈ I, ∑ j ∈ I,
          (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) := by
        simp only [d,pow_two,Finset.sum_mul_sum]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ U,
          (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j _
        have he (x : β) :
            (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) =
            if x ∈ A i ∩ A j then 1 else 0 := by
          by_cases hx : x ∈ A i <;> by_cases hy : x ∈ A j <;> simp [hx,hy]
        simp_rw [he]
        exact finite_membership_sum U _ fun x hx => hsub i hi (Finset.mem_inter.mp hx).1
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) d
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,htotal,hsquare] using hCS

 theorem finite_family_common_row {α β : Type*} [DecidableEq β]
    (I : Finset α) (U : Finset β) (A : α → Finset β)
    (hI : I.Nonempty) (hU : U.Nonempty) {m : ℝ} (hm : 0 < m)
    (hsub : ∀ i ∈ I, A i ⊆ U) (hsize : ∀ i ∈ I, m ≤ ((A i).card : ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      (m^2/(U.card : ℝ))*(I.card : ℝ) ≤ 2*(U.card : ℝ)*(J.card : ℝ) ∧
      ∀ j ∈ J, m^2/(2*(U.card : ℝ)) ≤ ((A i₀ ∩ A j).card : ℝ) := by
  classical
  have hIpos : 0 < (I.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hI)
  have hUpos : 0 < (U.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hU)
  let w := fun i => ∑ j ∈ I, ((A i ∩ A j).card : ℝ)
  obtain ⟨i₀,hi₀,hmax⟩ := I.exists_max_image w hI
  have hsum : m*(I.card : ℝ) ≤ ∑ i ∈ I, ((A i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ I, m := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hsize
  have hmoment := finite_family_overlap_moment I U A hsub
  have hmaxsum : (∑ i ∈ I, w i) ≤ (I.card : ℝ)*w i₀ := by
    calc
      _ ≤ ∑ _i ∈ I, w i₀ := Finset.sum_le_sum fun i hi => hmax i hi
      _ = _ := by simp
  have hlower : (m*(I.card : ℝ))^2 ≤ (U.card : ℝ)*((I.card : ℝ)*w i₀) := by
    exact (pow_le_pow_left₀ (mul_pos hm hIpos).le hsum 2).trans
      (hmoment.trans (mul_le_mul_of_nonneg_left hmaxsum hUpos.le))
  have hw : (m^2/(U.card : ℝ))*(I.card : ℝ) ≤ w i₀ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hUpos).2
    apply (mul_le_mul_iff_left₀ hIpos).1
    calc
      _ = (m*(I.card : ℝ))^2 := by ring
      _ ≤ _ := hlower
      _ = _ := by ring
  let J := I.filter fun j => m^2/(2*(U.card : ℝ)) ≤ ((A i₀ ∩ A j).card : ℝ)
  have hp := finite_popular_mass I (fun j => ((A i₀ ∩ A j).card : ℝ))
    (I := (m^2/(U.card : ℝ))*(I.card : ℝ))
    (θ := m^2/(2*(U.card : ℝ))) (L := (U.card : ℝ))
    (by positivity) hw (le_of_eq (by ring))
    (fun j _ => Nat.cast_le.mpr (Finset.card_le_card
      (fun x hx => hsub i₀ hi₀ (Finset.mem_inter.mp hx).1)))
  refine ⟨i₀,hi₀,J,Finset.filter_subset _ _,?_,?_⟩
  · have hh := hp.2
    change (m^2/(U.card : ℝ))*(I.card : ℝ)/2 ≤ (U.card : ℝ)*(J.card : ℝ) at hh
    linarith
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_CommonSliceSelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative common-slice selection and loss bounds for deleting short
intervals of directions. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem finite_relative_common_row {α β : Type*} [DecidableEq β]
    (I : Finset α) (U : Finset β) (A : α → Finset β)
    (hI : I.Nonempty) (hU : U.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ i ∈ I, A i ⊆ U) (hsize : ∀ i ∈ I, ρ*(U.card:ℝ) ≤ ((A i).card:ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I, (ρ^2/2)*(I.card:ℝ) ≤ (J.card:ℝ) ∧
      ∀ j ∈ J, (ρ^2/2)*(U.card:ℝ) ≤ ((A i₀ ∩ A j).card:ℝ) := by
  have hUp : 0 < (U.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hU)
  obtain ⟨i,hi,J,hJI,hJ,hcount⟩ := finite_family_common_row I U A hI hU (mul_pos hρ hUp) hsub hsize
  refine ⟨i,hi,J,hJI,?_,?_⟩
  · have he : (ρ*(U.card:ℝ))^2/(U.card:ℝ) = ρ^2*(U.card:ℝ) := by field_simp
    rw [he] at hJ
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2*(U.card:ℝ))).1
    first | (convert hJ using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hJ.trans (le_of_eq (by ring)))
  · intro j hj
    have he : (ρ*(U.card:ℝ))^2/(2*(U.card:ℝ)) = (ρ^2/2)*(U.card:ℝ) := by field_simp
    simpa only [he] using hcount j hj

 theorem finite_delete_interval {I J : Finset ℝ} (hJI : J ⊆ I) (z r : ℝ) :
    (J.card:ℝ)-scalarBallMass I z r ≤ ((J.filter fun y => r < |y-z|).card:ℝ) := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := J) (p := fun y => |y-z| ≤ r)
  have hsmall : ((J.filter fun y => |y-z| ≤ r).card:ℝ) ≤ scalarBallMass I z r :=
    Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hJI))
  have he : (J.filter fun y => ¬ |y-z| ≤ r) = J.filter fun y => r < |y-z| := by
    simp only [not_le]
  rw [he] at hc
  have hcR : ((J.filter fun y => |y-z| ≤ r).card:ℝ)+
      ((J.filter fun y => r < |y-z|).card:ℝ) = (J.card:ℝ) := by exact_mod_cast hc
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SeparatedProjectionBases
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two separated projection bases with many common large slices. The
separation comes from the original direction-set ball count. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem separated_projection_bases {β : Type*} [DecidableEq β]
    (I : Finset ℝ) (U : Finset β) (A : ℝ → Finset β)
    (hI : I.Nonempty) (hU : U.Nonempty) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 0 < r)
    (hsub : ∀ i ∈ I, A i ⊆ U)
    (hsize : ∀ i ∈ I, ρ*(U.card:ℝ) ≤ ((A i).card:ℝ))
    (hball : ∀ z : ℝ, scalarBallMass I z r ≤ (ρ^6/128)*(I.card:ℝ)) :
    ∃ a ∈ I, ∃ b ∈ I, r < |b-a| ∧ b ≠ a ∧ ∃ J ⊆ I,
      (ρ^6/64)*(I.card:ℝ) ≤ (J.card:ℝ) ∧
      ∀ j ∈ J, r < |j-a| ∧ r < |j-b| ∧
        (ρ^4/8)*(U.card:ℝ) ≤ (((A a ∩ A b) ∩ A j).card:ℝ) := by
  classical
  obtain ⟨a,ha,J1,hJ1I,hJ1,hpair1⟩ := finite_relative_common_row I U A hI hU hρ hsub hsize
  let F1 := J1.filter fun y => r < |y-a|
  have hF1I : F1 ⊆ I := (Finset.filter_subset _ _).trans hJ1I
  have hpow : ρ^6 ≤ ρ^2 := pow_le_pow_of_le_one hρ.le hρ1 (by omega)
  have hnear : scalarBallMass I a r ≤ (ρ^2/4)*(I.card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show ρ^6/128 ≤ ρ^2/4 by nlinarith [sq_nonneg ρ])
      (Nat.cast_nonneg (α := ℝ) I.card)
    exact (hball a).trans hh
  have hF1count : (ρ^2/4)*(I.card:ℝ) ≤ (F1.card:ℝ) := by
    have hh := finite_delete_interval hJ1I a r
    change (J1.card:ℝ)-scalarBallMass I a r ≤ (F1.card:ℝ) at hh
    nlinarith
  have hF1 : F1.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < (ρ^2/4)*(I.card:ℝ) := mul_pos (by positivity)
      (Nat.cast_pos.mpr (Finset.card_pos.mpr hI))
    exact_mod_cast hp.trans_le hF1count
  let B := fun j => A a ∩ A j
  have hBsub : ∀ j ∈ F1, B j ⊆ U := fun _ _ =>
    Finset.inter_subset_left.trans (hsub a ha)
  have hBsize : ∀ j ∈ F1, (ρ^2/2)*(U.card:ℝ) ≤ ((B j).card:ℝ) :=
    fun j hj => hpair1 j (Finset.mem_filter.mp hj).1
  obtain ⟨b,hb,J2,hJ2F,hJ2,hpair2⟩ := finite_relative_common_row F1 U B hF1 hU
    (by positivity : 0 < ρ^2/2) hBsub hBsize
  have hbI : b ∈ I := hF1I hb
  have hba : r < |b-a| := (Finset.mem_filter.mp hb).2
  have hJ2I : J2 ⊆ I := hJ2F.trans hF1I
  have hJ2count : (ρ^6/32)*(I.card:ℝ) ≤ (J2.card:ℝ) := by
    calc
      _ = ((ρ^2/2)^2/2)*((ρ^2/4)*(I.card:ℝ)) := by ring
      _ ≤ ((ρ^2/2)^2/2)*(F1.card:ℝ) := mul_le_mul_of_nonneg_left hF1count (by positivity)
      _ ≤ _ := hJ2
  let J3 := J2.filter fun y => r < |y-a|
  let J := J3.filter fun y => r < |y-b|
  have hJ3I : J3 ⊆ I := (Finset.filter_subset _ _).trans hJ2I
  have hJI : J ⊆ I := (Finset.filter_subset _ _).trans hJ3I
  have hJcount : (ρ^6/64)*(I.card:ℝ) ≤ (J.card:ℝ) := by
    have h0 := finite_delete_interval hJ2I a r
    have h1 := finite_delete_interval hJ3I b r
    change (J2.card:ℝ)-scalarBallMass I a r ≤ (J3.card:ℝ) at h0
    change (J3.card:ℝ)-scalarBallMass I b r ≤ (J.card:ℝ) at h1
    nlinarith [hball a,hball b]
  have hbaNe : b ≠ a := sub_ne_zero.mp (abs_pos.mp (hr.trans hba))
  refine ⟨a,ha,b,hbI,hba,hbaNe,J,hJI,hJcount,?_⟩
  intro j hj
  obtain ⟨hj3,hjb⟩ := Finset.mem_filter.mp hj
  obtain ⟨hj2,hja⟩ := Finset.mem_filter.mp hj3
  refine ⟨hja,hjb,?_⟩
  have hh := hpair2 j hj2
  have he : B b ∩ B j = (A a ∩ A b) ∩ A j := by
    ext x
    simp only [B,Finset.mem_inter]
    tauto
  rw [he] at hh
  convert hh using 1 <;> first | rfl | ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CommonProjectionConfiguration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two bases and every graph slice are selected from the original
common projection family, retaining explicit relative mass and regularity. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem common_projection_configuration {δ t K ρ r : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 0 < r)
    (I : Finset ℝ) (U : Finset (Space 2)) (A : ℝ → Finset (Space 2))
    (hI : I.Nonempty) (hU : U.Nonempty)
    (hsub : ∀ i ∈ I, A i ⊆ U)
    (hsize : ∀ i ∈ I, ρ*(U.card:ℝ) ≤ ((A i).card:ℝ))
    (hball : ∀ z : ℝ, scalarBallMass I z r ≤ (ρ^6/128)*(I.card:ℝ))
    (hUreg : NormalizedFiniteBallBound δ t K U)
    (P : ℕ) (hproj : ∀ i ∈ I, (projectionCells δ i (A i)).card ≤ P) :
    ∃ a ∈ I, ∃ b ∈ I, r < |b-a| ∧ b ≠ a ∧ ∃ J ⊆ I,
      J.Nonempty ∧ (ρ^6/64)*(I.card:ℝ) ≤ (J.card:ℝ) ∧
      let V := A a ∩ A b
      V.Nonempty ∧ V ⊆ U ∧ (U.card:ℝ) ≤ (8/ρ^4)*(V.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*(8/ρ^4)) V ∧
      (projectionCells δ a V).card ≤ P ∧ (projectionCells δ b V).card ≤ P ∧
      ∀ j ∈ J, r < |j-a| ∧ r < |j-b| ∧
        (ρ^4/8)*(V.card:ℝ) ≤ ((V ∩ A j).card:ℝ) ∧
        (projectionCells δ j (V ∩ A j)).card ≤ P := by
  classical
  obtain ⟨a,ha,b,hb,hab,hba,J,hJI,hJsize,htriple⟩ :=
    separated_projection_bases I U A hI hU hρ hρ1 hr hsub hsize hball
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < (ρ^6/64)*(I.card:ℝ) :=
      mul_pos (by positivity) (Nat.cast_pos.mpr hI.card_pos)
    exact_mod_cast hp.trans_le hJsize
  let V := A a ∩ A b
  have hVU : V ⊆ U := Finset.inter_subset_left.trans (hsub a ha)
  obtain ⟨j,hj⟩ := hJ
  have hVlower : (ρ^4/8)*(U.card:ℝ) ≤ (V.card:ℝ) :=
    (htriple j hj).2.2.trans (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left))
  have hV : V.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < (ρ^4/8)*(U.card:ℝ) :=
      mul_pos (by positivity) (Nat.cast_pos.mpr hU.card_pos)
    exact_mod_cast hp.trans_le hVlower
  have hVUsize : (U.card:ℝ) ≤ (8/ρ^4)*(V.card:ℝ) := by
    have hpos : 0 < ρ^4 := by positivity
    have hh := mul_le_mul_of_nonneg_left hVlower (show 0 ≤ 8/ρ^4 by positivity)
    have he : (8/ρ^4)*((ρ^4/8)*(U.card:ℝ)) = (U.card:ℝ) := by field_simp
    rwa [he] at hh
  refine ⟨a,ha,b,hb,hab,hba,J,hJI,⟨j,hj⟩,hJsize,hV,hVU,hVUsize,
    normalized_finite_ball_bound_subset hδ hK hVU hVUsize hUreg,?_,?_,?_⟩
  · exact (Finset.card_le_card (projectionCells_mono δ a Finset.inter_subset_left)).trans (hproj a ha)
  · exact (Finset.card_le_card (projectionCells_mono δ b Finset.inter_subset_right)).trans (hproj b hb)
  · intro j hj
    obtain ⟨hja,hjb,hcard⟩ := htriple j hj
    refine ⟨hja,hjb,?_,?_⟩
    · exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hVU))
        (show 0 ≤ ρ^4/8 by positivity)).trans hcard
    · exact (Finset.card_le_card (projectionCells_mono δ j Finset.inter_subset_right)).trans (hproj j (hJI hj))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CommonProjectionLosses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single weak constant controls every loss from selecting the common
projection bases and restricting to their intersection. -/
namespace Falconer

 theorem common_projection_losses {W : ℝ} (hW : 1 ≤ W) :
    let ρ := W⁻¹
    let Z := 64*W^6
    0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ Z ∧ W ≤ Z ∧ W*(8/ρ^4) ≤ Z ∧
      64/ρ^6 = Z ∧ 0 < ρ^4/8 ∧ (ρ^4/8)⁻¹ ≤ Z := by
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hρ : 0 < W⁻¹ := inv_pos.mpr hWpos
  have hρ1 : W⁻¹ ≤ 1 := (inv_le_one₀ hWpos).2 hW
  have h6 : 1 ≤ W^6 := one_le_pow₀ hW
  have hW6 : W ≤ W^6 := by simpa only [pow_one] using pow_le_pow_right₀ hW (show 1 ≤ (6:ℕ) by omega)
  have hW5 : W^5 ≤ W^6 := pow_le_pow_right₀ hW (by omega)
  have hW4 : W^4 ≤ W^6 := pow_le_pow_right₀ hW (by omega)
  have he4 : 8/(W⁻¹)^4 = 8*W^4 := by field_simp
  have he6 : 64/(W⁻¹)^6 = 64*W^6 := by field_simp
  have hei : ((W⁻¹)^4/8)⁻¹ = 8*W^4 := by field_simp
  refine ⟨hρ,hρ1,by nlinarith,by nlinarith,?_,he6,by positivity,?_⟩
  · rw [he4]
    have he : W*(8*W^4) = 8*W^5 := by ring
    rw [he]
    nlinarith
  · rw [hei]
    nlinarith

 theorem common_projection_direction_count {ρ : ℝ} (hρ : 0 < ρ)
    (I J : Finset ℝ) (hcount : (ρ^6/64)*(I.card:ℝ) ≤ (J.card:ℝ)) :
    (I.card:ℝ) ≤ (64/ρ^6)*(J.card:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 64/ρ^6 by positivity)
  have he : (64/ρ^6)*((ρ^6/64)*(I.card:ℝ)) = (I.card:ℝ) := by field_simp
  rwa [he] at hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionRatioGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometry of the fractional-linear direction map generated by two
projection bases. All constants depend only on their separation. -/
namespace Falconer

 theorem projectionRatio_difference {a b y z : ℝ} (hy : y ≠ b) (hz : z ≠ b) :
    (projectionRatio a b y-projectionRatio a b z)*(b-y)*(b-z) = (b-a)*(y-z) := by
  have hy' : b-y ≠ 0 := sub_ne_zero.mpr hy.symm
  have hz' : b-z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold projectionRatio
  field_simp
  ring

 theorem projectionRatio_injOn {a b : ℝ} (hab : b ≠ a) :
    Set.InjOn (projectionRatio a b) {y : ℝ | y ≠ b} := by
  intro y hy z hz he
  have hh := projectionRatio_difference (a := a) hy hz
  rw [he,sub_self,zero_mul,zero_mul] at hh
  have hba : b-a ≠ 0 := sub_ne_zero.mpr hab
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_left hba)

 theorem projectionRatio_inverse_bound {a b y z : ℝ} (hab : b ≠ a)
    (hy : y ≠ b) (hz : z ≠ b) (hb : |b| ≤ 1) (hy1 : |y| ≤ 1) (hz1 : |z| ≤ 1) :
    |y-z| ≤ (4/|b-a|)*|projectionRatio a b y-projectionRatio a b z| := by
  have hsep : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hby : |b-y| ≤ 2 := (abs_sub b y).trans (by linarith)
  have hbz : |b-z| ≤ 2 := (abs_sub b z).trans (by linarith)
  have hh := congrArg abs (projectionRatio_difference (a := a) hy hz)
  simp only [abs_mul] at hh
  have hp : |b-y| * |b-z| ≤ 4 := by nlinarith [abs_nonneg (b-y),abs_nonneg (b-z)]
  have hm := mul_le_mul_of_nonneg_left hp (abs_nonneg (projectionRatio a b y-projectionRatio a b z))
  have hnum : |y-z| * |b-a| ≤ 4*|projectionRatio a b y-projectionRatio a b z| := by nlinarith
  have he : (4/|b-a|)*|projectionRatio a b y-projectionRatio a b z| =
      (4*|projectionRatio a b y-projectionRatio a b z|)/|b-a| := by ring
  rw [he]
  exact (le_div_iff₀ hsep).2 hnum

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionRatioBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interpolation normalization is controlled by the same coefficient
bound as the scalar graph projection. -/
namespace Falconer

 theorem projectionRatio_normalizing_bound {a b y M : ℝ} (hy : y ≠ b)
    (hM : 1 ≤ M) (hc : |projectionRatio a b y| ≤ M) :
    |((b-a)/(b-y))/4| ≤ M := by
  have hby : b-y ≠ 0 := sub_ne_zero.mpr hy.symm
  have he : (b-a)/(b-y) = 1+projectionRatio a b y := by
    unfold projectionRatio
    field_simp
    ring
  rw [he,abs_div]
  norm_num
  have hh := abs_add_le (1:ℝ) (projectionRatio a b y)
  norm_num at hh
  linarith

 theorem projectionRatio_ne_pole {a b y : ℝ} (hc : projectionRatio a b y ≠ 0) : y ≠ b := by
  intro h
  subst y
  simp only [projectionRatio,sub_self,div_zero] at hc
  exact hc rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScalarScaleAlignment
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Align any fine dyadic resolution with a fixed block width. The
 difference is at most one block and all covering losses stay fixed. -/
namespace Falconer

 theorem scalar_fixed_losses {η C D : ℝ} (hη : 0 < η) (hC : 0 < C) (hD : 0 < D) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*Real.exp ((η/4)*(N:ℝ)*Real.log 2) ≤ Real.exp (η*(N:ℝ)*Real.log 2) ∧
      D*Real.exp ((η/4)*(N:ℝ)*Real.log 2) ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1
    (max (Real.log C) (Real.log D)/((3*η/4)*Real.log 2)))
  have hNpos : 0 < N0 := by
    have hh := (le_max_left _ _).trans_lt hN0
    exact_mod_cast (show (0:ℝ) < N0 by linarith)
  have hbase : max (Real.log C) (Real.log D) ≤ (3*η/4)*(N0:ℝ)*Real.log 2 := by
    have hh := (div_lt_iff₀ (by positivity : 0 < (3*η/4)*Real.log 2)).1
      ((le_max_right _ _).trans_lt hN0)
    nlinarith
  refine ⟨N0,hNpos,?_⟩
  intro N hN
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hN)
    (show 0 ≤ (3*η/4)*Real.log 2 by positivity)
  have hmax : max (Real.log C) (Real.log D) ≤ (3*η/4)*(N:ℝ)*Real.log 2 := by nlinarith
  constructor
  · calc
      _ = Real.exp (Real.log C+(η/4)*(N:ℝ)*Real.log 2) := by rw [Real.exp_add,Real.exp_log hC]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [le_max_left (Real.log C) (Real.log D)])
  · calc
      _ = Real.exp (Real.log D+(η/4)*(N:ℝ)*Real.log 2) := by rw [Real.exp_add,Real.exp_log hD]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [le_max_right (Real.log C) (Real.log D)])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_RoundedProjectionGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact edge counts and original projection bounds for the rounded
coordinate graphs, before any asymptotic loss absorption. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem roundedProjectionCoordinates_projection_cells {δ σ ρ a b y : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hρ : 0 < ρ) (hab : b ≠ a) (hy : y ≠ b)
    (G : Finset (Space 2)) (k M m : ℕ)
    (hk : (1+|(y-a)/(b-y)|)*σ ≤ (k:ℝ)*δ)
    (hM : |((b-a)/(b-y))/4| ≤ M) (hm : ρ ≤ (m:ℝ)*δ) :
    (scalarCells δ ((G.image (roundedProjectionCoordinates σ a b)).image
      (cartesianProjection ((y-a)/(b-y))))).card ≤
      (2*k+3)*(2*M+3)*(2*m+3)*(projectionCells ρ y G).card := by
  rw [roundedProjectionCoordinates_image]
  have hg := cartesianProjection_grid_cells hδ hσ ((y-a)/(b-y))
    (G.image (boundedProjectionCoordinates a b)) k hk
  rw [boundedProjectionCoordinates_projection_image hab hy] at hg
  have hd := scalar_dilation_cells hδ (G.image (lineParameterProjection y)) M hM
  have hr := scalar_cells_resolution hδ hρ m hm (G.image (lineParameterProjection y))
  have he : scalarCells ρ (G.image (lineParameterProjection y)) = projectionCells ρ y G := by
    simp only [scalarCells,projectionCells,Finset.image_image,Function.comp_def]
  rw [he] at hr
  calc
    _ ≤ (2*k+3)*(scalarCells δ ((G.image (lineParameterProjection y)).image
        (fun v => (((b-a)/(b-y))/4)*v))).card := hg
    _ ≤ (2*k+3)*((2*M+3)*(scalarCells δ (G.image (lineParameterProjection y))).card) :=
      Nat.mul_le_mul_left _ hd
    _ ≤ (2*k+3)*((2*M+3)*((2*m+3)*(projectionCells ρ y G).card)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr)
    _ = _ := by ring

 theorem coordinate_graph_factor_lower {X Y G N K : ℝ}
    (hN : 0 < N) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hK : 0 ≤ K)
    (hXN : X ≤ N) (hYN : Y ≤ N) (hG : G ≤ X*Y) (hlarge : N^2 ≤ K*G) :
    N ≤ K*X ∧ N ≤ K*Y := by
  have hKG := mul_le_mul_of_nonneg_left hG hK
  have h0 := mul_le_mul_of_nonneg_left hYN (mul_nonneg hK hX)
  have h1 := mul_le_mul_of_nonneg_left hXN (mul_nonneg hK hY)
  constructor
  · apply (mul_le_mul_iff_right₀ hN).1
    nlinarith
  · apply (mul_le_mul_iff_right₀ hN).1
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_RoundedGraphCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original cardinality bounds supply both coordinate comparability and
graph density; no balance or density condition is added to the point set. -/
namespace Falconer

 theorem coordinate_graph_scaled_bounds {X Y G n F K : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hn : 0 < n) (hF : 0 < F) (hK : 0 ≤ K)
    (hXN : X ≤ F*n) (hYN : Y ≤ F*n) (hG : G ≤ X*Y) (hlarge : n^2 ≤ K*G) :
    X ≤ (K*F^2)*Y ∧ Y ≤ (K*F^2)*X ∧
      n ≤ K*F*X ∧ n ≤ K*F*Y ∧ X*Y ≤ (K*F^2)*G := by
  have hN : 0 < F*n := mul_pos hF hn
  have hK' : 0 ≤ K*F^2 := mul_nonneg hK (sq_nonneg F)
  have hlarge' : (F*n)^2 ≤ (K*F^2)*G := by
    have hh := mul_le_mul_of_nonneg_left hlarge (sq_nonneg F)
    nlinarith
  obtain ⟨hcX,hcY⟩ := coordinate_graph_comparable hX hY hK' hXN hYN hG hlarge'
  obtain ⟨hlX,hlY⟩ := coordinate_graph_factor_lower hN hX.le hY.le hK' hXN hYN hG hlarge'
  have hlX' : n ≤ K*F*X := by
    apply (mul_le_mul_iff_right₀ hF).1
    nlinarith [hlX]
  have hlY' : n ≤ K*F*Y := by
    apply (mul_le_mul_iff_right₀ hF).1
    nlinarith [hlY]
  have hp : X*Y ≤ (F*n)^2 := by
    have hh := mul_le_mul hXN hYN hY.le hN.le
    nlinarith
  exact ⟨hcX,hcY,hlX',hlY',hp.trans hlarge'⟩

 theorem roundedProjectionCoordinates_coordinate_upper {δ σ a b : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (U : Finset (Space 2)) (m P : ℕ)
    (hm : δ ≤ (m:ℝ)*σ)
    (ha : (projectionCells δ a U).card ≤ P) (hb : (projectionCells δ b U).card ≤ P)
    (i : Fin 2) :
    (((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p i)).card:ℝ) ≤
      (5*(2*(m:ℝ)+3))*(P:ℝ) := by
  have hh := roundedProjectionCoordinates_coordinate_card (a := a) (b := b) hσ hδ U m hm i
  have hp : (projectionCells δ (if i = 0 then a else b) U).card ≤ P := by
    split_ifs <;> assumption
  have hc := hh.trans (Nat.mul_le_mul_left (5*(2*m+3)) hp)
  exact_mod_cast hc

 theorem scalar_dilation_separated {δ σ M c : ℝ} (hM : 0 < M)
    (hscale : δ*M ≤ σ) (hc : c ≠ 0) (hcM : |c⁻¹| ≤ M)
    (Y : Finset ℝ) (hsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → σ ≤ |x-y|) :
    ∀ x ∈ Y.image (fun y => c*y), ∀ y ∈ Y.image (fun y => c*y), x ≠ y → δ ≤ |x-y| := by
  intro x hx y hy hxy
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
  have huv : u ≠ v := fun h => hxy (by rw [h])
  have hs := hsep u hu v hv huv
  have he : |u-v| = |c⁻¹| * |c*u-c*v| := by
    rw [← mul_sub,abs_mul,← mul_assoc,← abs_mul,inv_mul_cancel₀ hc,abs_one,one_mul]
  rw [he] at hs
  have hm := mul_le_mul_of_nonneg_right hcM (abs_nonneg (c*u-c*v))
  apply (mul_le_mul_iff_right₀ hM).1
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_RoundedGraphData
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original planar point and projection counts determine all size
parameters in the rounded graph. -/
namespace Falconer

 theorem rounded_graph_size_bounds {δ σ a b L : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (U : Finset (Space 2)) (hU : U.Nonempty) (hsep : FiniteSeparatedAt δ U)
    (m P : ℕ) (hP : 0 < P) (hL : 0 ≤ L) (hm : δ ≤ (m:ℝ)*σ)
    (hpa : (projectionCells δ a U).card ≤ P) (hpb : (projectionCells δ b U).card ≤ P)
    (hlarge : (P:ℝ)^2 ≤ L*(U.card:ℝ)) :
    let G := U.image (roundedProjectionCoordinates σ a b)
    let X := G.image (fun p => p 0)
    let Y := G.image (fun p => p 1)
    let F : ℝ := 5*(2*(m:ℝ)+3)
    X.Nonempty ∧ Y.Nonempty ∧
      (X.card:ℝ) ≤ F*(P:ℝ) ∧ (Y.card:ℝ) ≤ F*(P:ℝ) ∧
      (X.card:ℝ) ≤ (L*F^2)*(Y.card:ℝ) ∧
      (P:ℝ) ≤ L*F*(X.card:ℝ) ∧
      (X.card:ℝ)*(Y.card:ℝ) ≤ (L*F^2)*(U.card:ℝ) := by
  classical
  dsimp only
  let G := U.image (roundedProjectionCoordinates σ a b)
  let X := G.image (fun p => p 0)
  let Y := G.image (fun p => p 1)
  let F : ℝ := 5*(2*(m:ℝ)+3)
  have hX : X.Nonempty := (hU.image _).image _
  have hY : Y.Nonempty := (hU.image _).image _
  have hx : (X.card:ℝ) ≤ F*(P:ℝ) :=
    roundedProjectionCoordinates_coordinate_upper hδ hσ U m P hm hpa hpb 0
  have hy : (Y.card:ℝ) ≤ F*(P:ℝ) :=
    roundedProjectionCoordinates_coordinate_upper hδ hσ U m P hm hpa hpb 1
  have hc : G.card = U.card := roundedProjectionCoordinates_card hδ hσ hab ha hb hsmall U hsep
  have hg : (U.card:ℝ) ≤ (X.card:ℝ)*(Y.card:ℝ) := by
    rw [← hc]
    exact_mod_cast coordinate_graph_card_le X Y G (fun p hp =>
      ⟨Finset.mem_image_of_mem _ hp,Finset.mem_image_of_mem _ hp⟩)
  obtain ⟨hxy,_,hpx,_,hprod⟩ := coordinate_graph_scaled_bounds
    (Nat.cast_pos.mpr hX.card_pos) (Nat.cast_pos.mpr hY.card_pos)
    (Nat.cast_pos.mpr hP) (by dsimp [F]; positivity) hL hx hy hg hlarge
  exact ⟨hX,hY,hx,hy,hxy,hpx,hprod⟩

 theorem rounded_graph_density_bound {δ σ a b ρ Q : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hsmall : 4*σ < (δ/(4/|b-a|))/4)
    (U A : Finset (Space 2)) (hAU : A ⊆ U) (hsep : FiniteSeparatedAt δ U)
    (hρ : 0 ≤ ρ) (hQ : 0 < Q) (hdense : ρ*(U.card:ℝ) ≤ (A.card:ℝ))
    (hprod :
      (((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p 0)).card:ℝ)*
        (((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p 1)).card:ℝ) ≤ Q*(U.card:ℝ)) :
    (ρ/Q)*(((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p 0)).card:ℝ)*
      (((U.image (roundedProjectionCoordinates σ a b)).image (fun p => p 1)).card:ℝ) ≤
      ((A.image (roundedProjectionCoordinates σ a b)).card:ℝ) := by
  have hi := (roundedProjectionCoordinates_injOn hδ hσ hab ha hb hsmall U hsep).mono hAU
  rw [Finset.card_image_of_injOn hi]
  exact coordinate_graph_density hρ hQ hprod hdense

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RoundedPlanarObstruction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dense scalar obstruction applies to original planar sets and
large common slices. Every coordinate and graph hypothesis is derived. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem rounded_planar_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let α := (1/2:ℝ)^N
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (δ σ a b t K C L ρ : ℝ) (m q k M P : ℕ)
        (J : Finset ℝ) (U : Finset (Space 2)) (H : ℝ → Finset (Space 2)),
      let F : ℝ := 5*(2*(m:ℝ)+3)
      let Q := L*F^2
      let B : ℝ := (2*(k:ℝ)+3)*(2*(M:ℝ)+3)*(2*(q:ℝ)+3)
      0 < δ → 0 < σ → σ ≤ 1/2 → b ≠ a → |a| ≤ 1 → |b| ≤ 1 →
      4*σ < (δ/(4/|b-a|))/4 → 1 ≤ M → (M:ℝ) ≤ S → α*(M:ℝ) ≤ σ →
      δ ≤ (m:ℝ)*σ → δ ≤ (q:ℝ)*α → (1+(M:ℝ))*σ ≤ (k:ℝ)*α →
      1 ≤ C → (δ/(4/|b-a|))/4 ≤ C*α → 2*σ ≤ (C-1)*α →
      2*κ ≤ t → t ≤ 2 → 1 ≤ K → 0 ≤ L → 0 ≤ ρ →
      1 ≤ Q → Q ≤ S → S⁻¹ ≤ ρ/Q → B*L*F ≤ S →
      (K*(4/|b-a|)^t*4^t)*C^t ≤ S →
      0 < P → J.Nonempty → U.Nonempty →
      (∀ p ∈ U, ∀ i, |p i| ≤ 1) → FiniteSeparatedAt δ U →
      NormalizedFiniteBallBound δ t K U →
      (projectionCells δ a U).card ≤ P → (projectionCells δ b U).card ≤ P →
      (P:ℝ)^2 ≤ L*(U.card:ℝ) →
      (∀ j ∈ J, projectionRatio a b j ≠ 0 ∧ |projectionRatio a b j| ≤ M ∧ |(projectionRatio a b j)⁻¹| ≤ M) →
      (∀ j ∈ J, H j ⊆ U) → (∀ j ∈ J, ρ*(U.card:ℝ) ≤ ((H j).card:ℝ)) →
      (∀ j ∈ J, (projectionCells δ j (H j)).card ≤ P) →
      (∀ u r : ℝ, α ≤ r → r ≤ 1 → scalarBallMass (J.image (projectionRatio a b)) u r ≤
        S*r^(2*κ)*((J.image (projectionRatio a b)).card:ℝ)) →
      Real.log (F*(P:ℝ)) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  classical
  obtain ⟨γ,N0,hγ,hN0,hmain⟩ := coordinate_graph_obstruction hκ hκ1
  refine ⟨γ,N0,hγ,hN0,?_⟩
  intro N hN
  dsimp only
  intro δ σ a b t K C L ρ m q k M P J U H hδ hσ hσ1 hab ha hb hsmall
    hM hMS hασ hm hq hk hC hscale herror ht ht2 hK hL hρ hQ hQS hdensity
    hprojectioncost hregularcost hP hJ hU hUbound hUsep hUreg hpa hpb hlarge hc hHU hHlarge hHp hball hlog
  let α := (1/2:ℝ)^N
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let f := roundedProjectionCoordinates σ a b
  let G := U.image f
  let X := G.image (fun p => p 0)
  let Y := G.image (fun p => p 1)
  let F : ℝ := 5*(2*(m:ℝ)+3)
  let Q := L*F^2
  let B : ℝ := (2*(k:ℝ)+3)*(2*(M:ℝ)+3)*(2*(q:ℝ)+3)
  have hα : 0 < α := by positivity
  have hMR : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hασ' : α ≤ σ := by nlinarith
  have hF : 0 < F := by dsimp [F]; positivity
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨hX,hY,hXupper,_,hXY,hPX,hprod⟩ := rounded_graph_size_bounds
    hδ hσ hab ha hb hsmall U hU hUsep m P hP hL hm hpa hpb hlarge
  have hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → α ≤ |x-y| := by
    intro x hx y hy hne
    exact hασ'.trans (roundedProjectionCoordinates_coordinate_separated hσ U 0 x hx y hy hne)
  have hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → α ≤ |x-y| := by
    intro x hx y hy hne
    exact hασ'.trans (roundedProjectionCoordinates_coordinate_separated hσ U 1 x hx y hy hne)
  have hXd : ∀ x ∈ X, |x| ≤ 1 := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    exact roundedProjectionCoordinates_bound hσ hσ1 ha hb z (hUbound z hz) 0
  have hGregular : NormalizedFiniteBallBound α t S G := by
    have hr := roundedProjectionCoordinates_regular hδ hσ hα hC hab ha hb hscale herror
      hsmall ht0 hK U hUsep hUreg
    intro z r hr0 hr1
    have hh := mul_le_mul_of_nonneg_right hregularcost
      (mul_nonneg (Real.rpow_nonneg (hα.le.trans hr0) t) (Nat.cast_nonneg G.card))
    exact (hr z r hr0 hr1).trans (by simpa only [mul_assoc,G,f,S] using hh)
  have hdense : ∀ j ∈ J, S⁻¹*(X.card:ℝ)*(Y.card:ℝ) ≤ ((H j).image f).card := by
    intro j hj
    have hh := rounded_graph_density_bound hδ hσ hab ha hb hsmall U (H j)
      (hHU j hj) hUsep hρ hQpos (hHlarge j hj) hprod
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdensity
      (Nat.cast_nonneg X.card)) (Nat.cast_nonneg Y.card)).trans hh
  have hproj : ∀ j ∈ J,
      ((scalarCells α (((H j).image f).image (cartesianProjection (projectionRatio a b j)))).card:ℝ) ≤ S*(X.card:ℝ) := by
    intro j hj
    have hnorm := projectionRatio_normalizing_bound (projectionRatio_ne_pole (hc j hj).1)
      hMR (hc j hj).2.1
    have hgrid : (1+|(j-a)/(b-j)|)*σ ≤ (k:ℝ)*α := by
      have hcb : 1+|(j-a)/(b-j)| ≤ 1+(M:ℝ) := by
        have hcc := (hc j hj).2.1
        change |(j-a)/(b-j)| ≤ (M:ℝ) at hcc
        linarith
      have hh := mul_le_mul_of_nonneg_right hcb hσ.le
      exact hh.trans hk
    have hn := (roundedProjectionCoordinates_projection_cells hα hσ hδ hab
      (projectionRatio_ne_pole (hc j hj).1) (H j) k M q hgrid hnorm hq).trans
      (Nat.mul_le_mul_left _ (hHp j hj))
    have hcP : ((scalarCells α (((H j).image f).image
        (cartesianProjection (projectionRatio a b j)))).card:ℝ) ≤ B*(P:ℝ) := by
      have hnR : ((scalarCells α (((H j).image (roundedProjectionCoordinates σ a b)).image
          (cartesianProjection ((j-a)/(b-j))))).card:ℝ) ≤
          (((2*k+3)*(2*M+3)*(2*q+3)*P:ℕ):ℝ) := by exact_mod_cast hn
      simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,B,f,projectionRatio] using hnR
    have hmP := mul_le_mul_of_nonneg_left hPX (show 0 ≤ B by dsimp [B]; positivity)
    have hcost := mul_le_mul_of_nonneg_right hprojectioncost (Nat.cast_nonneg X.card)
    apply hcP.trans
    calc
      _ ≤ B*(L*F*(X.card:ℝ)) := hmP
      _ = (B*L*F)*(X.card:ℝ) := by ring
      _ ≤ S*(X.card:ℝ) := hcost
  have hlogX : Real.log (X.card:ℝ) ≤ (1-κ)*(N:ℝ)*Real.log 2 :=
    (Real.log_le_log (Nat.cast_pos.mpr hX.card_pos) hXupper).trans hlog
  apply hmain N hN M hM hMS Q hQ hQS t J (projectionRatio a b) G (fun j => (H j).image f)
    ht ht2 hJ (hU.image f) hXY hXd hXsep hYsep
  · intro j hj
    exact scalar_dilation_separated (by positivity : (0:ℝ) < M) hασ
      (hc j hj).1 (hc j hj).2.2 Y
      (roundedProjectionCoordinates_coordinate_separated hσ U 1)
  · exact hc
  · intro j hj
    exact Finset.image_subset_image (hHU j hj)
  · exact hdense
  · exact hproj
  · exact hGregular
  · exact hball
  · exact hlogX

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionRatioRegularity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original direction-set ball counts survive the actual fractional-linear
coefficient map, with explicit cardinality and separation losses. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem projectionRatio_ball_bound {δ α s K C A a b : ℝ}
    (hα : 0 < α) (hs : 0 ≤ s) (hK : 1 ≤ K) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hab : b ≠ a) (hb : |b| ≤ 1) (hscale : δ ≤ C*α) (hsep : 8/|b-a| ≤ C)
    (I J : Finset ℝ) (hJI : J ⊆ I) (hJavoid : ∀ y ∈ J, y ≠ b)
    (hIbound : ∀ y ∈ I, |y| ≤ 1) (hsize : (I.card:ℝ) ≤ A*(J.card:ℝ))
    (hball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ K*r^s*(I.card:ℝ)) :
    ∀ u r : ℝ, α ≤ r → scalarBallMass (J.image (projectionRatio a b)) u r ≤
      (A*K*C^s)*r^s*((J.image (projectionRatio a b)).card:ℝ) := by
  classical
  let f := projectionRatio a b
  have hinj : Set.InjOn f (J:Set ℝ) := (projectionRatio_injOn hab).mono hJavoid
  have hcard : (J.image f).card = J.card := Finset.card_image_of_injOn hinj
  intro u r hr
  have hr0 : 0 < r := hα.trans_le hr
  let F := (J.image f).filter fun v => |v-u| ≤ r
  by_cases hF : F.Nonempty
  · obtain ⟨v,hv⟩ := hF
    obtain ⟨hv,hvu⟩ := Finset.mem_filter.mp hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    have hsub : F ⊆ (I.filter fun z => |z-y| ≤ C*r).image f := by
      intro w hw
      obtain ⟨hw,hwu⟩ := Finset.mem_filter.mp hw
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
      refine Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hJI hz,?_⟩,rfl⟩
      have hd : |f z-f y| ≤ 2*r := by
        have hh := abs_sub_le (f z) u (f y)
        rw [abs_sub_comm u (f y)] at hh
        linarith
      have hi := projectionRatio_inverse_bound hab (hJavoid z hz) (hJavoid y hy)
        hb (hIbound z (hJI hz)) (hIbound y (hJI hy))
      have hL : 0 ≤ 4/|b-a| := by positivity
      have hm := mul_le_mul_of_nonneg_left hd hL
      have hCr := mul_le_mul_of_nonneg_right hsep hr0.le
      change |z-y| ≤ C*r
      change |z-y| ≤ (4/|b-a|)*|f z-f y| at hi
      calc
        _ ≤ (4/|b-a|)*(2*r) := hi.trans hm
        _ = (8/|b-a|)*r := by ring
        _ ≤ C*r := hCr
    have hc : (F.card:ℝ) ≤ scalarBallMass I y (C*r) := by
      change (F.card:ℝ) ≤ ((I.filter fun z => |z-y| ≤ C*r).card:ℝ)
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    have hdr : δ ≤ C*r := hscale.trans (mul_le_mul_of_nonneg_left hr hC)
    have hbound := scalar_ball_bound_all_radii hK hs I hball y (C*r) hdr
    have hm := mul_le_mul_of_nonneg_left hsize (show 0 ≤ K*(C*r)^s by positivity)
    rw [Real.mul_rpow hC hr0.le] at hbound hm
    change (F.card:ℝ) ≤ _
    rw [hcard]
    calc
      _ ≤ scalarBallMass I y (C*r) := hc
      _ ≤ K*(C^s*r^s)*(I.card:ℝ) := hbound
      _ ≤ K*(C^s*r^s)*(A*(J.card:ℝ)) := hm
      _ = _ := by ring
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card:ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_PlanarGraphBudgetApplication
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the original planar obstruction with one polynomial budget.
All coordinate, density and directional costs are now discharged. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem planar_graph_budget_application {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ γ : ℝ, ∃ N0 : ℕ, 0 < γ ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let α := (1/2:ℝ)^N
      let S := Real.exp (γ*(N:ℝ)*Real.log 2)
      ∀ (δ W ρ a b t : ℝ) (M P : ℕ)
        (I J : Finset ℝ) (U : Finset (Space 2)) (H : ℝ → Finset (Space 2)),
      0 < δ → δ ≤ 1 → 1 ≤ W → 0 < ρ → ρ⁻¹ ≤ W → 1 ≤ M →
      α = δ/(64*(M:ℝ)^2) → 4000000*W^5*(M:ℝ)^6 ≤ S →
      b ≠ a → |a| ≤ 1 → |b| ≤ 1 → 4/(M:ℝ) ≤ |b-a| →
      2*κ ≤ t → t ≤ 2 → 0 < P → J.Nonempty → U.Nonempty →
      (∀ p ∈ U, ∀ i, |p i| ≤ 1) → FiniteSeparatedAt δ U →
      NormalizedFiniteBallBound δ t W U →
      (projectionCells δ a U).card ≤ P → (projectionCells δ b U).card ≤ P →
      (P:ℝ)^2 ≤ W*(U.card:ℝ) →
      J ⊆ I → (I.card:ℝ) ≤ W*(J.card:ℝ) → (∀ i ∈ I, |i| ≤ 1) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ W*r^(2*κ)*(I.card:ℝ)) →
      (∀ j ∈ J, 4/(M:ℝ) ≤ |j-a| ∧ 4/(M:ℝ) ≤ |j-b|) →
      (∀ j ∈ J, H j ⊆ U) → (∀ j ∈ J, ρ*(U.card:ℝ) ≤ ((H j).card:ℝ)) →
      (∀ j ∈ J, (projectionCells δ j (H j)).card ≤ P) →
      Real.log (655*(M:ℝ)*(P:ℝ)) ≤ (1-κ)*(N:ℝ)*Real.log 2 → False := by
  classical
  obtain ⟨γ,N0,hγ,hN0,hmain⟩ := rounded_planar_obstruction hκ hκ1
  refine ⟨γ,N0,hγ,hN0,?_⟩
  intro N hN
  dsimp only
  intro δ W ρ a b t M P I J U H hδ hδ1 hW hρ hρW hM hcompat hbudget
    hab ha hb hgap ht ht2 hP hJ hU hUbound hUsep hUreg hpa hpb hlarge
    hJI hIJ hIbound hIball hJsep hHU hHsize hHproj hlog
  let α := (1/2:ℝ)^N
  let S := Real.exp (γ*(N:ℝ)*Real.log 2)
  let MR : ℝ := M
  let σ := δ/(64*MR)
  let C := 128*MR^2
  let m : ℕ := 64*M
  let q : ℕ := 64*M^2
  let k : ℕ := 2*M^2
  let F : ℝ := 5*(2*(m:ℝ)+3)
  let Q := W*F^2
  let B : ℝ := (2*(k:ℝ)+3)*(2*MR+3)*(2*(q:ℝ)+3)
  have hMR : 1 ≤ MR := by
    change (1:ℝ) ≤ (M:ℝ)
    exact_mod_cast hM
  have hMRpos : 0 < MR := lt_of_lt_of_le zero_lt_one hMR
  have hα : 0 < α := by positivity
  have hS : 0 < S := Real.exp_pos _
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hmR : (m:ℝ) = 64*MR := by dsimp [m,MR]; push_cast; rfl
  have hqR : (q:ℝ) = 64*MR^2 := by dsimp [q,MR]; push_cast; rfl
  have hkR : (k:ℝ) = 2*MR^2 := by dsimp [k,MR]; push_cast; rfl
  have hFform : F = 5*(2*(64*MR)+3) := by dsimp [F]; rw [hmR]
  have hBform : B = (2*(2*MR^2)+3)*(2*MR+3)*(2*(64*MR^2)+3) := by
    dsimp [B]; rw [hkR,hqR]
  obtain ⟨hσ,hσ1,_,hs,hδσ,hδα,hC,hsmall,hscale,herror⟩ :=
    planar_grid_scale_bounds hδ hδ1 hMR hab ha hb hgap
  rw [← hcompat] at hs hδα hscale herror
  change σ = MR*α at hs
  have hFpos : 0 < F := by dsimp [F]; positivity
  have hF1 : 1 ≤ F := by
    dsimp [F]
    nlinarith only [Nat.cast_nonneg (α := ℝ) m]
  have hQ1 : 1 ≤ Q := by
    have hF2 : 1 ≤ F^2 := by nlinarith only [hF1]
    dsimp [Q]
    nlinarith only [hW,hF2]
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hbasepos : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hbase2 : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith only [ha,hb])
  have hbase1 : 1 ≤ 4/|b-a| := (le_div_iff₀ hbasepos).2 (by linarith only [hbase2])
  have hbaseM : 4/|b-a| ≤ MR := by
    apply (div_le_iff₀ hbasepos).2
    have hh := (div_le_iff₀ hMRpos).1 hgap
    simpa only [mul_comm] using hh
  obtain ⟨hFbound,hQbound,hBbound,hRbound⟩ := planar_grid_polynomial_costs
    hMR hW0 hW0 hbase1 hbaseM (by linarith only [ht,hκ] : 0 ≤ t) ht2
  rw [← hFform] at hFbound hQbound hBbound
  rw [← hBform] at hBbound
  obtain ⟨hMb,hQb,hBb,hRb,hDb,hρb⟩ := planar_common_budget hW hMR
  have hMS : MR ≤ S := hMb.trans hbudget
  have hQS : Q ≤ S := hQbound.trans (hQb.trans hbudget)
  have hBC : B*W*F ≤ S := hBbound.trans (hBb.trans hbudget)
  have hRC : (W*(4/|b-a|)^t*4^t)*C^t ≤ S := hRbound.trans (hRb.trans hbudget)
  have hQρ : Q/ρ ≤ S := by
    have hh := mul_le_mul hQbound hρW (inv_nonneg.mpr hρ.le) (by positivity)
    have he : (429025*W*MR^2)*W = 429025*W^2*MR^2 := by ring
    rw [he] at hh
    have hstep : Q/ρ ≤ 429025*W^2*MR^2 := by simpa only [div_eq_mul_inv] using hh
    exact hstep.trans (hρb.trans hbudget)
  have hden : S⁻¹ ≤ ρ/Q := by
    apply (le_div_iff₀ hQpos).2
    have hh : Q ≤ S*ρ := (div_le_iff₀ hρ).1 hQρ
    have hi := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hS.le)
    have he : S⁻¹*(S*ρ) = ρ := by field_simp
    rw [he] at hi
    simpa only [mul_comm] using hi
  have hc : ∀ j ∈ J, projectionRatio a b j ≠ 0 ∧ |projectionRatio a b j| ≤ MR ∧
      |(projectionRatio a b j)⁻¹| ≤ MR := by
    intro j hj
    have hr : 0 < 4/MR := by positivity
    have hby : 4/MR ≤ |b-j| := by simpa only [abs_sub_comm] using (hJsep j hj).2
    obtain ⟨h0,h1,h2⟩ := planar_projection_ratio_bound hr ha hb (hIbound j (hJI hj))
      (hJsep j hj).1 hby
    have hh : 2/(4/MR) ≤ MR := by
      have he : 2/(4/MR) = MR/2 := by field_simp; norm_num
      rw [he]
      linarith only [hMR]
    exact ⟨h0,h1.trans hh,h2.trans hh⟩
  have hdirscale : δ ≤ (64*MR^2)*α := hδα.le
  have hdirsep : 8/|b-a| ≤ 64*MR^2 := by
    have he : 8/|b-a| = 2*(4/|b-a|) := by ring
    rw [he]
    nlinarith only [hbaseM,hMR]
  have hdircost : (W*W)*(64*MR^2)^(2*κ) ≤ S := by
    have hd := planar_direction_polynomial_cost hMR hW0 hW0 (by linarith only [hκ1] : 2*κ ≤ 2)
    calc
      _ ≤ 4096*W*W*MR^4 := hd
      _ = 4096*W^2*MR^4 := by ring
      _ ≤ _ := hDb.trans hbudget
  have hball : ∀ u r : ℝ, α ≤ r → r ≤ 1 →
      scalarBallMass (J.image (projectionRatio a b)) u r ≤ S*r^(2*κ)*((J.image (projectionRatio a b)).card:ℝ) := by
    intro u r hr _
    have hh := projectionRatio_ball_bound hα (by linarith only [hκ] : 0 ≤ 2*κ) hW
      (by positivity : 0 ≤ 64*MR^2) hW0 hab hb hdirscale hdirsep I J hJI
      (fun j hj => projectionRatio_ne_pole (hc j hj).1) hIbound hIJ hIball u r hr
    have hm := mul_le_mul_of_nonneg_right hdircost
      (mul_nonneg (Real.rpow_nonneg (hα.le.trans hr) (2*κ))
        (Nat.cast_nonneg (α := ℝ) (J.image (projectionRatio a b)).card))
    exact hh.trans (by simpa only [mul_assoc] using hm)
  have hlogF : Real.log (F*(P:ℝ)) ≤ (1-κ)*(N:ℝ)*Real.log 2 := by
    have hp : 0 < (P:ℝ) := Nat.cast_pos.mpr hP
    have hh := Real.log_le_log (mul_pos hFpos hp) (mul_le_mul_of_nonneg_right hFbound hp.le)
    exact hh.trans hlog
  apply hmain N hN δ σ a b t W C W ρ m q k M P J U H hδ hσ hσ1 hab ha hb hsmall hM hMS
  · change α*MR ≤ σ
    rw [hs,mul_comm]
  · rw [hmR]
    exact hδσ.le
  · rw [hqR]
    exact hδα.le
  · change (1+MR)*σ ≤ (k:ℝ)*α
    rw [hs,hkR]
    have hh : (1+MR)*MR ≤ 2*MR^2 := by nlinarith only [hMR]
    have hm := mul_le_mul_of_nonneg_right hh hα.le
    nlinarith only [hm]
  · exact hC
  · exact hscale
  · exact herror
  · exact ht
  · exact ht2
  · exact hW
  · exact hW0
  · exact hρ.le
  · exact hQ1
  · exact hQS
  · exact hden
  · exact hBC
  · exact hRC
  · exact hP
  · exact hJ
  · exact hU
  · exact hUbound
  · exact hUsep
  · exact hUreg
  · exact hpa
  · exact hpb
  · exact hlarge
  · exact hc
  · exact hHU
  · exact hHsize
  · exact hHproj
  · exact hball
  · exact hlogF

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RegularSmallProjections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict small-projection obstruction for an actual regular planar set
and a nonconcentrated family of directions, with all weak losses chosen. -/
namespace Falconer

private theorem base_radius_identity (l : ℕ) :
    4/(2:ℝ)^(l+2) = (1/2:ℝ)^l := by
  rw [pow_add]
  norm_num
  rw [div_pow,one_pow]
  field_simp

 theorem regular_small_projection_obstruction {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ n0 : ℕ, 0 < ε ∧ 0 < n0 ∧ ∀ n : ℕ, n0 ≤ n →
      let δ := (1/2:ℝ)^n
      let W := Real.exp (ε*(n:ℝ)*Real.log 2)
      ∀ (t : ℝ) (I : Finset ℝ) (U : Finset (Space 2))
        (A : ℝ → Finset (Space 2)) (P : ℕ),
      2*κ ≤ t → t ≤ 2 → I.Nonempty → U.Nonempty → 0 < P →
      (∀ i ∈ I, |i| ≤ 1) → (∀ p ∈ U, ∀ i, |p i| ≤ 1) →
      FiniteSeparatedAt δ U → NormalizedFiniteBallBound δ t W U →
      (P:ℝ)^2 ≤ W*(U.card:ℝ) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass I u r ≤ W*r^(2*κ)*(I.card:ℝ)) →
      (∀ i ∈ I, A i ⊆ U ∧ W⁻¹*(U.card:ℝ) ≤ ((A i).card:ℝ) ∧
        (projectionCells δ i (A i)).card ≤ P) →
      Real.log (P:ℝ) ≤ (1-4*κ)*(n:ℝ)*Real.log 2 → False := by
  obtain ⟨γ,Nmin,hγ,_,hmain⟩ := planar_graph_budget_application hκ hκ1
  obtain ⟨ε,n0,hε,hn0,hparameters⟩ := planar_weak_parameters hγ hκ hκ1 Nmin
  refine ⟨ε,n0,hε,hn0,?_⟩
  intro n hn
  dsimp only
  intro t I U A P ht ht2 hI hU hP hIbound hUbound hUsep hUreg hlarge hIball hA hPlog
  let δ := (1/2:ℝ)^n
  let W := Real.exp (ε*(n:ℝ)*Real.log 2)
  let ρ := W⁻¹
  let Z := 64*W^6
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨l,_,hN,hW,_,hr,hr1,hδr,hselect,hbudget,hlog⟩ := hparameters n hn
  let r := (1/2:ℝ)^l
  let M : ℕ := 2^(l+2)
  let N := n+2*l+10
  obtain ⟨hρ,hρ1,hZ,hWZ,hKZ,hAZ,hρnew,hρnewZ⟩ := common_projection_losses hW
  have hballSelect : ∀ z : ℝ, scalarBallMass I z r ≤ (ρ^6/128)*(I.card:ℝ) := by
    intro z
    have hh := mul_le_mul_of_nonneg_right hselect (Nat.cast_nonneg I.card)
    exact (hIball z r hδr hr1).trans (by simpa only [mul_assoc,r,ρ,W] using hh)
  obtain ⟨a,ha,b,hb,hab,hba,J,hJI,hJ,hJsize,hV,hVU,hUV,hVreg,hpa,hpb,htriple⟩ :=
    common_projection_configuration hδ.le (zero_le_one.trans hW) hρ hρ1 hr I U A hI hU
      (fun i hi => (hA i hi).1) (fun i hi => (hA i hi).2.1) hballSelect hUreg P
      (fun i hi => (hA i hi).2.2)
  let V := A a ∩ A b
  have hVregular : NormalizedFiniteBallBound δ t Z V := by
    intro z s hs hs1
    have hh := mul_le_mul_of_nonneg_right hKZ
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hs) t) (Nat.cast_nonneg V.card))
    exact (hVreg z s hs hs1).trans (by simpa only [mul_assoc,V,Z,ρ,W] using hh)
  have hVlarge : (P:ℝ)^2 ≤ Z*(V.card:ℝ) := by
    calc
      _ ≤ W*(U.card:ℝ) := hlarge
      _ ≤ W*((8/ρ^4)*(V.card:ℝ)) := mul_le_mul_of_nonneg_left hUV (zero_le_one.trans hW)
      _ = (W*(8/ρ^4))*(V.card:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKZ (Nat.cast_nonneg V.card)
  have hIJ : (I.card:ℝ) ≤ Z*(J.card:ℝ) := by
    have hh := common_projection_direction_count hρ I J hJsize
    rwa [hAZ] at hh
  have hIballZ : ∀ u s : ℝ, δ ≤ s → s ≤ 1 → scalarBallMass I u s ≤ Z*s^(2*κ)*(I.card:ℝ) := by
    intro u s hs hs1
    have hh := mul_le_mul_of_nonneg_right hWZ
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hs) (2*κ)) (Nat.cast_nonneg I.card))
    exact (hIball u s hs hs1).trans (by simpa only [mul_assoc,Z,W] using hh)
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hMr : 4/(M:ℝ) = r := by
    simpa only [M,Nat.cast_pow,Nat.cast_ofNat,r] using base_radius_identity l
  have hcompat : (1/2:ℝ)^N = δ/(64*(M:ℝ)^2) := by
    simpa only [N,δ,M,Nat.cast_pow,Nat.cast_ofNat] using (planar_analysis_dyadic n l).symm
  have hbudget' : 4000000*Z^5*(M:ℝ)^6 ≤ Real.exp (γ*(N:ℝ)*Real.log 2) := by
    simpa only [Z,M,N,Nat.cast_pow,Nat.cast_ofNat] using hbudget
  have hlog' : Real.log (655*(M:ℝ)*(P:ℝ)) ≤ (1-κ)*(N:ℝ)*Real.log 2 := by
    simpa only [M,N,Nat.cast_pow,Nat.cast_ofNat] using hlog (P:ℝ) (Nat.cast_pos.mpr hP) hPlog
  apply hmain N hN δ Z (ρ^4/8) a b t M P I J V (fun j => V ∩ A j)
    hδ hδ1 hZ hρnew hρnewZ hM hcompat hbudget' hba (hIbound a ha) (hIbound b hb)
  · rw [hMr]
    exact hab.le
  · exact ht
  · exact ht2
  · exact hP
  · exact hJ
  · exact hV
  · intro p hp i
    exact hUbound p (hVU hp) i
  · exact finiteSeparatedAt_subset hVU hUsep
  · exact hVregular
  · exact hpa
  · exact hpb
  · exact hVlarge
  · exact hJI
  · exact hIJ
  · exact hIbound
  · exact hIballZ
  · intro j hj
    rw [hMr]
    exact ⟨(htriple j hj).1.le,(htriple j hj).2.1.le⟩
  · intro j hj
    exact Finset.inter_subset_left
  · intro j hj
    exact (htriple j hj).2.2.1
  · intro j hj
    exact (htriple j hj).2.2.2
  · exact hlog'

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RowTubeBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local parameter-space counts for all tubes through a regular row.
This proves the 2s-dimensional count in the product-structure reduction. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem row_tube_parameter_near {δ r y : ℝ} (hδ : 0 ≤ δ) (hδr : δ ≤ r)
    (hy : |y| ≤ 1) {x l z : Space 2} (hx : x 0 = y)
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) (hlz : dist l z ≤ r) :
    dist x (rowPoint y (lineParameterProjection y z)) ≤ 4*r := by
  rw [row_dist_projection hx]
  have hp := tube_projection_near hδ hl hi
  rw [hx] at hp
  calc
    _ ≤ |x 1-lineParameterProjection y l|+
        |lineParameterProjection y l-lineParameterProjection y z| := abs_sub_le _ _ _
    _ ≤ _ := by linarith [lineParameterProjection_dist hy l z]

theorem row_tube_ball_count {δ y s KP KT M r : ℝ} (hδ : 0 < δ)
    (hδr : δ ≤ r) (hr : 4*r ≤ 1) (hy : |y| ≤ 1) (hKT : 0 ≤ KT) (hM0 : 0 ≤ M)
    {P : Finset (Space 2)} (hrow : ∀ x ∈ P, x 0 = y)
    (hP : NormalizedFiniteBallBound δ s KP P) (T : Space 2 → Finset (Space 2))
    (hchart : ∀ x ∈ P, InBoundedLineChart (T x))
    (hT : ∀ x ∈ P, NormalizedFiniteBallBound δ s KT (T x))
    (hM : ∀ x ∈ P, ((T x).card : ℝ) ≤ M)
    (hinc : ∀ x ∈ P, ∀ l ∈ T x, TubeIncident δ x l) (z : Space 2) :
    (((P.biUnion T).filter fun l => dist l z ≤ r).card : ℝ) ≤
      (KP*(4*r)^s*(P.card : ℝ))*(KT*r^s*M) := by
  classical
  let S := P.filter fun x => dist x (rowPoint y (lineParameterProjection y z)) ≤ 4*r
  let U := fun x => (T x).filter fun l => dist l z ≤ r
  have hsub : (P.biUnion T).filter (fun l => dist l z ≤ r) ⊆ S.biUnion U := by
    intro l hl
    obtain ⟨hlP,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨x,hx,hxl⟩ := Finset.mem_biUnion.mp hlP
    refine Finset.mem_biUnion.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,
      Finset.mem_filter.mpr ⟨hxl,hlr⟩⟩
    exact row_tube_parameter_near hδ.le hδr hy (hrow x hx)
      (hchart x hx l hxl).1 (hinc x hx l hxl) hlr
  have hr0 : 0 < r := hδ.trans_le hδr
  have hc : (S.card : ℝ) ≤ KP*(4*r)^s*(P.card : ℝ) :=
    hP _ (4*r) (by linarith) hr
  calc
    _ ≤ ((S.biUnion U).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ x ∈ S, ((U x).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, KT*r^s*M := by
      apply Finset.sum_le_sum
      intro x hx
      have hxP := (Finset.mem_filter.mp hx).1
      exact (hT x hxP z r hδr (by linarith)).trans
        (mul_le_mul_of_nonneg_left (hM x hxP)
          (mul_nonneg hKT (Real.rpow_nonneg hr0.le _)))
    _ = (S.card : ℝ)*(KT*r^s*M) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg
      (mul_nonneg hKT (Real.rpow_nonneg hr0.le _)) hM0)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RowRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative 2s-regularity of the union of the tube pencils on one
regular row, as used in the product-structure projection argument. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem row_tube_union_regular {δ y s KP KT m M : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hy : |y| ≤ 1) (hKP : 0 ≤ KP) (hKT : 0 ≤ KT)
    (hm : 0 < m) (hM : 0 ≤ M)
    {P : Finset (Space 2)} (hsep : FiniteSeparatedAt δ P)
    (hrow : ∀ x ∈ P, x 0 = y) (hP : NormalizedFiniteBallBound δ s KP P)
    (T : Space 2 → Finset (Space 2))
    (hchart : ∀ x ∈ P, InBoundedLineChart (T x))
    (hT : ∀ x ∈ P, NormalizedFiniteBallBound δ s KT (T x))
    (hsize : ∀ x ∈ P, m ≤ ((T x).card : ℝ) ∧ ((T x).card : ℝ) ≤ M)
    (hinc : ∀ x ∈ P, ∀ l ∈ T x, TubeIncident δ x l) :
    NormalizedFiniteBallBound δ (2*s)
      ((4 : ℝ)^(2*s)+25*KP*KT*(M/m)*(4 : ℝ)^s) (P.biUnion T) := by
  classical
  let U := P.biUnion T
  have hmass : (P.card : ℝ)*m ≤ 25*(U.card : ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp
      _ ≤ ∑ x ∈ P, ((T x).card : ℝ) := Finset.sum_le_sum fun x hx => (hsize x hx).1
      _ ≤ _ := row_tube_union_count hδ hsep hrow T hchart hinc
  have hratio : (P.card : ℝ)*M ≤ (25*(M/m))*(U.card : ℝ) := by
    have hb := mul_le_mul_of_nonneg_right hmass (div_nonneg hM hm.le)
    have he : ((P.card : ℝ)*m)*(M/m) = (P.card : ℝ)*M := by field_simp
    rw [he] at hb
    exact hb.trans_eq (by ring)
  let D := 25*KP*KT*(M/m)*(4 : ℝ)^s
  have hD : 0 ≤ D := by dsimp [D]; positivity
  intro z r hδr hr1
  have hr0 : 0 < r := hδ.trans_le hδr
  have hrpow : 0 ≤ r^(2*s) := Real.rpow_nonneg hr0.le _
  by_cases hsmall : 4*r ≤ 1
  · have hb := row_tube_ball_count hδ hδr hsmall hy hKT hM hrow hP T hchart hT
      (fun x hx => (hsize x hx).2) hinc z
    have he : (KP*(4*r)^s*(P.card : ℝ))*(KT*r^s*M) =
        (KP*KT*(4 : ℝ)^s*r^(2*s))*((P.card : ℝ)*M) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr0.le]
      have hp : r^(2*s) = r^s*r^s := by rw [two_mul,Real.rpow_add hr0]
      rw [hp]
      ring
    rw [he] at hb
    have hb' := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ KP*KT*(4 : ℝ)^s*r^(2*s) by positivity)
    have he' : (KP*KT*(4 : ℝ)^s*r^(2*s))*((25*(M/m))*(U.card : ℝ)) =
        D*r^(2*s)*(U.card : ℝ) := by dsimp [D]; ring
    rw [he'] at hb'
    exact (hb.trans hb').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hrpow)
      (Nat.cast_nonneg _))
  · have hlarge : 1 ≤ 4*r := le_of_lt (lt_of_not_ge hsmall)
    have hp : 1 ≤ (4*r)^(2*s) := Real.one_le_rpow hlarge (by positivity)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr0.le] at hp
    have hp' : 1 ≤ ((4 : ℝ)^(2*s)+D)*r^(2*s) :=
      hp.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hrpow)
    calc
      _ ≤ (U.card : ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ ≤ _ := by simpa only [D,U,one_mul,mul_assoc] using
        mul_le_mul_of_nonneg_right hp' (Nat.cast_nonneg U.card)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PopularRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging local counts over rows proves regularity of popular line
parameters. This is the refinement in Orponen--Shmerkin, Appendix A.7. -/
namespace Falconer

theorem familyDegree_restrict_sum {α β : Type*} [DecidableEq β]
    (J : Finset α) (A : α → Finset β) (S : Finset β) :
    (∑ x ∈ S, familyDegree J A x) = ∑ j ∈ J, ((S ∩ A j).card : ℝ) := by
  have hd := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := J) (t := S) (fun j x => x ∈ A j)
  have he : (∑ j ∈ J, (S ∩ A j).card) =
      ∑ x ∈ S, (J.filter fun j => x ∈ A j).card := by
    simpa only [Finset.bipartiteAbove,Finset.bipartiteBelow,Finset.filter_mem_eq_inter] using hd
  unfold familyDegree
  exact_mod_cast he.symm

theorem popular_family_regular {α : Type*} (J : Finset α) (hJ : J.Nonempty)
    (A : α → Finset (Space 2)) {δ s K θ C : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hθ : 0 < θ)
    (hA : ∀ j ∈ J, NormalizedFiniteBallBound δ s K (A j))
    (G : Finset (Space 2)) (hsize : ((J.biUnion A).card : ℝ) ≤ C*(G.card : ℝ))
    (hdegree : ∀ x ∈ G, θ*(J.card : ℝ) ≤ familyDegree J A x) :
    NormalizedFiniteBallBound δ s (K*C/θ) G := by
  have hJpos : 0 < (J.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
  intro z r hdr hr1
  let H := G.filter fun x => dist x z ≤ r
  have hr0 : 0 ≤ r := hδ.trans hdr
  have hb : θ*(J.card : ℝ)*(H.card : ℝ) ≤
      (J.card : ℝ)*(K*r^s*((J.biUnion A).card : ℝ)) := by
    calc
      _ = ∑ _x ∈ H, θ*(J.card : ℝ) := by simp; ring
      _ ≤ ∑ x ∈ H, familyDegree J A x :=
        Finset.sum_le_sum fun x hx => hdegree x (Finset.mem_filter.mp hx).1
      _ = ∑ j ∈ J, ((H ∩ A j).card : ℝ) := familyDegree_restrict_sum J A H
      _ ≤ ∑ j ∈ J, K*r^s*((J.biUnion A).card : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hsub : H ∩ A j ⊆ (A j).filter (fun x => dist x z ≤ r) := by
          intro x hx
          obtain ⟨hxH,hxA⟩ := Finset.mem_inter.mp hx
          exact Finset.mem_filter.mpr ⟨hxA,(Finset.mem_filter.mp hxH).2⟩
        calc
          _ ≤ (((A j).filter fun x => dist x z ≤ r).card : ℝ) :=
            Nat.cast_le.mpr (Finset.card_le_card hsub)
          _ ≤ K*r^s*((A j).card : ℝ) := hA j hj z r hdr hr1
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_biUnion_of_mem A hj)))
            (mul_nonneg hK (Real.rpow_nonneg hr0 _))
      _ = _ := by simp
  have hb' : θ*(H.card : ℝ) ≤ K*r^s*((J.biUnion A).card : ℝ) := by
    apply (mul_le_mul_iff_right₀ hJpos).1
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hc : θ*(H.card : ℝ) ≤ K*C*r^s*(G.card : ℝ) := by
    calc
      _ ≤ K*r^s*((J.biUnion A).card : ℝ) := hb'
      _ ≤ K*r^s*(C*(G.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg hr0 _))
      _ = _ := by ring
  have hd : (H.card : ℝ) ≤ (K*C*r^s*(G.card : ℝ))/θ :=
    (le_div_iff₀ hθ).2 (by simpa only [mul_comm] using hc)
  exact hd.trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonRegularFamily
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common regular parameter set extracted from a family of regular rows.
The loss is explicit and polynomial in the union-to-row cardinality ratio. -/
namespace Falconer

theorem common_regular_family {α : Type*} (J : Finset α) (hJ : J.Nonempty)
    (A : α → Finset (Space 2)) {δ s K m R : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hm : 0 < m) (hR : 0 < R)
    (hsize : ∀ j ∈ J, m ≤ ((A j).card : ℝ))
    (hunion : ((J.biUnion A).card : ℝ) ≤ R*m)
    (hA : ∀ j ∈ J, NormalizedFiniteBallBound δ s K (A j)) :
    ∃ G ⊆ J.biUnion A, m/2 ≤ (G.card : ℝ) ∧
      NormalizedFiniteBallBound δ s (4*R^2*K) G ∧
      m*(J.card : ℝ)/2 ≤ ∑ x ∈ G, familyDegree J A x := by
  obtain ⟨G,hGU,hGcard,hGmass,hdegree⟩ := family_popular_selection J A hJ hm hsize
  have hGpos : 0 < (G.card : ℝ) := (half_pos hm).trans_le hGcard
  have hUpos : 0 < ((J.biUnion A).card : ℝ) :=
    hGpos.trans_le (Nat.cast_le.mpr (Finset.card_le_card hGU))
  have hc : ((J.biUnion A).card : ℝ) ≤ (2*R)*(G.card : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hGcard hR.le]
  have hd (x : Space 2) (hx : x ∈ G) :
      (1/(2*R))*(J.card : ℝ) ≤ familyDegree J A x := by
    have hr : 1/(2*R) ≤ m/(2*((J.biUnion A).card : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2*R) (by positivity : 0 < 2*((J.biUnion A).card : ℝ))).2
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg J.card)
    have he : m/(2*((J.biUnion A).card : ℝ))*(J.card : ℝ) =
        m*(J.card : ℝ)/(2*((J.biUnion A).card : ℝ)) := by ring
    rw [he] at hh
    exact hh.trans (hdegree x hx)
  have hreg := popular_family_regular J hJ A hδ hK (by positivity : 0 < 1/(2*R)) hA G hc hd
  have he : K*(2*R)/(1/(2*R)) = 4*R^2*K := by field_simp; ring
  rw [he] at hreg
  exact ⟨G,hGU,hGcard,hreg,hGmass⟩

theorem popular_family_rows {α : Type*} (J : Finset α) (A : α → Finset (Space 2))
    (G : Finset (Space 2)) (hG : G ⊆ J.biUnion A) {m R : ℝ} (hm : 0 < m) (_hR : 0 ≤ R)
    (hunion : ((J.biUnion A).card : ℝ) ≤ R*m)
    (hmass : m*(J.card : ℝ)/2 ≤ ∑ x ∈ G, familyDegree J A x) :
    ∃ Y ⊆ J, (J.card : ℝ) ≤ 4*R*(Y.card : ℝ) ∧
      ∀ j ∈ Y, m/4 ≤ ((G ∩ A j).card : ℝ) := by
  let w := fun j => ((G ∩ A j).card : ℝ)
  have ht : m*(J.card : ℝ)/2 ≤ ∑ j ∈ J, w j := by
    simpa only [familyDegree_restrict_sum,w] using hmass
  have hb := finite_popular_mass J w (show 0 ≤ m/4 by positivity) ht
    (show (m/4)*(J.card : ℝ) ≤ (m*(J.card : ℝ)/2)/2 by nlinarith)
    (fun j _ => (Nat.cast_le.mpr (Finset.card_le_card
      (show G ∩ A j ⊆ J.biUnion A from fun x hx => hG (Finset.mem_inter.mp hx).1))).trans hunion)
  refine ⟨J.filter (fun j => m/4 ≤ w j),Finset.filter_subset _ _,?_,?_⟩
  · have hb' := hb.2
    have hm' := mul_pos hm (show (0 : ℝ) < 1/4 by norm_num)
    nlinarith
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CommonSmallProjections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common regular parameters with large subsets having small projections.
This is the exact finite configuration produced before the projection theorem
in Orponen--Shmerkin, Appendix A.7. No projection estimate is assumed here. -/
namespace Falconer

theorem common_regular_small_projections {α : Type*} (J : Finset α) (hJ : J.Nonempty)
    (A : α → Finset (Space 2)) (direction : α → ℝ) {δ s K m R : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hm : 0 < m) (hR : 0 < R)
    (hsize : ∀ j ∈ J, m ≤ ((A j).card : ℝ))
    (hunion : ((J.biUnion A).card : ℝ) ≤ R*m)
    (hA : ∀ j ∈ J, NormalizedFiniteBallBound δ s K (A j))
    (M : ℕ) (hproj : ∀ j ∈ J, (projectionCells δ (direction j) (A j)).card ≤ M) :
    ∃ G ⊆ J.biUnion A, G.Nonempty ∧ m/2 ≤ (G.card : ℝ) ∧
      NormalizedFiniteBallBound δ s (4*R^2*K) G ∧
      ∃ Y ⊆ J, Y.Nonempty ∧ (J.card : ℝ) ≤ 4*R*(Y.card : ℝ) ∧
        ∀ j ∈ Y, m/4 ≤ ((G ∩ A j).card : ℝ) ∧
          (projectionCells δ (direction j) (G ∩ A j)).card ≤ M := by
  obtain ⟨G,hGU,hGcard,hGregular,hGmass⟩ := common_regular_family J hJ A hδ hK hm hR
    hsize hunion hA
  obtain ⟨Y,hYJ,hYcard,hYsize⟩ := popular_family_rows J A G hGU hm hR.le hunion hGmass
  have hG : G.Nonempty := Finset.card_pos.mp (by
    have hh := (half_pos hm).trans_le hGcard
    exact_mod_cast hh)
  have hY : Y.Nonempty := by
    apply Finset.card_pos.mp
    by_contra h
    have hz : Y.card = 0 := Nat.eq_zero_of_not_pos h
    rw [hz,Nat.cast_zero,mul_zero] at hYcard
    have hJpos : 0 < (J.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
    linarith
  refine ⟨G,hGU,hG,hGcard,hGregular,Y,hYJ,hY,hYcard,?_⟩
  intro j hj
  exact ⟨hYsize j hj,
    (Finset.card_le_card (projectionCells_mono δ (direction j) Finset.inter_subset_right)).trans
      (hproj j (hYJ hj))⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ProductProjectionReduction
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric product configuration yields a single regular parameter
set and many large subsets with small projections. This is the preparation
for the strict projection gain in Orponen--Shmerkin, Proposition A.7. -/
namespace Falconer

theorem product_projection_reduction (Y : Finset ℝ) (hY : Y.Nonempty)
    (P : ℝ → Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    {δ s KP KT n m M R : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s)
    (hKP : 0 ≤ KP) (hKT : 0 ≤ KT) (hn : 0 < n) (hm : 0 < m)
    (hM : 0 ≤ M) (hR : 0 < R) (NP : ℕ)
    (hrows : ∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt δ (P y) ∧
      NormalizedFiniteBallBound δ s KP (P y) ∧
      n ≤ ((P y).card : ℝ) ∧ (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y)
    (hpencils : ∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound δ s KT (T x) ∧
      m ≤ ((T x).card : ℝ) ∧ ((T x).card : ℝ) ≤ M ∧
      ∀ l ∈ T x, TubeIncident δ x l)
    (hunion : ((Y.biUnion fun y => (P y).biUnion T).card : ℝ) ≤ R*(n*m/25)) :
    let A := fun y => (P y).biUnion T
    let Krow := (4 : ℝ)^(2*s)+25*KP*KT*(M/m)*(4 : ℝ)^s
    ∃ G ⊆ Y.biUnion A, G.Nonempty ∧ (n*m/25)/2 ≤ (G.card : ℝ) ∧
      NormalizedFiniteBallBound δ (2*s) (4*R^2*Krow) G ∧
      ∃ Z ⊆ Y, Z.Nonempty ∧ (Y.card : ℝ) ≤ 4*R*(Z.card : ℝ) ∧
        ∀ y ∈ Z, (n*m/25)/4 ≤ ((G ∩ A y).card : ℝ) ∧
          (projectionCells δ y (G ∩ A y)).card ≤ 7*NP := by
  let A := fun y => (P y).biUnion T
  let Krow := (4 : ℝ)^(2*s)+25*KP*KT*(M/m)*(4 : ℝ)^s
  have hKrow : 0 ≤ Krow := by dsimp [Krow]; positivity
  have hsize (y : ℝ) (hy : y ∈ Y) : n*m/25 ≤ ((A y).card : ℝ) := by
    have hr := hrows y hy
    have hb := row_tube_union_count hδ hr.2.1 hr.2.2.2.2.2 T
      (fun x hx => (hpencils y hy x hx).1)
      (fun x hx => (hpencils y hy x hx).2.2.2.2)
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 25)).2
    calc
      n*m ≤ ((P y).card : ℝ)*m := mul_le_mul_of_nonneg_right hr.2.2.2.1 hm.le
      _ = ∑ _x ∈ P y, m := by simp
      _ ≤ ∑ x ∈ P y, ((T x).card : ℝ) :=
        Finset.sum_le_sum fun x hx => (hpencils y hy x hx).2.2.1
      _ ≤ _ := by simpa only [mul_comm] using hb
  have hregular (y : ℝ) (hy : y ∈ Y) : NormalizedFiniteBallBound δ (2*s) Krow (A y) := by
    have hr := hrows y hy
    exact row_tube_union_regular hδ hs hr.1 hKP hKT hm hM hr.2.1 hr.2.2.2.2.2 hr.2.2.1 T
      (fun x hx => (hpencils y hy x hx).1)
      (fun x hx => (hpencils y hy x hx).2.1)
      (fun x hx => ⟨(hpencils y hy x hx).2.2.1,(hpencils y hy x hx).2.2.2.1⟩)
      (fun x hx => (hpencils y hy x hx).2.2.2.2)
  have hproj (y : ℝ) (hy : y ∈ Y) : (projectionCells δ y (A y)).card ≤ 7*NP := by
    have hr := hrows y hy
    exact (projectionCells_row_count hδ hr.2.2.2.2.2 T
      (fun x hx => (hpencils y hy x hx).1)
      (fun x hx => (hpencils y hy x hx).2.2.2.2)).trans
        (Nat.mul_le_mul_left 7 hr.2.2.2.2.1)
  exact common_regular_small_projections Y hY A id hδ.le hKrow
    (by positivity : 0 < n*m/25) hR hsize hunion hregular (7*NP) hproj

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RegularProductIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict incidence gain on the actual regular product configuration.
The sole analytic ingredient is the proved small-projection obstruction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem regular_product_incidence {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let δ := (1/2:ℝ)^N
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (Y : Finset ℝ) (P : ℝ → Finset (Space 2)) (T : Space 2 → Finset (Space 2))
        (s KP KT KY n m M R : ℝ) (NP : ℕ),
      Y.Nonempty → κ ≤ s → s ≤ 1 → 0 ≤ KP → 0 ≤ KT → 0 ≤ KY →
      0 < n → 0 < m → 0 ≤ M → 0 < R → 0 < NP →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt δ (P y) ∧
        NormalizedFiniteBallBound δ s KP (P y) ∧ n ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (T x) ∧
        NormalizedFiniteBallBound δ s KT (T x) ∧ m ≤ ((T x).card:ℝ) ∧
        ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident δ x l) →
      FiniteSeparatedAt δ (Y.biUnion fun y => (P y).biUnion T) →
      (∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ KY*r^(2*κ)*(Y.card:ℝ)) →
      4*R ≤ W → 4*R*KY ≤ W →
      4*R^2*((4:ℝ)^(2*s)+25*KP*KT*(M/m)*(4:ℝ)^s) ≤ W →
      ((7*NP:ℕ):ℝ)^2 ≤ W*(n*m/50) →
      Real.log ((7*NP:ℕ):ℝ) ≤ (1-4*κ)*(N:ℝ)*Real.log 2 →
      R*(n*m/25) < ((Y.biUnion fun y => (P y).biUnion T).card:ℝ) := by
  obtain ⟨ε,N0,hε,hN0,hmain⟩ := regular_small_projection_obstruction hκ hκ1
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro N hN
  dsimp only
  intro Y P T s KP KT KY n m M R NP hY hs hs1 hKP hKT hKY hn hm hM hR hNP
    hrows hpencils hsep hYball hRcost hYcost hGcost hPcost hlog
  let δ := (1/2:ℝ)^N
  let W := Real.exp (ε*(N:ℝ)*Real.log 2)
  let A := fun y => (P y).biUnion T
  let U := Y.biUnion A
  have hδ : 0 < δ := by positivity
  have hW : 0 < W := Real.exp_pos _
  have hs0 : 0 ≤ s := hκ.le.trans hs
  by_contra hnot
  have hunion : (U.card:ℝ) ≤ R*(n*m/25) := le_of_not_gt hnot
  obtain ⟨G,hGU,hG,hGcard,hGreg,Z,hZY,hZ,hYZ,hcommon⟩ :=
    product_projection_reduction Y hY P T hδ hs0 hKP hKT hn hm hM hR NP hrows hpencils hunion
  have hGupper : (G.card:ℝ) ≤ W*(n*m/100) := by
    calc
      _ ≤ (U.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hGU)
      _ ≤ R*(n*m/25) := hunion
      _ = (4*R)*(n*m/100) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hRcost (by positivity)
  have hmass : W⁻¹*(G.card:ℝ) ≤ n*m/100 := by
    have hh := mul_le_mul_of_nonneg_left hGupper (inv_nonneg.mpr hW.le)
    have he : W⁻¹*(W*(n*m/100)) = n*m/100 := by field_simp
    rwa [he] at hh
  have hGregular : NormalizedFiniteBallBound δ (2*s) W G := by
    intro z r hr hr1
    have hh := mul_le_mul_of_nonneg_right hGcost
      (mul_nonneg (Real.rpow_nonneg (hδ.le.trans hr) (2*s)) (Nat.cast_nonneg G.card))
    exact (hGreg z r hr hr1).trans (by simpa only [mul_assoc,W] using hh)
  have hZball : ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass Z u r ≤ W*r^(2*κ)*(Z.card:ℝ) := by
    intro u r hr hr1
    have hrpow : 0 ≤ r^(2*κ) := Real.rpow_nonneg (hδ.le.trans hr) _
    calc
      _ ≤ scalarBallMass Y u r := scalarBallMass_mono hZY u r
      _ ≤ KY*r^(2*κ)*(Y.card:ℝ) := hYball u r hr hr1
      _ ≤ KY*r^(2*κ)*(4*R*(Z.card:ℝ)) := mul_le_mul_of_nonneg_left hYZ (mul_nonneg hKY hrpow)
      _ = (4*R*KY)*(r^(2*κ)*(Z.card:ℝ)) := by ring
      _ ≤ W*(r^(2*κ)*(Z.card:ℝ)) :=
        mul_le_mul_of_nonneg_right hYcost (mul_nonneg hrpow (Nat.cast_nonneg Z.card))
      _ = _ := by ring
  have hGbounded : ∀ p ∈ G, ∀ i, |p i| ≤ 1 := by
    intro p hp i
    obtain ⟨y,hy,hp⟩ := Finset.mem_biUnion.mp (hGU hp)
    obtain ⟨x,hx,hp⟩ := Finset.mem_biUnion.mp hp
    have hbound := (hpencils y hy x hx).1 p hp
    fin_cases i
    · exact hbound.1
    · exact hbound.2
  apply hmain N hN (2*s) Z G (fun y => G ∩ A y) (7*NP)
    (by linarith only [hs]) (by linarith only [hs1]) hZ hG (by omega)
    (fun z hz => (hrows z (hZY hz)).1) hGbounded (finiteSeparatedAt_subset hGU hsep)
    hGregular
  · have hGc : n*m/50 ≤ (G.card:ℝ) := by convert hGcard using 1; ring
    exact hPcost.trans (mul_le_mul_of_nonneg_left hGc hW.le)
  · exact hZball
  · intro y hy
    refine ⟨Finset.inter_subset_left,?_,(hcommon y hy).2⟩
    exact hmass.trans (by convert (hcommon y hy).1 using 1 <;> first | (with_reducible_and_instances rfl) | ring)
  · exact hlog

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_WideProductIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product incidence for the actual width-three packet geometry. The
rounding and bounded-chart normalization are performed inside the proof;
separation of the original union is not required. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem wide_product_incidence {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let α := (1/2:ℝ)^N
      let δ := 4*α
      let W := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (Y : Finset ℝ) (P : ℝ → Finset (Space 2)) (T : Space 2 → Finset (Space 2))
        (s KP KT KY n m M R : ℝ) (NP : ℕ),
      δ ≤ 1/8 → Y.Nonempty → κ ≤ s → s ≤ 1 → 1 ≤ KP → 1 ≤ KT → 0 ≤ KY →
      0 < n → 0 < m → 0 ≤ M → 0 < R → 0 < NP →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt δ (P y) ∧
        NormalizedFiniteBallBound δ s KP (P y) ∧ n ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
        NormalizedFiniteBallBound δ s KT (T x) ∧ m ≤ ((T x).card:ℝ) ∧
        ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (3*δ) x l) →
      (∀ u r : ℝ, α ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ KY*r^(2*κ)*(Y.card:ℝ)) →
      4*(361^2*R) ≤ W → 4*(361^2*R)*KY ≤ W →
      4*(361^2*R)^2*((4:ℝ)^(2*s)+25*(KP*(4:ℝ)^s)*
        ((361*KT*(10:ℝ)^s)*(4:ℝ)^s)*(M/(m/361))*(4:ℝ)^s) ≤ W →
      ((7*NP:ℕ):ℝ)^2 ≤ W*(n*(m/361)/50) →
      Real.log ((7*NP:ℕ):ℝ) ≤ (1-4*κ)*(N:ℝ)*Real.log 2 →
      R*(n*m/25) < ((Y.biUnion fun y => (P y).biUnion T).card:ℝ) := by
  obtain ⟨ε,N0,hε,hN0,hmain⟩ := regular_product_incidence hκ hκ1
  refine ⟨ε,N0,hε,hN0,?_⟩
  intro N hN
  dsimp only
  intro Y P T s KP KT KY n m M R NP hsmall hY hs hs1 hKP hKT hKY hn hm hM hR hNP
    hrows hpencils hYball hRc hYc hGc hPc hlog
  let α := (1/2:ℝ)^N
  let δ := 4*α
  let Q := fun y => (P y).image verticalQuarter
  let U := normalizedRowPencils δ T
  let F := Y.biUnion P
  have hδ : 0 < δ := by dsimp [δ,α]; positivity
  have hscale : δ/4 = α := by dsimp [δ]; ring
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hQrows : ∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt α (Q y) ∧
      NormalizedFiniteBallBound α s (KP*(4:ℝ)^s) (Q y) ∧ n ≤ ((Q y).card:ℝ) ∧
      (Q y).card ≤ NP ∧ ∀ x ∈ Q y, x 0 = y := by
    intro y hy
    obtain ⟨hy1,hsep,hreg,hlo,hup,hrow⟩ := hrows y hy
    refine ⟨hy1,?_,?_,?_,?_,?_⟩
    · simpa only [hscale,Q] using verticalQuarter_row_separated (δ := δ) (P y) hrow hsep
    · simpa only [hscale,Q] using verticalQuarter_row_regular hδ hs0 hKP (P y) hrow hreg
    · simpa only [Q,Finset.card_image_of_injective _ verticalQuarter_injective] using hlo
    · simpa only [Q,Finset.card_image_of_injective _ verticalQuarter_injective] using hup
    · intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact hrow p hp
  have hUpencils : ∀ y ∈ Y, ∀ x ∈ Q y, InBoundedLineChart (U x) ∧
      NormalizedFiniteBallBound α s ((361*KT*(10:ℝ)^s)*(4:ℝ)^s) (U x) ∧
      m/361 ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
      ∀ l ∈ U x, TubeIncident α x l := by
    intro y hy x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    have hp0 : |p 0| ≤ 1 := by rw [(hrows y hy).2.2.2.2.2 p hp]; exact (hrows y hy).1
    obtain ⟨hchart,hsep,hreg,hlo,hup,hinc⟩ := hpencils y hy p hp
    simp only [U,normalizedRowPencils,verticalFour_verticalQuarter]
    refine ⟨normalizedPencil_chart hδ hsmall p (T p) hp0 hchart hinc,?_,?_,?_,?_⟩
    · simpa only [hscale] using normalizedPencil_regular hδ hs0 hKT p (T p) hp0 hsep hchart hinc hreg
    · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 361)).2
      have hh := hlo.trans (normalizedPencil_card_lower hδ p (T p) hp0 hsep
        (fun l hl => ⟨(hchart l hl).1,hinc l hl⟩))
      simpa only [mul_comm] using hh
    · exact (Nat.cast_le.mpr (normalizedPencil_card_upper δ p (T p))).trans hup
    · simpa only [hscale] using normalizedPencil_incident hδ p (T p)
  have hF0 : ∀ p ∈ F, |p 0| ≤ 1 := by
    intro p hp
    obtain ⟨y,hy,hp⟩ := Finset.mem_biUnion.mp hp
    rw [(hrows y hy).2.2.2.2.2 p hp]
    exact (hrows y hy).1
  have hFT : ∀ p ∈ F, ∀ l ∈ T p, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l := by
    intro p hp l hl
    obtain ⟨y,hy,hp⟩ := Finset.mem_biUnion.mp hp
    exact ⟨((hpencils y hy p hp).1 l hl).1,(hpencils y hy p hp).2.2.2.2.2 l hl⟩
  have he : Y.biUnion (fun y => (Q y).biUnion U) =
      (F.image verticalQuarter).biUnion U := by
    simp only [F,Q,Finset.biUnion_image,Finset.biUnion_biUnion]
  have hsep : FiniteSeparatedAt α (Y.biUnion fun y => (Q y).biUnion U) := by
    rw [he]
    simpa only [hscale,U] using normalizedRowPencils_union_separated hδ F T
  have hupper : ((Y.biUnion fun y => (Q y).biUnion U).card:ℝ) ≤
      361*((Y.biUnion fun y => (P y).biUnion T).card:ℝ) := by
    rw [he]
    simpa only [U,F,Finset.biUnion_biUnion] using normalizedRowPencils_union_card hδ F T hF0 hFT
  have hgrowth := hmain N hN Y Q U s (KP*(4:ℝ)^s) ((361*KT*(10:ℝ)^s)*(4:ℝ)^s)
    KY n (m/361) M (361^2*R) NP hY hs hs1 (by positivity) (by positivity) hKY
    hn (by positivity) hM (by positivity) hNP hQrows hUpencils hsep hYball hRc hYc hGc hPc hlog
  nlinarith only [hgrowth,hupper]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_RegularProductParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform weak losses for the regular product incidence estimate. -/
namespace Falconer

 theorem regular_product_parameters {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let x := (N:ℝ)*Real.log 2
      let D := Real.exp (ε*x)
      let R := Real.exp (η*x)
      let W := Real.exp (θ*x)
      1 ≤ D ∧ 1 ≤ R ∧ 4*R ≤ W ∧ 4*R*D ≤ W ∧
        4*R^2*(16+400*D^4) ≤ W ∧ 2450*D^4 ≤ W ∧
        Real.log 7+ε*x ≤ 4*κ*x ∧ 25*D^2 ≤ Real.exp ((η/2)*x) := by
  let η := min θ κ/100
  let ε := η/100
  have hη : 0 < η := by dsimp [η]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hηθ : η ≤ θ/100 := by
    dsimp [η]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hηκ : η ≤ κ/100 := by
    dsimp [η]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hεη : ε = η/100 := rfl
  obtain ⟨N1,hN1,hcost⟩ := scalar_fixed_losses hθ (by norm_num : (0:ℝ) < 1664) (by norm_num : (0:ℝ) < 2450)
  obtain ⟨N2,hN2,hsmall⟩ := scalar_fixed_losses (by positivity : 0 < η/2)
    (by norm_num : (0:ℝ) < 25) (by norm_num : (0:ℝ) < 7)
  refine ⟨ε,η,max N1 N2,hε,hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  let x := (N:ℝ)*Real.log 2
  let D := Real.exp (ε*x)
  let R := Real.exp (η*x)
  let W := Real.exp (θ*x)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hD : 1 ≤ D := Real.one_le_exp_iff.mpr (mul_nonneg hε.le hx)
  have hR : 1 ≤ R := Real.one_le_exp_iff.mpr (mul_nonneg hη.le hx)
  obtain ⟨h1664,h2450⟩ := hcost N ((le_max_left _ _).trans hN)
  obtain ⟨h25,h7⟩ := hsmall N ((le_max_right _ _).trans hN)
  have hpoly : R^2*D^4 ≤ Real.exp ((θ/4)*x) := by
    change (Real.exp (η*x))^2*(Real.exp (ε*x))^4 ≤ _
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : 2*η+4*ε ≤ θ/4 := by rw [hεη]; linarith only [hηθ,hη]
    have hm := mul_le_mul_of_nonneg_right hh hx
    nlinarith only [hm]
  have hbase : 1664*R^2*D^4 ≤ W := by
    calc
      _ = 1664*(R^2*D^4) := by ring
      _ ≤ 1664*Real.exp ((θ/4)*x) := mul_le_mul_of_nonneg_left hpoly (by norm_num)
      _ ≤ W := by simpa only [x,W,mul_assoc] using h1664
  have hR2 : R ≤ R^2 := by nlinarith only [hR]
  have hD4 : 1 ≤ D^4 := one_le_pow₀ hD
  have hD14 : D ≤ D^4 := by simpa only [pow_one] using pow_le_pow_right₀ hD (show 1 ≤ (4:ℕ) by omega)
  have hR2pos : 0 ≤ R^2 := sq_nonneg R
  have hRbase : 4*R ≤ 1664*R^2*D^4 := by
    have hm := mul_le_mul_of_nonneg_left hD4 hR2pos
    nlinarith only [hR2,hR,hR2pos,hm]
  have hRDbase : 4*R*D ≤ 1664*R^2*D^4 := by
    have hm := mul_le_mul hR2 hD14 (zero_le_one.trans hD) hR2pos
    have hp : 0 ≤ R*D := by positivity
    nlinarith only [hm,hp]
  have hG : 4*R^2*(16+400*D^4) ≤ W := by
    have hh : 16+400*D^4 ≤ 416*D^4 := by linarith only [hD4]
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*R^2 by positivity)
    exact hm.trans_eq (by ring) |>.trans hbase
  have hDpoly : D^4 ≤ Real.exp ((θ/4)*x) := by
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ R^2 by nlinarith only [hR]) (pow_nonneg (zero_le_one.trans hD) 4)
    have hmul : D^4 ≤ R^2*D^4 := by simpa only [one_mul] using hm
    exact hmul.trans hpoly
  have hP : 2450*D^4 ≤ W :=
    (mul_le_mul_of_nonneg_left hDpoly (by norm_num)).trans (by
      simpa only [x,W,mul_assoc] using h2450)
  have hsmallD : D^2 ≤ Real.exp ((η/8)*x) := by
    change (Real.exp (ε*x))^2 ≤ _
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh : 2*ε ≤ η/8 := by rw [hεη]; linarith only [hη]
    have hm := mul_le_mul_of_nonneg_right hh hx
    nlinarith only [hm]
  have h25' : 25*D^2 ≤ Real.exp ((η/2)*x) := by
    apply (mul_le_mul_of_nonneg_left hsmallD (by norm_num)).trans
    have he : (η/2/4)*(N:ℝ)*Real.log 2 = (η/8)*x := by dsimp [x]; ring
    have he' : (η/2)*(N:ℝ)*Real.log 2 = (η/2)*x := by dsimp [x]; ring
    rwa [he,he'] at h25
  have h7log : Real.log 7+(η/8)*x ≤ (η/2)*x := by
    have hh := Real.log_le_log (by positivity : (0:ℝ) < 7*Real.exp (((η/2)/4)*(N:ℝ)*Real.log 2)) h7
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp,Real.log_exp] at hh
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [x] <;> ring)
  have hlog : Real.log 7+ε*x ≤ 4*κ*x := by
    have he : ε ≤ κ := by rw [hεη]; linarith only [hηκ,hκ]
    have hh := mul_le_mul_of_nonneg_right hηκ hx
    have he' := mul_le_mul_of_nonneg_right he hx
    nlinarith only [h7log,hh,he',hx,hη,hκ]
  exact ⟨hD,hR,hRbase.trans hbase,hRDbase.trans hbase,hG,hP,hlog,h25'⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_WideProductParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorb the explicit packing and rounding constants of the actual
width-three product configuration into an arbitrarily small power loss. -/
namespace Falconer

theorem wide_product_parameters {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let x := (N:ℝ)*Real.log 2
      let D := Real.exp (ε*x)
      let R := Real.exp (η*x)
      let W := Real.exp (θ*x)
      1 ≤ D ∧ 1 ≤ R ∧ 4*(361^2*R) ≤ W ∧ 4*(361^2*R)*D ≤ W ∧
        (10:ℝ)^22*R^2*D^4 ≤ W ∧ 884450*D^4 ≤ W ∧
        Real.log 7+ε*x ≤ 4*κ*x ∧ 25*D^2 ≤ Real.exp ((η/2)*x) := by
  obtain ⟨ε,η,N1,hε,hη,hN1,hbase⟩ := regular_product_parameters
    (by positivity : 0 < θ/4) hκ
  obtain ⟨N2,hN2,hlarge⟩ := scalar_fixed_losses hθ
    (by norm_num : (0:ℝ) < 10^22) (by norm_num : (0:ℝ) < 1)
  refine ⟨ε,η,max N1 N2,hε,hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  let x := (N:ℝ)*Real.log 2
  let D := Real.exp (ε*x)
  let R := Real.exp (η*x)
  let W0 := Real.exp ((θ/4)*x)
  let W := Real.exp (θ*x)
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  have hW0 : 0 ≤ W0 := (Real.exp_pos _).le
  obtain ⟨hD,hR,hRc,hRD,hGc,hPc,hlog,h25⟩ := hbase N ((le_max_left _ _).trans hN)
  have hfixed : (10:ℝ)^22*W0 ≤ W := by
    simpa only [W0,W,x,mul_assoc] using (hlarge N ((le_max_right _ _).trans hN)).1
  have hRcost : 4*(361^2*R) ≤ W := by
    have hh := mul_le_mul_of_nonneg_left hRc (by norm_num : (0:ℝ) ≤ 361^2)
    have hh' : (361:ℝ)^2*W0 ≤ (10:ℝ)^22*W0 :=
      mul_le_mul_of_nonneg_right (by norm_num) hW0
    exact (show 4*(361^2*R) ≤ (361:ℝ)^2*W0 by nlinarith only [hh]).trans (hh'.trans hfixed)
  have hRDcost : 4*(361^2*R)*D ≤ W := by
    have hh := mul_le_mul_of_nonneg_left hRD (by norm_num : (0:ℝ) ≤ 361^2)
    have hh' : (361:ℝ)^2*W0 ≤ (10:ℝ)^22*W0 :=
      mul_le_mul_of_nonneg_right (by norm_num) hW0
    exact (show 4*(361^2*R)*D ≤ (361:ℝ)^2*W0 by nlinarith only [hh]).trans (hh'.trans hfixed)
  have hpoly : R^2*D^4 ≤ W0 := by
    have hpos : 0 ≤ R^2*D^4 := mul_nonneg (sq_nonneg _) (pow_nonneg hD0 _)
    have hh : R^2*D^4 ≤ 4*R^2*(16+400*D^4) := by
      nlinarith only [hpos,sq_nonneg R]
    exact hh.trans hGc
  have hGcost : (10:ℝ)^22*R^2*D^4 ≤ W := by
    have hh := mul_le_mul_of_nonneg_left hpoly (by norm_num : (0:ℝ) ≤ 10^22)
    exact (show (10:ℝ)^22*R^2*D^4 ≤ (10:ℝ)^22*W0 by nlinarith only [hh]).trans hfixed
  have hDpoly : D^4 ≤ W0 := by nlinarith only [hPc,pow_nonneg hD0 4]
  have hPcost : 884450*D^4 ≤ W := by
    calc
      _ ≤ 884450*W0 := mul_le_mul_of_nonneg_left hDpoly (by norm_num)
      _ ≤ (10:ℝ)^22*W0 := mul_le_mul_of_nonneg_right (by norm_num) hW0
      _ ≤ W := hfixed
  exact ⟨hD,hR,hRcost,hRDcost,hGcost,hPcost,hlog,h25⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_WideProductPower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform power gain after the actual packet and common-row normalization.
Only the individual original pencils need be separated. -/
namespace Falconer

 theorem wide_product_power {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let α := (1/2:ℝ)^N
      let δ := 4*α
      let D := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (s : ℝ) (Y : Finset ℝ) (P : ℝ → Finset (Space 2))
        (T : Space 2 → Finset (Space 2)) (NP : ℕ),
      let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
      let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
      κ ≤ s → s ≤ 1-8*κ → Y.Nonempty → 0 < NP → (NP:ℝ) ≤ U →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt δ (P y) ∧
        NormalizedFiniteBallBound δ s D (P y) ∧ L ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
        NormalizedFiniteBallBound δ s D (T x) ∧ L ≤ ((T x).card:ℝ) ∧
        ((T x).card:ℝ) ≤ U ∧ ∀ l ∈ T x, TubeIncident (3*δ) x l) →
      (∀ u r : ℝ, α ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*(N:ℝ)*Real.log 2) ≤ ((Y.biUnion fun y => (P y).biUnion T).card:ℝ) := by
  obtain ⟨θ,Nmin,hθ,_,hmain⟩ := wide_product_incidence hκ hκ1
  obtain ⟨ε,η,Np,hε,hη,hNp,hparams⟩ := wide_product_parameters hθ hκ
  refine ⟨ε,η/2,max Nmin (max Np 5),hε,by positivity,lt_of_lt_of_le hNp ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro N hN
  dsimp only
  intro s Y P T NP hs hs1 hY hNP hNPupper hrows hpencils hYball
  let x := (N:ℝ)*Real.log 2
  let α := (1/2:ℝ)^N
  let δ := 4*α
  let D := Real.exp (ε*x)
  let R := Real.exp (η*x)
  let W := Real.exp (θ*x)
  let L := Real.exp ((s-ε)*x)
  let U := Real.exp ((s+ε)*x)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hDpos : 0 < D := Real.exp_pos _
  have hLpos : 0 < L := Real.exp_pos _
  have hUpos : 0 < U := Real.exp_pos _
  have hRpos : 0 < R := Real.exp_pos _
  obtain ⟨hD,hR,hRc,hRD,hGc,hPc,hlogc,h25⟩ := hparams N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hUL : U/L = D^2 := by
    change Real.exp ((s+ε)*x)/Real.exp ((s-ε)*x) = (Real.exp (ε*x))^2
    rw [← Real.exp_sub,← Real.exp_nat_mul]
    congr 1
    ring
  have hUeq : U = D^2*L := (div_eq_iff hLpos.ne').1 hUL
  have h4s : (4:ℝ)^s ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
      (show s ≤ 1 by linarith only [hs1,hκ])
    simpa only [Real.rpow_one] using hh
  have h42s : (4:ℝ)^(2*s) ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
      (show 2*s ≤ 2 by linarith only [hs1,hκ])
    norm_num only [Real.rpow_two,Nat.reducePow] at hh
    exact hh
  have h10s : (10:ℝ)^s ≤ 10 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 10)
      (show s ≤ 1 by linarith only [hs1,hκ])
    simpa only [Real.rpow_one] using hh
  have hULwide : U/(L/361) = 361*D^2 := by
    calc
      _ = 361*(U/L) := by field_simp
      _ = _ := by rw [hUL]
  have hrow : (4:ℝ)^(2*s)+25*(D*(4:ℝ)^s)*((361*D*(10:ℝ)^s)*(4:ℝ)^s)*
      (U/(L/361))*(4:ℝ)^s ≤ 16+2085136000*D^4 := by
    rw [hULwide]
    calc
      _ ≤ 16+25*(D*4)*((361*D*10)*4)*(361*D^2)*4 := by
        apply add_le_add h42s
        gcongr
      _ = _ := by ring
  have hD4 : 1 ≤ D^4 := one_le_pow₀ hD
  have hrow' : 16+2085136000*D^4 ≤ (16+2085136000)*D^4 := by linarith only [hD4]
  have hGcost : 4*(361^2*R)^2*((4:ℝ)^(2*s)+25*(D*(4:ℝ)^s)*
      ((361*D*(10:ℝ)^s)*(4:ℝ)^s)*(U/(L/361))*(4:ℝ)^s) ≤ W := by
    calc
      _ ≤ 4*(361^2*R)^2*((16+2085136000)*D^4) :=
        mul_le_mul_of_nonneg_left (hrow.trans hrow') (by positivity)
      _ = (4*361^4*(16+2085136000))*(R^2*D^4) := by ring
      _ ≤ (10:ℝ)^22*(R^2*D^4) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (10:ℝ)^22*R^2*D^4 := by ring
      _ ≤ W := hGc
  have hPupper : ((7*NP:ℕ):ℝ) ≤ 7*U := by
    have hh := mul_le_mul_of_nonneg_left hNPupper (by norm_num : (0:ℝ) ≤ 7)
    simpa only [Nat.cast_mul,Nat.cast_ofNat,U,x,mul_assoc] using hh
  have hPcost : ((7*NP:ℕ):ℝ)^2 ≤ W*(L*(L/361)/50) := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (7*NP)) hPupper 2
    have hm := mul_le_mul_of_nonneg_right hPc (sq_nonneg L)
    calc
      _ ≤ (7*U)^2 := hsq
      _ = (884450*D^4)*L^2/18050 := by rw [hUeq]; ring
      _ ≤ W*L^2/18050 := div_le_div_of_nonneg_right hm (by norm_num)
      _ = _ := by ring
  have hlogNP : Real.log (NP:ℝ) ≤ (s+ε)*x := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr hNP) hNPupper
    simpa only [U,x,Real.log_exp,mul_assoc] using hh
  have hlog : Real.log ((7*NP:ℕ):ℝ) ≤ (1-4*κ)*x := by
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) (Nat.cast_pos.mpr hNP).ne']
    have hsx := mul_le_mul_of_nonneg_right hs1 hx
    nlinarith only [hlogNP,hlogc,hsx]
  have hN5 : 5 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hsmall : δ ≤ 1/8 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) hN5
    norm_num at hh
    dsimp [δ,α]
    linarith only [hh]
  have hgrowth := hmain N ((le_max_left _ _).trans hN) Y P T s D D D L L U R NP
    hsmall hY hs (by linarith only [hs1,hκ]) hD hD hDpos.le hLpos hLpos hUpos.le hRpos hNP
    (by simpa only [D,L,x,mul_assoc] using hrows)
    (by simpa only [D,L,U,x,mul_assoc] using hpencils)
    (by simpa only [D,x,mul_assoc] using hYball)
    (by simpa only [W,x,mul_assoc] using hRc)
    (by simpa only [W,x,mul_assoc] using hRD)
    (by simpa only [W,x,mul_assoc] using hGcost)
    (by simpa only [W,x,mul_assoc] using hPcost)
    (by simpa only [x,mul_assoc] using hlog)
  have hfinal : Real.exp ((2*s+η/2)*x) ≤ R*(L*L/25) := by
    apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity)).1
    have hh := Real.log_le_log (by positivity : 0 < 25*D^2) h25
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
    simp only [D,Real.log_exp] at hh
    change Real.log (Real.exp ((2*s+η/2)*x)) ≤ Real.log (R*(L*L/25))
    rw [Real.log_exp,Real.log_mul hRpos.ne' (by positivity),Real.log_div (by positivity) (by norm_num),
      Real.log_mul hLpos.ne' hLpos.ne']
    simp only [R,L,Real.log_exp]
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith only [hh]
  simpa only [x,mul_assoc] using hfinal.trans hgrowth.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CenteredPacketPower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The product gain applies to the original fine pencils of a coarse
packet. The proof constructs their row pencils by dilation and retains
control of the actual original union. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_product_power_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let Δ := 4*(1/2:ℝ)^N
      let D := Real.exp (ε*(N:ℝ)*Real.log 2)
      ∀ (s c b : ℝ) (Y : Finset ℝ) (P : ℝ → Finset (Space 2))
        (S : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (NP : ℕ),
      let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
      let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
      κ ≤ s → s ≤ 1-8*κ → Y.Nonempty → 0 < NP → (NP:ℝ) ≤ U →
      (∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt Δ (P y) ∧
        NormalizedFiniteBallBound Δ s D (P y) ∧ L ≤ ((P y).card:ℝ) ∧
        (P y).card ≤ NP ∧ ∀ x ∈ P y, x 0 = y) →
      (∀ y ∈ Y, ∀ x ∈ P y, ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-y| ≤ Δ) →
      (∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
        NormalizedFiniteBallBound (Δ^2) s (D/Δ^s) (T p) ∧
        L ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ U ∧
        ∀ l ∈ T p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) →
      (∀ u r : ℝ, (1/2:ℝ)^N ≤ r → r ≤ 1 →
        scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*(N:ℝ)*Real.log 2) ≤ ((S.biUnion T).card:ℝ) := by
  obtain ⟨ε,η,Nmin,hε,hη,hNmin,hmain⟩ := wide_product_power hκ hκ1
  refine ⟨ε,η,max Nmin 5,hε,hη,lt_of_lt_of_le hNmin (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  intro s c b Y P S T NP hs hs1 hY hNP hNPup hrows hrep hT hYball
  let Δ := 4*(1/2:ℝ)^N
  let D := Real.exp (ε*(N:ℝ)*Real.log 2)
  let L := Real.exp ((s-ε)*(N:ℝ)*Real.log 2)
  let U := Real.exp ((s+ε)*(N:ℝ)*Real.log 2)
  let Z := Y.biUnion P
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hN5 : 5 ≤ N := (le_max_right _ _).trans hN
  have hΔ1 : Δ ≤ 1 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) hN5
    norm_num at hh
    dsimp [Δ]
    linarith only [hh]
  have hrepZ : ∀ x ∈ Z, ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
    intro x hx
    obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨p,hp,h1,h0⟩ := hrep y hy x hx
    refine ⟨p,hp,h1,?_⟩
    rwa [(hrows y hy).2.2.2.2.2 x hx]
  obtain ⟨V,hcard,hV⟩ := centered_packet_pencil_lift hΔ hΔ1 Z S T hrepZ hT
  have hVp : ∀ y ∈ Y, ∀ x ∈ P y, InBoundedLineChart (V x) ∧
      FiniteSeparatedAt Δ (V x) ∧ NormalizedFiniteBallBound Δ s D (V x) ∧
      L ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ U ∧
      ∀ l ∈ V x, TubeIncident (3*Δ) x l := by
    intro y hy x hx
    obtain ⟨hc,hs,hr,hl,hu,hi⟩ := hV x (Finset.mem_biUnion.mpr ⟨y,hy,hx⟩)
    have he : (D/Δ^s)*Δ^s = D := div_mul_cancel₀ D (Real.rpow_pos_of_pos hΔ s).ne'
    rw [he] at hr
    exact ⟨hc,hs,hr,hl,hu,hi⟩
  have hgain := hmain N ((le_max_left _ _).trans hN) s Y P V NP hs hs1 hY hNP hNPup
    hrows hVp hYball
  have hunion : Y.biUnion (fun y => (P y).biUnion V) = Z.biUnion V := by
    simp only [Z,Finset.biUnion_biUnion]
  rw [hunion] at hgain
  exact hgain.trans hcard

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.centered_packet_product_power_oai := @OAI.Falconer.centered_packet_product_power_oai
