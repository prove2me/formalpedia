-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_distance_degrees
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:28:09.015347+00:00
-- url     : https://prove2.me/submissions/0f5311a1-bcfa-42c3-849c-e5cd677e61dc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothAngleMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem smoothAngleMask_support (G : Set ℝ) (η : ℝ) (hη : 0 < η) :
    Function.support (smoothAngleMask G η hη) ⊆ thickening (3*η) G := by
  intro x hx
  obtain ⟨a,ha,b,hb,hab⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
  rw [(angleBump η hη).support_normed_eq] at ha
  have hb' : b ∈ thickening (2*η) G := by
    by_contra hn
    exact hb (Set.indicator_of_notMem hn (fun _ : ℝ => (1:ℝ)))
  obtain ⟨z,hz,hbz⟩ := mem_thickening_iff.mp hb'
  apply mem_thickening_iff.mpr
  refine ⟨z,hz,?_⟩
  change dist a 0 < η at ha
  rw [← hab]
  have he : dist (a+b) b = dist a 0 := by simp [dist_eq_norm]
  have hd := dist_triangle (a+b) b z
  rw [he] at hd
  linarith

theorem smoothAngleMask_tsupport (G : Set ℝ) (η : ℝ) (hη : 0 < η) :
    tsupport (smoothAngleMask G η hη) ⊆ thickening (4*η) G := by
  exact (closure_mono (smoothAngleMask_support G η hη)).trans
    ((closure_thickening_subset_cthickening (3*η) G).trans
      (cthickening_subset_thickening' (by positivity) (by linarith) G))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleMaskPeriodicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem thickening_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (r x : ℝ) :
    x+T ∈ thickening r G ↔ x ∈ thickening r G := by
  constructor
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    refine mem_thickening_iff.mpr ⟨z-T,?_,?_⟩
    · exact (hG (z-T)).mp (by simpa using hz)
    · simpa only [Real.dist_eq] using (show |x-(z-T)| < r by
        convert hd using 1; simp only [Real.dist_eq]; congr 1; ring)
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    exact mem_thickening_iff.mpr ⟨z+T,(hG z).mpr hz,by simpa using hd⟩

theorem thickenedIndicator_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) :
    Function.Periodic (thickenedIndicator G η) T := by
  intro x
  classical
  simp only [thickenedIndicator,Set.indicator_apply,thickening_periodic hG]

theorem smoothAngleMask_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) (hη : 0 < η) :
    Function.Periodic (smoothAngleMask G η hη) T := by
  intro x
  unfold smoothAngleMask
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp := thickenedIndicator_periodic hG η (x-t)
  rw [show x+T-t = (x-t)+T by ring,hp]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem DyadicSquare.dist_le (Q : DyadicSquare) (hQ : 0 ≤ Q.side)
    {z w : Plane} (hz : z ∈ Q.carrier) (hw : w ∈ Q.carrier) :
    dist z w ≤ 2 * Q.side := by
  have h0 : |z 0 - w 0| ≤ Q.side := by
    apply abs_le.mpr; constructor <;> linarith [hz.1,hz.2.1,hw.1,hw.2.1]
  have h1 : |z 1 - w 1| ≤ Q.side := by
    apply abs_le.mpr; constructor <;>
      linarith [hz.2.2.1,hz.2.2.2,hw.2.2.1,hw.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq z w
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h0
  have hs1 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [dist_nonneg (x := z) (y := w)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem DyadicSquare.descendant_side_pos (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : List (Bool × Bool)) : 0 < (Q.descendant p).side := by
  induction p generalizing Q with
  | nil => exact hQ
  | cons a p ih => exact ih _ (Q.child_side_pos hQ a.1 a.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem DyadicSquare.descendant_side (Q : DyadicSquare) (p : List (Bool × Bool)) :
    (Q.descendant p).side = Q.side / (2 : ℝ)^p.length := by
  induction p generalizing Q with
  | nil => simp [descendant]
  | cons a p ih =>
    simp only [descendant, ih, child, List.length_cons, pow_succ]
    ring

theorem DyadicSquare.box_measurable (Q : DyadicSquare) : MeasurableSet Q.box :=
  measurableSet_Ico.prod measurableSet_Ico

theorem DyadicSquare.box_area (Q : DyadicSquare) :
    (volume.prod volume) Q.box = ENNReal.ofReal Q.side * ENNReal.ofReal Q.side := by
  simp [box, Measure.prod_prod, Real.volume_Ico]

theorem DyadicSquare.boxes_disjoint (Q : DyadicSquare) (hQ : 0 < Q.side)
    {p q : List (Bool × Bool)} (hlen : p.length = q.length) (hne : p ≠ q) :
    Disjoint (Q.descendant p).box (Q.descendant q).box := by
  apply Set.disjoint_left.mpr
  intro z hp hq
  exact Set.disjoint_left.mp (Q.descendants_disjoint hQ hlen hne)
    ((pairToPlane_mem _ _).mpr hp) ((pairToPlane_mem _ _).mpr hq)

theorem plane_coordinate_dist_le (z x : Plane) (i : Fin 2) :
    |z i - x i| ≤ dist z x := by
  simpa only [Real.dist_eq] using PiLp.dist_apply_le z x i

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_ScaledDyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem DyadicSquare.center_mem (Q : DyadicSquare) (hQ : 0 < Q.side) : Q.center ∈ Q.carrier := by
  simp only [center,carrier,mem_ofPred_eq,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · linarith
  · exact ⟨by linarith,by linarith,by linarith⟩

theorem box_subset_of_meets_scaled_ball (Q : DyadicSquare) (x : Plane) {r w C₀ : ℝ}
    (hside : Q.side = w) (hr : r ≤ C₀*w)
    (hmeet : (Q.carrier ∩ ball x r).Nonempty) :
    Q.box ⊆ Icc (x 0-(C₀+1)*w) (x 0+(C₀+1)*w) ×ˢ
      Icc (x 1-(C₀+1)*w) (x 1+(C₀+1)*w) := by
  obtain ⟨z,hz,hball⟩ := hmeet
  have hx0 := abs_lt.mp ((plane_coordinate_dist_le z x 0).trans_lt hball)
  have hx1 := abs_lt.mp ((plane_coordinate_dist_le z x 1).trans_lt hball)
  intro u hu
  simp only [DyadicSquare.box,mem_prod,mem_Ico] at hu
  simp only [DyadicSquare.carrier,mem_ofPred_eq] at hz
  simp only [mem_prod,mem_Icc]
  rw [hside] at hz hu
  constructor <;> constructor <;>
    linarith [hu.1.1,hu.1.2,hu.2.1,hu.2.2,hz.1,hz.2.1,hz.2.2.1,hz.2.2.2,
      hx0.1,hx0.2,hx1.1,hx1.2]

theorem dyadic_scaled_ball_card_le (Q : DyadicSquare) (hQ : 0 < Q.side)
    (n : ℕ) (x : Plane) {r C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hr : r ≤ C₀*(Q.side/(2:ℝ)^n)) :
    ((cellsMeeting Q n x r).card:ℝ) ≤ 4*(C₀+1)^2 := by
  classical
  let S := cellsMeeting Q n x r
  let w := Q.side/(2:ℝ)^n
  have hw : 0 < w := by dsimp [w]; positivity
  have hlen {path : List (Bool × Bool)} (hp : path ∈ S) : path.length = n :=
    (mem_dyadicPaths n path).mp (Finset.mem_filter.mp hp).1
  have hside {path : List (Bool × Bool)} (hp : path ∈ S) :
      (Q.descendant path).side = w := by rw [Q.descendant_side,hlen hp]
  have hdis : PairwiseDisjoint (S : Set (List (Bool × Bool)))
      (fun p => (Q.descendant p).box) := by
    intro p hp q hq hne
    exact Q.boxes_disjoint hQ ((hlen hp).trans (hlen hq).symm) hne
  have harea : (∑ _path ∈ S, ENNReal.ofReal w*ENNReal.ofReal w) ≤
      ENNReal.ofReal (2*(C₀+1)*w)*ENNReal.ofReal (2*(C₀+1)*w) := by
    calc
      _ = ∑ p ∈ S, (volume.prod volume) (Q.descendant p).box := by
        apply Finset.sum_congr rfl
        intro p hp; rw [DyadicSquare.box_area,hside hp]
      _ = (volume.prod volume) (⋃ p ∈ S, (Q.descendant p).box) :=
        (measure_biUnion_finset hdis (fun p _ => (Q.descendant p).box_measurable)).symm
      _ ≤ (volume.prod volume)
          (Icc (x 0-(C₀+1)*w) (x 0+(C₀+1)*w) ×ˢ Icc (x 1-(C₀+1)*w) (x 1+(C₀+1)*w)) := by
        apply measure_mono
        intro u hu
        obtain ⟨p,hp,hu⟩ := mem_iUnion₂.mp hu
        exact box_subset_of_meets_scaled_ball _ x (hside hp) hr (Finset.mem_filter.mp hp).2 hu
      _ = _ := by
        rw [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
        congr 2 <;> ring
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) harea
  simp only [Finset.sum_const,nsmul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hw.le, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(C₀+1)*w)] at hreal
  have he : (2*(C₀+1)*w)*(2*(C₀+1)*w) = (4*(C₀+1)^2)*(w*w) := by ring
  rw [he,mul_assoc] at hreal
  apply (mul_le_mul_iff_left₀ (mul_pos hw hw)).mp
  simpa only [mul_assoc] using hreal

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.descendant_append (Q : DyadicSquare) (p q : CellPath) :
    Q.descendant (p++q) = (Q.descendant p).descendant q := by
  induction p generalizing Q with
  | nil => rfl
  | cons a p ih => exact ih (Q.child a.1 a.2)

theorem DyadicSquare.descendant_subset_take (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : CellPath) (a : ℕ) : (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  have he := Q.descendant_append (p.take a) (p.drop a)
  rw [List.take_append_drop] at he
  rw [he]
  exact (Q.descendant (p.take a)).descendant_subset (Q.descendant_side_pos hQ _) _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem planeDot_abs_le (v w : Plane) : |planeDot v w| ≤ ‖v‖*‖w‖ := by
  have hv := EuclideanSpace.real_norm_sq_eq v
  have hw := EuclideanSpace.real_norm_sq_eq w
  simp only [Fin.sum_univ_two] at hv hw
  have hsq : (planeDot v w)^2 ≤ ‖v‖^2*‖w‖^2 := by
    rw [hv,hw]
    unfold planeDot
    nlinarith [sq_nonneg (v 0*w 1-v 1*w 0)]
  have hp : 0 ≤ ‖v‖*‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs (planeDot v w),abs_nonneg (planeDot v w)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularTests
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem stripCount_transfer {ι : Type*} (S : Finset ι) (v : ι → Plane)
    {W W' D d : ℝ} (hD : 0 ≤ D) (hv : ∀ i ∈ S, ‖v i‖ ≤ D)
    {ω ω' : Plane} (hd : dist ω ω' ≤ d) (hgap : W'+D*d ≤ W) :
    stripCount S v W' ω' ≤ stripCount S v W ω := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hstrip⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  have he : planeDot (v i) ω = planeDot (v i) ω' + planeDot (v i) (ω-ω') := by
    simp [planeDot]; ring
  have hn : ‖ω-ω'‖ ≤ d := by simpa only [dist_eq_norm] using hd
  calc
    |planeDot (v i) ω| ≤ |planeDot (v i) ω'|+|planeDot (v i) (ω-ω')| := by
      rw [he]; exact abs_add_le _ _
    _ ≤ W'+D*d := add_le_add hstrip ((planeDot_abs_le _ _).trans
      (mul_le_mul (hv i hi) hn (norm_nonneg _) hD))
    _ ≤ W := hgap

theorem norm_quarterTurn (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  simpa using norm_quarterTurn_add 0 v

theorem quarterTurn_sub (v w : Plane) : quarterTurn (v-w) = quarterTurn v-quarterTurn w := by
  ext i
  fin_cases i <;> simp [quarterTurn]
  ring

theorem parallelTestCount_transfer (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) {W W' d : ℝ} {ω ω' : Plane}
    (hd : dist ω ω' ≤ d) (hgap : W'+(10/(2:ℝ)^g)*d ≤ W) :
    parallelTestCount Q ρ g p P W' ω' ≤ parallelTestCount Q ρ g p P W ω := by
  classical
  apply stripCount_transfer _ _ (by positivity : 0 ≤ 10/(2:ℝ)^g) _ _ hgap
  · intro c hc
    have hh : ‖(Q.descendant c).center-(Q.descendant P).center‖ < 10/(2:ℝ)^g := by
      simpa only [mem_ball,dist_eq_norm] using (Finset.mem_filter.mp hc).2.2
    exact hh.le
  · simpa only [dist_eq_norm,← quarterTurn_sub,norm_quarterTurn] using hd

theorem projectionTestCount_transfer (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (p u : ℕ) {P : CellPath} (hP : P.length = p) {W W' d : ℝ} {ω ω' : Plane}
    (hd : dist ω ω' ≤ d) (hgap : W'+(2*Q.side/(2:ℝ)^p)*d ≤ W) :
    projectionTestCount Q ρ p u P W' ω' ≤ projectionTestCount Q ρ p u P W ω := by
  classical
  apply stripCount_transfer _ _ (by positivity : 0 ≤ 2*Q.side/(2:ℝ)^p) _ hd hgap
  intro cc hcc
  have hmem {c : CellPath} (hc : c ∈ projectionTestCells Q ρ p u P) :
      (Q.descendant c).center ∈ (Q.descendant P).carrier := by
    rw [← (Finset.mem_filter.mp hc).2.2]
    exact Q.descendant_subset_take hQ c p ((Q.descendant c).center_mem (Q.descendant_side_pos hQ c))
  have hh := (Q.descendant P).dist_le (Q.descendant_side_pos hQ P).le
    (hmem (Finset.mem_product.mp hcc).1) (hmem (Finset.mem_product.mp hcc).2)
  simpa only [dist_eq_norm,Q.descendant_side,hP,mul_div_assoc] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_FrostmanProfileCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularWidths
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourceAngularWidth_gap (N : ℕ) (sig : ℝ) {J : ℕ} (hJ : 0 < J) (i n : ℕ) :
    sourceAngularWidth N sig J i n-sourceAngularWidth N sig J (i+1) n =
      ((2:ℝ)^N)^(1000*sig)/((J:ℝ)*(2:ℝ)^n) := by
  have hj : (J:ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  simp only [sourceAngularWidth,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem uniform_angular_width_gap {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g n : ℕ, g ≤ n → ∀ i : ℕ,
      sourceAngularWidth N sig J (i+1) n+
        (C/(2:ℝ)^g)*sourceAngularRadius N sig (n-g) ≤
      sourceAngularWidth N sig J i n := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by positivity : 0 < 950*sig) (C*(J:ℝ))
  refine ⟨N₀,?_⟩
  intro N hN g n hgn i
  have hj : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hconst := mul_le_mul_of_nonneg_right (hN₀ N hN)
    (by positivity : 0 ≤ ((2:ℝ)^N)^(50*sig))
  have he : ((2:ℝ)^N)^(950*sig)*((2:ℝ)^N)^(50*sig) =
      ((2:ℝ)^N)^(1000*sig) := by rw [← Real.rpow_add hRp]; congr 1; ring
  rw [he] at hconst
  have hp : (2:ℝ)^g*(2:ℝ)^(n-g) = (2:ℝ)^n := by rw [← pow_add,Nat.add_sub_of_le hgn]
  have hb : (C/(2:ℝ)^g)*sourceAngularRadius N sig (n-g) ≤
      ((2:ℝ)^N)^(1000*sig)/((J:ℝ)*(2:ℝ)^n) := by
    calc
      _ ≤ (C/(2:ℝ)^g)*(1/(2:ℝ)^(n-g)*((2:ℝ)^N)^(50*sig)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (C*(J:ℝ)*((2:ℝ)^N)^(50*sig))/((J:ℝ)*(2:ℝ)^n) := by
        rw [← hp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)
  rw [← sourceAngularWidth_gap N sig hJ i n] at hb
  linarith

theorem uniform_parallel_width_transfer {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare) (ρ : Measure Plane),
      ∀ g p : ℕ, g ≤ p → ∀ (P : CellPath) (i : ℕ) (ω ω' : Plane),
      dist ω ω' ≤ C₀*sourceAngularRadius N sig (p-g) →
      parallelTestCount Q ρ g p P (sourceAngularWidth N sig J (i+1) p) ω' ≤
      parallelTestCount Q ρ g p P (sourceAngularWidth N sig J i p) ω := by
  obtain ⟨N₀,hN₀⟩ := uniform_angular_width_gap hsig hJ (10*C₀) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN Q ρ g p hgp P i ω ω' hdist
  apply parallelTestCount_transfer Q ρ g p P hdist
  convert hN₀ N hN g p hgp i using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem uniform_projection_width_transfer {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 → ∀ (ρ : Measure Plane),
      ∀ p u : ℕ, p ≤ u → ∀ P : CellPath, P.length = p → ∀ (i : ℕ) (ω ω' : Plane),
      dist ω ω' ≤ C₀*sourceAngularRadius N sig (u-p) →
      projectionTestCount Q ρ p u P (sourceAngularWidth N sig J (i+1) u) ω' ≤
      projectionTestCount Q ρ p u P (sourceAngularWidth N sig J i u) ω := by
  obtain ⟨N₀,hN₀⟩ := uniform_angular_width_gap hsig hJ (2*C₀) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ p u hpu P hP i ω ω' hdist
  apply projectionTestCount_transfer Q (by rw [hQ]; norm_num) ρ p u hP hdist
  rw [hQ]
  convert hN₀ N hN p u hpu i using 1
  all_goals try with_reducible_and_instances rfl
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngleMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_support_transfer {G H : Set UnitCircle} {d : ℝ} (hd : 0 < d)
    (htransfer : ∀ (dir : UnitCircle), dir ∈ G → ∀ dir' : UnitCircle, dist (dir:Plane) (dir':Plane) ≤ d → dir' ∈ H) :
    tsupport (sourceTestMask G d hd) ⊆ sourceUnitDirection ⁻¹' H := by
  intro θ hθ
  obtain ⟨φ,hφ,hclose⟩ := mem_thickening_iff.mp (smoothAngleMask_tsupport _ _ _ hθ)
  apply htransfer (sourceUnitDirection φ) hφ (sourceUnitDirection θ)
  change dist (sourceDirection φ) (sourceDirection θ) ≤ d
  have hh := sourceDirection_dist_le φ θ
  rw [dist_comm θ φ] at hclose
  exact hh.trans (by linarith only [hclose, hd])

theorem uniform_parallel_mask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare) (ρ : Measure Plane),
      ∀ g p : ℕ, g ≤ p → ∀ (P : CellPath) (i : ℕ) (T : ℝ),
      tsupport (sourceParallelMask N sig J i Q ρ g p P T) ⊆
        sourceUnitDirection ⁻¹' parallelGoodSet Q ρ g p P (sourceAngularWidth N sig J (i+1) p) T := by
  obtain ⟨N₀,hN₀⟩ := uniform_parallel_width_transfer hsig hJ (C₀ := 1) zero_le_one
  refine ⟨N₀,?_⟩
  intro N hN Q ρ g p hgp P i T
  apply sourceTestMask_support_transfer
  intro dir hdir dir' hdist
  change (parallelTestCount Q ρ g p P (sourceAngularWidth N sig J (i+1) p) (dir':Plane):ℝ) ≤ T
  exact (Nat.cast_le.mpr (hN₀ N hN Q ρ g p hgp P i dir dir' (by simpa using hdist))).trans hdir

theorem uniform_projection_mask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 → ∀ (ρ : Measure Plane),
      ∀ p u : ℕ, p ≤ u → ∀ P : CellPath, P.length = p → ∀ (i : ℕ) (T : ℝ),
      tsupport (sourceProjectionMask N sig J i Q ρ p u P T) ⊆
        sourceUnitDirection ⁻¹' projectionGoodSet Q ρ p u P (sourceAngularWidth N sig J (i+1) u) T := by
  obtain ⟨N₀,hN₀⟩ := uniform_projection_width_transfer hsig hJ (C₀ := 1) zero_le_one
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ p u hpu P hP i T
  apply sourceTestMask_support_transfer
  intro dir hdir dir' hdist
  change (projectionTestCount Q ρ p u P (sourceAngularWidth N sig J (i+1) u) (dir':Plane):ℝ) ≤ T
  exact (Nat.cast_le.mpr (hN₀ N hN Q hQ ρ p u hpu P hP i dir dir' (by simpa using hdist))).trans hdir

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_periodic (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Function.Periodic (sourceTestMask G d hd) (2*Real.pi) := by
  apply smoothAngleMask_periodic
  intro θ
  have he : sourceUnitDirection (θ+2*Real.pi) = sourceUnitDirection θ := by
    apply Subtype.ext
    simp only [sourceUnitDirection,sourceDirection,Real.cos_add_two_pi,Real.sin_add_two_pi]
  simp only [mem_preimage,he]

theorem circleTestMask_comp (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (θ : ℝ) :
    circleTestMask G d hd (sourceUnitDirection θ) = sourceTestMask G d hd θ := by
  unfold circleTestMask
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := (sourceTestMask_periodic G d hd).int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SymbolProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

 theorem iteratedDeriv_tsupport {f : ℝ → ℝ} (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

 theorem product_iteratedDeriv_support {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) {b : ι} (hb : b ∈ S) (j : ℕ) :
    tsupport (iteratedDeriv j (fun x => ∏ i ∈ S, f i x)) ⊆ tsupport (f b) := by
  apply (iteratedDeriv_tsupport j).trans
  have he : (fun x => ∏ i ∈ S, f i x) =
      fun x => f b x * ∏ i ∈ S.erase b, f i x := by
    funext x
    exact (Finset.mul_prod_erase S (fun i => f i x) hb).symm
  rw [he]
  exact tsupport_mul_subset_left

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_NormalizedSymbolFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem normalizedMaskFactor_support (w : ℝ → ℝ) (d : ℝ) (k : ℕ) :
    tsupport (normalizedMaskFactor w d k) ⊆ tsupport w :=
  tsupport_mul_subset_right.trans (iteratedDeriv_tsupport k)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedAngularSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem inheritedMaskProduct_support {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane) {a : ι} (ha : a ∈ S) (j : ℕ) :
    tsupport (iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x)) ⊆
      tsupport (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a)) :=
  (product_iteratedDeriv_support S _ ha j).trans (normalizedMaskFactor_support _ _ _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_InheritedSymbolSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem uniform_descriptorAngleMask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Q : DyadicSquare, Q.side = 1 →
    ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (lam : ℝ) (i : ℕ) (b : PolicyDescriptor),
    ValidDescriptor N b → ∀ (P : CellPath), P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor b) →
    ∀ x ∈ (Q.descendant P).carrier,
    tsupport (descriptorAngleMask Q ρ m N lam sig J i b x) ⊆
      sourceUnitDirection ⁻¹' descriptorGoodSet Q ρ m N lam sig J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_parallel_mask_support hsig hJ
  obtain ⟨N₂,h₂⟩ := uniform_projection_mask_support hsig hJ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ m lam i b hb P hP x hx
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have he : descriptorAngleMask Q ρ m N lam sig J i b x =
      sourceTestMask (descriptorGoodSet Q ρ m N lam sig J i P b)
        (sourceAngularRadius N sig (descriptorLength b)) (sourceAngularRadius_pos _ _ _) := by
    funext θ
    exact (spatialAnchorMask_eq Q hQpos ρ _ _ _ _ hP hx _).trans (circleTestMask_comp _ _ _ _)
  rw [he]
  have hlen := (mem_dyadicPaths _ P).mp (Finset.mem_filter.mp hP).1
  cases b with
  | parallel g p => exact h₁ N ((le_max_left _ _).trans hN) Q ρ g p hb.1 P i _
  | projection p u => exact h₂ N ((le_max_right _ _).trans hN) Q hQ ρ p u hb.1 P hlen i _

 theorem uniform_inheritedMaskProduct_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (x : ι → Plane) (j : ℕ),
    ∀ a ∈ S, ValidDescriptor N (b a) → ∀ P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (b a)),
    x a ∈ (Q.descendant P).carrier →
    tsupport (iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x)) ⊆
      sourceUnitDirection ⁻¹' descriptorGoodSet Q ρ m N lam sig J (i+1) P (b a) := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorAngleMask_support hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k Q hQ ρ m lam i x j a ha hb P hP hx
  exact (inheritedMaskProduct_support S b k Q ρ m N lam sig J i x ha j).trans
    (h₀ N hN Q hQ ρ m lam i (b a) hb P hP (x a) hx)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularLabelEligibility
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem eligible_label_witness {ρ : Measure Plane} {X : Set Plane}
    (hX : MeasurableSet X) {b : Plane → UnitCircle → ℂ} {n j : ℕ}
    (h : AngularLabelEligible ρ X b n j) (G : Plane → UnitCircle → Prop)
    (hG : ∀ ω, ∀ᵐ x ∂ρ.restrict X, b x ω ≠ 0 → G x ω) :
    ∃ ω ∈ tsupport (circleAngularBin n j), ∃ x ∈ X, b x ω ≠ 0 ∧ G x ω := by
  classical
  obtain ⟨ω,hω,hnon⟩ := h
  refine ⟨ω,hω,?_⟩
  by_contra hh
  apply hnon
  filter_upwards [ae_restrict_mem hX, hG ω] with x hx hg
  by_contra hb
  exact hh ⟨x,hx,hb,hg hb⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem dyadic_power_real (N : ℕ) (s : ℝ) :
    ((2 : ℝ)^N)^s = (2 : ℝ)^((N : ℝ)*s) := by
  rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem graphAngularScale_cap_inactive {sig κ c₀ : ℝ}
    (hgap : 10*sig < κ) (hc : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t : ℝ, κ*(N : ℝ) ≤ t →
      graphAngularScale N sig t c₀ = graphUncappedAngularScale N sig t := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (sub_pos.mpr hgap) c₀⁻¹
  refine ⟨N₀,?_⟩
  intro N hN t ht
  apply min_eq_right
  have hb : graphUncappedAngularScale N sig t ≤ ((2 : ℝ)^N)^(sig*10-κ) := by
    simp only [graphUncappedAngularScale, dyadic_power_real, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hp : 0 < ((2 : ℝ)^N)^(κ-10*sig) := by positivity
  have hi := inv_anti₀ (inv_pos.mpr hc) (hN₀ N hN)
  simp only [inv_inv] at hi
  apply hb.trans
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  rw [show sig*10-κ = -(κ-10*sig) by ring, Real.rpow_neg (by positivity)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentBinFamily
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentBinLabels_spec {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    e.1.1 ∈ occupiedAnchorPaths X ρ n ∧ e.1.2 ∈ occupiedAnchorPaths Y ν n ∧
      e.2 ∈ sourceParentActiveLabels N sig t X Y e.1.1 e.1.2 := by
  rcases Finset.mem_sigma.mp he with ⟨hpaths, hbin⟩
  exact ⟨(Finset.mem_product.mp hpaths).1, (Finset.mem_product.mp hpaths).2, hbin⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedGraphEligibility
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem rotated_eligible_label_witness {ρ : Measure Plane} {X : Set Plane}
    (hX : MeasurableSet X) {b : Plane → UnitCircle → ℂ} {n j : ℕ} {axis : ℝ}
    (h : RotatedAngularLabelEligible ρ X b n j axis) (G : Plane → UnitCircle → Prop)
    (hG : ∀ dir, ∀ᵐ x ∂ρ.restrict X, b x dir ≠ 0 → G x dir) :
    ∃ dir, sourceCircleRotate (-axis) dir ∈ tsupport (circleAngularBin n j) ∧
      ∃ x ∈ X, b x dir ≠ 0 ∧ G x dir := by
  obtain ⟨u,hu,x,hx,hb,hgood⟩ := eligible_label_witness hX h
    (fun x u => G x (sourceCircleRotate axis u)) (fun u => hG _)
  refine ⟨sourceCircleRotate axis u,?_,x,hx,hb,hgood⟩
  simpa only [sourceCircleRotate_add,add_neg_cancel,sourceCircleRotate_zero] using hu

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InheritedEligibleWitness
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_inheritedCircleSymbol_good {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset (ι)) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ),
    ∀ e ∈ S, ValidDescriptor N (d e) →
    ∀ A ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (d e)),
    ∀ x ∈ (Q.descendant A).carrier, ∀ dir,
    inheritedCircleSymbol S d k Q ρ m N lam sig J i h x dir ≠ 0 →
      dir ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) A (d e) := by
  obtain ⟨N₀,hgood⟩ := uniform_inheritedMaskProduct_support hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i h e he hd A hA x hx dir hn
  have hz : inheritedMaskProduct S d k Q ρ m N lam sig J i (fun _ => x) (sourceAngle dir) ≠ 0 := by
    intro hzero
    exact hn (by simp only [inheritedCircleSymbol,hzero,Complex.ofReal_zero,mul_zero])
  have hsup := hgood N hN S d k Q hQ ρ m lam i (fun _ => x) 0 e he hd A hA hx
  simp only [iteratedDeriv_zero] at hsup
  have hh := hsup (subset_closure hz)
  simpa only [mem_preimage,sourceUnitDirection_sourceAngle] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeErrorScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem graph_representative_error_small {sig C : ℝ} (hsig : 0 < sig) (_hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p θ ℓ : ℝ, 0 ≤ θ → 0 ≤ ℓ →
      θ ≤ graphUncappedAngularScale N sig (p-a) → ℓ ≤ C*(2:ℝ)^(-a) →
      20*(2:ℝ)^(-p)+θ*ℓ ≤ ((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))/2 := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by positivity : 0 < 20*sig) (2*(20+C))
  refine ⟨N₀,?_⟩
  intro N hN a p θ ℓ _hθ hℓ hθbound hℓbound
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := by positivity
  have h10 : 1 ≤ R^(10*sig) := Real.one_le_rpow hR (by positivity)
  have hpow : R^(30*sig) = R^(20*sig)*R^(10*sig) := by
    rw [← Real.rpow_add hRpos]
    congr 1
    ring
  have he : graphUncappedAngularScale N sig (p-a)*(C*(2:ℝ)^(-a)) = C*(2:ℝ)^(-p)*R^(10*sig) := by
    dsimp [graphUncappedAngularScale,R]
    calc
      _ = C*((2:ℝ)^(-(p-a))*(2:ℝ)^(-a))*((2:ℝ)^N)^(10*sig) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        congr 3
        ring
  have hprod := mul_le_mul hθbound hℓbound hℓ (graphUncappedAngularScale_pos N sig (p-a)).le
  rw [he] at hprod
  have hconst : 2*(20+C) ≤ R^(20*sig) := hN₀ N hN
  have hgain := mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ (2:ℝ)^(-p)*R^(10*sig))
  have hone := mul_le_mul_of_nonneg_left h10 (by positivity : 0 ≤ (2:ℝ)^(-p))
  change _ ≤ ((2:ℝ)^(-p)*R^(30*sig))/2
  rw [hpow]
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphParentDiameter
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_two_parent_diameter (X Y : DyadicSquare) {a : ℝ}
    (hX : 0 < X.side) (hY : 0 < Y.side)
    (hXa : X.side ≤ (2:ℝ)^(-a)) (hYa : Y.side ≤ (2:ℝ)^(-a))
    (hsep : dist X.center Y.center ≤ 2000*(2:ℝ)^(-a))
    {x y : Plane} (hx : x ∈ X.carrier ∪ Y.carrier) (hy : y ∈ X.carrier ∪ Y.carrier) :
    dist x y ≤ 2004*(2:ℝ)^(-a) := by
  have cross {x y : Plane} (hx : x ∈ X.carrier) (hy : y ∈ Y.carrier) :
      dist x y ≤ 2004*(2:ℝ)^(-a) := by
    have h₁ := X.dist_le hX.le hx (X.center_mem hX)
    have h₂ := Y.dist_le hY.le (Y.center_mem hY) hy
    have ht := dist_triangle4 x X.center Y.center y
    linarith
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have ht := X.dist_le hX.le hx hy
    have hp : 0 < (2:ℝ)^(-a) := by positivity
    linarith
  · exact cross hx hy
  · rw [dist_comm]; exact cross hy hx
  · have ht := Y.dist_le hY.le hx hy
    have hp : 0 < (2:ℝ)^(-a) := by positivity
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphRetainedEdges
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem graphChosenRepresentative_spec {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ) :
    GraphSourceRepresentative distance plus axis δ j k (graphChosenRepresentative hδ hcap distance plus axis j k) ∨
      ¬(tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty := by
  classical
  by_cases hs : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty
  · left
    simpa only [graphChosenRepresentative,dite_eq_left hs] using
      Classical.choose_spec (graphSourceRepresentative_exists hδ hcap distance plus axis j k hs)
  · exact Or.inr hs

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ProductRetainedStrip
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem planeDot_eq_inner (u v : Plane) : planeDot u v = inner ℝ u v := by
  simp [planeDot,EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,dotProduct]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ParallelCandidateCount
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem common_strip_relative_bound (z x y : Plane) (u w : UnitCircle)
    {b D d : ℝ} (_ : 0 ≤ D) (hd : 0 ≤ d)
    (hx : |inner ℝ (quarterTurn (u:Plane)) (z-x)| ≤ b)
    (hy : |inner ℝ (quarterTurn (u:Plane)) (z-y)| ≤ b)
    (hxy : dist x y ≤ D) (huw : dist u w ≤ d) :
    |planeDot (x-y) (quarterTurn (w:Plane))| ≤ 2*b+D*d := by
  have he : inner ℝ (quarterTurn (u:Plane)) (x-y) =
      inner ℝ (quarterTurn (u:Plane)) (z-y) - inner ℝ (quarterTurn (u:Plane)) (z-x) := by
    rw [← inner_sub_right]
    congr 1
    abel
  have hbase : |inner ℝ (quarterTurn (u:Plane)) (x-y)| ≤ 2*b := by
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add hy hx).trans_eq (by ring))
  have hnorm : ‖quarterTurn ((w:Plane)-(u:Plane))‖ ≤ d := by
    rw [graph_quarterTurn_norm,← dist_eq_norm,dist_comm]
    exact huw
  have herr : |inner ℝ (quarterTurn ((w:Plane)-(u:Plane))) (x-y)| ≤ D*d := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [← dist_eq_norm]
    exact (mul_le_mul hnorm hxy (dist_nonneg) hd).trans_eq (mul_comm _ _)
  have hw : quarterTurn (w:Plane) = quarterTurn (u:Plane)+quarterTurn ((w:Plane)-(u:Plane)) := by
    rw [quarterTurn_sub]
    abel
  rw [planeDot_eq_inner,real_inner_comm,hw,inner_add_left]
  exact (abs_add_le _ _).trans (add_le_add hbase herr)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceActivityStrip
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem radial_perpendicular_bound (x y : Plane) (u : UnitCircle) {D d : ℝ}
    (hD : dist x y ≤ D) (hd : dist (sourceRadialUnit y x) u ≤ d) :
    |inner ℝ (quarterTurn (u:Plane)) (x-y)| ≤ D*d := by
  have hdp : 0 ≤ d := dist_nonneg.trans hd
  have he : ‖x-y‖ • (sourceRadialUnit y x : Plane) = x-y := by
    by_cases h : x = y
    · simp [h]
    · simp only [sourceRadialUnit,sourceRadialVector,ite_eq_right h,smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)),one_smul]
  have horth : inner ℝ (quarterTurn (sourceRadialUnit y x:Plane)) (x-y) = 0 := by
    calc
      _ = inner ℝ (quarterTurn (sourceRadialUnit y x:Plane))
          (‖x-y‖ • (sourceRadialUnit y x:Plane)) := congrArg _ he.symm
      _ = 0 := by
        rw [real_inner_smul_right]
        have hz : inner ℝ (quarterTurn (sourceRadialUnit y x:Plane)) (sourceRadialUnit y x:Plane) = 0 := by
          simp [quarterTurn,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
          ring
        rw [hz,mul_zero]
  have hn : ‖quarterTurn ((u:Plane)-(sourceRadialUnit y x:Plane))‖ ≤ d := by
    rw [graph_quarterTurn_norm,← dist_eq_norm,dist_comm]
    exact hd
  have hh := abs_real_inner_le_norm (quarterTurn ((u:Plane)-(sourceRadialUnit y x:Plane))) (x-y)
  rw [quarterTurn_sub,inner_sub_left,horth,sub_zero] at hh
  apply hh.trans
  rw [quarterTurn_sub] at hn
  exact (mul_le_mul hn (by simpa only [dist_eq_norm] using hD) (norm_nonneg _) hdp).trans_eq (mul_comm _ _)

theorem active_rotated_bin_direction_bound {θ : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 2*Real.pi)
    (axis : ℝ) (j : ℕ) (e u : UnitCircle)
    (hu : sourceCircleRotate (-axis) u ∈ tsupport (circleAngularBin (angularBinCount θ) j))
    (ha : AngularBinActive (angularBinCount θ) j (sourceCircleRotate (-axis) e) (3*θ)) :
    dist e u ≤ 7*θ := by
  obtain ⟨w,hw,hew⟩ := ha
  have hh := circleAngularBin_scale_diameter hθ hcap j hw hu
  have ht := dist_triangle (sourceCircleRotate (-axis) e) w (sourceCircleRotate (-axis) u)
  rw [sourceCircleRotate_dist] at ht
  linarith

theorem sourceParentBinLabels_activity {N n : ℕ} {sig t : ℝ} {X Y : DyadicSquare}
    {ρ ν : Measure Plane} {e : ParentDistanceBinLabel}
    (he : e ∈ sourceParentBinLabels N sig t X Y ρ ν n) :
    AngularBinActive (angularBinCount (graphUncappedAngularScale N sig t)) e.2
      (sourceCenteredCellDirection X Y (X.descendant e.1.1) (Y.descendant e.1.2))
      (3*graphUncappedAngularScale N sig t) := by
  classical
  obtain ⟨hj,hn⟩ := Finset.mem_sdiff.mp (sourceParentBinLabels_spec he).2.2
  by_contra ha
  exact hn (Finset.mem_filter.mpr ⟨hj,ha⟩)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedParallelCandidates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem rotated_parallel_candidates_le_good_test
    (Q : DyadicSquare) (hQ : 0 < Q.side) (hQs : Q.side ≤ 1) (ρ : Measure Plane)
    (g p : ℕ) (A : CellPath) (hA : A.length = g) (S : Finset CellPath)
    (hS : S ⊆ occupiedAnchorPaths Q ρ p)
    (hparent : ∀ c ∈ S, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier)
    (z : Plane) (u : UnitCircle) {θ b W threshold : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 2*Real.pi)
    (axis : ℝ) (j : ℕ) (hu : sourceCircleRotate (-axis) u ∈ tsupport (circleAngularBin (angularBinCount θ) j))
    (hstrip : ∀ c ∈ S, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ b)
    (hwidth : 2*b+(2/(2:ℝ)^g)*(4*θ) ≤ W) (hthreshold : 0 ≤ threshold)
    (hgood : ∀ c ∈ S, ∃ w, sourceCircleRotate (-axis) w ∈ tsupport (circleAngularBin (angularBinCount θ) j) ∧
      w ∈ parallelGoodSet Q ρ g p c W threshold) :
    (S.card : ℝ) ≤ threshold := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hne
    obtain ⟨w,hw,hgoodw⟩ := hgood c₀ hc₀
    have hside : (Q.descendant A).side ≤ 1/(2:ℝ)^g := by
      rw [DyadicSquare.descendant_side,hA]
      exact div_le_div_of_nonneg_right hQs (by positivity)
    have hd (c : CellPath) (hc : c ∈ S) :
        dist (Q.descendant c).center (Q.descendant c₀).center ≤ 2/(2:ℝ)^g := by
      apply ((Q.descendant A).dist_le (Q.descendant_side_pos hQ A).le
        (hparent c hc ((Q.descendant c).center_mem (Q.descendant_side_pos hQ c)))
        (hparent c₀ hc₀ ((Q.descendant c₀).center_mem (Q.descendant_side_pos hQ c₀)))).trans
      exact (mul_le_mul_of_nonneg_left hside (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
    have hsub : S ⊆ (parallelTestCells Q ρ g p c₀).filter (fun c =>
        |planeDot ((Q.descendant c).center-(Q.descendant c₀).center) (quarterTurn (w:Plane))| ≤ W) := by
      intro c hc
      obtain ⟨hlen,hocc⟩ := Finset.mem_filter.mp (hS hc)
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨hlen,hocc,?_⟩
        exact (hd c hc).trans_lt (div_lt_div_of_pos_right (by norm_num : (2:ℝ) < 10) (by positivity))
      · exact (common_strip_relative_bound z (Q.descendant c).center (Q.descendant c₀).center u w
          (by positivity) (by positivity) (hstrip c hc) (hstrip c₀ hc₀) (hd c hc)
          (by simpa only [sourceCircleRotate_dist] using
            circleAngularBin_scale_diameter hθ hcap j hu hw)).trans hwidth
    have hcard : S.card ≤ parallelTestCount Q ρ g p c₀ W (w:Plane) := Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hcard).trans hgoodw
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa only [Finset.card_empty,Nat.cast_zero] using hthreshold

theorem uniform_inherited_rotated_parallel_candidates {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ), ∀ e ∈ S, ∀ a p : ℕ,
    d e = .parallel a p → a ≤ p → p ≤ N →
    ∀ A : CellPath, A.length = a → ∀ C : Finset CellPath,
    C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier) →
    ∀ (z : Plane) (u : UnitCircle) (θ b axis : ℝ), 0 < θ → θ ≤ 2*Real.pi →
    ∀ j : ℕ, sourceCircleRotate (-axis) u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ b) →
    2*b+(2/(2:ℝ)^a)*(4*θ) ≤ sourceAngularWidth N sig J (i+1) p →
    (∀ c ∈ C, RotatedAngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j axis) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)) := by
  obtain ⟨N₀,hgood⟩ := uniform_inheritedCircleSymbol_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i h e he a p hd hap hp A hA C hC hparent
    z u θ b axis hθ hcap j hu hstrip hwidth hel
  apply rotated_parallel_candidates_le_good_test Q (by rw [hQ]; norm_num) hQ.le ρ a p A hA C hC hparent
    z u hθ hcap axis j hu hstrip hwidth (by positivity)
  intro c hc
  obtain ⟨w,hw,x,hx,hn,_⟩ := rotated_eligible_label_witness (Q.descendant c).measurable
    (hel c hc) (fun _ _ => True) (fun _ => Filter.Eventually.of_forall (fun _ _ => True.intro))
  refine ⟨w,hw,?_⟩
  have hg := hgood N hN S d k Q hQ ρ m lam i h e he
    (by simpa only [hd,ValidDescriptor] using And.intro hap hp)
    c (by simpa only [hd,descriptorAnchor] using hC hc) x hx w hn
  simpa only [hd,descriptorGoodSet] using hg

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductCandidateWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_product_candidate_width {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a g p J i : ℕ, a ≤ g → 0 < J → i < J →
    ∀ c₀ : ℝ, 0 < c₀ →
      2*(5*graphNonedgeThreshold N sig p)+(2/(2:ℝ)^g)*(4*graphAngularScale N sig ((p:ℝ)-a) c₀) ≤
        sourceAngularWidth N sig J (i+1) p := by
  obtain ⟨N₁,hsmall⟩ := graph_representative_error_small hsig (C := 8) (by norm_num)
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed (by positivity : 0 < 970*sig) 11
  refine ⟨max N₁ N₂,?_⟩
  intro N hN a g p J i hag hJ hi c₀ hc
  have hgscale : 8/(2:ℝ)^g ≤ 8*(2:ℝ)^(-(a:ℝ)) := by
    rw [div_eq_mul_inv,← Real.rpow_natCast (2:ℝ) g,← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg (Nat.cast_le.mpr hag))
  have hs := hsmall N ((le_max_left _ _).trans hN) a p (graphAngularScale N sig ((p:ℝ)-a) c₀)
    (8/(2:ℝ)^g) (graphAngularScale_pos N sig _ hc).le (by positivity) (min_le_right _ _) hgscale
  change 20*(2:ℝ)^(-(p:ℝ))+_ ≤ graphNonedgeThreshold N sig p/2 at hs
  have hnorm : 11*graphNonedgeThreshold N sig p ≤ (1/(2:ℝ)^p)*((2:ℝ)^N)^(1000*sig) := by
    have hh := mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN))
      (by positivity : 0 ≤ (2:ℝ)^(-(p:ℝ))*((2:ℝ)^N)^(30*sig))
    have he : ((2:ℝ)^N)^(970*sig)*((2:ℝ)^N)^(30*sig) = ((2:ℝ)^N)^(1000*sig) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring
    calc
      _ ≤ ((2:ℝ)^N)^(970*sig)*((2:ℝ)^(-(p:ℝ))*((2:ℝ)^N)^(30*sig)) := hh
      _ = (2:ℝ)^(-(p:ℝ))*((2:ℝ)^N)^(1000*sig) := by rw [mul_left_comm,he]
      _ = _ := by rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  have hiR : ((i+1:ℕ):ℝ)/(J:ℝ) ≤ 1 :=
    (div_le_one (by exact_mod_cast hJ)).mpr (by exact_mod_cast hi)
  have hw : (1/(2:ℝ)^p)*((2:ℝ)^N)^(1000*sig) ≤ sourceAngularWidth N sig J (i+1) p := by
    unfold sourceAngularWidth
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  apply le_trans _ (hnorm.trans hw)
  have hspos : 0 ≤ graphNonedgeThreshold N sig p := by unfold graphNonedgeThreshold; positivity
  have hp : 0 ≤ (2:ℝ)^(-(p:ℝ)) := by positivity
  rw [show (2/(2:ℝ)^g)*(4*graphAngularScale N sig ((p:ℝ)-a) c₀) =
    graphAngularScale N sig ((p:ℝ)-a) c₀*(8/(2:ℝ)^g) by ring]
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceCandidateWidth
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_distance_candidate_width {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p J i : ℕ, 0 < J → i < J →
    ∀ c₀ : ℝ, 0 < c₀ →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    2*(14028*(2:ℝ)^(-(a:ℝ))*θ)+(2/(2:ℝ)^a)*(4*θ) ≤
      sourceAngularWidth N sig J (i+1) p := by
  obtain ⟨N₁,hsmall⟩ := graph_representative_error_small hsig (C := 28064) (by norm_num)
  obtain ⟨N₂,hwidth⟩ := uniform_product_candidate_width hsig
  refine ⟨max N₁ N₂,?_⟩
  intro N hN a p J i hJ hi c₀ hc
  dsimp only
  let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
  have hθ : 0 ≤ θ := (graphAngularScale_pos N sig _ hc).le
  have hs := hsmall N ((le_max_left _ _).trans hN) a p θ
    (28064*(2:ℝ)^(-(a:ℝ))) hθ (by positivity) (min_le_right _ _) le_rfl
  have hw := hwidth N ((le_max_right _ _).trans hN) a a p J i le_rfl hJ hi c₀ hc
  have he : 2*(14028*(2:ℝ)^(-(a:ℝ))*θ)+(2/(2:ℝ)^a)*(4*θ) =
      θ*(28064*(2:ℝ)^(-(a:ℝ))) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    ring
  rw [he]
  have hp : 0 ≤ (2:ℝ)^(-(p:ℝ)) := by positivity
  have hS : 0 ≤ graphNonedgeThreshold N sig p := by unfold graphNonedgeThreshold; positivity
  have hv : 0 ≤ (2/(2:ℝ)^a)*(4*θ) := by positivity
  change 20*(2:ℝ)^(-(p:ℝ))+_ ≤ graphNonedgeThreshold N sig p/2 at hs
  change 2*(5*graphNonedgeThreshold N sig p)+(2/(2:ℝ)^a)*(4*θ) ≤ _ at hw
  linarith

theorem uniform_inherited_distance_candidates {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ), i < J → ∀ h : Plane → ℂ, ∀ e ∈ S, ∀ a p : ℕ,
    d e = .parallel a p → a ≤ p → p ≤ N →
    ∀ A : CellPath, A.length = a → ∀ C : Finset CellPath,
    C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier) →
    ∀ X Y : DyadicSquare, 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-(a:ℝ)) → Y.side ≤ (2:ℝ)^(-(a:ℝ)) →
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    (Q.descendant A).carrier ⊆ X.carrier ∪ Y.carrier →
    ∀ z ∈ X.carrier ∪ Y.carrier, ∀ (u : UnitCircle) (axis c₀ : ℝ),
    0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    ∀ (j : ℕ) (flip : Bool),
    sourceCircleRotate (-axis) u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, AngularBinActive (angularBinCount θ) j
      (sourceCircleRotate (-axis) (if flip then sourceRadialUnit z (Q.descendant c).center
        else sourceRadialUnit (Q.descendant c).center z)) (3*θ)) →
    (∀ c ∈ C, RotatedAngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j axis) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)) := by
  obtain ⟨N₁,hcount⟩ := uniform_inherited_rotated_parallel_candidates hsig hJ
  obtain ⟨N₂,hwidth⟩ := uniform_distance_candidate_width hsig
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a p hd hap hp A hA C hC hparent
    X Y hX hY hXa hYa hsep hAY z hz u axis c₀ hc hcap
  dsimp only
  intro j flip hu ha hel
  let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
  have hθ := graphAngularScale_pos N sig ((p:ℝ)-a) hc
  have hθcap := (min_le_left c₀ (graphUncappedAngularScale N sig ((p:ℝ)-a))).trans hcap
  apply hcount N ((le_max_left _ _).trans hN) S d k Q hQ ρ m lam i h e he a p hd hap hp A hA C hC hparent
    z u θ (14028*(2:ℝ)^(-(a:ℝ))*θ) axis hθ hθcap j hu ?_
    (hwidth N ((le_max_right _ _).trans hN) a p J i hJ hi c₀ hc) hel
  intro c hcC
  have hcY := hAY (hparent c hcC ((Q.descendant c).center_mem (Q.descendant_side_pos (by rw [hQ]; norm_num) c)))
  have hdist := dyadic_two_parent_diameter X Y hX hY hXa hYa hsep hz hcY
  have hdirection := active_rotated_bin_direction_bound hθ hθcap axis j _ u hu (ha c hcC)
  cases flip
  · exact (radial_perpendicular_bound z (Q.descendant c).center u hdist hdirection).trans_eq (by ring)
  · have hh := radial_perpendicular_bound (Q.descendant c).center z u
      (by simpa only [dist_comm] using hdist) hdirection
    rw [show (Q.descendant c).center-z = -(z-(Q.descendant c).center) by abel,
      inner_neg_right,abs_neg] at hh
    exact hh.trans_eq (by ring)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentGraphIndices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentGraphIndex_cells (Q₁ Q₂ : DyadicSquare) (A B : CellPath)
    (e f : ParentDistanceBinLabel) (l : Fin 4) :
    graphQuadCells ![Q₁,Q₂,Q₂,Q₁] (sourceParentGraphIndex A B (e,f)).1 l =
      ![((Q₁.descendant A).descendant e.1.1),((Q₂.descendant B).descendant e.1.2),
        ((Q₂.descendant B).descendant f.1.2),((Q₁.descendant A).descendant f.1.1)] l := by
  fin_cases l <;> simp [graphQuadCells,graphQuadPath,sourceParentGraphIndex,DyadicSquare.descendant_append]

theorem sourceParentGraphIndices_parent (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : CellPath) (N n : ℕ) (sig t : ℝ) (ρ ν : Measure Plane)
    {q : GraphNonedgeIndex}
    (hq : q ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    (l : Fin 4) :
    (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] q.1 l).carrier ⊆
      (graphSlotParent true (Q₁.descendant A) (Q₂.descendant B) l).carrier := by
  classical
  obtain ⟨⟨e,f⟩,_,rfl⟩ := Finset.mem_image.mp hq
  rw [sourceParentGraphIndex_cells]
  fin_cases l <;> simp only [graphSlotParent,↓reduceIte] <;>
    apply DyadicSquare.descendant_subset <;>
    first | exact Q₁.descendant_side_pos hQ₁ A | exact Q₂.descendant_side_pos hQ₂ B

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFiberPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem graphB_norm_exact (z : ℝ) (v : Plane) :
    ‖graphB z v‖ = (Real.sqrt (1+z^2)/2)*‖v‖ := by
  have he : quarterTurn (v+z • quarterTurn v) = quarterTurn v+(-z) • v := by
    ext l
    fin_cases l <;> simp [quarterTurn]
    ring
  have hn : ‖v+z • quarterTurn v‖ = Real.sqrt (1+z^2)*‖v‖ := by
    rw [← graph_quarterTurn_norm (v+z • quarterTurn v),he,norm_quarterTurn_add,neg_sq]
  rw [graphB,norm_smul,hn,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  ring

theorem graphB_inverse_norm_le (z : ℝ) (v : Plane) : ‖v‖ ≤ 2*‖graphB z v‖ := by
  rw [graphB_norm_exact]
  have hs : 1 ≤ Real.sqrt (1+z^2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg z]
  calc
    ‖v‖ = 1*‖v‖ := (one_mul _).symm
    _ ≤ Real.sqrt (1+z^2)*‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    _ = 2*((Real.sqrt (1+z^2)/2)*‖v‖) := by ring

theorem graphA_inverse_norm_le (z : ℝ) (v : Plane) : ‖v‖ ≤ 2*‖graphA z v‖ := by
  simpa only [graphB,graphA,neg_smul,← sub_eq_add_neg] using graphB_inverse_norm_le (-z) v

theorem graphB_two_edges_close (z s S : ℝ) (v w w' : Plane) (hs : s = 1 ∨ s = -1)
    (h : ‖graphA z v+s • graphB z w‖ ≤ S)
    (h' : ‖graphA z v+s • graphB z w'‖ ≤ S) : dist w w' ≤ 4*S := by
  have he : (graphA z v+s • graphB z w)-(graphA z v+s • graphB z w') = s • graphB z (w-w') := by
    ext l
    fin_cases l <;> simp [graphB,quarterTurn] <;> ring
  have hn : ‖s • graphB z (w-w')‖ = ‖graphB z (w-w')‖ := by
    rcases hs with rfl | rfl <;> simp
  have hb := (norm_sub_le (graphA z v+s • graphB z w) (graphA z v+s • graphB z w')).trans (add_le_add h h')
  rw [he,hn] at hb
  have hl := graphB_inverse_norm_le z (w-w')
  rw [dist_eq_norm]
  linarith

theorem graphA_two_edges_close (z s S : ℝ) (v v' w : Plane)
    (h : ‖graphA z v+s • graphB z w‖ ≤ S)
    (h' : ‖graphA z v'+s • graphB z w‖ ≤ S) : dist v v' ≤ 4*S := by
  have he : (graphA z v+s • graphB z w)-(graphA z v'+s • graphB z w) = graphA z (v-v') := by
    ext l
    fin_cases l <;> simp [graphA,quarterTurn] <;> ring
  have hb := (norm_sub_le (graphA z v+s • graphB z w) (graphA z v'+s • graphB z w)).trans (add_le_add h h')
  rw [he] at hb
  have hl := graphA_inverse_norm_le z (v-v')
  rw [dist_eq_norm]
  linarith

theorem graph_unit_center_fiber_card (Q : DyadicSquare) (hQ : Q.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (S : Finset CellPath) (hS : S ⊆ dyadicPaths p)
    (x : Plane) (hb : ∀ c ∈ S, dist (Q.descendant c).center x ≤ 4*graphNonedgeThreshold N sig p) :
    (S.card : ℝ) ≤ 144*((2:ℝ)^N)^(60*sig) := by
  classical
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hpos : 0 < graphNonedgeThreshold N sig p := by unfold graphNonedgeThreshold; positivity
  have hsub : S ⊆ cellsMeeting Q p x (5*graphNonedgeThreshold N sig p) := by
    intro c hc
    apply Finset.mem_filter.mpr
    refine ⟨hS hc,(Q.descendant c).center,(Q.descendant c).center_mem (Q.descendant_side_pos hQpos c),?_⟩
    exact (hb c hc).trans_lt (by linarith)
  have hp := dyadic_scaled_ball_card_le Q hQpos p x
    (C₀ := 5*((2:ℝ)^N)^(30*sig)) (by positivity) (r := 5*graphNonedgeThreshold N sig p) (by
      rw [hQ,graphNonedgeThreshold,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
      exact le_of_eq (by ring))
  have hR : 1 ≤ ((2:ℝ)^N)^(30*sig) := Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  have he : (((2:ℝ)^N)^(30*sig))^2 = ((2:ℝ)^N)^(60*sig) := by
    rw [← Real.rpow_natCast _ 2,← Real.rpow_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
    congr 1
    ring
  have hsquare : 4*(5*((2:ℝ)^N)^(30*sig)+1)^2 ≤ 144*(((2:ℝ)^N)^(30*sig))^2 := by
    nlinarith [sq_nonneg (((2:ℝ)^N)^(30*sig)-1)]
  rw [he] at hsquare
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hp.trans hsquare)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_DistancePairDegree
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distance_pair_fiber_card (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (P : CellPath) :
    ((C.filter (fun c => c.1 = P)).card : ℝ) ≤ 144*((2:ℝ)^N)^(60*sig) := by
  classical
  let F := C.filter (fun c => c.1 = P)
  by_cases hn : F.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hn
    have hproj : (F.image Prod.snd).card = F.card := by
      apply Finset.card_image_iff.mpr
      intro c hc b hb he
      exact Prod.ext ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hb).2.symm) he
    rw [← show F.card = (C.filter (fun c => c.1 = P)).card from rfl,← hproj]
    apply graph_unit_center_fiber_card Q₁ hQ₁ N p hsig (F.image Prod.snd)
      (by
        intro b hb
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
        exact hlen c (Finset.mem_filter.mp hc).1)
      (Q₁.descendant c₀.2).center
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have h0 := (hedge c₀ (Finset.mem_filter.mp hc₀).1).1
    have h1 := (hedge c (Finset.mem_filter.mp hc).1).1
    have he : c.1 = c₀.1 := (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc₀).2.symm
    simp only [distancePairCells,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1
    rw [he] at h1
    have hh := graphB_two_edges_close _ _ _ _ _ _ (graphSourceSign_cases true plus) h1 h0
    simpa only [dist_sub_left] using hh
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (F.card : ℝ) ≤ _
    rw [hz,Finset.card_empty,Nat.cast_zero]
    positivity

theorem distance_pair_card_of_projection (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (b : ℝ) (hproj : ((C.image Prod.fst).card : ℝ) ≤ b) :
    (C.card : ℝ) ≤ b*(144*((2:ℝ)^N)^(60*sig)) := by
  classical
  have he := Finset.card_eq_sum_card_image Prod.fst C
  calc
    _ = ∑ P ∈ C.image Prod.fst, ((C.filter (fun c => c.1 = P)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _P ∈ C.image Prod.fst, 144*((2:ℝ)^N)^(60*sig) :=
      Finset.sum_le_sum (fun P _ => distance_pair_fiber_card Q₁ Q₂ hQ₁ N p hsig plus q row C hlen hedge P)
    _ = ((C.image Prod.fst).card : ℝ)*(144*((2:ℝ)^N)^(60*sig)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hproj (by positivity)

theorem distance_pair_first_fiber_card (Q₁ Q₂ : DyadicSquare) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.1 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (P : CellPath) :
    ((C.filter (fun c => c.2 = P)).card : ℝ) ≤ 144*((2:ℝ)^N)^(60*sig) := by
  classical
  let F := C.filter (fun c => c.2 = P)
  by_cases hn : F.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hn
    have hproj : (F.image Prod.fst).card = F.card := by
      apply Finset.card_image_iff.mpr
      intro c hc b hb he
      exact Prod.ext he ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hb).2.symm)
    rw [← show F.card = (C.filter (fun c => c.2 = P)).card from rfl,← hproj]
    apply graph_unit_center_fiber_card Q₂ hQ₂ N p hsig (F.image Prod.fst)
      (by
        intro b hb
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
        exact hlen c (Finset.mem_filter.mp hc).1)
      (Q₂.descendant c₀.1).center
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have h0 := (hedge c₀ (Finset.mem_filter.mp hc₀).1).1
    have h1 := (hedge c (Finset.mem_filter.mp hc).1).1
    have he : c.2 = c₀.2 := (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc₀).2.symm
    simp only [distancePairCells,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1
    rw [he] at h1
    have hh := graphA_two_edges_close _ _ _ _ _ _ h1 h0
    simpa only [dist_sub_left] using hh
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (F.card : ℝ) ≤ _
    rw [hz,Finset.card_empty,Nat.cast_zero]
    positivity

theorem distance_pair_card_of_second_projection (Q₁ Q₂ : DyadicSquare) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.1 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells Q₁ Q₂ row c) q)
    (b : ℝ) (hproj : ((C.image Prod.snd).card : ℝ) ≤ b) :
    (C.card : ℝ) ≤ b*(144*((2:ℝ)^N)^(60*sig)) := by
  classical
  have he := Finset.card_eq_sum_card_image Prod.snd C
  calc
    _ = ∑ P ∈ C.image Prod.snd, ((C.filter (fun c => c.2 = P)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _P ∈ C.image Prod.snd, 144*((2:ℝ)^N)^(60*sig) :=
      Finset.sum_le_sum (fun P _ => distance_pair_first_fiber_card Q₁ Q₂ hQ₂ N p hsig plus q row C hlen hedge P)
    _ = ((C.image Prod.snd).card : ℝ)*(144*((2:ℝ)^N)^(60*sig)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hproj (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceMatrixData
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentGraphIndices_occupied
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (N a n : ℕ) (sig t : ℝ)
    (hA : A.length = a) (hB : B.length = a)
    {e : GraphNonedgeIndex}
    (he : e ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B)
    (l : Fin 4) :
    graphQuadPath e.1 l ∈ occupiedAnchorPaths (![Q₁,Q₂,Q₂,Q₁] l) (![ρ,ν,ν,ρ] l) (a+n) := by
  classical
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨he,hf⟩ := Finset.mem_product.mp hef
  obtain ⟨heP,heQ,_⟩ := sourceParentBinLabels_spec he
  obtain ⟨hfP,hfQ,_⟩ := sourceParentBinLabels_spec hf
  have happ (Q : DyadicSquare) (μ : Measure Plane) (P c : CellPath)
      (hP : P.length = a) (hc : c ∈ occupiedAnchorPaths (Q.descendant P) μ n) :
      P++c ∈ occupiedAnchorPaths Q μ (a+n) := by
    obtain ⟨hc,hpos⟩ := Finset.mem_filter.mp hc
    have hl := (mem_dyadicPaths _ _).mp hc
    apply Finset.mem_filter.mpr
    exact ⟨by simp [mem_dyadicPaths,hP,hl],by simpa only [DyadicSquare.descendant_append] using hpos⟩
  fin_cases l
  · exact happ Q₁ ρ A e.1.1 hA heP
  · exact happ Q₂ ν B e.1.2 hB heQ
  · exact happ Q₂ ν B f.1.2 hB hfQ
  · exact happ Q₁ ρ A f.1.1 hA hfP

theorem sourceParentGraphIndices_activity
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (N n : ℕ) (sig t : ℝ)
    {e : GraphNonedgeIndex}
    (he : e ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B) :
    let P := graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1
    let θ := graphUncappedAngularScale N sig t
    let X := Q₁.descendant A
    let Y := Q₂.descendant B
    AngularBinActive (angularBinCount θ) e.2.1.1 (sourceCenteredCellDirection X Y (P 0) (P 1)) (3*θ) ∧
    AngularBinActive (angularBinCount θ) e.2.1.2 (sourceCenteredCellDirection X Y (P 3) (P 2)) (3*θ) := by
  classical
  obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp he
  dsimp only
  simp only [sourceParentGraphIndex_cells]
  exact ⟨sourceParentBinLabels_activity (Finset.mem_product.mp hef).1,
    sourceParentBinLabels_activity (Finset.mem_product.mp hef).2⟩

theorem distanceMatrix_cells (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath)
    (j b : ℕ) (plus : Bool) :
    graphQuadCells ![Q₁,Q₂,Q₂,Q₁] (distanceMatrixIndex row col j b plus).1 =
      distancePairCells Q₁ Q₂ row col := by
  funext l
  fin_cases l <;> rfl

theorem graphRetainedDistance_reversal (N : ℕ) (sig p : ℝ) (plus : Bool)
    (P : Fin 4 → DyadicSquare) (q : UnitCircle × UnitCircle) :
    GraphRetainedEdge N sig p true plus ![P 1,P 0,P 3,P 2] q ↔
      GraphRetainedEdge N sig p true plus P q := by
  have he : ∀ (z s : ℝ) (v w : Plane), graphA z (-v)+s • graphB z (-w) = -(graphA z v+s • graphB z w) := by
    intro z s v w
    ext l
    fin_cases l <;> simp [graphA,graphB,quarterTurn] <;> ring
  simp only [GraphRetainedEdge,Bool.true_eq_false,false_implies, and_true,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [show (P 1).center-(P 0).center = -((P 0).center-(P 1).center) by abel,
    show (P 3).center-(P 2).center = -((P 2).center-(P 3).center) by abel,he,norm_neg]

theorem sourceRetainedDistanceIndices_data
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n N : ℕ) (sig t θ : ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) {e : GraphNonedgeIndex}
    (he : e ∈ sourceRetainedDistanceIndices Q₁ Q₂ ρ ν β γ A B a n N sig t θ rep) :
    e ∈ sourceParentGraphIndices N sig t (Q₁.descendant A) (Q₂.descendant B) ρ ν n A B ∧
    GraphRetainedEdge N sig (a+n) true e.2.2 (graphQuadCells ![Q₁,Q₂,Q₂,Q₁] e.1) (rep e.2) ∧
    GraphDistanceIndexEligible Q₁ Q₂ ρ ν β γ (angularBinCount θ)
      (sourceParentAxis (Q₁.descendant A) (Q₂.descendant B)) e := by
  classical
  obtain ⟨he,hel⟩ := Finset.mem_filter.mp he
  obtain ⟨he,hr⟩ := Finset.mem_filter.mp he
  exact ⟨he,hr,hel⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_UniformDistancePairDegree
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_inherited_distance_pair_degree {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ (h : Fin 2 → Plane → ℂ) (e : ∀ l, ι l), (∀ l, e l ∈ S l) →
    ∀ a p : ℕ, (∀ l, d l (e l) = .parallel a p) → a ≤ p → p ≤ N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    ∀ (row : CellPath × CellPath) (C : Finset (CellPath × CellPath)),
    ((Q 0).descendant row.1).center ∈ X.carrier ∪ Y.carrier →
    ((Q 1).descendant row.2).center ∈ X.carrier ∪ Y.carrier →
    (∀ c ∈ C, c.1 ∈ occupiedAnchorPaths (Q 1) (ρ 1) p) →
    (∀ c ∈ C, c.2 ∈ occupiedAnchorPaths (Q 0) (ρ 0) p) →
    (∀ c ∈ C, ((Q 1).descendant c.1).carrier ⊆ Y.carrier) →
    (∀ c ∈ C, ((Q 0).descendant c.2).carrier ⊆ X.carrier) →
    ∀ axis c₀ : ℝ, 0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
    ∀ (j b : ℕ) (flip plus : Bool) (q : UnitCircle × UnitCircle),
    sourceCircleRotate (-axis) q.1 ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    sourceCircleRotate (-axis) q.2 ∈ tsupport (circleAngularBin (angularBinCount θ) b) →
    (∀ c ∈ C, AngularBinActive (angularBinCount θ) j (sourceCircleRotate (-axis)
      (if flip then sourceRadialUnit ((Q 0).descendant row.1).center ((Q 1).descendant c.1).center
       else sourceRadialUnit ((Q 1).descendant c.1).center ((Q 0).descendant row.1).center)) (3*θ)) →
    (∀ c ∈ C, AngularBinActive (angularBinCount θ) b (sourceCircleRotate (-axis)
      (if !flip then sourceRadialUnit ((Q 1).descendant row.2).center ((Q 0).descendant c.2).center
       else sourceRadialUnit ((Q 0).descendant c.2).center ((Q 1).descendant row.2).center)) (3*θ)) →
    (∀ c ∈ C, RotatedAngularLabelEligible (ρ 1) ((Q 1).descendant c.1).carrier (β 1) (angularBinCount θ) j axis) →
    (∀ c ∈ C, RotatedAngularLabelEligible (ρ 0) ((Q 0).descendant c.2).carrier (β 0) (angularBinCount θ) b axis) →
    (∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells (Q 0) (Q 1) row c) q) →
    (C.card : ℝ) ≤ 144*((2:ℝ)^N)^(min (height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a p)
      (height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a p)+2000*(lam+sig)+60*sig) := by
  classical
  obtain ⟨N₀,hcount⟩ := uniform_inherited_distance_candidates hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a p hd hap hp A B hA hB
  try dsimp only
  intro hsep row C hr₁ hr₂ ho₁ ho₂ hc₁ hc₂ axis c₀ hc hcap
  try dsimp only
  intro j b flip plus q hu hw ha₁ ha₂ hel₁ hel₂ hedge
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  have hside (l : Fin 2) (D : CellPath) (hD : D.length = a) :
      ((Q l).descendant D).side ≤ (2:ℝ)^(-(a:ℝ)) := by
    rw [DyadicSquare.descendant_side,hD,hQ l,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  have h₁ := hcount N hN (S 1) (d 1) (k 1) (Q 1) (hQ 1) (ρ 1) (m 1) lam i hi (h 1) (e 1) (he 1)
    a p (hd 1) hap hp B hB (C.image Prod.fst)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact ho₁ v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hc₁ v hv)
    ((Q 0).descendant A) ((Q 1).descendant B)
    ((Q 0).descendant_side_pos (hQp 0) A) ((Q 1).descendant_side_pos (hQp 1) B)
    (hside 0 A hA) (hside 1 B hB) hsep (fun _ hx => Or.inr hx)
    ((Q 0).descendant row.1).center hr₁ q.1 axis c₀ hc hcap j flip hu
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact ha₁ v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hel₁ v hv)
  have h₂ := hcount N hN (S 0) (d 0) (k 0) (Q 0) (hQ 0) (ρ 0) (m 0) lam i hi (h 0) (e 0) (he 0)
    a p (hd 0) hap hp A hA (C.image Prod.snd)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact ho₂ v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hc₂ v hv)
    ((Q 0).descendant A) ((Q 1).descendant B)
    ((Q 0).descendant_side_pos (hQp 0) A) ((Q 1).descendant_side_pos (hQp 1) B)
    (hside 0 A hA) (hside 1 B hB) hsep (fun _ hx => Or.inl hx)
    ((Q 1).descendant row.2).center hr₂ q.2 axis c₀ hc hcap b (!flip) hw
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact ha₂ v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hel₂ v hv)
  let H₀ := height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a p
  let H₁ := height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a p
  have hn₁ := fun c hc => (Finset.mem_filter.mp (ho₁ c hc)).1
  have hn₂ := fun c hc => (Finset.mem_filter.mp (ho₂ c hc)).1
  rcases le_total H₀ H₁ with hmin | hmin
  · have hh := distance_pair_card_of_second_projection (Q 0) (Q 1) (hQ 1) N p hsig.le plus q row C hn₁ hedge _ h₂
    apply hh.trans_eq
    rw [min_eq_left hmin,mul_left_comm,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
  · have hh := distance_pair_card_of_projection (Q 0) (Q 1) (hQ 0) N p hsig.le plus q row C hn₂ hedge _ h₁
    apply hh.trans_eq
    rw [min_eq_right hmin,mul_left_comm,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualDistanceDegrees
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_actual_distance_degrees_oai {sig κ c₀ : ℝ} (hsig : 0 < sig)
    (hgap : 10*sig < κ) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ (h : Fin 2 → Plane → ℂ) (e : ∀ l, ι l), (∀ l, e l ∈ S l) →
    ∀ a n : ℕ, (∀ l, d l (e l) = .parallel a (a+n)) → a+n ≤ N → κ*N ≤ (n:ℝ) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let axis := sourceParentAxis ((Q 0).descendant A) ((Q 1).descendant B)
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2 axis e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
    let I := sourceRetainedDistanceIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
    ∀ (j b : ℕ) (plus reverse : Bool) (row : CellPath × CellPath),
    ((activeDistanceMatrixNeighbors I (a+n) j b θ axis plus reverse row).card : ℝ) ≤
      144*((2:ℝ)^N)^(min (height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a (a+n))
      (height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a (a+n))+2000*(lam+sig)+60*sig) := by
  classical
  obtain ⟨N₁,hcount⟩ := uniform_inherited_distance_pair_degree hsig hJ
  obtain ⟨N₂,hscale⟩ := graphAngularScale_cap_inactive hgap hc
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a n hd hp hlow A B hA hB hsep
  dsimp only
  let t : ℝ := (a+n:ℕ)-a
  let θ := graphAngularScale N sig t c₀
  let axis := sourceParentAxis ((Q 0).descendant A) ((Q 1).descendant B)
  let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2 axis e.1.1 e.1.2
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
  let I := sourceRetainedDistanceIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
  intro j b plus reverse row
  change ((activeDistanceMatrixNeighbors I (a+n) j b θ axis plus reverse row).card : ℝ) ≤ _
  by_cases hs : (tsupport (graphSourceWeight true plus axis (angularBinCount θ) j b)).Nonempty
  · rw [activeDistanceMatrixNeighbors,ite_eq_left hs]
    have hq : GraphSourceRepresentative true plus axis θ j b (rep ((j,b),plus)) := by
      rcases graphChosenRepresentative_spec (graphAngularScale_pos N sig t hc)
        ((min_le_left _ _).trans hcap) true plus axis j b with hq | hn
      · exact hq
      · exact (hn hs).elim
    have hbins := graphSourceWeight_support_bins true plus axis (angularBinCount θ) j b hq.1
    have hθ : θ = graphUncappedAngularScale N sig t := hscale N ((le_max_right _ _).trans hN) t
      (by simpa [t] using hlow)
    have hsc : graphAngularScale N sig (n:ℝ) c₀ = graphUncappedAngularScale N sig n := by
      simpa [θ,t] using hθ
    have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
    cases reverse
    · let C := distanceMatrixNeighbors I (a+n) j b plus false row
      have hdata (col : CellPath × CellPath) (hc : col ∈ C) :=
        sourceRetainedDistanceIndices_data (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
          (show distanceMatrixIndex row col j b plus ∈ I from (Finset.mem_filter.mp hc).2)
      have hocc (col : CellPath × CellPath) (hc : col ∈ C) (l : Fin 4) :=
        sourceParentGraphIndices_occupied (Q 0) (Q 1) (ρ 0) (ρ 1) A B N a n sig t hA hB (hdata col hc).1 l
      have hpar (col : CellPath × CellPath) (hc : col ∈ C) (l : Fin 4) :=
        sourceParentGraphIndices_parent (Q 0) (Q 1) (hQp 0) (hQp 1) A B N n sig t (ρ 0) (ρ 1) (hdata col hc).1 l
      have hact (col : CellPath × CellPath) (hc : col ∈ C) :=
        sourceParentGraphIndices_activity (Q 0) (Q 1) (ρ 0) (ρ 1) A B N n sig t (hdata col hc).1
      by_cases hn : C.Nonempty
      · obtain ⟨col₀,hcol₀⟩ := hn
        have hh := hcount N ((le_max_left _ _).trans hN) S d k Q hQ ρ m lam i hi h e he
          a (a+n) hd (Nat.le_add_right a n) hp A B hA hB hsep row C
          (Or.inl (show ((Q 0).descendant row.1).center ∈ ((Q 0).descendant A).carrier from
            hpar col₀ hcol₀ 0 (((Q 0).descendant row.1).center_mem ((Q 0).descendant_side_pos (hQp 0) row.1))))
          (Or.inr (show ((Q 1).descendant row.2).center ∈ ((Q 1).descendant B).carrier from
            hpar col₀ hcol₀ 2 (((Q 1).descendant row.2).center_mem ((Q 1).descendant_side_pos (hQp 1) row.2))))
          (fun col hc => hocc col hc 1) (fun col hc => hocc col hc 3)
          (fun col hc => hpar col hc 1) (fun col hc => hpar col hc 3)
          axis c₀ hc hcap j b false plus (rep ((j,b),plus)) hbins.1 hbins.2
          (fun col hc => by simpa [hsc,sourceCenteredCellDirection,graphQuadCells,graphQuadPath,distanceMatrixIndex,θ,t,axis,Fin.rev] using (hact col hc).1)
          (fun col hc => by simpa [hsc,sourceCenteredCellDirection,graphQuadCells,graphQuadPath,distanceMatrixIndex,θ,t,axis,Fin.rev] using (hact col hc).2)
          (fun col hc => (hdata col hc).2.2 1) (fun col hc => (hdata col hc).2.2 3)
          (fun col hc => by
            have hr := (hdata col hc).2.1
            rw [distanceMatrix_cells] at hr
            simpa only [Nat.cast_add,distanceMatrixIndex] using hr)
        exact hh
      · change (C.card : ℝ) ≤ _
        rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty,Nat.cast_zero]
        positivity
    · let C := distanceMatrixNeighbors I (a+n) j b plus true row
      have hdata (col : CellPath × CellPath) (hc : col ∈ C) :=
        sourceRetainedDistanceIndices_data (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
          (show distanceMatrixIndex col row j b plus ∈ I from (Finset.mem_filter.mp hc).2)
      have hocc (col : CellPath × CellPath) (hc : col ∈ C) (l : Fin 4) :=
        sourceParentGraphIndices_occupied (Q 0) (Q 1) (ρ 0) (ρ 1) A B N a n sig t hA hB (hdata col hc).1 l
      have hpar (col : CellPath × CellPath) (hc : col ∈ C) (l : Fin 4) :=
        sourceParentGraphIndices_parent (Q 0) (Q 1) (hQp 0) (hQp 1) A B N n sig t (ρ 0) (ρ 1) (hdata col hc).1 l
      have hact (col : CellPath × CellPath) (hc : col ∈ C) :=
        sourceParentGraphIndices_activity (Q 0) (Q 1) (ρ 0) (ρ 1) A B N n sig t (hdata col hc).1
      by_cases hn : C.Nonempty
      · obtain ⟨col₀,hcol₀⟩ := hn
        have hh := hcount N ((le_max_left _ _).trans hN)
          (fun l : Fin 2 => S l.rev) (fun l : Fin 2 => d l.rev) (fun l : Fin 2 => k l.rev)
          (fun l : Fin 2 => Q l.rev) (fun l => hQ l.rev)
          (fun l : Fin 2 => ρ l.rev) (fun l : Fin 2 => m l.rev) lam i hi
          (fun l : Fin 2 => h l.rev) (fun l : Fin 2 => e l.rev) (fun l => he l.rev)
          a (a+n) (fun l => hd l.rev) (Nat.le_add_right a n) hp B A hB hA
          (by simpa only [show (0:Fin 2).rev = 1 from rfl,show (1:Fin 2).rev = 0 from rfl,dist_comm] using hsep) row C
          (Or.inl (show ((Q 1).descendant row.1).center ∈ ((Q 1).descendant B).carrier from
            hpar col₀ hcol₀ 1 (((Q 1).descendant row.1).center_mem ((Q 1).descendant_side_pos (hQp 1) row.1))))
          (Or.inr (show ((Q 0).descendant row.2).center ∈ ((Q 0).descendant A).carrier from
            hpar col₀ hcol₀ 3 (((Q 0).descendant row.2).center_mem ((Q 0).descendant_side_pos (hQp 0) row.2))))
          (fun col hc => hocc col hc 0) (fun col hc => hocc col hc 2)
          (fun col hc => hpar col hc 0) (fun col hc => hpar col hc 2)
          axis c₀ hc hcap j b true plus (rep ((j,b),plus)) hbins.1 hbins.2
          (fun col hc => by simpa [hsc,sourceCenteredCellDirection,graphQuadCells,graphQuadPath,distanceMatrixIndex,θ,t,axis,Fin.rev] using (hact col hc).1)
          (fun col hc => by simpa [hsc,sourceCenteredCellDirection,graphQuadCells,graphQuadPath,distanceMatrixIndex,θ,t,axis,Fin.rev] using (hact col hc).2)
          (fun col hc => (hdata col hc).2.2 0) (fun col hc => (hdata col hc).2.2 2)
          (fun col hc => by
            have hr := (hdata col hc).2.1
            have heq : graphQuadCells ![Q 0,Q 1,Q 1,Q 0] (distanceMatrixIndex col row j b plus).1 =
                ![distancePairCells (Q 1) (Q 0) row col 1,distancePairCells (Q 1) (Q 0) row col 0,
                  distancePairCells (Q 1) (Q 0) row col 3,distancePairCells (Q 1) (Q 0) row col 2] := by
              funext l
              fin_cases l <;> rfl
            rw [heq] at hr
            simpa only [Nat.cast_add,distanceMatrixIndex,show (0:Fin 2).rev = 1 from rfl,show (1:Fin 2).rev = 0 from rfl] using
              (graphRetainedDistance_reversal N sig (a+n) plus _ _).mp hr)
        simpa only [show (0:Fin 2).rev = 1 from rfl,show (1:Fin 2).rev = 0 from rfl,min_comm] using hh
      · change (C.card : ℝ) ≤ _
        rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty,Nat.cast_zero]
        positivity
  · rw [activeDistanceMatrixNeighbors,ite_eq_right hs,Finset.card_empty,Nat.cast_zero]
    positivity

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_distance_degrees_oai := @OAI.PlanarFalconer.uniform_actual_distance_degrees_oai
