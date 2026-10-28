-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_product_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:31:50.042388+00:00
-- url     : https://prove2.me/submissions/b5c2e860-19dc-4603-bcf6-1c7243b30d4d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_original_product_graph_integral_bound
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_product_H_graph

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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem dyadicPaths_card_le (N : ℕ) : (dyadicPaths N).card ≤ 4 ^ N := by
  classical
  induction N with
  | zero => simp [dyadicPaths]
  | succ N ih =>
    calc
      (dyadicPaths (N+1)).card ≤ ∑ a ∈ (Finset.univ : Finset (Bool × Bool)),
          ((dyadicPaths N).image (List.cons a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ (Finset.univ : Finset (Bool × Bool)), 4 ^ N := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.card_image_le.trans ih
      _ = 4 ^ (N+1) := by simp [pow_succ, Nat.mul_comm]

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

theorem graph_transverse_identity (z s : ℝ) (ξ v w : Plane) :
    (1+z^2)*planeDot ξ (graphDerivative s v w) =
      planeDot (quarterTurn ξ-z • ξ) v +
        planeDot ξ (quarterTurn (graphA z v+s • graphB z w) +
          z • (graphA z v+s • graphB z w)) := by
  simp [planeDot,quarterTurn,graphDerivative,graphA,graphB]
  ring

theorem graph_direction_transverse (z : ℝ) (ξ v : Plane) :
    planeDot (quarterTurn (graphDirection z ξ)) v =
      (Real.sqrt (1+z^2))⁻¹ * planeDot (quarterTurn ξ-z • ξ) v := by
  simp [planeDot,quarterTurn,graphDirection]
  ring

theorem graph_product_strip (z s S : ℝ) (ξ v w : Plane)
    (hξ : ‖ξ‖ = 1) (hS : 0 ≤ S)
    (hchart : Real.sqrt (1+z^2) ≤ 4)
    (hedge : ‖graphA z v+s • graphB z w‖ ≤ S)
    (hderiv : |planeDot ξ (graphDerivative s v w)| ≤ S) :
    |planeDot (quarterTurn (graphDirection z ξ)) v| ≤ 5*S := by
  let t := Real.sqrt (1+z^2)
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t^2 = 1+z^2 := Real.sq_sqrt (by positivity)
  let e := graphA z v+s • graphB z w
  have herr : |planeDot ξ (quarterTurn e+z • e)| ≤ t*S := by
    calc
      _ ≤ ‖ξ‖*‖quarterTurn e+z • e‖ := planeDot_abs_le _ _
      _ = t*‖e‖ := by rw [hξ,one_mul,norm_quarterTurn_add]
      _ ≤ t*S := mul_le_mul_of_nonneg_left hedge ht.le
  have hid := graph_transverse_identity z s ξ v w
  have htrans : |planeDot (quarterTurn ξ-z • ξ) v| ≤ (t^2+t)*S := by
    have he : planeDot (quarterTurn ξ-z • ξ) v =
        (1+z^2)*planeDot ξ (graphDerivative s v w) -
          planeDot ξ (quarterTurn e+z • e) := by dsimp [e]; linarith [hid]
    rw [he]
    calc
      _ ≤ |(1+z^2)*planeDot ξ (graphDerivative s v w)| +
          |planeDot ξ (quarterTurn e+z • e)| := abs_sub _ _
      _ ≤ (t^2)*S+t*S := by
        rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1+z^2),← ht2]
        exact add_le_add (mul_le_mul_of_nonneg_left hderiv (sq_nonneg _)) herr
      _ = _ := by ring
  rw [graph_direction_transverse,abs_mul,abs_of_pos (inv_pos.mpr ht)]
  change t⁻¹ * |planeDot (quarterTurn ξ-z • ξ) v| ≤ 5*S
  have hmul := mul_le_mul_of_nonneg_left htrans (inv_nonneg.mpr ht.le)
  have he : t⁻¹*((t^2+t)*S) = (t+1)*S := by field_simp
  rw [he] at hmul
  exact hmul.trans (by dsimp [t] at *; nlinarith)

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Potential
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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Ledger
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleBumpScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function
open scoped ContDiff Topology

theorem angleBump_scale (η : ℝ) (hη : 0 < η) (x : ℝ) :
    angleBump η hη x = angleBump 1 zero_lt_one (η⁻¹*x) := by
  rw [ContDiffBump.apply,ContDiffBump.apply]
  simp only [angleBump,smul_eq_mul,sub_zero]
  congr 1 <;> field_simp

theorem angleBump_integral_scale (η : ℝ) (hη : 0 < η) :
    (∫ x : ℝ, angleBump η hη x) = η*(∫ x : ℝ, angleBump 1 zero_lt_one x) := by
  simp_rw [angleBump_scale η hη]
  rw [Measure.integral_comp_mul_left]
  simp [abs_of_pos hη,smul_eq_mul]

theorem angleBump_normed_scale (η : ℝ) (hη : 0 < η) (x : ℝ) :
    (angleBump η hη).normed volume x =
      η⁻¹*(angleBump 1 zero_lt_one).normed volume (η⁻¹*x) := by
  rw [ContDiffBump.normed_def,angleBump_scale,angleBump_integral_scale,ContDiffBump.normed_def]
  ring

theorem angleBump_normed_iteratedDeriv (η : ℝ) (hη : 0 < η) (j : ℕ) (x : ℝ) :
    iteratedDeriv j ((angleBump η hη).normed volume) x =
      η⁻¹*(η⁻¹)^j*iteratedDeriv j ((angleBump 1 zero_lt_one).normed volume) (η⁻¹*x) := by
  have he : (angleBump η hη).normed volume = fun x =>
      η⁻¹*(angleBump 1 zero_lt_one).normed volume (η⁻¹*x) := funext (angleBump_normed_scale η hη)
  rw [he,iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (angleBump 1 zero_lt_one).contDiff_normed]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleMaskDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem compactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j f) := by
  induction j with
  | zero => simpa using hf
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem iteratedDeriv_convolution_left {f g : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) (hg : LocallyIntegrable g volume)
    (j : ℕ) :
    iteratedDeriv j (f ⋆[lsmul ℝ ℝ,volume] g) =
      iteratedDeriv j f ⋆[lsmul ℝ ℝ,volume] g := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,ih]
    have hd : ContDiff ℝ 1 (iteratedDeriv j f) :=
      (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp
        (hf.of_le (by exact_mod_cast (le_top : (j+1:ℕ∞) ≤ ⊤)) : ContDiff ℝ (j+1:ℕ) f)).2
    funext x
    simpa only [iteratedDeriv_succ] using
      ((compactSupport_iteratedDeriv hfc j).hasDerivAt_convolution_left
        (lsmul ℝ ℝ) hd hg x).deriv

theorem angleDerivativeConstant_nonneg (j : ℕ) : 0 ≤ angleDerivativeConstant j :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem angleBump_derivative_L1 (η : ℝ) (hη : 0 < η) (j : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv j ((angleBump η hη).normed volume) x‖) =
      (η⁻¹)^j*angleDerivativeConstant j := by
  simp_rw [angleBump_normed_iteratedDeriv η hη j,norm_mul,Real.norm_eq_abs,abs_pow,
    abs_inv,abs_of_pos hη]
  rw [integral_const_mul,Measure.integral_comp_inv_mul_left
    (fun y : ℝ => |iteratedDeriv j ((angleBump 1 zero_lt_one).normed volume) y|) η]
  simp only [abs_of_pos hη,smul_eq_mul,angleDerivativeConstant,Real.norm_eq_abs]
  field_simp

theorem smoothAngleMask_derivative_bound (G : Set ℝ) (η : ℝ) (hη : 0 < η) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (smoothAngleMask G η hη) x‖ ≤
      (η⁻¹)^j*angleDerivativeConstant j := by
  rw [smoothAngleMask,iteratedDeriv_convolution_left
    (angleBump η hη).hasCompactSupport_normed (angleBump η hη).contDiff_normed
    (thickenedIndicator_locallyIntegrable G η),← angleBump_derivative_L1 η hη j]
  apply norm_integral_le_of_norm_le
  · exact (ContDiff.continuous_iteratedDeriv' j (angleBump η hη).contDiff_normed).integrable_of_hasCompactSupport
      (compactSupport_iteratedDeriv (angleBump η hη).hasCompactSupport_normed j) |>.norm
  · filter_upwards [] with t
    simp only [lsmul_apply,smul_eq_mul,norm_mul]
    have hb := thickenedIndicator_bounds G η (x-t)
    simp only [Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)).trans_eq (mul_one _)

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

theorem sourceTestMask_derivatives (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (sourceTestMask G d hd) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(d⁻¹)^j := by
  apply (smoothAngleMask_derivative_bound _ _ _ _ _).trans_eq
  rw [inv_div,div_eq_mul_inv,mul_pow]
  ring

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

theorem circleTestMask_angular_contDiff (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (fun θ => circleTestMask G d hd (sourceUnitDirection θ)) := by
  simpa only [circleTestMask_comp] using sourceTestMask_contDiff G d hd

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialAnchorMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem spatialAnchorMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection θ)) := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    simpa only [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx] using circleTestMask_angular_contDiff (G P) d hd
  · push Not at hx
    simp only [spatialAnchorMask_zero Q ρ n G d hd hx]
    exact contDiff_const

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

 theorem iteratedDeriv_product_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) (c : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (J : ℕ) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ n ≤ J, ∀ x, ‖iteratedDeriv n (f i) x‖ ≤ c i * d^n) :
    ∀ j ≤ J, ∀ x, ‖iteratedDeriv j (fun x => ∏ i ∈ S, f i x) x‖ ≤
      (∏ i ∈ S, c i) * ((S.card:ℝ)*d)^j := by
  induction S using Finset.induction_on with
  | empty =>
    intro j hj x
    cases j with
    | zero => simp
    | succ j => simp [iteratedDeriv_const]
  | @insert a S ha ih =>
    have hcS : ∀ i ∈ S, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hfS : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbS := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ih := ih hcS hfS hbS
    intro j hj x
    have hfa : ContDiffAt ℝ j (f a) x :=
      ((hf a (Finset.mem_insert_self _ _)).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    have hfp : ContDiffAt ℝ j (fun x => ∏ i ∈ S, f i x) x :=
      ((contDiff_prod fun i hi => hfS i hi).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    rw [iteratedDeriv_fun_mul hfa hfp]
    calc
      _ ≤ ∑ k ∈ Finset.range (j+1),
          (j.choose k:ℝ) * (c a*d^k) * ((∏ i ∈ S, c i)*((S.card:ℝ)*d)^(j-k)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simp only [norm_mul, Real.norm_natCast]
        have hca := hc a (Finset.mem_insert_self _ _)
        gcongr
        · exact hb a (Finset.mem_insert_self _ _) k (hk.trans hj) x
        · exact ih (j-k) ((Nat.sub_le _ _).trans hj) x
      _ = (c a * ∏ i ∈ S, c i) * (d+(S.card:ℝ)*d)^j := by
        rw [add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by congr 2; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMaskSymmetry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem spatialAnchorMask_derivative_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection φ)) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(d⁻¹)^j := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    simpa only [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx,circleTestMask_comp] using
      sourceTestMask_derivatives (G P) d hd j θ
  · push Not at hx
    simp only [spatialAnchorMask_zero Q ρ n G d hd hx,iteratedDeriv_fun_const_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (angleDerivativeConstant_nonneg j)) (by positivity)

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

theorem symbolDerivativeConstant_one_le (B : ℕ) : 1 ≤ symbolDerivativeConstant B := by
  have : 0 ≤ ∑ n ∈ Finset.range (B+1), (100:ℝ)^n * angleDerivativeConstant n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (angleDerivativeConstant_nonneg n)
  unfold symbolDerivativeConstant
  linarith

theorem symbolDerivativeConstant_dominates {B n : ℕ} (hn : n ≤ B) :
    (100:ℝ)^n * angleDerivativeConstant n ≤ symbolDerivativeConstant B := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (B+1)) =>
      mul_nonneg (by positivity : 0 ≤ (100:ℝ)^i) (angleDerivativeConstant_nonneg i))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  unfold symbolDerivativeConstant
  linarith

theorem iteratedDeriv_shift (f : ℝ → ℝ) (j k : ℕ) :
    iteratedDeriv j (iteratedDeriv k f) = iteratedDeriv (j+k) f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ,ih,Nat.succ_add,iteratedDeriv_succ]

theorem smooth_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

 theorem normalizedMaskFactor_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (d : ℝ) (k : ℕ) : ContDiff ℝ ∞ (normalizedMaskFactor w d k) :=
  contDiff_const.mul (smooth_iteratedDeriv hw k)

 theorem normalizedMaskFactor_support (w : ℝ → ℝ) (d : ℝ) (k : ℕ) :
    tsupport (normalizedMaskFactor w d k) ⊆ tsupport w :=
  tsupport_mul_subset_right.trans (iteratedDeriv_tsupport k)

 theorem normalizedMaskFactor_derivative_bound {w : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hzero : ∀ θ, ‖w θ‖ ≤ 1)
    (hall : ∀ n θ, ‖iteratedDeriv n w θ‖ ≤
      ((100:ℝ)^n*angleDerivativeConstant n)*(d⁻¹)^n)
    {B k j : ℕ} (hkj : k+j ≤ B) (θ : ℝ) :
    ‖iteratedDeriv j (normalizedMaskFactor w d k) θ‖ ≤
      (symbolDerivativeConstant B)^k * (symbolDerivativeConstant B*d⁻¹)^j := by
  have hA := symbolDerivativeConstant_one_le B
  have hA0 : 0 ≤ symbolDerivativeConstant B := le_trans zero_le_one hA
  unfold normalizedMaskFactor
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_shift]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_pos hd]
  by_cases hz : j+k = 0
  · have hj : j = 0 := by omega
    have hk : k = 0 := by omega
    subst j; subst k
    simpa only [Nat.zero_add,pow_zero,one_mul,mul_one,iteratedDeriv_zero,Real.norm_eq_abs] using hzero θ
  · have hbudget : j+k ≤ B := by omega
    have hC : (100:ℝ)^(j+k)*angleDerivativeConstant (j+k) ≤
        symbolDerivativeConstant B^(j+k) := by
      apply (symbolDerivativeConstant_dominates hbudget).trans
      exact le_self_pow₀ hA (by omega)
    calc
      _ ≤ d^k * (((100:ℝ)^(j+k)*angleDerivativeConstant (j+k))*(d⁻¹)^(j+k)) :=
        mul_le_mul_of_nonneg_left (hall (j+k) θ) (by positivity)
      _ ≤ d^k * (symbolDerivativeConstant B^(j+k)*(d⁻¹)^(j+k)) := by gcongr
      _ = _ := by
        rw [pow_add,pow_add,mul_pow]
        have he : d^k*(d⁻¹)^k = 1 := by rw [← mul_pow,mul_inv_cancel₀ hd.ne',one_pow]
        calc
          _ = (d^k*(d⁻¹)^k) * (symbolDerivativeConstant B)^k *
              (symbolDerivativeConstant B)^j * (d⁻¹)^j := by ring
          _ = _ := by rw [he]; ring

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

 theorem descriptorAngleMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) :
    ContDiff ℝ ∞ (descriptorAngleMask Q ρ m N lam sig J i b x) :=
  spatialAnchorMask_contDiff Q hQ _ _ _ _ _ _

 theorem descriptorAngleMask_norm_le_one (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (θ : ℝ) :
    ‖descriptorAngleMask Q ρ m N lam sig J i b x θ‖ ≤ 1 := by
  have hb := descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x (sourceUnitDirection θ)
  simpa only [descriptorAngleMask,Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2

 theorem descriptorAngleMask_derivatives (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (descriptorAngleMask Q ρ m N lam sig J i b x) θ‖ ≤
      ((100:ℝ)^j*angleDerivativeConstant j)*(sourceAngularRadius N sig (descriptorLength b))⁻¹^j :=
  spatialAnchorMask_derivative_bound Q hQ _ _ _ _ _ _ _ _

 theorem inheritedMaskProduct_support {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane) {a : ι} (ha : a ∈ S) (j : ℕ) :
    tsupport (iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x)) ⊆
      tsupport (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a)) :=
  (product_iteratedDeriv_support S _ ha j).trans (normalizedMaskFactor_support _ _ _)

 theorem inheritedMaskProduct_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane)
    (K j : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (D : ℝ) (hD : 0 ≤ D)
    (hscale : ∀ a ∈ S, (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹ ≤ D)
    (θ : ℝ) :
    ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x) θ‖ ≤
      symbolDerivativeConstant (K+j)^(K+j) * ((S.card:ℝ)*D)^j := by
  let A := symbolDerivativeConstant (K+j)
  have hA : 1 ≤ A := symbolDerivativeConstant_one_le _
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hk (a : ι) (ha : a ∈ S) : k a ≤ K :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha).trans hK
  have hh := iteratedDeriv_product_bound S
    (fun a => normalizedMaskFactor (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a))
      (sourceAngularRadius N sig (descriptorLength (b a))) (k a))
    (fun a => A^(k a)) (A*D) (mul_nonneg hA0 hD) j
    (fun _ _ => pow_nonneg hA0 _) (fun a _ => normalizedMaskFactor_contDiff
      (descriptorAngleMask_contDiff Q hQ ρ m N lam sig J i (b a) (x a)) _ _)
    (fun a ha n hn θ => (normalizedMaskFactor_derivative_bound (sourceAngularRadius_pos _ _ _)
      (descriptorAngleMask_norm_le_one Q hQ ρ m N lam sig J i (b a) (x a))
      (descriptorAngleMask_derivatives Q hQ ρ m N lam sig J i (b a) (x a))
      (Nat.add_le_add (hk a ha) hn) θ).trans (by
        change A^(k a)*(A*_ )^n ≤ _
        have hp := sourceAngularRadius_pos N sig (descriptorLength (b a))
        gcongr
        exact hscale a ha)) j le_rfl θ
  change ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x) θ‖ ≤ _ at hh
  apply hh.trans
  rw [Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ A^K * ((S.card:ℝ)*(A*D))^j := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hK) (by positivity)
    _ = A^(K+j)*((S.card:ℝ)*D)^j := by rw [pow_add,mul_pow,mul_pow]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_AnchorSymbolDropping
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem inheritedMaskProduct_zero_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (θ : ℝ) :
    ‖inheritedMaskProduct S b k Q ρ m N lam sig J i x θ‖ ≤ symbolDerivativeConstant K^K := by
  let D := ∑ a ∈ S, (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹
  have hp a : 0 ≤ (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹ :=
    inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => hp a)
  have hh := inheritedMaskProduct_bound S b k Q hQ ρ m N lam sig J i x K 0 hK D hD
    (fun a ha => Finset.single_le_sum (fun a _ => hp a) ha) θ
  simpa using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_InheritedSymbolMeasurability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped ContDiff Topology

 theorem spatialAnchorMask_derivative_formula (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection φ)) θ =
      ∑ P ∈ occupiedAnchorPaths Q ρ n,
        if x ∈ (Q.descendant P).carrier then iteratedDeriv j (sourceTestMask (G P) d hd) θ else 0 := by
  classical
  unfold spatialAnchorMask
  simp only [circleTestMask_comp]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro P _
    by_cases hx : x ∈ (Q.descendant P).carrier <;> simp [hx]
  · intro P _
    by_cases hx : x ∈ (Q.descendant P).carrier
    · simp only [hx, ↓reduceIte]
      exact ((sourceTestMask_contDiff (G P) d hd).of_le
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    · simp only [hx, ↓reduceIte]
      exact contDiffAt_const

 theorem measurable_spatialAnchorMask_derivative (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (j : ℕ) :
    Measurable (fun z : Plane × UnitCircle =>
      iteratedDeriv j (fun φ => spatialAnchorMask Q ρ n G d hd z.1 (sourceUnitDirection φ)) (sourceAngle z.2)) := by
  simp only [spatialAnchorMask_derivative_formula]
  apply Finset.measurable_sum
  intro P _
  apply Measurable.ite ((Q.descendant P).measurable.preimage measurable_fst) _ measurable_const
  exact ((smooth_iteratedDeriv (sourceTestMask_contDiff (G P) d hd) j).continuous.measurable.comp
    measurable_sourceAngle).comp measurable_snd

 theorem measurable_inheritedCircleSymbol {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (hh : Measurable h) :
    Measurable (fun z : Plane × UnitCircle => inheritedCircleSymbol S b k Q ρ m N lam sig J i h z.1 z.2) := by
  unfold inheritedCircleSymbol
  apply (hh.comp measurable_fst).mul
  apply Complex.measurable_ofReal.comp
  apply Finset.measurable_prod
  intro a _
  apply measurable_const.mul
  exact measurable_spatialAnchorMask_derivative Q ρ _ _ _ _ (k a)

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

theorem eligible_label_good_direction {ρ : Measure Plane} {X : Set Plane}
    (hX : MeasurableSet X) {b : Plane → UnitCircle → ℂ} {n j : ℕ}
    (h : AngularLabelEligible ρ X b n j) (G : Set UnitCircle)
    (hG : ∀ x ∈ X, ∀ ω, b x ω ≠ 0 → ω ∈ G) :
    ∃ ω ∈ tsupport (circleAngularBin n j), ω ∈ G := by
  obtain ⟨ω,hω,x,hx,hb,hgood⟩ := eligible_label_witness hX h (fun _ ω => ω ∈ G)
    (fun ω => by filter_upwards [ae_restrict_mem hX] with x hx; exact hG x hx ω)
  exact ⟨ω,hω,hgood⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphCoordinateInverse
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem quarterTurn_smul (r : ℝ) (v : Plane) : quarterTurn (r • v) = r • quarterTurn v := by
  ext i
  fin_cases i <;> simp [quarterTurn]

theorem graph_chart_endpoints (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) : u = graphB (graphChartZ u v) (u+v) ∧
      v = graphA (graphChartZ u v) (u+v) := by
  have hd := graph_chart_difference u v hu hv hw
  constructor
  · rw [graphB, ← hd, smul_add, smul_sub]
    module
  · rw [graphA, ← hd, smul_sub, smul_add, smul_sub]
    module

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphKernelBounds
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem inheritedCircleSymbol_norm_le {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Plane → ℂ) (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K)
    (x : Plane) (hx : ‖h x‖ ≤ 1) (ω : UnitCircle) :
    ‖inheritedCircleSymbol S b k Q ρ m N lam sig J i h x ω‖ ≤
      symbolDerivativeConstant K^K := by
  classical
  simp only [inheritedCircleSymbol, norm_mul, Complex.norm_real]
  exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans
    (by simpa using (inheritedMaskProduct_zero_bound S b k Q hQ ρ m N lam sig J i
      (fun _ => x) K hK (sourceAngle ω)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphInheritedTransformChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem continuous_supported_bump_bound {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |Ψ t| ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (1/4:ℝ) 4)).exists_bound_of_continuousOn
    hΨ.continuousOn
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t
  by_cases hz : Ψ t = 0
  · simp only [hz, abs_zero]; exact le_max_left _ _
  · exact (hC t (Ioo_subset_Icc_self (hsupp t hz))).trans (le_max_right _ _)

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

theorem graphDirection_chart_endpoint (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : u+v ≠ 0) : graphDirection (graphChartZ u v) (graphChartAxis u v) = u := by
  have he := (graph_chart_endpoints u v hu hv hw).1
  have hr := graph_chart_radius_identity u v hu hv hw
  have hp : (u+v)+graphChartZ u v • quarterTurn (u+v) = (2:ℝ) • u := by
    calc
      _ = (2:ℝ) • graphB (graphChartZ u v) (u+v) := by dsimp only [graphB]; module
      _ = _ := congrArg (fun x : Plane => (2:ℝ) • x) he.symm
  calc
    _ = ((Real.sqrt (1+(graphChartZ u v)^2))⁻¹ * ‖u+v‖⁻¹) •
        ((u+v)+graphChartZ u v • quarterTurn (u+v)) := by
      simp only [graphDirection,graphChartAxis,quarterTurn_smul]
      module
    _ = _ := by
      rw [hp,smul_smul,← mul_inv, mul_comm (Real.sqrt _) ‖u+v‖,hr]
      norm_num

theorem graphChartAxis_norm {u v : Plane} (h : u+v ≠ 0) : ‖graphChartAxis u v‖ = 1 := by
  rw [graphChartAxis,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem GraphSourceRepresentative.product_strip
    {plus : Bool} {axis θ : ℝ} {j k : ℕ} {q : UnitCircle × UnitCircle}
    (hq : GraphSourceRepresentative false plus axis θ j k q)
    (N : ℕ) (sig p : ℝ) (P : Fin 4 → DyadicSquare)
    (he : GraphRetainedEdge N sig p false plus P q) :
    |inner ℝ (quarterTurn (q.1:Plane)) ((P 0).center-(P 1).center)| ≤
      5*graphNonedgeThreshold N sig p := by
  have hn := graphSourceWeight_support_nondegenerate false plus axis (angularBinCount θ) j k hq.1
  change 1/2 ≤ ‖(q.1:Plane)+graphSourceSign false plus • (q.2:Plane)‖ at hn
  have hv := circle_sign_norm _ (graphSourceSign_cases false plus) q.2
  have hz := (graph_chart_nondegenerate_bound (q.1:Plane) _ q.1.property hv hn).1
  have hne : (q.1:Plane)+graphSourceSign false plus • (q.2:Plane) ≠ 0 :=
    norm_pos_iff.mp (by linarith)
  have hh := graph_product_strip (graphRepresentativeZ false plus q) (graphSourceSign false plus)
    (graphNonedgeThreshold N sig p) (graphRepresentativeAxis false plus q)
    ((P 0).center-(P 1).center) ((P 2).center-(P 3).center)
    (graphChartAxis_norm hne) (by unfold graphNonedgeThreshold; positivity) hz he.1
    (by rw [planeDot_eq_inner]; exact he.2 rfl)
  rw [graphRepresentativeZ,graphRepresentativeAxis,
    graphDirection_chart_endpoint _ _ q.1.property hv hne,planeDot_eq_inner] at hh
  exact hh

theorem graphRetainedProduct_reversal (N : ℕ) (sig p : ℝ) (plus : Bool)
    (P : Fin 4 → DyadicSquare) (q : UnitCircle × UnitCircle) :
    GraphRetainedEdge N sig p false plus ![P 1,P 0,P 3,P 2] q ↔
      GraphRetainedEdge N sig p false plus P q := by
  have hn (z s : ℝ) (u v : Plane) : graphA z (-u)+s • graphB z (-v) = -(graphA z u+s • graphB z v) := by
    ext l
    fin_cases l <;> simp [graphA,graphB,quarterTurn] <;> ring
  have hd (s : ℝ) (u v : Plane) : graphDerivative s (-u) (-v) = -graphDerivative s u v := by
    ext l
    fin_cases l <;> simp [graphDerivative,quarterTurn] <;> ring
  simp only [GraphRetainedEdge,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [show (P 1).center-(P 0).center = -((P 0).center-(P 1).center) by abel,
    show (P 3).center-(P 2).center = -((P 2).center-(P 3).center) by abel]
  simp only [hn,hd,norm_neg,inner_neg_right,abs_neg]

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

theorem uniform_inherited_eligible_good_witness {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ),
    ∀ e ∈ S, ValidDescriptor N (d e) →
    ∀ A ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (d e)), ∀ n j : ℕ,
    AngularLabelEligible ρ (Q.descendant A).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) n j →
    ∃ dir ∈ tsupport (circleAngularBin n j),
      dir ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) A (d e) := by
  obtain ⟨N₀,hgood⟩ := uniform_inheritedCircleSymbol_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i h e he hd A hA n j hel
  exact eligible_label_good_direction (Q.descendant A).measurable hel _
    (hgood N hN S d k Q hQ ρ m lam i h e he hd A hA)

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

theorem parallel_candidates_le_good_test
    (Q : DyadicSquare) (hQ : 0 < Q.side) (hQs : Q.side ≤ 1) (ρ : Measure Plane)
    (g p : ℕ) (A : CellPath) (hA : A.length = g) (S : Finset CellPath)
    (hS : S ⊆ occupiedAnchorPaths Q ρ p)
    (hparent : ∀ c ∈ S, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier)
    (z : Plane) (u : UnitCircle) {θ b W threshold : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 2*Real.pi)
    (j : ℕ) (hu : u ∈ tsupport (circleAngularBin (angularBinCount θ) j))
    (hstrip : ∀ c ∈ S, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ b)
    (hwidth : 2*b+(2/(2:ℝ)^g)*(4*θ) ≤ W) (hthreshold : 0 ≤ threshold)
    (hgood : ∀ c ∈ S, ∃ w ∈ tsupport (circleAngularBin (angularBinCount θ) j),
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
          (circleAngularBin_scale_diameter hθ hcap j hu hw)).trans hwidth
    have hcard : S.card ≤ parallelTestCount Q ρ g p c₀ W (w:Plane) := Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hcard).trans hgoodw
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa only [Finset.card_empty,Nat.cast_zero] using hthreshold

theorem uniform_inherited_parallel_candidates {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ), ∀ e ∈ S, ∀ g p : ℕ,
    d e = .parallel g p → g ≤ p → p ≤ N →
    ∀ A : CellPath, A.length = g → ∀ C : Finset CellPath,
    C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier) →
    ∀ (z : Plane) (u : UnitCircle) (θ b : ℝ), 0 < θ → θ ≤ 2*Real.pi →
    ∀ j : ℕ, u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ b) →
    2*b+(2/(2:ℝ)^g)*(4*θ) ≤ sourceAngularWidth N sig J (i+1) p →
    (∀ c ∈ C, AngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) g p+2000*(lam+sig)) := by
  obtain ⟨N₀,hgood⟩ := uniform_inherited_eligible_good_witness hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i h e he g p hd hgp hp A hA C hC hparent
    z u θ b hθ hcap j hu hstrip hwidth hel
  apply parallel_candidates_le_good_test Q (by rw [hQ]; norm_num) hQ.le ρ g p A hA C hC hparent
    z u hθ hcap j hu hstrip hwidth (by positivity)
  intro c hc
  have hh := hgood N hN S d k Q hQ ρ m lam i h e he (by simpa only [hd,ValidDescriptor] using And.intro hgp hp)
    c (by simpa only [hd,descriptorAnchor] using hC hc) (angularBinCount θ) j (hel c hc)
  simpa only [hd,descriptorGoodSet] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductCandidateWidth
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
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

theorem uniform_inherited_product_group_count {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ), i < J → ∀ h : Plane → ℂ, ∀ e ∈ S, ∀ a g p : ℕ,
    d e = .parallel g p → a ≤ g → g ≤ p → p ≤ N →
    ∀ A : CellPath, A.length = g → ∀ C : Finset CellPath,
    C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, (Q.descendant c).carrier ⊆ (Q.descendant A).carrier) →
    ∀ (z : Plane) (u : UnitCircle) (c₀ : ℝ), 0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    ∀ j : ℕ, u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ 5*graphNonedgeThreshold N sig p) →
    (∀ c ∈ C, AngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) g p+2000*(lam+sig)) := by
  obtain ⟨N₁,hcount⟩ := uniform_inherited_parallel_candidates hsig hJ
  obtain ⟨N₂,hwidth⟩ := uniform_product_candidate_width hsig
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a g p hd hag hgp hp A hA C hC hparent z u c₀ hc hcap
  dsimp only
  intro j hu hstrip hel
  exact hcount N ((le_max_left _ _).trans hN) S d k Q hQ ρ m lam i h e he g p hd hgp hp A hA C hC hparent
    z u _ (5*graphNonedgeThreshold N sig p) (graphAngularScale_pos N sig _ hc)
    ((min_le_left _ _).trans hcap) j hu hstrip
    (hwidth N ((le_max_right _ _).trans hN) a g p J i hag hJ hi c₀ hc) hel

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ProductPrefixCount
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem candidate_prefix_card_le {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (A : CellPath) (C : Finset CellPath) (hC : C ⊆ dyadicPaths p)
    (hparent : ∀ c ∈ C, c.take a = A) :
    (C.image (List.take g)).card ≤ 4^(g-a) := by
  classical
  have hsub : C.image (List.take g) ⊆ (dyadicPaths (g-a)).image (fun c => A++c) := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have hl := (mem_dyadicPaths _ _).mp (hC hc)
    refine Finset.mem_image.mpr ⟨(c.take g).drop a,?_,?_⟩
    · simp [mem_dyadicPaths,List.length_take,hl,hgp]
    · simpa only [List.take_take,Nat.min_eq_left hag,hparent c hc] using
        List.take_append_drop a (c.take g)
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (dyadicPaths_card_le (g-a)))

theorem candidate_card_le_prefix_groups {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (A : CellPath) (C : Finset CellPath) (hC : C ⊆ dyadicPaths p)
    (hparent : ∀ c ∈ C, c.take a = A) (b : ℝ) (hb : 0 ≤ b)
    (hgroup : ∀ G ∈ C.image (List.take g), ((prefixFiber C g G).card : ℝ) ≤ b) :
    (C.card : ℝ) ≤ (4:ℝ)^(g-a)*b := by
  classical
  have he : C.card = ∑ G ∈ C.image (List.take g), (prefixFiber C g G).card :=
    Finset.card_eq_sum_card_image (List.take g) C
  calc
    _ = ∑ G ∈ C.image (List.take g), ((prefixFiber C g G).card : ℝ) := by
      exact_mod_cast he
    _ ≤ ∑ _G ∈ C.image (List.take g), b := Finset.sum_le_sum hgroup
    _ = ((C.image (List.take g)).card : ℝ)*b := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast candidate_prefix_card_le hag hgp A C hC hparent) hb

theorem height_mono_start (m : ℕ → ℝ) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p) :
    height m g p ≤ height m a p := by
  obtain ⟨t,hgt,htp,he⟩ := intervalMin_attained m hgp
  have hh := intervalMin_le m (hag.trans hgt) htp
  unfold height
  rw [he]
  linarith

theorem coarse_prefix_power {a g N : ℕ} (hag : a ≤ g) {sig : ℝ}
    (hgap : (g:ℝ)-a ≤ 2*sig*N) : (4:ℝ)^(g-a) ≤ ((2:ℝ)^N)^(4*sig) := by
  have he : (4:ℝ)^(g-a) = (2:ℝ)^(2*((g:ℝ)-a)) := by
    rw [← Nat.cast_sub hag,show (4:ℝ) = 2^2 by norm_num,← pow_mul]
    norm_cast
  rw [he,← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

theorem uniform_inherited_product_candidate_count {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ), i < J → ∀ h : Plane → ℂ, ∀ e ∈ S, ∀ a g p : ℕ,
    d e = .parallel g p → a ≤ g → g ≤ p → p ≤ N → (g:ℝ)-a ≤ 2*sig*N →
    ∀ (A : CellPath) (C : Finset CellPath), C ⊆ occupiedAnchorPaths Q ρ p →
    (∀ c ∈ C, c.take a = A) →
    ∀ (z : Plane) (u : UnitCircle) (c₀ : ℝ), 0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    ∀ j : ℕ, u ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    (∀ c ∈ C, |inner ℝ (quarterTurn (u:Plane)) (z-(Q.descendant c).center)| ≤ 5*graphNonedgeThreshold N sig p) →
    (∀ c ∈ C, AngularLabelEligible ρ (Q.descendant c).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) (angularBinCount θ) j) →
    (C.card : ℝ) ≤ ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)+4*sig) := by
  obtain ⟨N₀,hcount⟩ := uniform_inherited_product_group_count hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a g p hd hag hgp hp hgap A C hC hparent z u c₀ hc hcap
  dsimp only
  intro j hu hstrip hel
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hpaths : C ⊆ dyadicPaths p := fun c hc => (Finset.mem_filter.mp (hC hc)).1
  have hb := candidate_card_le_prefix_groups hag hgp A C hpaths hparent
    (((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) g p+2000*(lam+sig))) (by positivity) (by
      intro G hG
      have hlen : G.length = g := by
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hG
        have hl := (mem_dyadicPaths _ _).mp (hpaths hc)
        simp [List.length_take,hl,hgp]
      exact hcount N hN S d k Q hQ ρ m lam i hi h e he a g p hd hag hgp hp G hlen
        (prefixFiber C g G) (fun c hc => hC (Finset.mem_filter.mp hc).1)
        (by
          intro c hc
          obtain ⟨hc,he⟩ := Finset.mem_filter.mp hc
          rw [← he]
          exact Q.descendant_subset_take hQpos c g)
        z u c₀ hc hcap j hu
        (fun c hc => hstrip c (Finset.mem_filter.mp hc).1)
        (fun c hc => hel c (Finset.mem_filter.mp hc).1))
  have hh : ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) g p+2000*(lam+sig)) ≤
      ((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
      (add_le_add (height_mono_start _ hag hgp) le_rfl)
  calc
    _ ≤ _ := hb
    _ ≤ ((2:ℝ)^N)^(4*sig)*((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)) :=
      mul_le_mul (coarse_prefix_power hag hgap) hh (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]; congr 1; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductPairDegree
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem product_pair_fiber_card (Q₁ Q₂ : DyadicSquare) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p false plus (productPairCells Q₁ Q₂ row c) q)
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
    change (F.card : ℝ) ≤ _
    rw [← hproj]
    apply graph_unit_center_fiber_card Q₂ hQ₂ N p hsig (F.image Prod.snd)
      (by
        intro b hb
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
        exact hlen c (Finset.mem_filter.mp hc).1)
      (Q₂.descendant c₀.2).center
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have h0 := (hedge c₀ (Finset.mem_filter.mp hc₀).1).1
    have h1 := (hedge c (Finset.mem_filter.mp hc).1).1
    have he : c.1 = c₀.1 := (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc₀).2.symm
    simp only [productPairCells,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1
    rw [he] at h1
    have hh := graphB_two_edges_close _ _ _ _ _ _ (graphSourceSign_cases false plus) h1 h0
    simpa only [dist_sub_left] using hh
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (F.card : ℝ) ≤ _
    rw [hz,Finset.card_empty,Nat.cast_zero]
    positivity

theorem product_pair_card_of_projection (Q₁ Q₂ : DyadicSquare) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p false plus (productPairCells Q₁ Q₂ row c) q)
    (b : ℝ) (hproj : ((C.image Prod.fst).card : ℝ) ≤ b) :
    (C.card : ℝ) ≤ b*(144*((2:ℝ)^N)^(60*sig)) := by
  classical
  have he := Finset.card_eq_sum_card_image Prod.fst C
  calc
    _ = ∑ P ∈ C.image Prod.fst, ((C.filter (fun c => c.1 = P)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _P ∈ C.image Prod.fst, 144*((2:ℝ)^N)^(60*sig) :=
      Finset.sum_le_sum (fun P _ => product_pair_fiber_card Q₁ Q₂ hQ₂ N p hsig plus q row C hlen hedge P)
    _ = ((C.image Prod.fst).card : ℝ)*(144*((2:ℝ)^N)^(60*sig)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hproj (by positivity)

theorem uniform_inherited_product_pair_degree {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q₁ Q₂ : DyadicSquare, Q₁.side = 1 → Q₂.side = 1 →
    ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ h : Plane → ℂ, ∀ e ∈ S, ∀ a g p : ℕ,
    d e = .parallel g p → a ≤ g → g ≤ p → p ≤ N → (g:ℝ)-a ≤ 2*sig*N →
    ∀ (A : CellPath) (row : CellPath × CellPath) (C : Finset (CellPath × CellPath)),
    (∀ c ∈ C, c.1 ∈ occupiedAnchorPaths Q₁ ρ p) →
    (∀ c ∈ C, c.1.take a = A) → (∀ c ∈ C, c.2 ∈ dyadicPaths p) →
    ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    ∀ (j b : ℕ) (plus : Bool) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative false plus 0 θ j b q →
    (∀ c ∈ C, GraphRetainedEdge N sig p false plus (productPairCells Q₁ Q₂ row c) q) →
    (∀ c ∈ C, AngularLabelEligible ρ (Q₁.descendant c.1).carrier
      (inheritedCircleSymbol S d k Q₁ ρ m N lam sig J i h) (angularBinCount θ) j) →
    (C.card : ℝ) ≤ 144*((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)+64*sig) := by
  obtain ⟨N₀,hcount⟩ := uniform_inherited_product_candidate_count hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q₁ Q₂ hQ₁ hQ₂ ρ m lam i hi h e he a g p hd hag hgp hp hgap A row C hC hparent hlen c₀ hc hcap
  dsimp only
  intro j b plus q hq hedge hel
  have hu := (graphSourceWeight_support_bins false plus 0 _ j b hq.1).1
  have hb := hcount N hN S d k Q₁ hQ₁ ρ m lam i hi h e he a g p hd hag hgp hp hgap
    A (C.image Prod.fst)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hC v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hparent v hv)
    (Q₁.descendant row.1).center q.1 c₀ hc hcap j hu
    (by
      intro c hc
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
      exact hq.product_strip N sig p (productPairCells Q₁ Q₂ row v) (hedge v hv))
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hel v hv)
  have hh := product_pair_card_of_projection Q₁ Q₂ hQ₂ N p hsig.le plus q row C hlen hedge _ hb
  refine hh.trans_eq ?_
  rw [mul_left_comm,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
  congr 2
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductMatrix
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceProductGraphIndices_path_data
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (A B : CellPath) (a n m : ℕ)
    (hA : A.length = a) (hB : B.length = a)
    {e : GraphNonedgeIndex}
    (he : e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    (l : Fin 4) :
    graphQuadPath e.1 l ∈ occupiedAnchorPaths (![Q₁,Q₁,Q₂,Q₂] l) (![ρ,ρ,ν,ν] l) (a+n) ∧
      (graphQuadPath e.1 l).take a = ![A,A,B,B] l := by
  classical
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  simp only [sourceProductRelativeIndices,Finset.mem_product] at hq
  have happ (Q : DyadicSquare) (μ : Measure Plane) (P c : CellPath)
      (hP : P.length = a) (hc : c ∈ occupiedAnchorPaths (Q.descendant P) μ n) :
      P++c ∈ occupiedAnchorPaths Q μ (a+n) ∧ (P++c).take a = P := by
    obtain ⟨hc,hpos⟩ := Finset.mem_filter.mp hc
    have hl := (mem_dyadicPaths _ _).mp hc
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨by simp [mem_dyadicPaths,hP,hl],by simpa only [DyadicSquare.descendant_append] using hpos⟩
    · simp [hP]
  fin_cases l
  · exact happ Q₁ ρ A q.1.1.1 hA hq.1.1.1
  · exact happ Q₁ ρ A q.1.1.2 hA hq.1.1.2
  · exact happ Q₂ ν B q.1.2.1 hB hq.1.2.1
  · exact happ Q₂ ν B q.1.2.2 hB hq.1.2.2

theorem productMatrix_cells (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath)
    (j b : ℕ) (plus : Bool) :
    graphQuadCells ![Q₁,Q₁,Q₂,Q₂] (productMatrixIndex row col j b plus).1 =
      productPairCells Q₁ Q₂ row col := by
  funext l
  fin_cases l <;> rfl

theorem productPairCells_reverse (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath) :
    productPairCells Q₁ Q₂ col row =
      ![productPairCells Q₁ Q₂ row col 1,productPairCells Q₁ Q₂ row col 0,
        productPairCells Q₁ Q₂ row col 3,productPairCells Q₁ Q₂ row col 2] := rfl

theorem productMatrixNeighbors_data
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n m N : ℕ) (sig : ℝ) (hA : A.length = a) (hB : B.length = a)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle)
    (I : Finset GraphNonedgeIndex)
    (hI : I ⊆ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B)
    (hret : ∀ e ∈ I, GraphRetainedEdge N sig (a+n) false e.2.2
      (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1) (rep e.2))
    (hel : ∀ e ∈ I, GraphProductIndexEligible ![ρ,ρ,ν,ν] ![Q₁,Q₁,Q₂,Q₂] ![β,β,γ,γ] m e)
    (j b : ℕ) (plus reverse : Bool) (row col : CellPath × CellPath)
    (hc : col ∈ productMatrixNeighbors I (a+n) j b plus reverse row) :
    col.1 ∈ occupiedAnchorPaths Q₁ ρ (a+n) ∧ col.1.take a = A ∧
    col.2 ∈ dyadicPaths (a+n) ∧
    GraphRetainedEdge N sig (a+n) false plus (productPairCells Q₁ Q₂ row col) (rep ((j,b),plus)) ∧
    AngularLabelEligible ρ (Q₁.descendant col.1).carrier β m j := by
  classical
  obtain ⟨hc,hi⟩ := Finset.mem_filter.mp hc
  have hlen := (Finset.mem_product.mp hc).2
  cases reverse
  · change productMatrixIndex row col j b plus ∈ I at hi
    have hp := sourceProductGraphIndices_path_data Q₁ Q₂ ρ ν A B a n m hA hB (hI hi) 1
    have hr := hret _ hi
    rw [productMatrix_cells] at hr
    exact ⟨hp.1,hp.2,hlen,hr,hel _ hi 1⟩
  · change productMatrixIndex col row j b plus ∈ I at hi
    have hp := sourceProductGraphIndices_path_data Q₁ Q₂ ρ ν A B a n m hA hB (hI hi) 0
    have hr := hret _ hi
    rw [productMatrix_cells,productPairCells_reverse] at hr
    have hr' := (graphRetainedProduct_reversal N sig (a+n) plus (productPairCells Q₁ Q₂ row col)
      (rep ((j,b),plus))).mp hr
    exact ⟨hp.1,hp.2,hlen,hr',hel _ hi 0⟩

theorem sourceRetainedProductIndices_data
    (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (A B : CellPath) (a n m N : ℕ) (sig : ℝ)
    (rep : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle)
    {e : GraphNonedgeIndex}
    (he : e ∈ sourceRetainedProductIndices Q₁ Q₂ ρ ν β γ A B a n m N sig rep) :
    e ∈ sourceProductGraphIndices (Q₁.descendant A) (Q₂.descendant B) ρ ν n m A B ∧
    GraphRetainedEdge N sig (a+n) false e.2.2 (graphQuadCells ![Q₁,Q₁,Q₂,Q₂] e.1) (rep e.2) ∧
    GraphProductIndexEligible ![ρ,ρ,ν,ν] ![Q₁,Q₁,Q₂,Q₂] ![β,β,γ,γ] m e := by
  classical
  obtain ⟨he,hel⟩ := Finset.mem_filter.mp he
  obtain ⟨he,hr⟩ := Finset.mem_filter.mp he
  exact ⟨he,hr,hel⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductDegrees
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_actual_product_degrees {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q₁ Q₂ : DyadicSquare, Q₁.side = 1 → Q₂.side = 1 →
    ∀ (ρ ν : Measure Plane) (mass : ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ (h : Plane → ℂ) (γ : Plane → UnitCircle → ℂ), ∀ e ∈ S, ∀ a g n : ℕ,
    d e = .parallel g (a+n) → a ≤ g → g ≤ a+n → a+n ≤ N → (g:ℝ)-a ≤ 2*sig*N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    ∀ c₀ : ℝ, ∀ hc : 0 < c₀, ∀ hcap : c₀ ≤ 2*Real.pi,
    let θ := graphAngularScale N sig (((a+n:ℕ):ℝ)-a) c₀
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc) ((min_le_left _ _).trans hcap) false e.2 0 e.1.1 e.1.2
    let β := inheritedCircleSymbol S d k Q₁ ρ mass N lam sig J i h
    let I := sourceRetainedProductIndices Q₁ Q₂ ρ ν β γ A B a n (angularBinCount θ) N sig rep
    ∀ (j b : ℕ) (plus reverse : Bool) (row : CellPath × CellPath),
    ((activeProductMatrixNeighbors I (a+n) j b θ plus reverse row).card : ℝ) ≤
      144*((2:ℝ)^N)^(height (fun t : ℕ => mass t-(t:ℝ)/(N:ℝ)) a (a+n)+2000*(lam+sig)+64*sig) := by
  classical
  obtain ⟨N₀,hcount⟩ := uniform_inherited_product_pair_degree hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q₁ Q₂ hQ₁ hQ₂ ρ ν mass lam i hi h γ e he a g n hd hag hgp hp hgap A B hA hB c₀ hc hcap
  dsimp only
  let θ := graphAngularScale N sig (((a+n:ℕ):ℝ)-a) c₀
  let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc) ((min_le_left _ _).trans hcap) false e.2 0 e.1.1 e.1.2
  let β := inheritedCircleSymbol S d k Q₁ ρ mass N lam sig J i h
  let I := sourceRetainedProductIndices Q₁ Q₂ ρ ν β γ A B a n (angularBinCount θ) N sig rep
  intro j b plus reverse row
  change ((activeProductMatrixNeighbors I (a+n) j b θ plus reverse row).card : ℝ) ≤ _
  by_cases hs : (tsupport (graphSourceWeight false plus 0 (angularBinCount θ) j b)).Nonempty
  · rw [activeProductMatrixNeighbors,ite_eq_left hs]
    have hq : GraphSourceRepresentative false plus 0 θ j b (rep ((j,b),plus)) := by
      rcases graphChosenRepresentative_spec (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc)
        ((min_le_left _ _).trans hcap) false plus 0 j b with hq | hn
      · exact hq
      · exact (hn hs).elim
    have hdata (col : CellPath × CellPath) (hc : col ∈ productMatrixNeighbors I (a+n) j b plus reverse row) :=
      productMatrixNeighbors_data Q₁ Q₂ ρ ν β γ A B a n (angularBinCount θ) N sig hA hB rep I
        (fun _ hi => (sourceRetainedProductIndices_data Q₁ Q₂ ρ ν β γ A B a n _ N sig rep hi).1)
        (fun _ hi => (sourceRetainedProductIndices_data Q₁ Q₂ ρ ν β γ A B a n _ N sig rep hi).2.1)
        (fun _ hi => (sourceRetainedProductIndices_data Q₁ Q₂ ρ ν β γ A B a n _ N sig rep hi).2.2)
        j b plus reverse row col hc
    exact hcount N hN S d k Q₁ Q₂ hQ₁ hQ₂ ρ mass lam i hi h e he a g (a+n) hd hag hgp hp hgap
      A row (productMatrixNeighbors I (a+n) j b plus reverse row)
      (fun c hc => (hdata c hc).1) (fun c hc => (hdata c hc).2.1)
      (fun c hc => (hdata c hc).2.2.1) c₀ hc hcap j b plus (rep ((j,b),plus)) hq
      (fun c hc => by simpa only [Nat.cast_add] using (hdata c hc).2.2.2.1) (fun c hc => (hdata c hc).2.2.2.2)
  · rw [activeProductMatrixNeighbors,ite_eq_right hs,Finset.card_empty,Nat.cast_zero]
    positivity

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductOccupiedVertices
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sourceProductVertices_card (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) :
    (sourceProductVertices Q₁ Q₂ ρ ν A B n).card =
      (occupiedAnchorPaths (Q₁.descendant A) ρ n).card*
      (occupiedAnchorPaths (Q₂.descendant B) ν n).card := by
  rw [sourceProductVertices,Finset.card_product]
  congr 1 <;> apply Finset.card_image_of_injective <;>
    intro c d he <;> exact List.append_cancel_left he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductEnergyTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem product_outer_norm (a p v c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    ‖((2:ℝ)^(2*(v-a))) • (c • z)‖ =
      ((2:ℝ)^(2*(p-a)))*c*‖((2:ℝ)^(2*(v-p))) • z‖ := by
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,
    abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-a))),
    abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-p)))]
  have he : (2:ℝ)^(2*(v-a)) = (2:ℝ)^(2*(p-a))*(2:ℝ)^(2*(v-p)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [he]
  ring

theorem product_energy_transfer (a p v c x E ε : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) (z : ℂ)
    (herror : ‖(x:ℂ) - ((2:ℝ)^(2*(v-a))) • (c • z)‖ ≤ ε)
    (hgraph : ‖((2:ℝ)^(2*(v-p))) • z‖ ≤ E) :
    x ≤ ((2:ℝ)^(2*(p-a)))*c*E+ε := by
  have hnorm := norm_add_le ((x:ℂ)-((2:ℝ)^(2*(v-a))) • (c • z))
    (((2:ℝ)^(2*(v-a))) • (c • z))
  rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx,
    product_outer_norm a p v c hc z] at hnorm
  have hh := mul_le_mul_of_nonneg_left hgraph
    (mul_nonneg (by positivity : 0 ≤ (2:ℝ)^(2*(p-a))) hc)
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductChildEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_product_H_child_sum
    {sig c₀ : ℝ} (hsig : 0 < sig) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) {J : ℕ} (hJ : 0 < J) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (i : ℕ) (h : Fin 2 → Plane → ℂ), i < J → (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ e ∈ S 0, ∀ g : ℕ, d 0 e = .parallel g (a+n) →
    a ≤ g → g ≤ a+n → (g:ℝ)-a ≤ 2*sig*N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 0) X.carrier
      (((2:ℝ)^N)^(-mass 0 a)) (β 0) z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 1) Y.carrier
      (((2:ℝ)^N)^(-mass 1 a)) (β 1) z.1 z.2
    let Uc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 0) ((Q 0).descendant P).carrier (M 0) (β 0) z.1 z.2
    let Vc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 1) ((Q 1).descendant P).carrier (M 1) (β 1) z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal ≤
      (2:ℝ)^(2*((a:ℝ)+n-a)) * graphProfileCoefficient N ![mass 0,mass 0,mass 1,mass 1] a (a+n) *
      (144*((2:ℝ)^N)^(height (fun t : ℕ => mass 0 t-(t:ℝ)/(N:ℝ)) a (a+n)+2000*(lam+sig)+64*sig)) *
      (∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
        (sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)).toReal) + ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₁,hgraph⟩ := uniform_actual_product_H_graph hsig hc hcap K lam T hΨ hpos hs
  obtain ⟨N₂,hdegree⟩ := uniform_actual_product_degrees hsig hJ
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hu ht hLu hv
    e he g hdesc hag hgp hgap A B' hA hB
  have hQpos : ∀ l, 0 < (Q l).side := fun l => by rw [hQ l]; norm_num
  have hQle : ∀ l, (Q l).side ≤ 1 := fun l => (hQ l).le
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  have hg := hgraph N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQpos hQle
    ρ mass B δ hd J i h hh hhb a n v hp hu ht hLu hv A B' hA hB
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let θ := graphAngularScale N sig (((a+n:ℕ):ℝ)-a) c₀
  let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc) ((min_le_left _ _).trans hcap) false e.2 0 e.1.1 e.1.2
  let I := sourceRetainedProductIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B' a n (angularBinCount θ) N sig rep
  have hdeg := hdegree N ((le_max_right _ _).trans hN) (S 0) (d 0) (k 0) (Q 0) (Q 1) (hQ 0) (hQ 1)
    (ρ 0) (ρ 1) (mass 0) lam i hi (h 0) (β 1) e he a g n hdesc hag hgp hp hgap A B' hA hB c₀ hc hcap
  have hIsub : I ⊆ sourceProductGraphIndices ((Q 0).descendant A) ((Q 1).descendant B')
      (ρ 0) (ρ 1) n (angularBinCount θ) A B' :=
    fun _ hmem => (sourceRetainedProductIndices_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmem).1
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQpos l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  have hbound := original_product_graph_integral_bound (Q 0) (Q 1) (ρ 0) (ρ 1) A B' a n hA hB
    (graphAngularScale_pos N sig (((a+n:ℕ):ℝ)-a) hc) I hIsub (by positivity) hdeg
    (M₁ := ((2:ℝ)^N)^(-mass 0 (a+n))) (M₂ := ((2:ℝ)^N)^(-mass 1 (a+n)))
    (by positivity) (by positivity) (β 0) (β 1) (hm 0) (hm 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K) (hb 0) (hb 1)
    v hΨ.continuous.measurable hpos hs hW (fun t => (le_abs_self _).trans (hw t))
  dsimp only at hg hbound ⊢
  simp only [Nat.cast_add,β,θ,rep,I,sourceRetainedProductIndices] at hg hbound ⊢
  refine ⟨hg.1,?_⟩
  have hcprof : 0 ≤ graphProfileCoefficient N ![mass 0,mass 0,mass 1,mass 1] a (a+n) :=
    Finset.prod_nonneg (fun _ _ => by positivity)
  have hresult := product_energy_transfer (a:ℝ) ((a:ℝ)+n) v _ _ _ _ hcprof
    ENNReal.toReal_nonneg _ hg.2 hbound
  simpa only [Nat.cast_add,β,θ,rep,I,sourceRetainedProductIndices,mul_assoc] using hresult

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProductOccupiedCount
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem occupied_parent_profile_count (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (N B : ℕ) (δ lam : ℝ) (mass : ℝ → ℝ)
    (hd : RegularizedProfileData Q ρ N B δ lam mass) (A : CellPath) (a n : ℕ)
    (hA : A.length = a) (hp : a+n ≤ N) :
    ((occupiedAnchorPaths (Q.descendant A) ρ n).card : ℝ) ≤
      64*((2:ℝ)^N)^(mass (a+n)-mass a+6*lam) := by
  classical
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hPpos := Q.descendant_side_pos hQpos A
  let C := occupiedAnchorPaths (Q.descendant A) ρ n
  have hsub : C.image (fun c => A++c) ⊆ occupiedCenterCells Q ρ (a+n) (Q.descendant A).center (3/(2:ℝ)^a) := by
    intro c hc
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hlen,hmass⟩ := Finset.mem_filter.mp hb
    have hl := (mem_dyadicPaths _ _).mp hlen
    apply Finset.mem_filter.mpr
    refine ⟨by simp [mem_dyadicPaths,hA,hl],?_,?_⟩
    · simpa only [DyadicSquare.descendant_append] using hmass
    · rw [mem_ball,DyadicSquare.descendant_append]
      have hdist := (Q.descendant A).dist_le hPpos.le
        ((Q.descendant A).descendant_subset hPpos b
          (((Q.descendant A).descendant b).center_mem ((Q.descendant A).descendant_side_pos hPpos b)))
        ((Q.descendant A).center_mem hPpos)
      have hside : (Q.descendant A).side = 1/(2:ℝ)^a := by
        rw [DyadicSquare.descendant_side,hA,hQ]
      rw [hside] at hdist
      apply hdist.trans_lt
      rw [mul_one_div]
      exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  have hinj : Function.Injective (fun c : CellPath => A++c) := fun _ _ hh => List.append_cancel_left hh
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hh := hd.packing a (a+n) (Nat.le_add_right a n) hp (Q.descendant A).center 3 (by norm_num)
  simp only [hQ] at hh
  norm_num at hh
  exact (by exact_mod_cast hcard : (C.card:ℝ) ≤ _).trans hh

theorem sourceProductVertices_profile_count
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) (N B : ℕ) (δ lam : ℝ) (m₁ m₂ : ℝ → ℝ)
    (hd₁ : RegularizedProfileData Q₁ ρ N B δ lam m₁)
    (hd₂ : RegularizedProfileData Q₂ ν N B δ lam m₂)
    (A B' : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B'.length = a) (hp : a+n ≤ N) :
    ((sourceProductVertices Q₁ Q₂ ρ ν A B' n).card:ℝ) ≤
      4096*((2:ℝ)^N)^(m₁ (a+n)-m₁ a+(m₂ (a+n)-m₂ a)+12*lam) := by
  rw [sourceProductVertices_card,Nat.cast_mul]
  have h1 := occupied_parent_profile_count Q₁ hQ₁ ρ N B δ lam m₁ hd₁ A a n hA hp
  have h2 := occupied_parent_profile_count Q₂ hQ₂ ν N B δ lam m₂ hd₂ B' a n hB hp
  apply (mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)).trans_eq
  rw [mul_mul_mul_comm,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
  norm_num
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ProductEnergyMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal NNReal

theorem finiteEnergyMaximum_nonneg {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) :
    0 ≤ finiteEnergyMaximum S E := NNReal.coe_nonneg _

theorem le_finiteEnergyMaximum {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) {i : ι} (hi : i ∈ S) :
    (E i).toReal ≤ finiteEnergyMaximum S E := by
  exact_mod_cast (Finset.le_sup (f := fun i => (E i).toNNReal) hi)

theorem sum_energy_le_maximum {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞) :
    (∑ i ∈ S, (E i).toReal) ≤ (S.card:ℝ)*finiteEnergyMaximum S E := by
  simpa only [Finset.sum_const,nsmul_eq_mul] using
    Finset.sum_le_sum (fun i hi => le_finiteEnergyMaximum S E hi)

theorem two_rpow_as_scale (N : ℕ) (hN : 0 < N) (t : ℝ) :
    (2:ℝ)^t = ((2:ℝ)^N)^(t/N) := by
  rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem product_profile_factor (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) (a p k : ℝ) (lam : ℝ) :
    (2:ℝ)^(2*(p-a))*graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p *
      (144*((2:ℝ)^N)^k) * (4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) =
    589824*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+k+12*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [two_rpow_as_scale N hN]
  simp only [graphProfileCoefficient,Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,← Real.rpow_sub hR]
  have he (x y z w t : ℝ) : x*(y*y*z*z)*(144*w)*(4096*t) = 589824*(x*y*y*z*z*w*t) := by ring
  rw [he]
  simp only [← Real.rpow_add hR]
  congr 2
  ring

theorem product_profile_sum_bound {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞)
    (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) (a p k lam : ℝ)
    (hcard : (S.card:ℝ) ≤ 4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) :
    (2:ℝ)^(2*(p-a))*graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p *
      (144*((2:ℝ)^N)^k) * (∑ i ∈ S, (E i).toReal) ≤
    589824*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+k+12*lam) *
      finiteEnergyMaximum S E := by
  have hs := (sum_energy_le_maximum S E).trans
    (mul_le_mul_of_nonneg_right hcard (finiteEnergyMaximum_nonneg S E))
  have hc : 0 ≤ graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p :=
    Finset.prod_nonneg (fun _ _ => by positivity)
  apply (mul_le_mul_of_nonneg_left hs (by positivity :
    0 ≤ (2:ℝ)^(2*(p-a))*graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p * (144*((2:ℝ)^N)^k))).trans_eq
  rw [← mul_assoc,product_profile_factor N hN]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualProductEstimate
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_product_estimate_oai
    {sig c₀ : ℝ} (hsig : 0 < sig) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 0 < J) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (i : ℕ) (h : Fin 2 → Plane → ℂ), i < J → (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ e ∈ S 0, ∀ g : ℕ, d 0 e = .parallel g (a+n) →
    a ≤ g → g ≤ a+n → (g:ℝ)-a ≤ 2*sig*N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 0) X.carrier
      (((2:ℝ)^N)^(-mass 0 a)) (β 0) z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 1) Y.carrier
      (((2:ℝ)^N)^(-mass 1 a)) (β 1) z.1 z.2
    let Uc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 0) ((Q 0).descendant P).carrier (M 0) (β 0) z.1 z.2
    let Vc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 1) ((Q 1).descendant P).carrier (M 1) (β 1) z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal ≤
      ((2:ℝ)^N)^(
        -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
        -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))
        +height (fun t : ℕ => mass 0 t-(t:ℝ)/(N:ℝ)) a (a+n)+4000*(lam+sig)+η) *
      finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n)
        (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) + ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₁,hchild⟩ := uniform_actual_product_H_child_sum hsig hc hcap K lam T hJ hΨ hpos hs
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hη (589824:ℝ)
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hu ht hLu hv
    e he g hdesc hag hgp hgap A B' hA hB
  have hNpos : 0 < N := (by omega : 0 < max 1 (max N₁ N₂)).trans_le hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hg := hchild N hN₁ S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hu ht hLu hv
    e he g hdesc hag hgp hgap A B' hA hB
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let E := fun row : CellPath × CellPath => sourceAngularH ((a:ℝ)+n) v Ψ
    (fun z => sourceAngularTransform (ρ 0) ((Q 0).descendant row.1).carrier
      (((2:ℝ)^N)^(-mass 0 (a+n))) (β 0) z.1 z.2)
    (fun z => sourceAngularTransform (ρ 1) ((Q 1).descendant row.2).carrier
      (((2:ℝ)^N)^(-mass 1 (a+n))) (β 1) z.1 z.2)
  let C := sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B' n
  let k0 := height (fun t : ℕ => mass 0 t-(t:ℝ)/(N:ℝ)) a (a+n)
  have hcount := sourceProductVertices_profile_count (Q 0) (Q 1) (hQ 0) (hQ 1)
    (ρ 0) (ρ 1) N B δ lam (mass 0) (mass 1) (hd 0) (hd 1) A B' a n hA hB hp
  have hmax := product_profile_sum_bound C E N hNpos (mass 0) (mass 1) a ((a:ℝ)+n)
    (k0+2000*(lam+sig)+64*sig) lam hcount
  let x := -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
    -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))
  have hpower : 589824*((2:ℝ)^N)^(x+(k0+2000*(lam+sig)+64*sig)+12*lam) ≤
      ((2:ℝ)^N)^(x+k0+4000*(lam+sig)+η) := by
    calc
      _ ≤ ((2:ℝ)^N)^η*((2:ℝ)^N)^(x+(k0+2000*(lam+sig)+64*sig)+12*lam) :=
        mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity)
      _ = ((2:ℝ)^N)^(η+(x+(k0+2000*(lam+sig)+64*sig)+12*lam)) :=
        (Real.rpow_add (by positivity : (0:ℝ)<(2:ℝ)^N) _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  have hmax' := hmax.trans (mul_le_mul_of_nonneg_right hpower (finiteEnergyMaximum_nonneg C E))
  dsimp only at hg ⊢
  refine ⟨hg.1,?_⟩
  apply hg.2.trans
  simpa only [C,E,β,k0,x] using add_le_add hmax' (le_refl (((2:ℝ)^N)^(-T)))

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_product_estimate_oai := @OAI.PlanarFalconer.uniform_actual_product_estimate_oai
