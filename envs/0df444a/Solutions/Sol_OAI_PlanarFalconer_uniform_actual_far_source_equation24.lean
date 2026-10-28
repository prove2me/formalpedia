-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_far_source_equation24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:29:37.338967+00:00
-- url     : https://prove2.me/submissions/8a18b054-21db-4478-9421-1d477d81320f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_comparable_shell_rebin
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_far_stationary_integrable
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_far_stationary_reduction

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
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
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

theorem measurable_stripCount {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) :
    Measurable (fun ω : Plane => stripCount S v W ω) := by
  classical
  have he : (fun ω : Plane => stripCount S v W ω) =
      fun ω => ∑ i ∈ S, if |planeDot (v i) ω| ≤ W then (1:ℕ) else 0 := by
    funext ω
    simp [stripCount]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_le _ measurable_const
  have hc : Continuous (fun ω : Plane => |planeDot (v i) ω|) := by
    unfold planeDot
    fun_prop
  exact hc.measurable

theorem continuous_quarterTurn : Continuous quarterTurn := by
  unfold quarterTurn
  fun_prop

theorem measurable_parallelGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W threshold : ℝ) : MeasurableSet (parallelGoodSet Q ρ g p P W threshold) := by
  apply measurableSet_le _ measurable_const
  apply (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
  exact (measurable_stripCount _ _ W).comp
    (continuous_quarterTurn.measurable.comp continuous_subtype_val.measurable)

theorem measurable_projectionGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W threshold : ℝ) : MeasurableSet (projectionGoodSet Q ρ p u P W threshold) := by
  apply measurableSet_le _ measurable_const
  apply (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
  exact (measurable_stripCount _ _ W).comp continuous_subtype_val.measurable

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem measurable_descriptorGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGoodSet Q ρ m N lam sig J i P b) := by
  cases b with
  | parallel g p => exact measurable_parallelGoodSet _ _ _ _ _ _ _
  | projection p u => exact measurable_projectionGoodSet _ _ _ _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFourMassBound
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graph_four_spatial_ae_carrier (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (hX : ∀ i, MeasurableSet (X i)) :
    ∀ᵐ x ∂Measure.pi (fun i => (ρ i).restrict (X i)), ∀ i, x i ∈ X i := by
  apply Filter.eventually_all.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem (hX i))

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

theorem sourceProductVertices_subset (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a) :
    sourceProductVertices Q₁ Q₂ ρ ν A B n ⊆ (dyadicPaths (a+n)) ×ˢ (dyadicPaths (a+n)) := by
  classical
  intro c hc
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hc
  obtain ⟨x,hx,hx'⟩ := Finset.mem_image.mp h1
  obtain ⟨y,hy,hy'⟩ := Finset.mem_image.mp h2
  have hlx := (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hx).1
  have hly := (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hy).1
  rw [Finset.mem_product,← hx',← hy']
  simp [mem_dyadicPaths,hA,hB,hlx,hly]

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularFarGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem dyadic_far_points (Q : DyadicSquare) (hQ : Q.side = 1)
    (p : ℕ) (P P' : CellPath) (hP : P.length = p) (hP' : P'.length = p)
    (hfar : 20/(2:ℝ)^p < dist (Q.descendant P).center (Q.descendant P').center)
    (x x' : Plane) (hx : x ∈ (Q.descendant P).carrier) (hx' : x' ∈ (Q.descendant P').carrier) :
    16/(2:ℝ)^p < dist x x' := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have h1 := (Q.descendant P).dist_le (Q.descendant_side_pos hQpos P).le
    ((Q.descendant P).center_mem (Q.descendant_side_pos hQpos P)) hx
  have h2 := (Q.descendant P').dist_le (Q.descendant_side_pos hQpos P').le hx'
    ((Q.descendant P').center_mem (Q.descendant_side_pos hQpos P'))
  rw [Q.descendant_side,hP,hQ,mul_one_div] at h1
  rw [Q.descendant_side,hP',hQ,mul_one_div] at h2
  have ht := (dist_triangle (Q.descendant P).center x (Q.descendant P').center).trans
    (add_le_add (le_refl _) (dist_triangle x x' (Q.descendant P').center))
  have he : 20/(2:ℝ)^p = 16/(2:ℝ)^p+2/(2:ℝ)^p+2/(2:ℝ)^p := by ring
  rw [he] at hfar
  linarith

theorem angular_far_displacement (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1) (p : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hc : col ∈ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (hfar : ¬ angularNear Q₁ Q₂ p row col)
    (x x' y y' : Plane) (hx : x ∈ (Q₁.descendant row.1).carrier)
    (hx' : x' ∈ (Q₁.descendant col.1).carrier) (hy : y ∈ (Q₂.descendant row.2).carrier)
    (hy' : y' ∈ (Q₂.descendant col.2).carrier) :
    16/(2:ℝ)^p < dist x x' ∨ 16/(2:ℝ)^p < dist y y' := by
  simp only [Finset.mem_product,mem_dyadicPaths] at hr hc
  unfold angularNear at hfar
  by_cases h1 : dist (Q₁.descendant row.1).center (Q₁.descendant col.1).center ≤ 20/(2:ℝ)^p
  · exact Or.inr (dyadic_far_points Q₂ hQ₂ p row.2 col.2 hr.2 hc.2
      (lt_of_not_ge (fun h2 => hfar ⟨h1,h2⟩)) y y' hy hy')
  · exact Or.inl (dyadic_far_points Q₁ hQ₁ p row.1 col.1 hr.1 hc.1 (lt_of_not_ge h1) x x' hx hx')

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DisplacementDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar dyadic selection for comparable positive displacements

The arithmetic is independent of dimension, angular energy and distance-set
estimates.
-/

namespace PlanarFalconer
open Set Metric

 theorem exists_displacement_depth {d : ℝ} (hd : 0 < d) :
    ∃ n : ℤ, (2:ℝ)^(-(n:ℝ)-1) < d ∧ d ≤ (2:ℝ)^(-(n:ℝ)) := by
  obtain ⟨m,hm⟩ := exists_mem_Ioc_zpow hd (by norm_num : (1:ℝ) < 2)
  refine ⟨-(m+1),?_,?_⟩
  · have he : -((-(m+1):ℤ):ℝ)-1 = (m:ℝ) := by push_cast; ring
    rw [he,Real.rpow_intCast]
    exact hm.1
  · have he : -((-(m+1):ℤ):ℝ) = ((m+1:ℤ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_intCast]
    exact hm.2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularLengthPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem measurable_angularLengthComparable : MeasurableSet angularLengthComparable := by
  change MeasurableSet ({x : Fin 4 → Plane | dist (x 0) (x 1) ≤ 2*dist (x 2) (x 3)} ∩
    {x | dist (x 2) (x 3) ≤ 2*dist (x 0) (x 1)})
  apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) (by fun_prop)

theorem measurable_angularLengthShell (b : ℕ) : MeasurableSet (angularLengthShell b) := by
  apply measurable_angularLengthComparable.inter
  change MeasurableSet ({x : Fin 4 → Plane |
    512*(2:ℝ)^(-(b:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3))} ∩
    {x | max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 1024*(2:ℝ)^(-(b:ℝ))})
  apply MeasurableSet.inter
  · exact measurableSet_lt measurable_const (by fun_prop)
  · exact measurableSet_le (by fun_prop) measurable_const

theorem angularLengthShell_disjoint : Pairwise fun b c =>
    Disjoint (angularLengthShell b) (angularLengthShell c) := by
  have horder (b c : ℕ) (hbc : b < c) :
      1024*(2:ℝ)^(-(c:ℝ)) ≤ 512*(2:ℝ)^(-(b:ℝ)) := by
    have he : (10:ℝ)-(c:ℝ) ≤ 9-(b:ℝ) := by
      have hh : (b:ℝ)+1 ≤ (c:ℝ) := by exact_mod_cast hbc
      linarith
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) he
    rw [sub_eq_add_neg,sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2),
      Real.rpow_add (by norm_num : (0:ℝ) < 2)] at hh
    norm_num at hh
    simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast] using hh
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro x hb hc
  rcases lt_or_gt_of_ne hbc with h | h
  · exact not_lt_of_ge (hc.2.2.trans (horder b c h)) hb.2.1
  · exact not_lt_of_ge (hb.2.2.trans (horder c b h)) hc.2.1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_AngularLengthShellCover
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem angularLengthShell_cover {x : Fin 4 → Plane} {a h : ℕ}
    (hc : x ∈ angularLengthComparable)
    (hupper : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)))
    (hfar : 16*(2:ℝ)^(-(h:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3))) :
    ∃ b ∈ Finset.Icc (a+9) (h+5), x ∈ angularLengthShell b := by
  let d := max (dist (x 0) (x 1)) (dist (x 2) (x 3))
  have hd : 0 < d := (by positivity : 0 < 16*(2:ℝ)^(-(h:ℝ))).trans hfar
  obtain ⟨n,hnlo,hnhi⟩ := exists_displacement_depth hd
  have hpow (k : ℝ) : (2:ℝ)^(k-(n:ℝ)-10) = (2:ℝ)^k*(2:ℝ)^(-((n:ℝ)+10)) := by
    rw [show k-(n:ℝ)-10 = k+(-((n:ℝ)+10)) by ring,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  have haexp : (2:ℝ)^(-(n:ℝ)-1) < (2:ℝ)^(1-(a:ℝ)) := by
    have he : (2:ℝ)^(1-(a:ℝ)) = 2*(2:ℝ)^(-(a:ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_one]
    rw [he]
    exact hnlo.trans_le hupper
  have hhexp : (2:ℝ)^(4-(h:ℝ)) < (2:ℝ)^(-(n:ℝ)) := by
    have he : (2:ℝ)^(4-(h:ℝ)) = 16*(2:ℝ)^(-(h:ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [he]
    exact hfar.trans_le hnhi
  have haR := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp haexp
  have hhR := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp hhexp
  have haZ : (a:ℤ)-2 < n := by exact_mod_cast (show (a:ℝ)-2 < (n:ℝ) by linarith)
  have hhZ : n < (h:ℤ)-4 := by exact_mod_cast (show (n:ℝ) < (h:ℝ)-4 by linarith)
  have hb0 : 0 ≤ n+10 := by omega
  let b := (n+10).toNat
  have hbZ : (b:ℤ) = n+10 := Int.toNat_of_nonneg hb0
  have hbR : (b:ℝ) = (n:ℝ)+10 := by exact_mod_cast hbZ
  refine ⟨b,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,hc,?_,?_⟩
  · have he : (2:ℝ)^(-(n:ℝ)-1) = 512*(2:ℝ)^(-(b:ℝ)) := by
      rw [hbR,show -(n:ℝ)-1 = 9-(n:ℝ)-10 by ring,hpow]
      norm_num
    rw [← he]
    exact hnlo
  · have he : (2:ℝ)^(-(n:ℝ)) = 1024*(2:ℝ)^(-(b:ℝ)) := by
      rw [hbR,show -(n:ℝ) = 10-(n:ℝ)-10 by ring,hpow]
      norm_num
    rw [← he]
    exact hnhi

theorem parent_cell_displacement_bound (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1) (a : ℕ) (A B : CellPath)
    (hA : A.length = a) (hB : B.length = a) (x : Fin 4 → Plane)
    (hx₀ : x 0 ∈ (Q₁.descendant A).carrier) (hx₁ : x 1 ∈ (Q₁.descendant A).carrier)
    (hx₂ : x 2 ∈ (Q₂.descendant B).carrier) (hx₃ : x 3 ∈ (Q₂.descendant B).carrier) :
    max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)) := by
  have h1 := (Q₁.descendant A).dist_le
    (Q₁.descendant_side_pos (by rw [hQ₁]; norm_num) A).le hx₀ hx₁
  have h2 := (Q₂.descendant B).dist_le
    (Q₂.descendant_side_pos (by rw [hQ₂]; norm_num) B).le hx₂ hx₃
  rw [Q₁.descendant_side,hA,hQ₁] at h1
  rw [Q₂.descendant_side,hB,hQ₂] at h2
  simp only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
    one_div] at *
  exact max_le h1 h2

theorem angular_far_max_displacement (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1) (h : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hc : col ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hfar : ¬ angularNear Q₁ Q₂ h row col) (x : Fin 4 → Plane)
    (hx₀ : x 0 ∈ (Q₁.descendant row.1).carrier) (hx₁ : x 1 ∈ (Q₁.descendant col.1).carrier)
    (hx₂ : x 2 ∈ (Q₂.descendant row.2).carrier) (hx₃ : x 3 ∈ (Q₂.descendant col.2).carrier) :
    16*(2:ℝ)^(-(h:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3)) := by
  have hh := angular_far_displacement Q₁ Q₂ hQ₁ hQ₂ h row col hr hc hfar
    (x 0) (x 1) (x 2) (x 3) hx₀ hx₁ hx₂ hx₃
  simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
    ← div_eq_mul_inv,lt_max_iff] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularLengthIntegralPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angular_comparable_shell_union (S : Set (Fin 4 → Plane)) (a h : ℕ)
    (hu : ∀ x ∈ S, max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)))
    (hf : ∀ x ∈ S, 16*(2:ℝ)^(-(h:ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3))) :
    S ∩ angularLengthComparable = ⋃ b ∈ Finset.Icc (a+9) (h+5), S ∩ angularLengthShell b := by
  ext x
  constructor
  · intro hx
    obtain ⟨b,hb,hs⟩ := angularLengthShell_cover hx.2 (hu x hx.1) (hf x hx.1)
    exact mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hb,hx.1,hs⟩⟩
  · intro hx
    obtain ⟨b,hx⟩ := mem_iUnion.mp hx
    obtain ⟨_,hx⟩ := mem_iUnion.mp hx
    exact ⟨hx.1,hx.2.1⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularOccupiedFarPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sourceProductVertices_parent (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) {row : CellPath × CellPath}
    (hr : row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n) :
    (Q₁.descendant row.1).carrier ⊆ (Q₁.descendant A).carrier ∧
    (Q₂.descendant row.2).carrier ⊆ (Q₂.descendant B).carrier := by
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hr
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp h1
  obtain ⟨d,_,hd⟩ := Finset.mem_image.mp h2
  rw [← hc,← hd,DyadicSquare.descendant_append,DyadicSquare.descendant_append]
  exact ⟨(Q₁.descendant A).descendant_subset (Q₁.descendant_side_pos hQ₁ A) c,
    (Q₂.descendant B).descendant_subset (Q₂.descendant_side_pos hQ₂ B) d⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularComparableCarrier
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angular_comparable_far_ae (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (h : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hc : col ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hfar : ¬ angularNear Q₁ Q₂ h row col) :
    ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict angularLengthComparable,
      4*(2:ℝ)^(-(h:ℝ)) ≤ ‖x 0-x 1‖ ∧ 4*(2:ℝ)^(-(h:ℝ)) ≤ ‖x 2-x 3‖ := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  have hae := graph_four_spatial_ae_carrier ρs X
    (by intro i; fin_cases i <;> exact DyadicSquare.measurable _)
  have haer : ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict angularLengthComparable,
      ∀ i, x i ∈ X i := ae_restrict_of_ae hae
  filter_upwards [haer,ae_restrict_mem measurable_angularLengthComparable] with x hx hcmp
  have hf := angular_far_max_displacement Q₁ Q₂ hQ₁ hQ₂ h row col hr hc hfar x
    (hx 0) (hx 1) (hx 2) (hx 3)
  have h1 : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*dist (x 0) (x 1) :=
    max_le (by simpa only [two_mul] using le_add_of_nonneg_right (dist_nonneg (x := x 0) (y := x 1))) hcmp.2
  have h2 : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*dist (x 2) (x 3) :=
    max_le hcmp.1 (by simpa only [two_mul] using le_add_of_nonneg_right (dist_nonneg (x := x 2) (y := x 3)))
  rw [← dist_eq_norm,← dist_eq_norm]
  constructor <;> linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-(h:ℝ))]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_ComparableIntegralPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angular_comparable_integral_partition (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a d : ℕ) (hA : A.length = a) (hB : B.length = a)
    (row col : CellPath × CellPath)
    (hr : row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d)
    (hc : col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d)
    (hfar : ¬ angularNear Q₁ Q₂ (a+d) row col)
    (F : (Fin 4 → Plane) → ℂ)
    (hF : IntegrableOn F angularLengthComparable (angularFourCellMeasure Q₁ Q₂ ρ ν row col)) :
    (∫ x in angularLengthComparable, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col) =
      ∑ b ∈ Finset.Icc (a+9) (a+d+5),
        ∫ x in angularLengthShell b, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
  have hp₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hp₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hparentr := sourceProductVertices_parent Q₁ Q₂ hp₁ hp₂ ρ ν A B d hr
  have hparentc := sourceProductVertices_parent Q₁ Q₂ hp₁ hp₂ ρ ν A B d hc
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  let μ := angularFourCellMeasure Q₁ Q₂ ρ ν row col
  let S : Set (Fin 4 → Plane) := {x | ∀ i, x i ∈ X i}
  have hX : ∀ i, MeasurableSet (X i) := by intro i; fin_cases i <;> exact DyadicSquare.measurable _
  have hS : MeasurableSet S := by
    convert MeasurableSet.iInter (fun i => (hX i).preimage (measurable_pi_apply i)) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [S]
  have hae : ∀ᵐ x ∂μ, x ∈ S := graph_four_spatial_ae_carrier ρs X hX
  have he (T : Set (Fin 4 → Plane)) : μ.restrict (S ∩ T) = μ.restrict T := by
    apply Measure.restrict_congr_set
    filter_upwards [hae] with x hx
    exact propext (and_iff_right hx)
  have hu : ∀ x ∈ S, max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*(2:ℝ)^(-(a:ℝ)) := by
    intro x hx
    exact parent_cell_displacement_bound Q₁ Q₂ hQ₁ hQ₂ a A B hA hB x
      (hparentr.1 (hx 0)) (hparentc.1 (hx 1)) (hparentr.2 (hx 2)) (hparentc.2 (hx 3))
  have hf : ∀ x ∈ S, 16*(2:ℝ)^(-((a+d:ℕ):ℝ)) < max (dist (x 0) (x 1)) (dist (x 2) (x 3)) := by
    intro x hx
    exact angular_far_max_displacement Q₁ Q₂ hQ₁ hQ₂ (a+d) row col
      (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a d hA hB hr)
      (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a d hA hB hc) hfar x
      (hx 0) (hx 1) (hx 2) (hx 3)
  have hint : (∫ x in S ∩ angularLengthComparable, F x ∂μ) =
      ∑ b ∈ Finset.Icc (a+9) (a+d+5), ∫ x in S ∩ angularLengthShell b, F x ∂μ := by
    rw [angular_comparable_shell_union S a (a+d) hu hf]
    apply integral_biUnion_finset
    · exact fun b _ => hS.inter (measurable_angularLengthShell b)
    · intro b _ c _ hbc
      exact (angularLengthShell_disjoint hbc).mono inter_subset_right inter_subset_right
    · intro b hb
      exact hF.mono_set (fun x hx => hx.2.1)
  simpa only [he] using hint

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ComparableContributionPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem angular_comparable_contribution_partition (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a d : ℕ) (hA : A.length = a) (hB : B.length = a)
    (v Ma₁ Ma₂ : ℝ) (F : (Fin 4 → Plane) → ℂ)
    (hF : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
      ¬ angularNear Q₁ Q₂ (a+d) row col →
      IntegrableOn F angularLengthComparable (angularFourCellMeasure Q₁ Q₂ ρ ν row col)) :
    angularComparableFarContribution Q₁ Q₂ ρ ν A B a d v Ma₁ Ma₂ F =
      ∑ b ∈ Finset.Icc (a+9) (a+d+5),
        (((2:ℝ)^(2*(v-a)))/(Ma₁^2*Ma₂^2)) •
          ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
            ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
              if ¬ angularNear Q₁ Q₂ (a+d) row col then
                ∫ x in angularLengthShell b, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
              else 0 := by
  unfold angularComparableFarContribution
  rw [← Finset.smul_sum]
  congr 1
  calc
    _ = ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B d,
          ∑ b ∈ Finset.Icc (a+9) (a+d+5),
            if ¬ angularNear Q₁ Q₂ (a+d) row col then
              ∫ x in angularLengthShell b, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
            else 0 := by
      apply Finset.sum_congr rfl
      intro row hr
      apply Finset.sum_congr rfl
      intro col hc
      by_cases hf : ¬ angularNear Q₁ Q₂ (a+d) row col
      · simp only [ite_eq_left hf]
        exact angular_comparable_integral_partition Q₁ Q₂ hQ₁ hQ₂ ρ ν A B a d hA hB row col hr hc hf F
          (hF row hr col hc hf)
      · simp [hf]
    _ = _ := by
      simp_rw [Finset.sum_comm (s := sourceProductVertices Q₁ Q₂ ρ ν A B d)
        (t := Finset.Icc (a+9) (a+d+5))]

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

theorem two_rpow_as_scale (N : ℕ) (hN : 0 < N) (t : ℝ) :
    (2:ℝ)^t = ((2:ℝ)^N)^(t/N) := by
  rw [← Real.rpow_natCast (2:ℝ) N,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ComparableProfileFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem comparable_profile_factor (N : ℕ) (hN : 0 < N)
    (m : ℝ → ℝ) (a b v lam : ℝ) :
    ((2:ℝ)^(2*(v-a))/(((2:ℝ)^N)^(-m a))^4) *
      ((((2:ℝ)^N)^(-m b))^4*(2:ℝ)^(-2*(v-b))) *
      (4096*((2:ℝ)^N)^(2*(m b-m a)+12*lam)) =
    4096*((2:ℝ)^N)^(-2*(m b-b/N-(m a-a/N))+12*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hMa : ((2:ℝ)^N)^(-m a) ≠ 0 := (Real.rpow_pos_of_pos hR _).ne'
  have rearrange :
      ((2:ℝ)^(2*(v-a))/(((2:ℝ)^N)^(-m a))^4) *
        ((((2:ℝ)^N)^(-m b))^4*(2:ℝ)^(-2*(v-b))) *
        (4096*((2:ℝ)^N)^(2*(m b-m a)+12*lam)) =
      4096*((2:ℝ)^(2*(v-a))*(2:ℝ)^(-2*(v-b))) *
        (((2:ℝ)^N)^(-m b)/((2:ℝ)^N)^(-m a))^4 *
        ((2:ℝ)^N)^(2*(m b-m a)+12*lam) := by field_simp
  rw [rearrange,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show 2*(v-a)+ -2*(v-b) = 2*(b-a) by ring,two_rpow_as_scale N hN]
  rw [← Real.rpow_sub hR]
  simp only [pow_succ,pow_zero,one_mul]
  have he (x y z : ℝ) : 4096*x*(y*y*y*y)*z = 4096*(x*y*y*y*y*z) := by ring
  rw [he]
  simp only [← Real.rpow_add hR]
  congr 2
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceGoodSet
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem measurable_endpointDescriptorGood (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (d : PolicyDescriptor) :
    MeasurableSet (endpointDescriptorGood Q ρ m N lam sig J i d) := by
  simp only [endpointDescriptorGood, ofPred_forall]
  apply MeasurableSet.iInter
  intro P
  apply MeasurableSet.iInter
  intro _
  exact ((Q.descendant P).measurable.preimage measurable_fst).himp
    ((measurable_descriptorGoodSet Q ρ m N lam sig J i P d).preimage measurable_snd)

theorem measurable_positiveDistanceGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N q a t : ℕ) (lam sig : ℝ) (J i : ℕ) :
    MeasurableSet (positiveDistanceGoodSet Q ρ m N q a t lam sig J i) := by
  simp only [positiveDistanceGoodSet, ofPred_forall]
  apply Finset.measurableSet_biInter
  intro d _
  exact ((measurable_endpointDescriptorGood Q ρ m N lam sig J i d).preimage
    (measurable_fst.prodMk measurable_pairRadialUnit)).inter
    ((measurable_endpointDescriptorGood Q ρ m N lam sig J i d).preimage
    (measurable_snd.prodMk measurable_pairRadialUnit))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistancePushforward
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

namespace PositiveDistanceData

theorem measurable_good (d : PositiveDistanceData) : MeasurableSet d.good :=
  measurable_positiveDistanceGoodSet _ _ _ _ _ _ _ _ _ _ _

theorem distance_prod (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] :
    d.distance.prod e.distance = Measure.map
      (fun z : (Plane × Plane) × (Plane × Plane) =>
        (dist z.1.1 z.1.2, dist z.2.1 z.2.2)) (d.pair.prod e.pair) :=
  Measure.map_prod_map _ _ (continuous_fst.dist continuous_snd).measurable
    (continuous_fst.dist continuous_snd).measurable

theorem distance_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] (w : ℝ) :
    (d.distance.prod d.distance) {z : ℝ × ℝ | |z.1-z.2| ≤ w} =
      (d.pair.prod d.pair) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} := by
  rw [distance_prod,Measure.map_apply (by fun_prop) (by measurability)]
  rfl

theorem lintegral_distance_prod (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂d.distance.prod e.distance) =
      ∫⁻ z, F (dist z.1.1 z.1.2,dist z.2.1 z.2.2) ∂d.pair.prod e.pair := by
  rw [distance_prod,lintegral_map hF (by fun_prop)]

theorem lintegral_drop_extra_restriction (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F)
    (S : Set ((Plane × Plane) × (Plane × Plane))) :
    (∫⁻ z in S, F (dist z.1.1 z.1.2,dist z.2.1 z.2.2) ∂d.pair.prod e.pair) ≤
      ∫⁻ z, F z ∂d.distance.prod e.distance := by
  rw [lintegral_distance_prod d e F hF]
  exact lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_Bins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem diagonal_bin_mass_le {ι : Type*} [Countable ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (I : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise fun i j => Disjoint (I i) (I j)) (w : ℝ)
    (hdiam : ∀ i x, x ∈ I i → ∀ y, y ∈ I i → |x-y| ≤ w) :
    (∑' i, (μ (I i))^2) ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have hd : Pairwise fun i j => Disjoint (I i ×ˢ I i) (I j ×ˢ I j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.1 hj.1
  calc
    (∑' i, (μ (I i))^2) = ∑' i, (μ.prod μ) (I i ×ˢ I i) := by
      simp only [Measure.prod_prod, pow_two]
    _ = (μ.prod μ) (⋃ i, I i ×ˢ I i) :=
      (measure_iUnion hd (fun i => (hmeas i).prod (hmeas i))).symm
    _ ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
      apply measure_mono
      intro z hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hdiam i z.1 hi.1 z.2 hi.2

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_disjoint {w : ℝ} (hw : 0 < w) :
    Pairwise fun i j => Disjoint (realBin w i) (realBin w j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i+1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxj.1.trans' hm)) hxi.2
  · have hc : ((j+1 : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxi.1.trans' hm)) hxj.2

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

theorem real_bin_collision_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∑' j : ℤ, (μ (realBin w j))^2) ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} :=
  diagonal_bin_mass_le μ (realBin w) (realBin_measurable w) (realBin_disjoint hw) w
    (fun j _ hx _ hy => realBin_diameter w j hx hy)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem ennreal_offset_cauchy (a b : ℤ → ℝ≥0∞) (h : ℤ) :
    (∑' j : ℤ, a j*b (j-h)) ≤
      (∑' j : ℤ, (a j)^2)^(1/2 : ℝ) * (∑' j : ℤ, (b j)^2)^(1/2 : ℝ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (measurable_of_countable a).aemeasurable
    (measurable_of_countable (fun j => b (j-h))).aemeasurable
  simp only [lintegral_count, ENNReal.rpow_two] at hh
  have he : (∑' j : ℤ, (b (j-h))^2) = ∑' j : ℤ, (b j)^2 :=
    (Equiv.subRight h).tsum_eq (fun j => (b j)^2)
  simpa only [one_div, he, Pi.mul_apply] using hh

 theorem realBin_cover {w : ℝ} (hw : 0 < w) (x : ℝ) :
    x ∈ realBin w ⌊x/w⌋ := by
  constructor
  · exact (le_div_iff₀ hw).mp (Int.floor_le (x/w))
  · simpa only [Int.cast_add,Int.cast_one] using
      (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/w))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_BinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem half_le_abs_int_add_half (h : ℤ) : (1/2:ℝ) ≤ |(h:ℝ)+1/2| := by
  by_cases hh : 0 ≤ h
  · have hr : (0:ℝ) ≤ h := by exact_mod_cast hh
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hr : (h:ℝ) ≤ -1 := by exact_mod_cast (show h ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith

 theorem realBin_kernel_bound {w x y : ℝ} (hw : 0 < w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    1/(1+|x-y|/w)^2 ≤ 4/(((i-j:ℤ):ℝ)+1/2)^2 := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hd : |(((i-j:ℤ):ℝ)+1/2)| ≤ 2*(1+|x-y|/w) := by
    rw [abs_le]
    have h1 := neg_abs_le ((x-y)/w)
    have h2 := le_abs_self ((x-y)/w)
    rw [abs_div,abs_of_pos hw,sub_div] at h1 h2
    simp only [Int.cast_sub]
    constructor <;> linarith [div_nonneg (abs_nonneg (x-y)) hw.le]
  have hpos : 0 < 1+|x-y|/w := by positivity
  have hh := half_le_abs_int_add_half (i-j)
  have hsq : 0 < ((((i-j:ℤ):ℝ)+1/2)^2) := by
    nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hsq).mpr
  nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2)), sq_nonneg (2*(1+|x-y|/w)-|(((i-j:ℤ):ℝ)+1/2)|)]

 theorem binKernelConstant_ne_top : binKernelConstant ≠ ∞ := by
  have hs := (Real.summable_one_div_int_add_rpow (1/2) 2).mpr (by norm_num)
  have ht : Summable (fun h : ℤ => 4/((h:ℝ)+1/2)^2) := by
    simpa only [Real.rpow_two,sq_abs,mul_one_div] using hs.mul_left 4
  exact ht.tsum_ofReal_ne_top

 theorem weighted_offset_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (c : ℤ → ℝ≥0∞) :
    (∫⁻ z : ℝ × ℝ, ∑' h : ℤ, ∑' j : ℤ,
      (realBin w j ×ˢ realBin w (j-h)).indicator (fun _ => c h) z ∂μ.prod ν) ≤
      (∑' h : ℤ, c h) * (binL2Norm μ w * binL2Norm ν w) := by
  have hm (h j : ℤ) : Measurable ((realBin w j ×ˢ realBin w (j-h)).indicator
      (fun _ : ℝ × ℝ => c h)) :=
    measurable_const.indicator ((realBin_measurable w j).prod (realBin_measurable w (j-h)))
  rw [lintegral_tsum (fun h => (Measurable.tsum (fun j => hm h j)).aemeasurable)]
  simp_rw [lintegral_tsum (fun j => (hm _ j).aemeasurable)]
  simp_rw [lintegral_indicator_const ((realBin_measurable w _).prod (realBin_measurable w _)),
    Measure.prod_prod, ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' h : ℤ, c h * (binL2Norm μ w * binL2Norm ν w) := by
      apply ENNReal.tsum_le_tsum
      intro h
      exact mul_le_mul_right (ennreal_offset_cauchy (fun j => μ (realBin w j))
        (fun j => ν (realBin w j)) h) (c h)
    _ = _ := ENNReal.tsum_mul_right

 theorem real_bin_decaying_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      binKernelConstant * (binL2Norm μ w * binL2Norm ν w) := by
  apply le_trans (lintegral_mono (fun z => ?_))
    (weighted_offset_kernel_bound μ ν w binKernelWeight)
  let i : ℤ := ⌊z.1/w⌋
  let j : ℤ := ⌊z.2/w⌋
  have hi := realBin_cover hw z.1
  have hj := realBin_cover hw z.2
  have he : i-(i-j)=j := by omega
  have hz : z ∈ realBin w i ×ˢ realBin w (i-(i-j)) := ⟨hi,by simpa only [he] using hj⟩
  calc
    _ ≤ binKernelWeight (i-j) := ENNReal.ofReal_le_ofReal (realBin_kernel_bound hw hi hj)
    _ = (realBin w i ×ˢ realBin w (i-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z := (indicator_of_mem hz (fun _ : ℝ × ℝ => binKernelWeight (i-j))).symm
    _ ≤ ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z :=
      ENNReal.le_tsum (f := fun index : ℤ =>
        (realBin w index ×ˢ realBin w (index-(i-j))).indicator
          (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z) i
    _ ≤ ∑' h : ℤ, ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-h)).indicator
        (fun _ : ℝ × ℝ => binKernelWeight h) z :=
      ENNReal.le_tsum (f := fun offset : ℤ => ∑' index : ℤ,
        (realBin w index ×ˢ realBin w (index-offset)).indicator
          (fun _ : ℝ × ℝ => binKernelWeight offset) z) (i-j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem binL2Norm_mul_self (μ : Measure ℝ) (w : ℝ) :
    binL2Norm μ w * binL2Norm μ w = ∑' j : ℤ, (μ (realBin w j))^2 := by
  unfold binL2Norm
  rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
  norm_num

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_PositiveDistanceBins
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem width_pos (d : PositiveDistanceData) : 0 < d.width := by
  unfold width; positivity

theorem levelMass_pos (d : PositiveDistanceData) : 0 < d.levelMass := by
  unfold levelMass; positivity

theorem normalization_pos (d : PositiveDistanceData) : 0 < d.normalization := by
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos d.levelMass_pos _)

theorem normalization_ne_top (d : PositiveDistanceData) : d.normalization ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem normalization_inv (d : PositiveDistanceData) :
    d.normalization⁻¹ = ENNReal.ofReal
      (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) := by
  rw [normalization,← ENNReal.ofReal_inv_of_pos
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos d.levelMass_pos _)),
    inv_div,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_eq_mul_inv]

theorem coincidence_ne_top (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence ≠ ∞ :=
  ENNReal.mul_ne_top d.normalization_ne_top (measure_ne_top _ _)

theorem unnormalized_coincidence (d : PositiveDistanceData) :
    d.normalization⁻¹ * d.coincidence =
      (d.pair.prod d.pair)
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width} := by
  rw [coincidence,← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt d.normalization_pos) d.normalization_ne_top,one_mul]

theorem bin_norm_sq_le_coincidence (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    binL2Norm d.distance d.width * binL2Norm d.distance d.width ≤
      ENNReal.ofReal (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) * d.coincidence := by
  rw [← d.normalization_inv,d.unnormalized_coincidence,binL2Norm_mul_self]
  apply (real_bin_collision_bound d.distance d.width_pos).trans
  rw [d.distance_collision]
  apply measure_mono
  intro z hz
  change |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ d.width at hz
  change |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width
  exact hz.trans (by nlinarith [d.width_pos])

theorem bin_norm_le_coincidence_sqrt (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    binL2Norm d.distance d.width ≤
      (d.normalization⁻¹ * d.coincidence)^(1/2:ℝ) := by
  have h := d.bin_norm_sq_le_coincidence
  rw [← d.normalization_inv] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact hh

theorem distance_kernel_bound (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (ht : d.t = e.t) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ((d.normalization⁻¹*d.coincidence)^(1/2:ℝ) *
        (e.normalization⁻¹*e.coincidence)^(1/2:ℝ)) := by
  have hw : d.width = e.width := by simp only [width,ht]
  apply (real_bin_decaying_kernel_bound d.distance e.distance d.width_pos).trans
  apply mul_le_mul_right
  exact mul_le_mul' d.bin_norm_le_coincidence_sqrt (hw ▸ e.bin_norm_le_coincidence_sqrt)

theorem common_profile_distance_kernel_bound (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) *
        (d.coincidence*e.coincidence)^(1/2:ℝ) := by
  have h := distance_kernel_bound d e ht
  rw [← hn] at h
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)] at h ⊢
  have he (x : ℝ≥0∞) : x^(1/2:ℝ)*x^(1/2:ℝ) = x := by
    rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
    norm_num
  have hr (x y z : ℝ≥0∞) : (x*y)*(x*z) = (x*x)*(y*z) := by ring
  rw [hr,he,d.normalization_inv] at h
  simpa only [mul_assoc] using h

theorem common_profile_distance_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) *
        max d.coincidence e.coincidence := by
  apply (common_profile_distance_kernel_bound d e ht hn).trans
  apply mul_le_mul_right
  have h := ENNReal.rpow_le_rpow (mul_le_mul'
    (le_max_left d.coincidence e.coincidence) (le_max_right d.coincidence e.coincidence))
    (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at h
  norm_num at h
  simpa only [le_max_iff] using h

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_PositiveDistanceSpatialKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem width_kernel (d : PositiveDistanceData) (z : ℝ × ℝ) :
    1/(1+|z.1-z.2|/d.width)^2 = 1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2 := by
  simp only [width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_natCast,div_eq_mul_inv,inv_inv,mul_comm]

theorem spatial_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (S : Set ((Plane × Plane) × (Plane × Plane))) :
    (∫⁻ z in S, ENNReal.ofReal
      (1/(1+(2:ℝ)^d.t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
      ∂d.pair.prod e.pair) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) * max d.coincidence e.coincidence := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2)
  have hF : Measurable F := by unfold F; fun_prop
  apply (d.lintegral_drop_extra_restriction e F hF S).trans
  have he : F = fun z => ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2) := by
    funext z
    rw [d.width_kernel]
  rw [he]
  exact common_profile_distance_kernel_max d e ht hn

theorem spatial_stationary_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (S : Set ((Plane × Plane) × (Plane × Plane))) :
    ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))) *
      (∫⁻ z in S, ENNReal.ofReal
        (1/(1+(2:ℝ)^d.t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
        ∂d.pair.prod e.pair) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a))) * max d.coincidence e.coincidence := by
  have hh := mul_le_mul_right (spatial_kernel_max d e ht hn S)
    (ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))))
  have he : (2:ℝ)^(-((d.t:ℝ)-d.a)) *
      (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) =
      d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a)) := by
    rw [mul_left_comm,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 2
    ring
  have hc (x y z w : ℝ≥0∞) : x*(y*z*w) = y*(x*z)*w := by ring
  rw [hc,← ENNReal.ofReal_mul (by positivity),he] at hh
  exact hh

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_FourSpatialPairMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem measurePreserving_fourSpatialPair (μ : Fin 4 → Measure Plane)
    [∀ i, IsFiniteMeasure (μ i)] :
    MeasurePreserving fourSpatialPairEquiv (Measure.pi μ)
      ((μ 0).prod (μ 1) |>.prod ((μ 2).prod (μ 3))) := by
  apply MeasurePreserving.symm fourSpatialPairEquiv.symm
  refine ⟨fourSpatialPairEquiv.symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply fourSpatialPairEquiv.symm.measurable (MeasurableSet.univ_pi hs)]
  have he : fourSpatialPairEquiv.symm ⁻¹' Set.pi univ s =
      (s 0 ×ˢ s 1) ×ˢ (s 2 ×ˢ s 3) := by
    ext z
    simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_prod]
    constructor
    · intro h
      exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩
    · intro h i
      fin_cases i
      · exact h.1.1
      · exact h.1.2
      · exact h.2.1
      · exact h.2.2
  rw [he,Measure.prod_prod,Measure.prod_prod,Measure.prod_prod,Fin.prod_univ_four]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceOriginalSpatial
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem fourCells_preserving (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] :
    MeasurePreserving fourSpatialPairEquiv (Measure.pi (fourCells d e))
      (d.cellPair.prod e.cellPair) := measurePreserving_fourSpatialPair (fourCells d e)

theorem original_spatial_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (S : Set ((Plane × Plane) × (Plane × Plane))) (hS : MeasurableSet S) :
    ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))) *
      (∫⁻ x in fourSpatialPairEquiv ⁻¹' (S ∩ (d.good ×ˢ e.good)), ENNReal.ofReal
        (1/(1+(2:ℝ)^d.t*|dist (x 0) (x 1)-dist (x 2) (x 3)|)^2)
        ∂Measure.pi (fourCells d e)) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a))) * max d.coincidence e.coincidence := by
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ≥0∞ := fun z => ENNReal.ofReal
    (1/(1+(2:ℝ)^d.t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
  have hF : Measurable F := by unfold F; fun_prop
  have he := (fourCells_preserving d e).setLIntegral_comp_preimage
    (hS.inter (d.measurable_good.prod e.measurable_good)) hF
  change (∫⁻ x in fourSpatialPairEquiv ⁻¹' (S ∩ (d.good ×ˢ e.good)),
    ENNReal.ofReal (1/(1+(2:ℝ)^d.t*|dist (x 0) (x 1)-dist (x 2) (x 3)|)^2)
    ∂Measure.pi (fourCells d e)) = _ at he
  rw [he]
  have hr : (d.cellPair.prod e.cellPair).restrict (S ∩ (d.good ×ˢ e.good)) =
      (d.pair.prod e.pair).restrict S := by
    rw [pair,pair,Measure.prod_restrict,Measure.restrict_restrict hS]
  rw [hr]
  exact spatial_stationary_kernel_max d e ht hn S

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GoodSupportedKernelMajorant
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem measurable_fourPairGood {G H : Set (Plane × Plane)}
    (hG : MeasurableSet G) (hH : MeasurableSet H) : MeasurableSet (fourPairGood G H) :=
  (hG.prod hH).preimage fourSpatialPairEquiv.measurable

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_ComparableNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ENNReal

theorem comparable_normalized_bound (N : ℕ) (hN : 0 < N)
    (m : ℝ → ℝ) (a b v lam : ℝ) (c : ℕ) (H D : ℝ≥0∞) (F : ℂ)
    (hc : (c:ℝ) ≤ 4096*((2:ℝ)^N)^(2*(m b-m a)+12*lam))
    (hF : ‖F‖ₑ ≤ H * ENNReal.ofReal
      ((((2:ℝ)^N)^(-m b))^4*(2:ℝ)^(-2*(v-b))) * (c:ℝ≥0∞) * 257025537024256 * D) :
    ‖((2:ℝ)^(2*(v-a))/(((2:ℝ)^N)^(-m a))^4) • F‖ₑ ≤
      (H*257025537024256*4096) *
        ENNReal.ofReal (((2:ℝ)^N)^(-2*(m b-b/N-(m a-a/N))+12*lam)) * D := by
  let p : ℝ := (2:ℝ)^(2*(v-a))/(((2:ℝ)^N)^(-m a))^4
  let g : ℝ := (((2:ℝ)^N)^(-m b))^4*(2:ℝ)^(-2*(v-b))
  let r : ℝ := 4096*((2:ℝ)^N)^(2*(m b-m a)+12*lam)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hce : (c:ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hc
  have hn : ‖p • F‖ₑ = ENNReal.ofReal p * ‖F‖ₑ := by
    simp only [← ofReal_norm,norm_smul,Real.norm_eq_abs,abs_of_nonneg hp,ENNReal.ofReal_mul hp]
  rw [hn]
  calc
    _ ≤ ENNReal.ofReal p * (H*ENNReal.ofReal g*(c:ℝ≥0∞)*257025537024256*D) :=
      mul_le_mul_right hF (ENNReal.ofReal p)
    _ ≤ ENNReal.ofReal p * (H*ENNReal.ofReal g*ENNReal.ofReal r*257025537024256*D) := by
      gcongr
    _ = H*257025537024256*ENNReal.ofReal (p*g*r)*D := by
      rw [ENNReal.ofReal_mul (mul_nonneg hp hg),ENNReal.ofReal_mul hp]
      ring
    _ = _ := by
      have he : p*g*r = 4096*((2:ℝ)^N)^(-2*(m b-b/N-(m a-a/N))+12*lam) :=
        comparable_profile_factor N hN m a b v lam
      rw [he,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4096)]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceRebinBound
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
namespace PositiveDistanceData

theorem angularFourCellMeasure_eq (d e : PositiveDistanceData) (row col : CellPath × CellPath) :
    angularFourCellMeasure d.Q e.Q d.ρ e.ρ row col =
      Measure.pi (fourCells (d.atCells row.1 col.1) (e.atCells row.2 col.2)) := by
  unfold angularFourCellMeasure
  congr 1
  funext j
  fin_cases j <;> rfl

theorem cell_shell_positive_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (row col : CellPath × CellPath) (b : ℕ) :
    ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))) *
      (∫⁻ x in angularLengthShell b,
        (fourPairGood d.good e.good).indicator (distanceDifferenceKernel d.t) x
          ∂angularFourCellMeasure d.Q e.Q d.ρ e.ρ row col) ≤
      binKernelConstant * ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a))) *
        max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence := by
  let D := d.atCells row.1 col.1
  let E := e.atCells row.2 col.2
  let T := fourSpatialPairEquiv.symm ⁻¹' angularLengthShell b
  have hT : MeasurableSet T := (measurable_angularLengthShell b).preimage fourSpatialPairEquiv.symm.measurable
  have he : fourPairGood d.good e.good ∩ angularLengthShell b =
      fourSpatialPairEquiv ⁻¹' (T ∩ (D.good ×ˢ E.good)) := by
    ext x
    simp only [T,D,E,good,fourPairGood,mem_inter_iff,mem_preimage,
      MeasurableEquiv.symm_apply_apply]
    exact and_comm
  rw [lintegral_indicator (measurable_fourPairGood d.measurable_good e.measurable_good),
    Measure.restrict_restrict (measurable_fourPairGood d.measurable_good e.measurable_good),
    he,angularFourCellMeasure_eq]
  simpa only [D,E,atCells,levelMass,distanceDifferenceKernel,Real.rpow_natCast] using
    original_spatial_kernel_max D E ht hn T hT

theorem rebinned_positive_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization)
    (A B : CellPath) (n b : ℕ) :
    ENNReal.ofReal ((2:ℝ)^(-((d.t:ℝ)-d.a))) *
      (∑ row ∈ sourceProductVertices d.Q e.Q d.ρ e.ρ A B n,
        ∑ col ∈ sourceProductVertices d.Q e.Q d.ρ e.ρ A B n,
          if angularSeparated d.Q e.Q b row col then
            ∫⁻ x in angularLengthShell b,
              (fourPairGood d.good e.good).indicator (distanceDifferenceKernel d.t) x
                ∂angularFourCellMeasure d.Q e.Q d.ρ e.ρ row col
          else 0) ≤
    (binKernelConstant * ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-2*((d.t:ℝ)-d.a)))) *
      ∑ row ∈ sourceProductVertices d.Q e.Q d.ρ e.ρ A B n,
        ∑ col ∈ sourceProductVertices d.Q e.Q d.ρ e.ρ A B n,
          if angularSeparated d.Q e.Q b row col then
            max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence
          else 0 := by
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  apply Finset.sum_le_sum
  intro row hr
  apply Finset.sum_le_sum
  intro col hc
  by_cases hs : angularSeparated d.Q e.Q b row col
  · simpa only [hs,↓reduceIte] using cell_shell_positive_kernel_max d e ht hn row col b
  · simp [hs]

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_ComparableCellCounting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem dyadic_two_thousand_neighbors (Q : DyadicSquare) (hQ : Q.side = 1)
    (p : ℕ) (x : Plane) :
    (((dyadicPaths p).filter (fun c => dist x (Q.descendant c).center ≤ 2000/(2:ℝ)^p)).card : ℝ) ≤ 16032016 := by
  classical
  have hpos : 0 < Q.side := by rw [hQ]; norm_num
  have hsub : (dyadicPaths p).filter (fun c => dist x (Q.descendant c).center ≤ 2000/(2:ℝ)^p) ⊆
      cellsMeeting Q p x (2001/(2:ℝ)^p) := by
    intro c hc
    obtain ⟨hc,hb⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hc,(Q.descendant c).center,
      (Q.descendant c).center_mem (Q.descendant_side_pos hpos c),?_⟩
    rw [mem_ball,dist_comm]
    exact hb.trans_lt (div_lt_div_of_pos_right (by norm_num) (by positivity))
  have hh := dyadic_scaled_ball_card_le Q hpos p x (C₀ := 2001) (by norm_num)
    (r := 2001/(2:ℝ)^p) (by rw [hQ]; ring_nf; exact le_rfl)
  norm_num at hh
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (by exact_mod_cast hh)

theorem angularSeparated_degree_real (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (row : CellPath × CellPath) :
    ((C.filter (angularSeparated Q₁ Q₂ p row)).card : ℝ) ≤ 257025537024256 := by
  classical
  let S₁ := (dyadicPaths p).filter (fun c =>
    dist (Q₁.descendant row.1).center (Q₁.descendant c).center ≤ 2000/(2:ℝ)^p)
  let S₂ := (dyadicPaths p).filter (fun c =>
    dist (Q₂.descendant row.2).center (Q₂.descendant c).center ≤ 2000/(2:ℝ)^p)
  have hsub : C.filter (angularSeparated Q₁ Q₂ p row) ⊆ S₁ ×ˢ S₂ := by
    intro col hc
    obtain ⟨hc,hnear⟩ := Finset.mem_filter.mp hc
    simp only [angularSeparated,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,← div_eq_mul_inv] at hnear
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hC hc)
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨h1,hnear.1.2⟩,
      Finset.mem_filter.mpr ⟨h2,hnear.2.2⟩⟩
  have h1 := dyadic_two_thousand_neighbors Q₁ hQ₁ p (Q₁.descendant row.1).center
  have h2 := dyadic_two_thousand_neighbors Q₂ hQ₂ p (Q₂.descendant row.2).center
  have hh := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
  rw [Finset.card_product,Nat.cast_mul] at hh
  exact hh.trans (by nlinarith [mul_le_mul h1 h2 (Nat.cast_nonneg S₂.card) (by norm_num : (0:ℝ) ≤ 16032016)])

theorem angularSeparated_degree (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (row : CellPath × CellPath) :
    (C.filter (angularSeparated Q₁ Q₂ p row)).card ≤ 257025537024256 := by
  exact_mod_cast angularSeparated_degree_real Q₁ Q₂ hQ₁ hQ₂ p C hC row

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_SeparatedDistanceMaximum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
theorem filtered_pair_sum_le_degree {α : Type*} [DecidableEq α]
    (C : Finset α) (R : α → α → Prop) [DecidableRel R]
    (W : α → α → ℝ≥0∞) (degree : ℕ)
    (hd : ∀ row ∈ C, (C.filter (R row)).card ≤ degree) :
    (∑ row ∈ C, ∑ col ∈ C, if R row col then W row col else 0) ≤
      (C.card:ℝ≥0∞)*(degree:ℝ≥0∞)*
        ((C ×ˢ C).filter (fun z => R z.1 z.2)).sup (fun z => W z.1 z.2) := by
  let U := ((C ×ˢ C).filter (fun z => R z.1 z.2)).sup (fun z => W z.1 z.2)
  have hrow (row : α) (hr : row ∈ C) :
      (∑ col ∈ C, if R row col then W row col else 0) ≤ (degree:ℝ≥0∞)*U := by
    rw [← Finset.sum_filter]
    have hle (col : α) (hc : col ∈ C.filter (R row)) : W row col ≤ U := by
      exact Finset.le_sup (s := (C ×ˢ C).filter (fun z => R z.1 z.2))
        (b := (row,col)) (f := fun z => W z.1 z.2)
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr,(Finset.mem_filter.mp hc).1⟩,
          (Finset.mem_filter.mp hc).2⟩)
    have hh := Finset.sum_le_sum hle
    rw [Finset.sum_const,nsmul_eq_mul] at hh
    have hhdeg : ((C.filter (R row)).card:ℝ≥0∞) ≤ (degree:ℝ≥0∞) := Nat.cast_le.mpr (hd row hr)
    exact hh.trans (mul_le_mul_left hhdeg U)
  have hh := Finset.sum_le_sum hrow
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc,U] using hh

namespace PositiveDistanceData

theorem separatedMaximum_ne_top (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (C : Finset (CellPath × CellPath)) (b : ℕ) : d.separatedMaximum e C b ≠ ⊤ := by
  apply ne_of_lt
  apply Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤) |>.mpr
  intro z hz
  exact max_lt (lt_top_iff_ne_top.mpr (coincidence_ne_top _))
    (lt_top_iff_ne_top.mpr (coincidence_ne_top _))

theorem separated_sum_le_degree (d e : PositiveDistanceData)
    (b : ℕ) (C : Finset (CellPath × CellPath)) (degree : ℕ)
    (hdegree : ∀ row ∈ C, (C.filter (angularSeparated d.Q e.Q b row)).card ≤ degree) :
    (∑ row ∈ C, ∑ col ∈ C, if angularSeparated d.Q e.Q b row col then
      max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence else 0) ≤
      (C.card : ℝ≥0∞)*(degree:ℝ≥0∞)*d.separatedMaximum e C b := by
  exact filtered_pair_sum_le_degree C (angularSeparated d.Q e.Q b)
    (fun row col => max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence) degree hdegree

theorem separated_sum_le_maximum (d e : PositiveDistanceData)
    (hQ : d.Q.side = 1) (hQ' : e.Q.side = 1) (b : ℕ)
    (C : Finset (CellPath × CellPath)) (hC : C ⊆ (dyadicPaths b) ×ˢ (dyadicPaths b)) :
    (∑ row ∈ C, ∑ col ∈ C, if angularSeparated d.Q e.Q b row col then
      max (d.atCells row.1 col.1).coincidence (e.atCells row.2 col.2).coincidence else 0) ≤
      (C.card : ℝ≥0∞)*257025537024256*d.separatedMaximum e C b := by
  simpa only [Nat.cast_ofNat] using separated_sum_le_degree d e b C 257025537024256
    (fun row _ => angularSeparated_degree d.Q e.Q hQ hQ' b C hC row)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ActualComparableShellDistance
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_shell_distance {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a d n v : ℕ),
    0 < q → a₀ ≤ a+n → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (lam : ℝ) (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m)
      N (lam) sig J (i l) (hsp l)
    let D : Fin 2 → PositiveDistanceData := fun l =>
      ⟨Q l,ρ l,m,N,q,a+n,v,lam,sig,J,i l+1,[],[]⟩
    ‖∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
      ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
        if ¬ angularNear (Q 0) (Q 1) (a+d) row col then
          ∫ x in angularLengthShell (a+n), angularStationarySpatialKernel (β 0) (β 1) o v Ψ x
            ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
        else 0‖ₑ ≤
    ENNReal.ofReal H * binKernelConstant *
      ENNReal.ofReal ((((2:ℝ)^N)^(-m (a+n)))^4*(2:ℝ)^(-2*((v:ℝ)-(a+n:ℕ)))) *
      ((sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n).card:ℝ≥0∞) *
      257025537024256 *
      (D 0).separatedMaximum (D 1) (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n) := by
  obtain ⟨H,hH,N₀,h₀⟩ := uniform_actual_comparable_shell_rebin hΨ hsΨ hsig K o hJ
  refine ⟨H,hH,N₀,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d n v hq ha₀ ht hv S k hS hcard hK L hL
    L₀ hvh hLL hL₀ lam i hsp hspb A B hA hB
  let D : Fin 2 → PositiveDistanceData := fun l =>
    ⟨Q l,ρ l,m,N,q,a+n,v,lam,sig,J,i l+1,[],[]⟩
  have he := h₀ N hN Q hQ ρ hcarry (fun _ => m) q a₀ t₀ a d n v hq ha₀ ht hv
    S k hS hcard hK L hL L₀ hvh hLL hL₀ (fun _ => lam) i hsp hspb A B hA hB
  have hn : (D 0).normalization = (D 1).normalization := rfl
  have hk := PositiveDistanceData.rebinned_positive_kernel_max (D 0) (D 1) rfl hn A B n (a+n)
  have hc := PositiveDistanceData.separated_sum_le_maximum (D 0) (D 1) (hQ 0) (hQ 1) (a+n)
    (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n)
    (sourceProductVertices_subset _ _ _ _ _ _ a n hA hB)
  dsimp only at he ⊢
  rw [mul_assoc] at he
  have hh := he.trans (mul_le_mul_right hk (ENNReal.ofReal H))
  have hh' := hh.trans (mul_le_mul_right
    (mul_le_mul_right hc (binKernelConstant * ENNReal.ofReal
      ((D 0).levelMass^4*(2:ℝ)^(-2*((v:ℝ)-(a+n:ℕ)))))) (ENNReal.ofReal H))
  simpa only [D,PositiveDistanceData.levelMass,mul_assoc,Nat.cast_add] using hh'

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ActualComparableShellNormalized
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_shell_normalized {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a d n v : ℕ),
    0 < q → a₀ ≤ a+n → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (B₀ : ℕ) (δ lam : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) → a+n ≤ N →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m)
      N (lam) sig J (i l) (hsp l)
    let D : Fin 2 → PositiveDistanceData := fun l =>
      ⟨Q l,ρ l,m,N,q,a+n,v,lam,sig,J,i l+1,[],[]⟩
    ‖((2:ℝ)^(2*((v:ℝ)-a))/(((2:ℝ)^N)^(-m a))^4) •
      (∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
      ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
        if ¬ angularNear (Q 0) (Q 1) (a+d) row col then
          ∫ x in angularLengthShell (a+n), angularStationarySpatialKernel (β 0) (β 1) o v Ψ x
            ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
        else 0)‖ ≤
    H * ((2:ℝ)^N)^(-2*(m (a+n)-(a+n:ℕ)/N-(m a-(a:ℝ)/N))+12*lam) *
      ((D 0).separatedMaximum (D 1) (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n)).toReal := by
  obtain ⟨H,hH,N₀,h₀⟩ := uniform_actual_comparable_shell_distance hΨ hsΨ hsig K o hJ
  let C : ℝ≥0∞ := ENNReal.ofReal H*binKernelConstant*257025537024256*4096
  have hC : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top binKernelConstant_ne_top) (by norm_num))
      (by norm_num)
  refine ⟨C.toReal,ENNReal.toReal_nonneg,max 1 N₀,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d n v hq ha₀ ht hv S k hS hcard hK L hL
    L₀ hvh hLL hL₀ B₀ δ lam hd hp i hsp hspb A B hA hB
  let D : Fin 2 → PositiveDistanceData := fun l =>
    ⟨Q l,ρ l,m,N,q,a+n,v,lam,sig,J,i l+1,[],[]⟩
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num : 0 < 1) ((le_max_left _ _).trans hN)
  have he := h₀ N ((le_max_right _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a d n v hq ha₀ ht hv
    S k hS hcard hK L hL L₀ hvh hLL hL₀ lam i hsp hspb A B hA hB
  have hc := sourceProductVertices_profile_count (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1)
    N B₀ δ lam m m (hd 0) (hd 1) A B a n hA hB hp
  have hcc : ((sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n).card:ℝ) ≤
      4096*((2:ℝ)^N)^(2*(m (a+n)-m a)+12*lam) := by
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    ring
  have hn := comparable_normalized_bound N hNp m a (a+n:ℕ) v lam
    (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n).card
    (ENNReal.ofReal H*binKernelConstant)
    ((D 0).separatedMaximum (D 1) (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n))
    _ (by simpa only [Nat.cast_add] using hcc) (by simpa only [Nat.cast_add] using he)
  have hmax := PositiveDistanceData.separatedMaximum_ne_top (D 0) (D 1)
    (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n)
  have hfin : C * ENNReal.ofReal (((2:ℝ)^N)^(-2*(m (a+n)-(a+n:ℕ)/N-(m a-(a:ℝ)/N))+12*lam)) *
      (D 0).separatedMaximum (D 1) (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) (a+n) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hmax
  simp only [Nat.cast_add] at hfin hn
  have ht := ENNReal.toReal_mono hfin hn
  have hrpow : 0 ≤ ((2:ℝ)^N)^(-2*(m ((a:ℝ)+n)-((a:ℝ)+n)/N-(m a-(a:ℝ)/N))+12*lam) := by positivity
  simpa only [← ofReal_norm,ENNReal.toReal_ofReal (norm_nonneg _),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hrpow,C,D,Nat.cast_add] using ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualComparableDepthSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_depth_sum {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a d v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (B₀ : ℕ) (δ lam : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) → a+d+5 ≤ N →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
    let M := ((2:ℝ)^N)^(-m a)
    let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
      ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
    ‖angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B a d v M M
      (angularStationarySpatialKernel (β 0) (β 1) o v Ψ)‖ ≤
    C * ∑ b ∈ Finset.Icc (a+9) (a+d+5),
      ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+12*lam) *
        ((D b 0).separatedMaximum (D b 1)
          (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_actual_comparable_shell_normalized hΨ hsΨ hsig K o hJ
  obtain ⟨N₂,h₂⟩ := uniform_actual_far_stationary_integrable hΨ hsΨ hsig K o
  refine ⟨C,hC,max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d v hq ha₀ ht hv S k hS hcard hK L hL
    L₀ hvh hLL hL₀ B₀ δ lam hd hp i hsp hm hb A B hA hB
  let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
  let M := ((2:ℝ)^N)^(-m a)
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; exact zero_lt_one
  have hint (row : CellPath × CellPath) (hr : row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d)
      (col : CellPath × CellPath) (hc : col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d)
      (hf : ¬ angularNear (Q 0) (Q 1) (a+d) row col) :
      IntegrableOn (angularStationarySpatialKernel (β 0) (β 1) o v Ψ) angularLengthComparable
        (angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col) := by
    exact h₂ N ((le_max_right _ _).trans hN) S (fun _ => id) k hcard hK L hL Q hQp ρ
      (fun _ => m) (fun _ => lam) (fun _ => J) i hsp hm hb v (a+d:ℕ) L₀ hvh hLL hL₀
      (angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col) angularLengthComparable
      (angular_comparable_far_ae (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) (a+d) row col
        (sourceProductVertices_subset _ _ _ _ _ _ a d hA hB hr)
        (sourceProductVertices_subset _ _ _ _ _ _ a d hA hB hc) hf)
  dsimp only
  rw [angular_comparable_contribution_partition (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1)
    A B a d hA hB v M M _ hint,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hbdepth
  have hba : a ≤ b := by have := (Finset.mem_Icc.mp hbdepth).1; omega
  have heq : a+(b-a) = b := Nat.add_sub_of_le hba
  have hbN : b ≤ N := (Finset.mem_Icc.mp hbdepth).2.trans hp
  have hs := h₁ N ((le_max_left _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a d (b-a) v
    hq (by omega) ht hv S k hS hcard hK L hL L₀ hvh hLL hL₀ B₀ δ lam hd
    (by omega) i hsp hb A B hA hB
  have hpow : M^2*M^2 = M^4 := by rw [← pow_add]
  simpa only [← Nat.cast_add,heq,hpow,M,β,mul_assoc] using hs

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualFarBuffer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem sourceFarBuffer_ge_length (N L : ℕ) (sig : ℝ) : L ≤ sourceFarBuffer N L sig :=
  le_max_left _ _

theorem sourceFarBuffer_ge_slack (N L : ℕ) (sig : ℝ) :
    10*sig*(N:ℝ) ≤ (sourceFarBuffer N L sig:ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

theorem uniform_source_far_buffer {sig : ℝ} (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L v a : ℕ,
      let L₀ := sourceFarBuffer N L sig
      let h := v-2*L₀
      a < h →
      let d := h-a
      a+d = h ∧ a+d+5 < v ∧
      (v:ℝ)-(a+d:ℕ) = 2*(L₀:ℝ) ∧ (L:ℝ) ≤ (L₀:ℝ) ∧
      10*sig*(N:ℝ) ≤ (L₀:ℝ) := by
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (1/sig)
  refine ⟨N₀,?_⟩
  intro N hN L v a
  dsimp only
  intro hah
  have hNs : 1/sig < (N:ℝ) := h₀.trans_le (Nat.cast_le.mpr hN)
  have hsigN : 1 < sig*(N:ℝ) := by
    have ht := (div_lt_iff₀ hsig).mp hNs
    linarith
  have hslack := sourceFarBuffer_ge_slack N L sig
  have hbuf : 5 < 2*sourceFarBuffer N L sig := by
    have hb : (5:ℝ) < 2*(sourceFarBuffer N L sig:ℝ) := by linarith
    exact_mod_cast hb
  have h2 : 2*sourceFarBuffer N L sig ≤ v := by omega
  have he : a+(v-2*sourceFarBuffer N L sig-a) = v-2*sourceFarBuffer N L sig := by omega
  refine ⟨he,by omega,?_,Nat.cast_le.mpr (sourceFarBuffer_ge_length N L sig),hslack⟩
  rw [he,Nat.cast_sub h2,Nat.cast_mul,Nat.cast_ofNat]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualFarEquation24
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_equation24 {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a d v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N → a+d+5 < v →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (B₀ : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
    let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
    let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
      ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
    ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
      (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)‖ ≤
    C * ∑ b ∈ Finset.Icc (a+9) (a+d+5),
      ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+12*lam) *
        ((D b 0).separatedMaximum (D b 1)
          (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal +
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨o,N₁,h₁⟩ := uniform_actual_far_stationary_reduction (T := T) (lam := lam)
    hsig K hΨ hpos hsΨ hW hΨW
  obtain ⟨C,hC,N₂,h₂⟩ := uniform_actual_comparable_depth_sum hΨ hsΨ hsig K o hJ
  refine ⟨C,hC,max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d v hq ha₀ ht hv hdepth S k hS hcard hK L hLN hL
    L₀ hvh hLL hL₀ B₀ δ hd i hsp hm hb A B hA hB
  let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
  let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
  let original := angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
    (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
    (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)
  let comparable := angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B a d v (M a) (M a)
    (angularStationarySpatialKernel (β 0) (β 1) o v Ψ)
  have he := h₁ N ((le_max_left _ _).trans hN) S (fun _ => id) k hcard hK L hLN hL
    Q hQ ρ (fun _ => m) B₀ δ hd (fun _ => J) i hsp hm hb a (by omega)
    ![A,B] (by intro l; fin_cases l <;> assumption) d v L₀ (by exact_mod_cast hv) hvh hLL hL₀
  have he' : ‖original-comparable‖ ≤ ((2:ℝ)^N)^(-T) := by
    simpa only [original,comparable,β,M,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_add] using he
  have hc := h₂ N ((le_max_right _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a d v hq ha₀ ht hv
    S k hS hcard hK L hL L₀ hvh hLL hL₀ B₀ δ lam hd (by omega) i hsp hm hb A B hA hB
  have hh := (norm_add_le (original-comparable) comparable).trans (add_le_add he' hc)
  rw [sub_add_cancel] at hh
  simpa only [original,β,M,add_comm] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualFarSourceBuffer
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_equation24_source_buffer {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    a < v-2*sourceFarBuffer N L sig →
    ∀ (B₀ : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let d := v-2*sourceFarBuffer N L sig-a
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
    let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
    let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
      ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
    ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
      (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)‖ ≤
    C * ∑ b ∈ Finset.Icc (a+9) (a+d+5),
      ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+12*lam) *
        ((D b 0).separatedMaximum (D b 1)
          (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal +
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_actual_far_equation24 (T := T) (lam := lam)
    hΨ hpos hsΨ hW hΨW hsig K hJ
  obtain ⟨N₂,h₂⟩ := uniform_source_far_buffer hsig
  refine ⟨C,hC,max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a v hq ha₀ ht hv S k hS hcard hK L hLN hL
    hbranch B₀ δ hd i hsp hm hb A B hA hB
  have hbuf := h₂ N ((le_max_right _ _).trans hN) L v a hbranch
  exact h₁ N ((le_max_left _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a
    (v-2*sourceFarBuffer N L sig-a) v hq ha₀ ht hv hbuf.2.1 S k hS hcard hK L hLN hL
    (sourceFarBuffer N L sig) hbuf.2.2.1 hbuf.2.2.2.1 hbuf.2.2.2.2 B₀ δ hd i hsp hm hb A B hA hB

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualFarPower
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_equation24_power {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ) {J : ℕ} (hJ : 0 < J) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    a < v-2*sourceFarBuffer N L sig →
    ∀ (B₀ : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let d := v-2*sourceFarBuffer N L sig-a
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
    let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
    let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
      ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
    ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
      (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)‖ ≤
    ∑ b ∈ Finset.Icc (a+9) (a+d+5),
      ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+12*lam+η) *
        ((D b 0).separatedMaximum (D b 1)
          (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal +
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_actual_far_equation24_source_buffer (T := T) (lam := lam)
    hΨ hpos hsΨ hW hΨW hsig K hJ
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed hη C
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a v hq ha₀ ht hv S k hS hcard hK L hLN hL
    hbranch B₀ δ hd i hsp hm hb A B hA hB
  have he := h₁ N ((le_max_left _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a v hq ha₀ ht hv
    S k hS hcard hK L hLN hL hbranch B₀ δ hd i hsp hm hb A B hA hB
  have hc := h₂ N ((le_max_right _ _).trans hN)
  let d := v-2*sourceFarBuffer N L sig-a
  let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
    ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
  let F : ℕ → ℝ := fun b => ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+12*lam) *
    ((D b 0).separatedMaximum (D b 1)
      (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal
  have hsum : 0 ≤ ∑ b ∈ Finset.Icc (a+9) (a+d+5), F b := by
    apply Finset.sum_nonneg
    intro b hb
    dsimp [F]
    positivity
  dsimp only at he ⊢
  apply he.trans
  calc
    _ ≤ ((2:ℝ)^N)^η * (∑ b ∈ Finset.Icc (a+9) (a+d+5), F b) + ((2:ℝ)^N)^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_right hc hsum) le_rfl
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [F,D]
      rw [← mul_assoc,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 2
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualFarSourceEquation24
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_source_equation24_oai {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ) {J : ℕ} (hJ : 0 < J) (hlam : 0 ≤ lam) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a v : ℕ),
    0 < q → a₀ ≤ a → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    a < v-2*sourceFarBuffer N L sig →
    ∀ (B₀ : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam m) →
    ∀ (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let d := v-2*sourceFarBuffer N L sig-a
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) m N lam sig J (i l) (hsp l)
    let M := fun p : ℝ => ((2:ℝ)^N)^(-m p)
    let D : ℕ → Fin 2 → PositiveDistanceData := fun b l =>
      ⟨Q l,ρ l,m,N,q,b,v,lam,sig,J,i l+1,[],[]⟩
    ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B d a v Ψ
      (M a) (M a) (M (a+d)) (M (a+d)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)‖ ≤
    ∑ b ∈ Finset.Icc (a+9) (a+d+5),
      ((2:ℝ)^N)^(-2*(m b-(b:ℝ)/N-(m a-(a:ℝ)/N))+4000*(lam+sig)) *
        ((D b 0).separatedMaximum (D b 1)
          (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B (b-a)) b).toReal +
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_far_equation24_power (T := T) (lam := lam)
    hΨ hpos hsΨ hW hΨW hsig K hJ (η := sig) hsig
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a v hq ha₀ ht hv S k hS hcard hK L hLN hL
    hbranch B₀ δ hd i hsp hm hb A B hA hB
  have he := h₀ N hN Q hQ ρ hcarry m q a₀ t₀ a v hq ha₀ ht hv
    S k hS hcard hK L hLN hL hbranch B₀ δ hd i hsp hm hb A B hA hB
  dsimp only at he ⊢
  apply he.trans
  apply add_le_add _ le_rfl
  apply Finset.sum_le_sum
  intro b hbdepth
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  linarith

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_far_source_equation24_oai := @OAI.PlanarFalconer.uniform_actual_far_source_equation24_oai
