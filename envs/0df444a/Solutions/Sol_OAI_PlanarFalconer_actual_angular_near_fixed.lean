-- Prove2me | solution 1 for OAI.PlanarFalconer.actual_angular_near_fixed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:07:49.291926+00:00
-- url     : https://prove2.me/submissions/a3229f66-7a0e-4546-bb4e-c1bcaa7c5cf2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

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

theorem DyadicSquare.cover_children (Q : DyadicSquare) :
    Q.carrier = ((Q.child false false).carrier ∪ (Q.child false true).carrier) ∪
      ((Q.child true false).carrier ∪ (Q.child true true).carrier) := by
  ext z
  simp only [carrier, child, Bool.false_eq_true, ↓reduceIte,
    add_zero, mem_ofPred_eq, mem_union]
  constructor
  · intro hz
    by_cases hx : z 0 < Q.x + Q.side / 2 <;>
      by_cases hy : z 1 < Q.y + Q.side / 2
    · exact Or.inl (Or.inl ⟨hz.1,hx,hz.2.2.1,hy⟩)
    · exact Or.inl (Or.inr ⟨hz.1,hx,by linarith,by linarith [hz.2.2.2]⟩)
    · exact Or.inr (Or.inl ⟨by linarith,by linarith [hz.2.1],hz.2.2.1,hy⟩)
    · exact Or.inr (Or.inr ⟨by linarith,by linarith [hz.2.1],
        by linarith,by linarith [hz.2.2.2]⟩)
  · intro hz
    rcases hz with (hz | hz) | (hz | hz) <;>
      refine ⟨by linarith [hz.1,hz.2.1], by linarith [hz.1,hz.2.1],
        by linarith [hz.2.2.1,hz.2.2.2], by linarith [hz.2.2.1,hz.2.2.2]⟩

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

theorem DyadicSquare.mem_descendant_at_depth (Q : DyadicSquare) (n : ℕ)
    {z : Plane} (hz : z ∈ Q.carrier) :
    ∃ p ∈ dyadicPaths n, z ∈ (Q.descendant p).carrier := by
  induction n generalizing Q with
  | zero => exact ⟨[],by simp, hz⟩
  | succ n ih =>
    have step (i j : Bool) (hz : z ∈ (Q.child i j).carrier) :
        ∃ p ∈ dyadicPaths (n+1), z ∈ (Q.descendant p).carrier := by
      obtain ⟨p,hp,hz⟩ := ih _ hz
      exact ⟨(i,j) :: p,by simpa using hp,hz⟩
    rw [Q.cover_children] at hz
    rcases hz with (hz | hz) | (hz | hz)
    · exact step false false hz
    · exact step false true hz
    · exact step true false hz
    · exact step true true hz

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
attribute [-instance] _root_.OAI.PlanarFalconer.unitCircle_compactSpace
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransform
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem measurable_sourceAngularTransform (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (M : ℝ) (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2)) :
    Measurable (fun z : ℝ × UnitCircle => sourceAngularTransform ρ X M b z.1 z.2) := by
  have hf : Measurable (fun z : (ℝ × UnitCircle) × Plane =>
      Complex.exp (Complex.I * (z.1.1 : ℂ) * (inner ℝ (z.1.2 : Plane) z.2 : ℂ)) * b z.2 z.1.2) := by
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := ρ.restrict X)).measurable
  exact (measurable_const (a := (M⁻¹ : ℝ))).smul hi

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
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicIntegralSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.biUnion_descendants (Q : DyadicSquare) (hQ : 0 < Q.side)
    (n : ℕ) : (⋃ P ∈ dyadicPaths n, (Q.descendant P).carrier) = Q.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, _, hx⟩ := mem_iUnion₂.mp hx
    exact Q.descendant_subset hQ P hx
  · intro hx
    obtain ⟨P, hP, hxP⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨P, hP, hxP⟩

theorem DyadicSquare.integral_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) (f : Plane → ℂ)
    (hf : IntegrableOn f Q.carrier ρ) :
    (∫ x in Q.carrier, f x ∂ρ) =
      ∑ P ∈ dyadicPaths n, ∫ x in (Q.descendant P).carrier, f x ∂ρ := by
  rw [← Q.biUnion_descendants hQ n]
  apply integral_biUnion_finset
  · exact fun P _ => (Q.descendant P).measurable
  · intro P hP S hS hne
    exact Q.descendants_disjoint hQ
      (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
  · exact fun P _ => hf.mono_set (Q.descendant_subset hQ P)

theorem DyadicSquare.integral_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) (f : Plane → ℂ)
    (hf : IntegrableOn f Q.carrier ρ) :
    (∫ x in Q.carrier, f x ∂ρ) =
      ∑ P ∈ occupiedAnchorPaths Q ρ n, ∫ x in (Q.descendant P).carrier, f x ∂ρ := by
  classical
  rw [Q.integral_split hQ ρ n f hf]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  have hz : ρ (Q.descendant P).carrier = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hP, bot_lt_iff_ne_bot.mpr hne⟩)
  rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransformSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem angular_integrand_norm (r : ℝ) (ω : UnitCircle) (x : Plane)
    (b : Plane → UnitCircle → ℂ) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω‖ =
      ‖b x ω‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem integrableOn_angular_integrand (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2))
    (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    IntegrableOn (fun x =>
      Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (ω : Plane) x : ℂ)) * b x ω) X ρ := by
  apply (integrable_const C).mono
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_id.prodMk measurable_const)
  · filter_upwards with x
    rw [angular_integrand_norm]
    exact (hC x ω).trans (le_abs_self C)

theorem sourceAngularTransform_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (n : ℕ) (Ma Mp : ℝ) (hMp : Mp ≠ 0)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2))
    (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ Q.carrier Ma b r ω =
      (Mp / Ma) • ∑ P ∈ occupiedAnchorPaths Q ρ n,
        sourceAngularTransform ρ (Q.descendant P).carrier Mp b r ω := by
  unfold sourceAngularTransform
  rw [Q.integral_split_occupied hQ ρ n _ (integrableOn_angular_integrand ρ _ b hb C hC r ω)]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ hMp, one_div]

theorem sourceAngularTransform_norm_le (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (M : ℝ) (hM : 0 < M) (b : Plane → UnitCircle → ℂ)
    (C : ℝ) (hC : ∀ x ∈ X, ∀ ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    ‖sourceAngularTransform ρ X M b r ω‖ ≤ C * (ρ X).toReal / M := by
  unfold sourceAngularTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_setIntegral_le_of_norm_le_const (measure_lt_top ρ X)
    (fun x hx => (angular_integrand_norm r ω x b).trans_le (hC x hx ω))
  calc
    _ ≤ M⁻¹ * (C * (ρ X).toReal) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphOriginalFubini
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem circle_pair_integral (F : UnitCircle × UnitCircle → ℂ)
    (hF : Measurable F) {C : ℝ} (hb : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, F p ∂sourceArcLength.prod sourceArcLength) =
      ∫ u, ∫ v, F (u,v) ∂sourceArcLength ∂sourceArcLength :=
  integral_prod _ (Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hb))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RadialShellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceAngularShellMeasure_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceAngularShellMeasure v Ψ univ ≤ ENNReal.ofReal (4*B) := by
  let A : ℝ := (2:ℝ)^v
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  unfold sourceAngularShellMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Ψ (r/A)/A)) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (Iic (4*A)).indicator (fun _ => ENNReal.ofReal (B/A)) r := by
      apply lintegral_mono
      intro r
      dsimp only
      by_cases hr : r ≤ 4*A
      · rw [indicator_of_mem (show r ∈ Iic (4*A) from hr)]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb _) hA.le)
      · rw [indicator_of_notMem (show r ∉ Iic (4*A) from hr)]
        rw [hs _ ((lt_div_iff₀ hA).mpr (lt_of_not_ge hr)), zero_div, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (B/A) * ENNReal.ofReal (4*A) := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iic]
      rw [inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (4*B) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hB hA.le)]
      congr 1
      rw [mul_left_comm, div_mul_cancel₀ _ hA.ne']

theorem sourceAngularShellMeasure_finite (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) : IsFiniteMeasure (sourceAngularShellMeasure v Ψ) :=
  ⟨(sourceAngularShellMeasure_mass_le v Ψ hB hb hs).trans_lt ENNReal.ofReal_lt_top⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_OriginalShellIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularShellMeasure_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0) (f : ℝ → E) :
    (∫ r, f r ∂sourceAngularShellMeasure v Ψ) =
      ((2:ℝ)^v)⁻¹ • ∫ r : ℝ, Ψ (r/(2:ℝ)^v) • f r := by
  have hR : 0 < (2:ℝ)^v := by positivity
  rw [sourceAngularShellMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hpos _) hR.le)]
  have he : (fun r => (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v) • f r) =
      fun r => ((2:ℝ)^v)⁻¹ • (Ψ (r/(2:ℝ)^v) • f r) := by
    funext r
    rw [smul_smul]
    congr 1
    ring
  rw [he, integral_smul]
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · exact Set.indicator_of_mem hr _
  · have hz : Ψ (r/(2:ℝ)^v) = 0 := hzero _ (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hR.le)
    simp [hr,hz]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularProductEnergyIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ComplexConjugate

theorem sourceRealAngularMoment_measurable (U : ℝ × UnitCircle → ℂ) (hU : Measurable U) :
    Measurable (sourceRealAngularMoment U) :=
  (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

theorem sourceRealAngularMoment_nonneg (U : ℝ × UnitCircle → ℂ) (r : ℝ) :
    0 ≤ sourceRealAngularMoment U r := integral_nonneg (fun _ => sq_nonneg _)

theorem integrable_circle_norm_square (U : UnitCircle → ℂ) (hU : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, ‖U u‖ ≤ C) :
    Integrable (fun u => ‖U u‖^2) sourceArcLength := by
  apply Integrable.of_bound (hU.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards with u
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb u)

theorem sourceRealAngularMoment_bound (U : ℝ × UnitCircle → ℂ) {C : ℝ}
    (hb : ∀ p, ‖U p‖ ≤ C) (r : ℝ) :
    sourceRealAngularMoment U r ≤ C^2*sourceArcLength.real univ := by
  have hC : 0 ≤ C := (norm_nonneg (U (r,sourceUnitDirection 0))).trans (hb _)
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with u
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb _)

theorem sourceAngularMoment_eq_ofReal (U : ℝ × UnitCircle → ℂ) (hU : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p, ‖U p‖ ≤ C) (r : ℝ) :
    sourceAngularMoment U r = ENNReal.ofReal (sourceRealAngularMoment U r) := by
  have hi := integrable_circle_norm_square (fun u => U (r,u))
    (hU.comp (measurable_const.prodMk measurable_id)) hC (fun u => hb (r,u))
  rw [sourceRealAngularMoment,ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  apply lintegral_congr
  intro u
  rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]

theorem sourceAngularH_finite_integral (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hbU : ∀ p, ‖U p‖ ≤ C) (hbV : ∀ p, ‖V p‖ ≤ D) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal = (2:ℝ)^(2*(v-a)) *
      ∫ r, sourceRealAngularMoment U r * sourceRealAngularMoment V r ∂sourceAngularShellMeasure v Ψ := by
  have hp (r : ℝ) : 0 ≤ sourceRealAngularMoment U r * sourceRealAngularMoment V r :=
    mul_nonneg (sourceRealAngularMoment_nonneg U r) (sourceRealAngularMoment_nonneg V r)
  have hi : Integrable (fun r => sourceRealAngularMoment U r * sourceRealAngularMoment V r)
      (sourceAngularShellMeasure v Ψ) := by
    apply Integrable.of_bound
      ((sourceRealAngularMoment_measurable U hU).mul (sourceRealAngularMoment_measurable V hV)).aestronglyMeasurable
      ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ))
    filter_upwards with r
    change ‖sourceRealAngularMoment U r * sourceRealAngularMoment V r‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (hp r)]
    exact mul_le_mul (sourceRealAngularMoment_bound U hbU r) (sourceRealAngularMoment_bound V hbV r)
      (sourceRealAngularMoment_nonneg V r) (by positivity)
  have he : sourceAngularH a v Ψ U V = ENNReal.ofReal ((2:ℝ)^(2*(v-a)) *
      ∫ r, sourceRealAngularMoment U r * sourceRealAngularMoment V r ∂sourceAngularShellMeasure v Ψ) := by
    simp only [sourceAngularH,sourceAngularMoment_eq_ofReal U hU hC hbU,sourceAngularMoment_eq_ofReal V hV hD hbV,
      ← ENNReal.ofReal_mul (sourceRealAngularMoment_nonneg U _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hp),
      ← ENNReal.ofReal_mul (by positivity)]
  rw [he]
  exact ⟨ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (mul_nonneg (by positivity) (integral_nonneg hp))⟩

theorem sourceAngularH_complex_integral (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hbU : ∀ p, ‖U p‖ ≤ C) (hbV : ∀ p, ‖V p‖ ≤ D) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) = ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
        ((U (r,u)*conj (U (r,u))) * (V (r,w)*conj (V (r,w)))) ∂sourceArcLength ∂sourceArcLength) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  obtain ⟨hfin,he⟩ := sourceAngularH_finite_integral a v Ψ U V hU hV hC hD hbU hbV
  refine ⟨hfin,?_⟩
  rw [he,Complex.ofReal_mul,← integral_complex_ofReal]
  rw [sourceAngularShellMeasure_integral v hΨ hpos (fun t ht => by
    by_contra hn
    have := (hs t hn).1
    linarith)]
  change ((2:ℝ)^(2*(v-a))) • (_ : ℂ) = _
  congr 2
  apply integral_congr_ae
  filter_upwards with r
  simp only [integral_smul,integral_const_mul,integral_mul_const,Complex.mul_conj,
    Complex.normSq_eq_norm_sq,integral_complex_ofReal,sourceRealAngularMoment,Complex.ofReal_mul]

theorem sourceAngularH_original_four_transform (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) :
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform ρ X M₁ b₁ z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform ν Y M₂ b₂ z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) = ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
        sourceGraphFourTransform ![ρ,ρ,ν,ν] ![X,X,Y,Y] ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂]
          (fun _ => 1) r u w ∂sourceArcLength ∂sourceArcLength) := by
  have he := sourceAngularH_complex_integral a v hΨ hpos hs hW hw
    (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
    (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2)
    (measurable_sourceAngularTransform ρ X M₁ b₁ h₁) (measurable_sourceAngularTransform ν Y M₂ b₂ h₂)
    (C := B₁*(ρ X).toReal/M₁) (D := B₂*(ν Y).toReal/M₂) (by positivity) (by positivity)
    (fun z => sourceAngularTransform_norm_le ρ X M₁ hM₁ b₁ B₁ (fun x _ => hb₁ x) z.1 z.2)
    (fun z => sourceAngularTransform_norm_le ν Y M₂ hM₂ b₂ B₂ (fun y _ => hb₂ y) z.1 z.2)
  simpa only [sourceGraphFourTransform,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one_mul] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_ProductSchurIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem product_moment_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbU : ∀ x, ‖U x‖ ≤ C) (hbV : ∀ x, ‖V x‖ ≤ D) :
    Integrable (fun r => sourceRealAngularMoment U r * sourceRealAngularMoment V r) μ := by
  apply Integrable.of_bound
    ((sourceRealAngularMoment_measurable U hU).mul (sourceRealAngularMoment_measurable V hV)).aestronglyMeasurable
    ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ))
  filter_upwards with r
  change ‖sourceRealAngularMoment U r * sourceRealAngularMoment V r‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRealAngularMoment_nonneg U r)
    (sourceRealAngularMoment_nonneg V r))]
  exact mul_le_mul (sourceRealAngularMoment_bound U hbU r) (sourceRealAngularMoment_bound V hbV r)
    (sourceRealAngularMoment_nonneg V r) (by positivity)

theorem circle_pair_schur_bound {ι : Type*} (S : Finset ι)
    (U V : ι → ℝ × UnitCircle → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ x, ‖U i x‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ x, ‖V i x‖ ≤ D i)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {d : ℝ} (_hd : 0 ≤ d)
    (hb : ∀ r u w, ‖F (r,(u,w))‖ ≤ d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2)
    (r : ℝ) :
    ‖∫ u, ∫ w, F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength‖ ≤
      d * ∑ i ∈ S, sourceRealAngularMoment (U i) r * sourceRealAngularMoment (V i) r := by
  have hiU (i : ι) (hi : i ∈ S) := integrable_circle_norm_square (fun u => U i (r,u))
    ((hU i hi).comp (measurable_const.prodMk measurable_id)) (hC i hi) (fun u => hbU i hi (r,u))
  have hiV (i : ι) (hi : i ∈ S) := integrable_circle_norm_square (fun w => V i (r,w))
    ((hV i hi).comp (measurable_const.prodMk measurable_id)) (hD i hi) (fun w => hbV i hi (r,w))
  have inner (u : UnitCircle) :
      ‖∫ w, F (r,(u,w)) ∂sourceArcLength‖ ≤
        d * ∑ i ∈ S, ‖U i (r,u)‖^2 * sourceRealAngularMoment (V i) r := by
    have hi : Integrable (fun w => d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2) sourceArcLength :=
      (integrable_finsetSum S (fun i hi => (hiV i hi).const_mul _)).const_mul d
    have he := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall (hb r u))
    simpa only [integral_const_mul,integral_finsetSum S (fun i hi => (hiV i hi).const_mul _),
      sourceRealAngularMoment] using he
  have hi : Integrable (fun u => d * ∑ i ∈ S, ‖U i (r,u)‖^2*sourceRealAngularMoment (V i) r) sourceArcLength :=
    (integrable_finsetSum S (fun i hi => (hiU i hi).mul_const _)).const_mul d
  have he := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall inner)
  simpa only [integral_const_mul,integral_finsetSum S (fun i hi => (hiU i hi).mul_const _),
    integral_mul_const,sourceRealAngularMoment] using he

theorem original_product_schur_integral {ι : Type*} (S : Finset ι)
    (U V : ι → ℝ × UnitCircle → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ x, ‖U i x‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ x, ‖V i x‖ ≤ D i)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {d : ℝ} (hd : 0 ≤ d)
    (hb : ∀ r u w, ‖F (r,(u,w))‖ ≤ d * ∑ i ∈ S, ‖U i (r,u)‖^2*‖V i (r,w)‖^2)
    (p v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ‖((2:ℝ)^(2*(v-p))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) • F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength)‖ ≤
      d * ∑ i ∈ S, (sourceAngularH p v Ψ (U i) (V i)).toReal := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hzero : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  have hi (i : ι) (hi : i ∈ S) := product_moment_integrable (sourceAngularShellMeasure v Ψ)
    (U i) (V i) (hU i hi) (hV i hi) (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  have hh := norm_integral_le_of_norm_le
    ((integrable_finsetSum S hi).const_mul d)
    (Filter.Eventually.of_forall (circle_pair_schur_bound S U V hU hV C D hC hD hbU hbV F hd hb))
  have he (i : ι) (hi : i ∈ S) := (sourceAngularH_finite_integral p v Ψ
    (U i) (V i) (hU i hi) (hV i hi) (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)).2
  simp_rw [integral_smul]
  rw [← sourceAngularShellMeasure_integral v hΨ hpos hzero]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-p)))]
  calc
    _ ≤ (2:ℝ)^(2*(v-p)) * (∫ r, d * ∑ i ∈ S,
        sourceRealAngularMoment (U i) r * sourceRealAngularMoment (V i) r ∂sourceAngularShellMeasure v Ψ) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum S hi]
      simp_rw [Finset.sum_congr rfl he]
      rw [← Finset.mul_sum]
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularKernelIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angularKernelIntegral_original (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) (hF : Measurable F)
    {C : ℝ} (hb : ∀ z, ‖F z‖ ≤ C) :
    angularKernelIntegral a v Ψ F = ((2:ℝ)^(2*(v-a))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) • F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength) := by
  have hi : Integrable F ((sourceAngularShellMeasure v Ψ).prod (sourceArcLength.prod sourceArcLength)) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  rw [angularKernelIntegral,integral_prod _ hi]
  have he (r : ℝ) := circle_pair_integral (fun z => F (r,z))
    (hF.comp (measurable_const.prodMk measurable_id)) (fun z => hb (r,z))
  simp_rw [he]
  rw [sourceAngularShellMeasure_integral v hΨ hpos hzero]
  simp only [integral_smul]

theorem angularKernelIntegral_add (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (F G : ℝ × (UnitCircle × UnitCircle) → ℂ) (hF : Measurable F) (hG : Measurable G)
    {C D : ℝ} (hbF : ∀ z, ‖F z‖ ≤ C) (hbG : ∀ z, ‖G z‖ ≤ D) :
    angularKernelIntegral a v Ψ (fun z => F z+G z) =
      angularKernelIntegral a v Ψ F + angularKernelIntegral a v Ψ G := by
  rw [angularKernelIntegral,integral_add
    (Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hbF))
    (Integrable.of_bound hG.aestronglyMeasurable D (Filter.Eventually.of_forall hbG)),smul_add]
  rfl

theorem angularKernelIntegral_smul (a v c : ℝ) (Ψ : ℝ → ℝ)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) :
    angularKernelIntegral a v Ψ (fun z => c • F z) = c • angularKernelIntegral a v Ψ F := by
  simp only [angularKernelIntegral,integral_smul]
  exact smul_comm _ _ _

theorem angularKernelIntegral_outer (a p v c : ℝ) (hc : 0 ≤ c) (Ψ : ℝ → ℝ)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) :
    ‖c • angularKernelIntegral a v Ψ F‖ =
      (2:ℝ)^(2*(p-a))*c*‖angularKernelIntegral p v Ψ F‖ := by
  rw [angularKernelIntegral,angularKernelIntegral,smul_comm c]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,
    abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-a))),
    abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-p)))]
  have he : (2:ℝ)^(2*(v-a)) = (2:ℝ)^(2*(p-a))*(2:ℝ)^(2*(v-p)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [he]
  ring

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_FinsetSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finset_bipartite_schur {α β : Type*} (A : Finset α) (B : Finset β)
    (G : α → β → Prop) [DecidableRel G] (u : α → ℝ) (v : β → ℝ) (d : ℝ)
    (hrow : ∀ a ∈ A, ((B.filter (G a)).card : ℝ) ≤ d)
    (hcol : ∀ b ∈ B, ((A.filter (fun a => G a b)).card : ℝ) ≤ d) :
    (∑ a ∈ A, ∑ b ∈ B, if G a b then u a*v b else 0) ≤
      d/2*((∑ a ∈ A, u a^2)+(∑ b ∈ B, v b^2)) := by
  have hp (a : α) (b : β) : 2*(if G a b then u a*v b else 0) ≤
      (if G a b then u a^2 else 0)+(if G a b then v b^2 else 0) := by
    split_ifs
    · nlinarith [sq_nonneg (u a-v b)]
    · norm_num
  have hs := Finset.sum_le_sum (s := A) (fun a _ =>
    Finset.sum_le_sum (s := B) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hR : (∑ a ∈ A, ∑ b ∈ B, if G a b then u a^2 else 0) ≤ d*(∑ a ∈ A, u a^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hrow a ha) (sq_nonneg _)
  have hC : (∑ a ∈ A, ∑ b ∈ B, if G a b then v b^2 else 0) ≤ d*(∑ b ∈ B, v b^2) := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  nlinarith

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNearNeighbors
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
attribute [local instance] Classical.propDecidable

theorem angularNear_symm (Q₁ Q₂ : DyadicSquare) (p : ℕ) (row col : CellPath × CellPath) :
    angularNear Q₁ Q₂ p row col ↔ angularNear Q₁ Q₂ p col row := by
  simp only [angularNear,dist_comm]

theorem dyadic_twenty_neighbors (Q : DyadicSquare) (hQ : Q.side = 1)
    (p : ℕ) (x : Plane) :
    (((dyadicPaths p).filter (fun c => dist x (Q.descendant c).center ≤ 20/(2:ℝ)^p)).card : ℝ) ≤ 1936 := by
  classical
  have hpos : 0 < Q.side := by rw [hQ]; norm_num
  have hsub : (dyadicPaths p).filter (fun c => dist x (Q.descendant c).center ≤ 20/(2:ℝ)^p) ⊆
      cellsMeeting Q p x (21/(2:ℝ)^p) := by
    intro c hc
    obtain ⟨hc,hb⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_filter.mpr ⟨hc,(Q.descendant c).center,
      (Q.descendant c).center_mem (Q.descendant_side_pos hpos c),?_⟩
    rw [mem_ball,dist_comm]
    exact hb.trans_lt (div_lt_div_of_pos_right (by norm_num) (by positivity))
  have hh := dyadic_scaled_ball_card_le Q hpos p x (C₀ := 21) (by norm_num)
    (r := 21/(2:ℝ)^p) (by rw [hQ]; ring_nf; exact le_rfl)
  norm_num at hh
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (by exact_mod_cast hh)

theorem angularNear_degree (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (row : CellPath × CellPath) :
    ((C.filter (angularNear Q₁ Q₂ p row)).card : ℝ) ≤ 3748096 := by
  classical
  let S₁ := (dyadicPaths p).filter (fun c =>
    dist (Q₁.descendant row.1).center (Q₁.descendant c).center ≤ 20/(2:ℝ)^p)
  let S₂ := (dyadicPaths p).filter (fun c =>
    dist (Q₂.descendant row.2).center (Q₂.descendant c).center ≤ 20/(2:ℝ)^p)
  have hsub : C.filter (angularNear Q₁ Q₂ p row) ⊆ S₁ ×ˢ S₂ := by
    intro col hc
    obtain ⟨hc,hnear⟩ := Finset.mem_filter.mp hc
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hC hc)
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨h1,hnear.1⟩,
      Finset.mem_filter.mpr ⟨h2,hnear.2⟩⟩
  have h1 := dyadic_twenty_neighbors Q₁ hQ₁ p (Q₁.descendant row.1).center
  have h2 := dyadic_twenty_neighbors Q₂ hQ₂ p (Q₂.descendant row.2).center
  have hh := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
  rw [Finset.card_product,Nat.cast_mul] at hh
  exact hh.trans (by nlinarith [mul_le_mul h1 h2 (Nat.cast_nonneg S₂.card) (by norm_num : (0:ℝ) ≤ 1936)])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNearSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem angularRestrictedSum_complement (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) (U V : CellPath → ℂ) :
    angularRestrictedSum C G U V + angularRestrictedSum C (fun row col => ¬ G row col) U V =
      ∑ row ∈ C, ∑ col ∈ C, angularPairTerm U V row col := by
  simp only [angularRestrictedSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  by_cases h : G row col <;> simp [h]

theorem angularRestrictedSum_schur (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℂ) (d : ℝ)
    (hr : ∀ row ∈ C, ((C.filter (G row)).card : ℝ) ≤ d)
    (hc : ∀ col ∈ C, ((C.filter (fun row => G row col)).card : ℝ) ≤ d) :
    ‖angularRestrictedSum C G U V‖ ≤ d * ∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2 := by
  classical
  have hh := finset_bipartite_schur C C G
    (fun row => ‖U row.1‖*‖V row.2‖) (fun row => ‖U row.1‖*‖V row.2‖) d hr hc
  have hn : ‖angularRestrictedSum C G U V‖ ≤
      ∑ row ∈ C, ∑ col ∈ C, if G row col then
        (‖U row.1‖*‖V row.2‖)*(‖U col.1‖*‖V col.2‖) else 0 := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro row _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro col _
    by_cases hg : G row col
    · simp only [hg,↓reduceIte,angularPairTerm,norm_mul,Complex.norm_conj]
      exact le_of_eq (by ring)
    · simp [hg]
  apply hn.trans (hh.trans_eq ?_)
  simp only [mul_pow]
  ring

theorem angularNearSum_bound (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p)) (U V : CellPath → ℂ) :
    ‖angularRestrictedSum C (angularNear Q₁ Q₂ p) U V‖ ≤
      3748096 * ∑ row ∈ C, ‖U row.1‖^2*‖V row.2‖^2 := by
  apply angularRestrictedSum_schur
  · intro row _
    exact angularNear_degree Q₁ Q₂ hQ₁ hQ₂ p C hC row
  · intro col _
    simp_rw [angularNear_symm Q₁ Q₂ p _ col]
    exact angularNear_degree Q₁ Q₂ hQ₁ hQ₂ p C hC col

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularRestrictedKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem angularRestrictedKernel_measurable (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ)
    (hU : ∀ P, Measurable (U P)) (hV : ∀ Q, Measurable (V Q)) :
    Measurable (angularRestrictedKernel C G U V) := by
  unfold angularRestrictedKernel angularRestrictedSum angularPairTerm
  apply Finset.measurable_sum
  intro row _
  apply Finset.measurable_sum
  intro col _
  by_cases hg : G row col
  · simp only [hg,↓reduceIte]
    exact ((hU row.1).comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (Complex.continuous_conj.measurable.comp ((hU col.1).comp (measurable_fst.prodMk measurable_snd.fst))) |>.mul
      (((hV row.2).comp (measurable_fst.prodMk measurable_snd.snd)).mul
      (Complex.continuous_conj.measurable.comp ((hV col.2).comp (measurable_fst.prodMk measurable_snd.snd))))
  · simp only [hg,↓reduceIte]
    exact measurable_const

theorem angularRestrictedKernel_bound (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbU : ∀ P z, ‖U P z‖ ≤ B) (hbV : ∀ Q z, ‖V Q z‖ ≤ D)
    (z : ℝ × (UnitCircle × UnitCircle)) :
    ‖angularRestrictedKernel C G U V z‖ ≤ (C.card:ℝ)^2*(B^2*D^2) := by
  have ht (row col : CellPath × CellPath) :
      ‖if G row col then angularPairTerm (fun P => U P (z.1,z.2.1))
        (fun Q => V Q (z.1,z.2.2)) row col else 0‖ ≤ B^2*D^2 := by
    by_cases hg : G row col
    · simp only [hg,↓reduceIte,angularPairTerm,norm_mul,Complex.norm_conj]
      simpa only [pow_two] using mul_le_mul
        (mul_le_mul (hbU row.1 _) (hbU col.1 _) (norm_nonneg _) hB)
        (mul_le_mul (hbV row.2 _) (hbV col.2 _) (norm_nonneg _) hD)
        (by positivity) (by positivity)
    · simp only [hg,↓reduceIte,norm_zero]
      positivity
  calc
    _ ≤ ∑ row ∈ C, ∑ col ∈ C, B^2*D^2 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro row _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun col _ => ht row col))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem angularRestrictedIntegral_complement (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ)
    (hU : ∀ P, Measurable (U P)) (hV : ∀ Q, Measurable (V Q))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbU : ∀ P z, ‖U P z‖ ≤ B) (hbV : ∀ Q z, ‖V Q z‖ ≤ D) :
    angularKernelIntegral a v Ψ (angularRestrictedKernel C G U V) +
      angularKernelIntegral a v Ψ (angularRestrictedKernel C (fun row col => ¬ G row col) U V) =
      angularKernelIntegral a v Ψ (fun z => ∑ row ∈ C, ∑ col ∈ C,
        angularPairTerm (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col) := by
  rw [← angularKernelIntegral_add a v Ψ _ _
    (angularRestrictedKernel_measurable C G U V hU hV)
    (angularRestrictedKernel_measurable C _ U V hU hV)
    (angularRestrictedKernel_bound C G U V hB hD hbU hbV)
    (angularRestrictedKernel_bound C _ U V hB hD hbU hbV)]
  congr 1
  funext z
  exact angularRestrictedSum_complement C G _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularCellKernels
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angularCellTransform_measurable (Q : DyadicSquare) (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (M : ℝ) (β : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2)) (P : CellPath) :
    Measurable (angularCellTransform Q ρ M β P) :=
  measurable_sourceAngularTransform ρ _ M β hβ

theorem sourceAngularTransform_global_bound (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {M : ℝ} (hM : 0 < M) (β : Plane → UnitCircle → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ x u, ‖β x u‖ ≤ D) (r : ℝ) (u : UnitCircle) :
    ‖sourceAngularTransform ρ X M β r u‖ ≤ D*(ρ univ).toReal/M := by
  apply (sourceAngularTransform_norm_le ρ X M hM β D (fun x _ => hb x) r u).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (measure_ne_top ρ univ) (measure_mono (subset_univ X))) hD) hM.le

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularOccupiedPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem angular_pair_sum_product (S T : Finset CellPath) (U V : CellPath → ℂ) :
    (∑ row ∈ S ×ˢ T, ∑ col ∈ S ×ˢ T, angularPairTerm U V row col) =
      ((∑ P ∈ S, U P)*conj (∑ P ∈ S, U P))*
      ((∑ Q ∈ T, V Q)*conj (∑ Q ∈ T, V Q)) := by
  have ht (row col : CellPath × CellPath) :
      angularPairTerm U V row col = (U row.1*V row.2)*conj (U col.1*V col.2) := by
    simp only [angularPairTerm,map_mul]
    ring
  simp_rw [ht]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul,← map_sum]
  simp only [Finset.sum_product,← Finset.mul_sum,← Finset.sum_mul,map_mul]
  ring

theorem sourceAngularTransform_split_absolute
    (Q : DyadicSquare) (hQ : 0 < Q.side) (A : CellPath)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (n : ℕ) (Ma Mp : ℝ) (hMp : Mp ≠ 0)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2))
    (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ (Q.descendant A).carrier Ma b r ω =
      (Mp / Ma) • ∑ P ∈ (occupiedAnchorPaths (Q.descendant A) ρ n).image (fun c => A++c),
        sourceAngularTransform ρ (Q.descendant P).carrier Mp b r ω := by
  classical
  rw [sourceAngularTransform_split (Q.descendant A) (Q.descendant_side_pos hQ A)
    ρ n Ma Mp hMp b hb C hC]
  congr 1
  rw [Finset.sum_image (fun _ _ _ _ he => List.append_cancel_left he)]
  simp only [DyadicSquare.descendant_append]

theorem angular_parent_occupied_partition
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : CellPath) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (n : ℕ) (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    (D₁ D₂ : ℝ) (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (r : ℝ) (u w : UnitCircle) :
    let U := sourceAngularTransform ρ (Q₁.descendant A).carrier Ma₁ β r u
    let V := sourceAngularTransform ν (Q₂.descendant B).carrier Ma₂ γ r w
    let Uc := fun P => sourceAngularTransform ρ (Q₁.descendant P).carrier Mp₁ β r u
    let Vc := fun Q => sourceAngularTransform ν (Q₂.descendant Q).carrier Mp₂ γ r w
    (U*conj U)*(V*conj V) = ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, angularPairTerm Uc Vc row col := by
  dsimp only
  rw [sourceProductVertices,angular_pair_sum_product]
  rw [sourceAngularTransform_split_absolute Q₁ hQ₁ A ρ n Ma₁ Mp₁ hMp₁ β hβ D₁ hbβ,
    sourceAngularTransform_split_absolute Q₂ hQ₂ B ν n Ma₂ Mp₂ hMp₂ γ hγ D₂ hbγ]
  simp only [Complex.real_smul,map_mul,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularParentNearFar
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem sourceAngularH_kernel (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) = angularKernelIntegral a v Ψ
      (fun z => (U (z.1,z.2.1)*conj (U (z.1,z.2.1)))*(V (z.1,z.2.2)*conj (V (z.1,z.2.2)))) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hz : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  have hm : Measurable (fun z : ℝ × (UnitCircle × UnitCircle) =>
      (U (z.1,z.2.1)*conj (U (z.1,z.2.1)))*(V (z.1,z.2.2)*conj (V (z.1,z.2.2)))) := by
    fun_prop
  have hb (z : ℝ × (UnitCircle × UnitCircle)) :
      ‖(U (z.1,z.2.1)*conj (U (z.1,z.2.1)))*(V (z.1,z.2.2)*conj (V (z.1,z.2.2)))‖ ≤ C^2*D^2 := by
    simp only [norm_mul,Complex.norm_conj,← pow_two]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hbU _) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hbV _) 2) (sq_nonneg _) (sq_nonneg _)
  rw [angularKernelIntegral_original a v hΨ hpos hz _ hm hb]
  exact sourceAngularH_complex_integral a v hΨ hpos hs hW hw U V hU hV hC hD hbU hbV

theorem angular_parent_near_far
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : CellPath) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (n : ℕ) (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    {Ma₁ Ma₂ Mp₁ Mp₂ : ℝ} (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) :
    let U := angularCellTransform Q₁ ρ Ma₁ β A
    let V := angularCellTransform Q₂ ν Ma₂ γ B
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    ((sourceAngularH a v Ψ U V).toReal : ℂ) =
      angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ G +
      angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ (fun row col => ¬ G row col) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  let U := angularCellTransform Q₁ ρ Ma₁ β A
  let V := angularCellTransform Q₂ ν Ma₂ γ B
  have hu := angularCellTransform_measurable Q₁ ρ Ma₁ β hβ A
  have hv := angularCellTransform_measurable Q₂ ν Ma₂ γ hγ B
  have hbu := fun z : ℝ × UnitCircle =>
    sourceAngularTransform_global_bound ρ (Q₁.descendant A).carrier hMa₁ β hD₁ hbβ z.1 z.2
  have hbv := fun z : ℝ × UnitCircle =>
    sourceAngularTransform_global_bound ν (Q₂.descendant B).carrier hMa₂ γ hD₂ hbγ z.1 z.2
  have hh := sourceAngularH_kernel a v hΨ hpos hs hW hw U V hu hv
    (C := D₁*(ρ univ).toReal/Ma₁) (D := D₂*(ν univ).toReal/Ma₂) (by positivity) (by positivity) hbu hbv
  refine ⟨hh.1,hh.2.trans ?_⟩
  let C := sourceProductVertices Q₁ Q₂ ρ ν A B n
  let Uc := angularCellTransform Q₁ ρ Mp₁ β
  let Vc := angularCellTransform Q₂ ν Mp₂ γ
  have hsplit := angularRestrictedIntegral_complement a v Ψ C G Uc Vc
    (angularCellTransform_measurable Q₁ ρ Mp₁ β hβ)
    (angularCellTransform_measurable Q₂ ν Mp₂ γ hγ)
    (B := D₁*(ρ univ).toReal/Mp₁) (D := D₂*(ν univ).toReal/Mp₂) (by positivity) (by positivity)
    (fun P z => sourceAngularTransform_global_bound ρ _ hMp₁ β hD₁ hbβ z.1 z.2)
    (fun P z => sourceAngularTransform_global_bound ν _ hMp₂ γ hD₂ hbγ z.1 z.2)
  unfold angularCellContribution
  rw [← smul_add,hsplit,← angularKernelIntegral_smul]
  congr 1
  funext z
  exact angular_parent_occupied_partition Q₁ Q₂ hQ₁ hQ₂ A B ρ ν n Ma₁ Ma₂ Mp₁ Mp₂
    hMp₁.ne' hMp₂.ne' β γ hβ hγ D₁ D₂ hbβ hbγ z.1 z.2.1 z.2.2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNearIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angularNearIntegral_bound
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (U V : CellPath → ℝ × UnitCircle → ℂ)
    (hU : ∀ P, Measurable (U P)) (hV : ∀ Q, Measurable (V Q))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbU : ∀ P z, ‖U P z‖ ≤ B) (hbV : ∀ Q z, ‖V Q z‖ ≤ D)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ‖angularKernelIntegral p v Ψ (angularRestrictedKernel C (angularNear Q₁ Q₂ p) U V)‖ ≤
      3748096 * ∑ row ∈ C, (sourceAngularH p v Ψ (U row.1) (V row.2)).toReal := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hz : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  rw [angularKernelIntegral_original p v hΨ hpos hz _
    (angularRestrictedKernel_measurable C _ U V hU hV)
    (angularRestrictedKernel_bound C _ U V hB hD hbU hbV)]
  apply original_product_schur_integral C (fun row => U row.1) (fun row => V row.2)
    (fun row _ => hU row.1) (fun row _ => hV row.2) (fun _ => B) (fun _ => D)
    (fun _ _ => hB) (fun _ _ => hD) (fun row _ => hbU row.1) (fun row _ => hbV row.2)
    _ (by norm_num) _ p v hΨ hpos hs hW hw
  intro r u w
  exact angularNearSum_bound Q₁ Q₂ hQ₁ hQ₂ p C hC _ _

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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNearProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

theorem angular_near_profile_factor (N : ℕ) (hN : 0 < N)
    (m₁ m₂ : ℝ → ℝ) (a p lam : ℝ) :
    (2:ℝ)^(2*(p-a))*
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2*
       (((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) *
      3748096 * (4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) =
      15352201216*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+12*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [two_rpow_as_scale N hN]
  simp only [← Real.rpow_sub hR,pow_two]
  have he (x y z t : ℝ) : x*(y*y*(z*z))*3748096*(4096*t) = 15352201216*(x*y*y*z*z*t) := by ring
  rw [he]
  simp only [← Real.rpow_add hR]
  congr 2
  ring

theorem angular_near_profile_sum_bound {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞)
    (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) (a p lam : ℝ)
    (hcard : (S.card:ℝ) ≤ 4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) :
    (2:ℝ)^(2*(p-a))*
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2*
       (((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) *
      (3748096 * ∑ i ∈ S, (E i).toReal) ≤
      15352201216*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+12*lam)*
        finiteEnergyMaximum S E := by
  have hh := (sum_energy_le_maximum S E).trans
    (mul_le_mul_of_nonneg_right hcard (finiteEnergyMaximum_nonneg S E))
  calc
    _ ≤ (2:ℝ)^(2*(p-a))*
      ((((2:ℝ)^N)^(-m₁ p)/((2:ℝ)^N)^(-m₁ a))^2*
       (((2:ℝ)^N)^(-m₂ p)/((2:ℝ)^N)^(-m₂ a))^2) *
      (3748096 * ((4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam))*finiteEnergyMaximum S E)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by norm_num)) (by positivity)
    _ = _ := by
      rw [← mul_assoc,← mul_assoc,angular_near_profile_factor N hN]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RegularizedAngularNear
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem regularized_angular_near_bound
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (N B₀ : ℕ) (hN : 0 < N) (δ lam : ℝ) (m₁ m₂ : ℝ → ℝ)
    (hd₁ : RegularizedProfileData Q₁ ρ N B₀ δ lam m₁)
    (hd₂ : RegularizedProfileData Q₂ ν N B₀ δ lam m₂)
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a) (hp : a+n ≤ N)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    let R := (2:ℝ)^N
    let Uc := angularCellTransform Q₁ ρ (R^(-m₁ (a+n))) β
    let Vc := angularCellTransform Q₂ ν (R^(-m₂ (a+n))) γ
    ‖angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ
        (R^(-m₁ a)) (R^(-m₂ a)) (R^(-m₁ (a+n))) (R^(-m₂ (a+n)))
        β γ (angularNear Q₁ Q₂ (a+n))‖ ≤
      15352201216*R^(-(m₁ (a+n)-((a:ℝ)+n)/N-(m₁ a-(a:ℝ)/N))
        -(m₂ (a+n)-((a:ℝ)+n)/N-(m₂ a-(a:ℝ)/N))+12*lam)*
      finiteEnergyMaximum (sourceProductVertices Q₁ Q₂ ρ ν A B n)
        (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) := by
  let C := sourceProductVertices Q₁ Q₂ ρ ν A B n
  let Uc := angularCellTransform Q₁ ρ (((2:ℝ)^N)^(-m₁ (a+n))) β
  let Vc := angularCellTransform Q₂ ν (((2:ℝ)^N)^(-m₂ (a+n))) γ
  have h1 : 0 < ((2:ℝ)^N)^(-m₁ (a+n)) := by positivity
  have h2 : 0 < ((2:ℝ)^N)^(-m₂ (a+n)) := by positivity
  have hh := angularNearIntegral_bound Q₁ Q₂ hQ₁ hQ₂ (a+n) C
    (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB) Uc Vc
    (angularCellTransform_measurable Q₁ ρ _ β hβ)
    (angularCellTransform_measurable Q₂ ν _ γ hγ)
    (B := D₁*(ρ univ).toReal/((2:ℝ)^N)^(-m₁ (a+n)))
    (D := D₂*(ν univ).toReal/((2:ℝ)^N)^(-m₂ (a+n))) (by positivity) (by positivity)
    (fun P z => sourceAngularTransform_global_bound ρ _ h1 β hD₁ hbβ z.1 z.2)
    (fun P z => sourceAngularTransform_global_bound ν _ h2 γ hD₂ hbγ z.1 z.2)
    v hΨ hpos hs hW hw
  simp only [Nat.cast_add] at hh
  have hc := sourceProductVertices_profile_count Q₁ Q₂ hQ₁ hQ₂ ρ ν N B₀ δ lam m₁ m₂ hd₁ hd₂ A B a n hA hB hp
  have hm := angular_near_profile_sum_bound C
    (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) N hN m₁ m₂ a (a+n) lam hc
  dsimp only
  unfold angularCellContribution
  rw [angularKernelIntegral_outer a (a+n) v _ (by positivity)]
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  simpa only [Nat.cast_add,C,Uc,Vc] using hm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ActualProductEnergyFinite
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

theorem inherited_product_energy_finite
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (mass : Fin 2 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (X Y : Set Plane) (p v : ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    sourceAngularH p v Ψ
      (fun z => sourceAngularTransform (ρ 0) X M₁ (β 0) z.1 z.2)
      (fun z => sourceAngularTransform (ρ 1) Y M₂ (β 1) z.1 z.2) ≠ ⊤ := by
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  exact (sourceAngularH_original_four_transform p v hΨ.continuous.measurable hpos hs hW
    (fun t => (le_abs_self _).trans (hw t)) (ρ 0) (ρ 1) X Y hM₁ hM₂ (β 0) (β 1) (hm 0) (hm 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K) (hb 0) (hb 1)).1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularNear
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem actual_angular_near_fixed_oai
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, (Q l).side = 1)
    (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (N B₀ : ℕ) (hN : 0 < N)
    (δ lam sig : ℝ) (hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam (mass l))
    (J i : ℕ) (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a) (hp : a+n ≤ N)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let R := (2:ℝ)^N
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l (p : ℝ) => R^(-mass l p)
    let U := angularCellTransform (Q 0) (ρ 0) (M 0 a) (β 0) A
    let V := angularCellTransform (Q 1) (ρ 1) (M 1 a) (β 1) B
    let E := fun row : CellPath × CellPath => sourceAngularH (a+n) v Ψ
      (angularCellTransform (Q 0) (ρ 0) (M 0 (a+n)) (β 0) row.1)
      (angularCellTransform (Q 1) (ρ 1) (M 1 (a+n)) (β 1) row.2)
    let near := angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B n a v Ψ
      (M 0 a) (M 1 a) (M 0 (a+n)) (M 1 (a+n)) (β 0) (β 1) (angularNear (Q 0) (Q 1) (a+n))
    let far := angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B n a v Ψ
      (M 0 a) (M 1 a) (M 0 (a+n)) (M 1 (a+n)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+n) row col)
    sourceAngularH a v Ψ U V ≠ ⊤ ∧ (∀ row, E row ≠ ⊤) ∧
      ((sourceAngularH a v Ψ U V).toReal : ℂ) = near+far ∧
      ‖near‖ ≤ 15352201216*R^(
        -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
        -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))+12*lam)*
        finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) E := by
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  have hQpos (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  let D := symbolDerivativeConstant K^K
  have hD : 0 ≤ D := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hb (l : Fin 2) (x : Plane) (u : UnitCircle) : ‖β l x u‖ ≤ D :=
    inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQpos l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) u
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hw' := fun t => (le_abs_self (Ψ t)).trans (hw t)
  have hparent := angular_parent_near_far (Q 0) (Q 1) (hQpos 0) (hQpos 1) A B (ρ 0) (ρ 1)
    n a v hΨ.continuous.measurable hpos hs hW hw'
    (Ma₁ := ((2:ℝ)^N)^(-mass 0 a)) (Ma₂ := ((2:ℝ)^N)^(-mass 1 a))
    (Mp₁ := ((2:ℝ)^N)^(-mass 0 (a+n))) (Mp₂ := ((2:ℝ)^N)^(-mass 1 (a+n)))
    (by positivity) (by positivity) (by positivity) (by positivity)
    (β 0) (β 1) (hm 0) (hm 1) hD hD (hb 0) (hb 1) (angularNear (Q 0) (Q 1) (a+n))
  have hnear := regularized_angular_near_bound (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1)
    N B₀ hN δ lam (mass 0) (mass 1) (hd 0) (hd 1) A B a n hA hB hp
    (β 0) (β 1) (hm 0) (hm 1) hD hD (hb 0) (hb 1) v hΨ.continuous.measurable hpos hs hW hw'
  dsimp only
  refine ⟨hparent.1,?_,hparent.2,hnear⟩
  intro row
  exact inherited_product_energy_finite S d k K hK Q hQpos ρ mass N lam sig J i h hh hhb
    ((Q 0).descendant row.1).carrier ((Q 1).descendant row.2).carrier (a+n) v
    (by positivity) (by positivity) hΨ hpos hs

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.actual_angular_near_fixed_oai := @OAI.PlanarFalconer.actual_angular_near_fixed_oai
