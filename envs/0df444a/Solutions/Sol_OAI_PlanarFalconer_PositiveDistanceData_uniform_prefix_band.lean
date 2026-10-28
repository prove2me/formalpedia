-- Prove2me | solution 1 for OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:03:51.358365+00:00
-- url     : https://prove2.me/submissions/1a23ebfe-ac98-4728-a049-8ac6129d1903

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_prefix_high_shell
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_distance_low_band

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

theorem smoothAngleMask_eq_one (G : Set ℝ) (η : ℝ) (hη : 0 < η) {x : ℝ} (hx : x ∈ G) :
    smoothAngleMask G η hη x = 1 := by
  have hi : thickenedIndicator G η x = 1 := by
    apply Set.indicator_of_mem
    exact mem_thickening_iff.mpr ⟨x,hx,by simpa using mul_pos (by norm_num : (0:ℝ)<2) hη⟩
  rw [smoothAngleMask,← hi]
  apply ContDiffBump.normed_convolution_eq_right
  intro y hy
  rw [hi]
  apply Set.indicator_of_mem
  apply mem_thickening_iff.mpr
  refine ⟨x,hx,?_⟩
  change dist y x < η at hy
  linarith

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

theorem sourceTestMask_eq_one (G : Set UnitCircle) (d : ℝ) (hd : 0 < d)
    {θ : ℝ} (hθ : sourceUnitDirection θ ∈ G) : sourceTestMask G d hd θ = 1 :=
  smoothAngleMask_eq_one _ _ _ hθ

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

theorem circleTestMask_eq_one (G : Set UnitCircle) (d : ℝ) (hd : 0 < d)
    {dir : UnitCircle} (hdir : dir ∈ G) : circleTestMask G d hd dir = 1 := by
  apply sourceTestMask_eq_one
  simpa only [sourceUnitDirection_sourceAngle] using hdir

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

theorem ae_occupied_anchor (Q : DyadicSquare) (ρ : Measure Plane) (hcarry : ρ Q.carrierᶜ = 0) (n : ℕ) :
    ∀ᵐ x ∂ρ, ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier := by
  have hroot : ∀ᵐ x ∂ρ, x ∈ Q.carrier := ae_iff.mpr hcarry
  have hz : ∀ᵐ x ∂ρ, ∀ P : CellPath, ρ (Q.descendant P).carrier = 0 → x ∉ (Q.descendant P).carrier := by
    apply ae_all_iff.mpr
    intro P
    by_cases h : ρ (Q.descendant P).carrier = 0
    · filter_upwards [show ∀ᵐ x ∂ρ, x ∉ (Q.descendant P).carrier from by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (fun _ h' => (h h').elim)
  filter_upwards [hroot,hz] with x hx hzero
  obtain ⟨P,hP,hx⟩ := Q.mem_descendant_at_depth n hx
  refine ⟨P,Finset.mem_filter.mpr ⟨hP,?_⟩,hx⟩
  exact bot_lt_iff_ne_bot.mpr (fun he => hzero P he hx)

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

theorem sourceAngularShellMeasure_real_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    (sourceAngularShellMeasure v Ψ).real univ ≤ 4*B := by
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (sourceAngularShellMeasure_mass_le v Ψ hB hb hs)).trans_eq
  exact ENNReal.toReal_ofReal (by positivity)

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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ProfileMassError
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem RegularizedProfileData.normalized_cell_mass_le
    {Q : DyadicSquare} {ρ : Measure Plane} {N B : ℕ} {δ lam : ℝ} {m : ℝ → ℝ}
    (hd : RegularizedProfileData Q ρ N B δ lam m) {a : ℕ} (ha : a ≤ N)
    {A : CellPath} (hA : A.length = a) :
    (ρ (Q.descendant A).carrier).toReal / ((2:ℝ)^N)^(-m a) ≤ ((2:ℝ)^N)^(3*lam) := by
  have hM : 0 < ((2:ℝ)^N)^(-m a) := Real.rpow_pos_of_pos (by positivity) _
  apply (div_le_iff₀ hM).mpr
  by_cases hp : 0 < ρ (Q.descendant A).carrier
  · exact (hd.cells a ha A hA hp).2
  · have hz : ρ (Q.descendant A).carrier = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz, ENNReal.toReal_zero]
    positivity

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularCellKernels
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTerminalBound
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularH_uniform_bound (a v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0)
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal ≤
      (2:ℝ)^(2*(v-a)) * ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ)) * (4*W) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw hs
  obtain ⟨hf,he⟩ := sourceAngularH_finite_integral a v Ψ U V hU hV hC hD hbU hbV
  refine ⟨hf,?_⟩
  rw [he]
  have hb : ∀ᵐ r ∂sourceAngularShellMeasure v Ψ,
      ‖sourceRealAngularMoment U r*sourceRealAngularMoment V r‖ ≤
        (C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ) := by
    filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRealAngularMoment_nonneg U r)
      (sourceRealAngularMoment_nonneg V r))]
    exact mul_le_mul (sourceRealAngularMoment_bound U hbU r) (sourceRealAngularMoment_bound V hbV r)
      (sourceRealAngularMoment_nonneg V r) (by positivity)
  have hi := (le_abs_self (∫ r, sourceRealAngularMoment U r*sourceRealAngularMoment V r
      ∂sourceAngularShellMeasure v Ψ)).trans (norm_integral_le_of_norm_le_const hb)
  have hm := sourceAngularShellMeasure_real_mass_le v Ψ hW hw hs
  calc
    _ ≤ (2:ℝ)^(2*(v-a)) *
        ((sourceAngularShellMeasure v Ψ).real univ * ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ))) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hi) (by positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hm
        (by positivity : 0 ≤ ((C^2*sourceArcLength.real univ)*(D^2*sourceArcLength.real univ)))
      nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ (2:ℝ)^(2*(v-a)))]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceFourierDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate

theorem integral_distanceDifferenceMeasure (μ : Measure ℝ) (F : ℝ → ℂ)
    (hF : StronglyMeasurable F) :
    (∫ s, F s ∂distanceDifferenceMeasure μ) = ∫ z, F (z.1-z.2) ∂μ.prod μ :=
  integral_map_of_stronglyMeasurable (by fun_prop) hF

theorem charFun_distanceDifferenceMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    charFun (distanceDifferenceMeasure μ) r = (‖charFun μ r‖^2:ℂ) := by
  rw [charFun_apply_real,integral_distanceDifferenceMeasure μ _ (by fun_prop)]
  have he : (fun z : ℝ × ℝ => Complex.exp ((r*(z.1-z.2):ℝ)*Complex.I)) =
      fun z => Complex.exp ((r*z.1:ℝ)*Complex.I) *
        conj (Complex.exp ((r*z.2:ℝ)*Complex.I)) := by
    funext z
    rw [← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_sub,Complex.ofReal_mul]
    ring
  simp only [Complex.ofReal_mul] at he
  rw [he,integral_prod_mul (fun x : ℝ => Complex.exp ((r:ℂ)*x*Complex.I))
    (fun y : ℝ => conj (Complex.exp ((r:ℂ)*y*Complex.I))),integral_conj,← charFun_apply_real,Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq (charFun μ r)

theorem integral_charFun_scale_swap (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    (∫ s, charFun μ (A*s) ∂ν) = ∫ r, charFun ν (A*r) ∂μ := by
  simp only [charFun_apply_real]
  rw [integral_integral_swap]
  · apply integral_congr_ae
    filter_upwards with r
    apply integral_congr_ae
    filter_upwards with s
    congr 2
    push_cast
    ring
  · exact (integrable_const (1:ℝ)).mono (by fun_prop)
      (by filter_upwards with z; simp [Function.uncurry,Complex.norm_exp])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceSincKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_nonneg (u s : ℝ) : 0 ≤ distanceSincKernel u s := sq_nonneg _

theorem distanceSincKernel_le_one (u s : ℝ) : distanceSincKernel u s ≤ 1 := by
  have h := Real.abs_sinc_le_one (u*s)
  dsimp [distanceSincKernel]
  exact (sq_abs _).symm.trans_le ((pow_le_pow_left₀ (abs_nonneg _) h 2).trans_eq (by norm_num))

theorem continuous_distanceSincKernel (u : ℝ) : Continuous (distanceSincKernel u) :=
  (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

theorem exists_distanceSincKernel : ∃ u : ℝ, 0 < u ∧ 2*u ≤ 1 ∧
    ∀ s : ℝ, |s| ≤ 100 → (1/4:ℝ) ≤ distanceSincKernel u s := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    Real.continuous_sinc.continuousAt (1/2:ℝ) (by norm_num)
  let u := min (δ/201) (1/4:ℝ)
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  refine ⟨u,hu,by have := min_le_right (δ/201) (1/4:ℝ); dsimp [u]; linarith,?_⟩
  intro s hs
  have hb : |u*s| < δ := by
    rw [abs_mul,abs_of_pos hu]
    have h₁ := mul_le_mul_of_nonneg_left hs hu.le
    have h₂ := min_le_left (δ/201) (1/4:ℝ)
    dsimp [u] at h₁ ⊢
    nlinarith
  have hc := hclose (show dist (u*s) 0 < δ by simpa [Real.dist_eq] using hb)
  rw [Real.dist_eq,Real.sinc_zero] at hc
  have hp : 1/2 < Real.sinc (u*s) := by have := (abs_lt.mp hc).1; linarith
  dsimp [distanceSincKernel]
  nlinarith

theorem interval_exp_eq_sinc (u s : ℝ) :
    (∫ r in -u..u, Complex.exp ((r*s:ℝ)*Complex.I)) =
      ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  by_cases hs : s = 0
  · simp [hs]
    ring
  have h := intervalIntegral.integral_comp_mul_right
    (fun t : ℝ => Complex.exp (t*Complex.I)) (a := -u) (b := u) hs
  rw [neg_mul,integral_exp_mul_I_eq_sinc] at h
  rw [h]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceFrequencyBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceFrequencyBox_mass {u : ℝ} (hu : 0 ≤ u) :
    distanceFrequencyBox u univ = ENNReal.ofReal (2*u) := by
  simp only [distanceFrequencyBox,Measure.restrict_apply_univ,Real.volume_Ioc]
  apply (ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.mpr (neg_le_self hu))
    (mul_nonneg (by norm_num) hu)).2
  ring

theorem distanceFrequencyBox_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceFrequencyBox u) s = ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  rw [charFun_apply_real]
  change (∫ r in Ioc (-u) u, Complex.exp ((s:ℂ)*r*Complex.I)) = _
  rw [← intervalIntegral.integral_of_le (by linarith : -u ≤ u)]
  simpa only [Complex.ofReal_mul,mul_comm (s:ℂ)] using interval_exp_eq_sinc u s

theorem distanceFrequencyBox_difference_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceDifferenceMeasure (distanceFrequencyBox u)) s =
      (((2*u)^2 * distanceSincKernel u s:ℝ):ℂ) := by
  rw [charFun_distanceDifferenceMeasure,distanceFrequencyBox_charFun hu,
    Complex.norm_real,Real.norm_eq_abs,← Complex.ofReal_pow,sq_abs]
  congr 1
  dsimp [distanceSincKernel]
  ring

theorem distanceFrequencyBox_difference_le_volume {u : ℝ} (hu : 0 ≤ u) :
    distanceDifferenceMeasure (distanceFrequencyBox u) ≤ ENNReal.ofReal (2*u) • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [distanceDifferenceMeasure,Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop))]
  calc
    _ ≤ ∫⁻ x, volume S ∂distanceFrequencyBox u := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ volume ((fun y : ℝ => x-y) ⁻¹' S) := Measure.restrict_apply_le _ _
        _ = volume S := (volume.measurePreserving_sub_left x).measure_preimage hS.nullMeasurableSet
    _ = _ := by
      rw [lintegral_const,distanceFrequencyBox_mass hu,Measure.smul_apply,smul_eq_mul,mul_comm]

theorem distanceFrequencyBox_difference_supported {u : ℝ} :
    ∀ᵐ s ∂distanceDifferenceMeasure (distanceFrequencyBox u), s ∈ Icc (-2*u) (2*u) := by
  rw [distanceDifferenceMeasure,ae_map_iff (by fun_prop) (by measurability)]
  have hm : ∀ᵐ x ∂distanceFrequencyBox u, x ∈ Ioc (-u) u := ae_restrict_mem measurableSet_Ioc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hm,
    Measure.quasiMeasurePreserving_snd.ae hm] with z hz₁ hz₂
  exact ⟨by linarith [hz₁.1,hz₂.2],by linarith [hz₁.2,hz₂.1]⟩

theorem distanceFrequencyBox_difference_le_band {u : ℝ} (hu : 0 ≤ u) :
    distanceDifferenceMeasure (distanceFrequencyBox u) ≤
      ENNReal.ofReal (2*u) • volume.restrict (Icc (-2*u) (2*u)) := by
  calc
    _ = (distanceDifferenceMeasure (distanceFrequencyBox u)).restrict (Icc (-2*u) (2*u)) :=
      (Measure.restrict_eq_self_of_ae_mem distanceFrequencyBox_difference_supported).symm
    _ ≤ (ENNReal.ofReal (2*u) • volume).restrict (Icc (-2*u) (2*u)) :=
      Measure.restrict_mono (Subset.refl _) (distanceFrequencyBox_difference_le_volume hu)
    _ = _ := Measure.restrict_smul _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceSincSpectralIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (u A : ℝ) :
    Integrable (fun s => distanceSincKernel u (A*s)) μ := by
  apply (integrable_const (1:ℝ)).mono
  · exact ((continuous_distanceSincKernel u).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with s
    rw [Real.norm_eq_abs,abs_of_nonneg (distanceSincKernel_nonneg _ _),norm_one]
    exact distanceSincKernel_le_one _ _

theorem charFun_sq_integrable_finite (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    Integrable (fun r => ‖charFun μ (A*r)‖^2) ν := by
  apply (integrable_const ((μ.real univ)^2)).mono
  · exact ((measurable_charFun.comp (measurable_const.mul measurable_id)).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

theorem distanceSincKernel_spectral_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 ≤ u) (A : ℝ) :
    (2*u)^2 * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
  have h := integral_charFun_scale_swap
    (distanceDifferenceMeasure (distanceFrequencyBox u)) (distanceDifferenceMeasure μ) A
  simp only [distanceFrequencyBox_difference_charFun hu,charFun_distanceDifferenceMeasure] at h
  have hr : (∫ s, (2*u)^2 * distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow,integral_complex_ofReal] using h
  rwa [integral_const_mul] at hr

theorem distanceSincKernel_frequency_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (A : ℝ) :
    (2*u) * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) ≤
      ∫ r in Icc (-2*u) (2*u), ‖charFun μ (A*r)‖^2 := by
  have hi := charFun_sq_integrable_finite μ (volume.restrict (Icc (-2*u) (2*u))) A
  have hb := integral_mono_measure (distanceFrequencyBox_difference_le_band hu.le)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ (A*r)‖))
    (hi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*u),smul_eq_mul,
    ← distanceSincKernel_spectral_identity μ hu.le A] at hb
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceSincCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_collision_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {u A : ℝ} (hA : 0 < A)
    (hu : ∀ s : ℝ, |s| ≤ 100 → (1/4:ℝ) ≤ distanceSincKernel u s) :
    ν.real {s : ℝ | |s| ≤ 100/A} ≤ 4 * ∫ s, distanceSincKernel u (A*s) ∂ν := by
  let S : Set ℝ := {s | |s| ≤ 100/A}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hb := integral_mono ((integrable_const (1/4:ℝ)).indicator hS)
    (distanceSincKernel_integrable ν u A) (show ∀ s, S.indicator (fun _ => (1/4:ℝ)) s ≤
      distanceSincKernel u (A*s) from by
      intro s
      by_cases hs : s ∈ S
      · rw [Set.indicator_of_mem hs]
        apply hu
        rw [abs_mul,abs_of_pos hA]
        have h := (le_div_iff₀ hA).mp hs
        nlinarith
      · rw [Set.indicator_of_notMem hs]
        exact distanceSincKernel_nonneg _ _)
  rw [integral_indicator_const _ hS,smul_eq_mul] at hb
  dsimp [S] at hb
  linarith

theorem integral_scale_Icc (f : ℝ → ℝ) {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    A * (∫ r in Icc (-u) u, f (A*r)) = ∫ r in Icc (-A*u) (A*u), f r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -u ≤ u),
    ← intervalIntegral.integral_of_le (by nlinarith : -A*u ≤ A*u)]
  have h := intervalIntegral.smul_integral_comp_mul_left f (a := -u) (b := u) A
  simpa only [smul_eq_mul,mul_neg,neg_mul] using h

theorem distanceSincKernel_scaled_frequency_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u A : ℝ} (hu : 0 < u) (hu₁ : 2*u ≤ 1) (hA : 0 < A) :
    A*(2*u) * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) ≤
      ∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  have h := mul_le_mul_of_nonneg_left (distanceSincKernel_frequency_bound μ hu A) hA.le
  rw [show -2*u = -(2*u) by ring,integral_scale_Icc (fun r => ‖charFun μ r‖^2) hA (by positivity)] at h
  have hs : Icc (-A*(2*u)) (A*(2*u)) ⊆ Icc (-A) A := by
    intro r hr
    constructor <;> nlinarith [hr.1,hr.2]
  have hi : IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc (-A) A) := by
    simpa only [one_mul,IntegrableOn] using charFun_sq_integrable_finite μ (volume.restrict (Icc (-A) A)) 1
  have hb := integral_mono_measure (Measure.restrict_mono hs le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ r‖)) hi
  apply le_trans ?_ hb
  simpa only [mul_assoc] using h

theorem finite_measure_distance_collision_fourier : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (A : ℝ), 0 < A →
      A * (μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100/A} ≤
        C * ∫ r in Icc (-A) A, ‖charFun μ r‖^2 := by
  obtain ⟨u,hu,hu₁,hkernel⟩ := exists_distanceSincKernel
  refine ⟨2/u,by positivity,?_⟩
  intro μ _ A hA
  have hl := distanceSincKernel_collision_bound (distanceDifferenceMeasure μ) hA hkernel
  have hh := distanceSincKernel_scaled_frequency_bound μ hu hu₁ hA
  have he : (distanceDifferenceMeasure μ).real {s : ℝ | |s| ≤ 100/A} =
      (μ.prod μ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100/A} := by
    simp only [measureReal_def,distanceDifferenceMeasure]
    rw [Measure.map_apply (by fun_prop) (by measurability)]
    rfl
  rw [he] at hl
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hu).mpr
  have h₁ := mul_le_mul_of_nonneg_left hl (show 0 ≤ A*u by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

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

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem descriptorSpatialMask_eq_one_of_good (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) {x : Plane} {dir : UnitCircle}
    (hx : ∃ P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor b), x ∈ (Q.descendant P).carrier)
    (hg : (x,dir) ∈ endpointDescriptorGood Q ρ m N lam sig J i b) :
    descriptorSpatialMask Q ρ m N lam sig J i b x dir = 1 := by
  obtain ⟨P,hP,hx⟩ := hx
  unfold descriptorSpatialMask
  rw [spatialAnchorMask_eq Q hQ ρ _ _ _ _ hP hx]
  exact circleTestMask_eq_one _ _ _ (hg P (Finset.mem_filter.mp hP).1 hx)

namespace PositiveDistanceData

theorem minimalMask_bounds (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (z : Plane × Plane) : 0 ≤ d.minimalMask z ∧ d.minimalMask z ≤ 1 := by
  have h₁ := descriptorListMask_bounds d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.1 (sourceRadialUnit z.2 z.1)
  have h₂ := descriptorListMask_bounds d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.2 (sourceRadialUnit z.2 z.1)
  exact ⟨mul_nonneg h₁.1 h₂.1,
    (mul_le_mul_of_nonneg_right h₁.2 h₂.1).trans (by simpa only [one_mul] using h₂.2)⟩

theorem ae_minimalMask_eq_one_on_good (d : PositiveDistanceData) [SFinite d.ρ]
    (hQ : 0 < d.Q.side) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    ∀ᵐ z ∂d.cellPair, z ∈ d.good → d.minimalMask z = 1 := by
  have ha : ∀ᵐ x ∂d.ρ, ∀ n : ℕ, ∃ P ∈ occupiedAnchorPaths d.Q d.ρ n,
      x ∈ (d.Q.descendant P).carrier :=
    ae_all_iff.mpr (fun n => ae_occupied_anchor d.Q d.ρ hcarry n)
  change ∀ᵐ z ∂(d.ρ.restrict (d.Q.descendant d.X).carrier).prod
    (d.ρ.restrict (d.Q.descendant d.Y).carrier), _
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae ha),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae ha)] with z hz₁ hz₂ hg
  have hprod : ∀ x : Plane,
      (∀ n : ℕ, ∃ P ∈ occupiedAnchorPaths d.Q d.ρ n, x ∈ (d.Q.descendant P).carrier) →
      (∀ b ∈ policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t,
        (x,sourceRadialUnit z.2 z.1) ∈ endpointDescriptorGood d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b) →
      descriptorListMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i
        (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
        x (sourceRadialUnit z.2 z.1) = 1 := by
    intro x hx hgood
    exact Finset.prod_eq_one (fun b hb => descriptorSpatialMask_eq_one_of_good
      d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i b (hx _) (hgood b hb))
  rw [minimalMask,hprod z.1 hz₁ (fun b hb => (hg b hb).1),
    hprod z.2 hz₂ (fun b hb => (hg b hb).2),one_mul]

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SourceStrongSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_strong_separation_endpoints (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center) (hu : dist P.center Q.center ≤ 2000*s)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    96*s ≤ dist x y ∧ dist x y ≤ 2004*s := by
  have hx' := P.dist_le hP.le hx (P.center_mem hP)
  have hy' := Q.dist_le hQ.le hy (Q.center_mem hQ)
  have ht₁ := dist_triangle P.center x Q.center
  have ht₂ := dist_triangle x y Q.center
  have ht₃ := dist_triangle x P.center y
  have ht₄ := dist_triangle P.center Q.center y
  rw [dist_comm P.center x] at ht₁
  rw [dist_comm Q.center y] at ht₄
  constructor <;> linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceWeight
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem spatialWeight_nonneg (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (z : Plane × Plane) : 0 ≤ d.spatialWeight z :=
  mul_nonneg (Real.rpow_nonneg (div_nonneg dist_nonneg (by positivity)) _)
    (d.minimalMask_bounds hQ z).1

theorem stronglySeparated_of_unit (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (hl : 100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center)
    (hu : dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ))) :
    d.StronglySeparated := by
  refine ⟨?_,?_,hl,hu⟩
  · simp only [DyadicSquare.descendant_side,hQ,hX,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div,le_refl]
  · simp only [DyadicSquare.descendant_side,hQ,hY,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div,le_refl]

theorem separated_distance_ratio (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) :
    96 ≤ dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)) ∧
    dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)) ≤ 2004 := by
  have h := dyadic_strong_separation_endpoints _ _
    (d.Q.descendant_side_pos hQ d.X) (d.Q.descendant_side_pos hQ d.Y)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hx hy
  exact ⟨(le_div_iff₀ (by positivity)).mpr h.1,
    (div_le_iff₀ (by positivity)).mpr h.2⟩

theorem spatialWeight_le_one (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) : d.spatialWeight z ≤ 1 := by
  have hr := d.separated_distance_ratio hQ hs hx hy
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos (by linarith :
    1 ≤ dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ))) (by norm_num : -(1/2:ℝ) ≤ 0)
  exact (mul_le_of_le_one_left (d.minimalMask_bounds hQ z).1 hpow).trans
    (d.minimalMask_bounds hQ z).2

theorem spatialWeight_lower (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) (hm : d.minimalMask z = 1) :
    (2004:ℝ)^(-(1/2:ℝ)) ≤ d.spatialWeight z := by
  rw [spatialWeight,hm,mul_one]
  have hr := d.separated_distance_ratio hQ hs hx hy
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hr.2 (by norm_num)

theorem ae_cellPair_mem (d : PositiveDistanceData) [SFinite d.ρ] :
    ∀ᵐ z ∂d.cellPair, z.1 ∈ (d.Q.descendant d.X).carrier ∧
      z.2 ∈ (d.Q.descendant d.Y).carrier := by
  exact (Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem (d.Q.descendant d.X).measurable)).and
    (Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (d.Q.descendant d.Y).measurable))

theorem ae_spatialWeight_bounds (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    ∀ᵐ z ∂d.cellPair, (0 ≤ d.spatialWeight z ∧ d.spatialWeight z ≤ 1) ∧
      (z ∈ d.good → (2004:ℝ)^(-(1/2:ℝ)) ≤ d.spatialWeight z) := by
  filter_upwards [d.ae_cellPair_mem,d.ae_minimalMask_eq_one_on_good hQ hcarry] with z hz hm
  exact ⟨⟨d.spatialWeight_nonneg hQ z,d.spatialWeight_le_one hQ hs hz.1 hz.2⟩,
    fun hg => d.spatialWeight_lower hQ hs hz.1 hz.2 (hm hg)⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_WeightedDistancePushforward
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

theorem weightedPair_le (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) :
    d.weightedPair ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.cellPair := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [d.ae_cellPair_mem] with z hz
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_right (by positivity) (d.spatialWeight_le_one hQ hs hz.1 hz.2)

theorem weightedPair_isFinite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) : IsFiniteMeasure d.weightedPair := by
  constructor
  apply (Measure.le_iff.mp (d.weightedPair_le hQ hs) univ MeasurableSet.univ).trans_lt
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem weightedDistance_isFinite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) : IsFiniteMeasure d.weightedDistance := by
  let := d.weightedPair_isFinite hQ hs
  unfold weightedDistance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

theorem weightedPair_lower (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    ENNReal.ofReal (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ))) • d.pair ≤
      d.weightedPair := by
  rw [pair,← withDensity_const,← withDensity_indicator d.measurable_good]
  apply withDensity_mono
  filter_upwards [d.ae_spatialWeight_bounds hQ hs hcarry] with z hz
  by_cases hg : z ∈ d.good
  · rw [Set.indicator_of_mem hg]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hz.2 hg) (by positivity))
  · rw [Set.indicator_of_notMem hg]
    exact zero_le

theorem weightedDistance_lower (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    ENNReal.ofReal (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ))) • d.distance ≤
      d.weightedDistance := by
  have h := Measure.map_mono (d.weightedPair_lower hQ hs hcarry)
    (continuous_fst.dist continuous_snd).measurable
  rw [Measure.map_smul] at h
  exact h

end PositiveDistanceData

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

theorem normalization_ne_top (d : PositiveDistanceData) : d.normalization ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem coincidence_ne_top (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence ≠ ∞ :=
  ENNReal.mul_ne_top d.normalization_ne_top (measure_ne_top _ _)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_WeightedDistanceCoincidence
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

theorem weighted_lower_constant_sq (d : PositiveDistanceData) :
    (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ)))^2 =
      (d.levelMass^4 * 2004)⁻¹ := by
  have hr : ((2004:ℝ)^(-(1/2:ℝ)))^2 = (2004:ℝ)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2004)]
    norm_num
  rw [mul_pow,hr]
  norm_num only [zpow_neg,zpow_ofNat]
  field_simp

theorem normalization_weighted_identity (d : PositiveDistanceData) :
    d.normalization.toReal = (2004*(2:ℝ)^((d.t:ℝ)-d.a)) *
      (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ)))^2 := by
  rw [normalization,ENNReal.toReal_ofReal (by positivity),d.weighted_lower_constant_sq]
  field_simp

theorem weightedDistance_collision_lower (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ)))^2 * (d.distance.prod d.distance).real S ≤
      (d.weightedDistance.prod d.weightedDistance).real S := by
  let := d.weightedDistance_isFinite hQ hs
  have hc : 0 ≤ d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ)) := by positivity
  have hp := Measure.prod_mono (d.weightedDistance_lower hQ hs hcarry)
    (d.weightedDistance_lower hQ hs hcarry)
  have h := ENNReal.toReal_mono (measure_ne_top (d.weightedDistance.prod d.weightedDistance) S)
    (Measure.le_iff.mp hp S hS)
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] at h
  simpa only [pow_two,measureReal_def] using h

theorem coincidence_le_weighted_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    d.coincidence.toReal ≤ 2004*(2:ℝ)^((d.t:ℝ)-d.a) *
      (d.weightedDistance.prod d.weightedDistance).real
        {z : ℝ × ℝ | |z.1-z.2| ≤ 100*d.width} := by
  have h := d.weightedDistance_collision_lower hQ hs hcarry
    {z : ℝ × ℝ | |z.1-z.2| ≤ 100*d.width} (by measurability)
  have he : d.coincidence.toReal = d.normalization.toReal *
      (d.distance.prod d.distance).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100*d.width} := by
    rw [coincidence,ENNReal.toReal_mul,measureReal_def,d.distance_collision]
  rw [he,d.normalization_weighted_identity,mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualDistanceEquation20
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem actual_weighted_distance_equation20 : ∃ C : ℝ, 0 < C ∧
    ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ], 0 < d.Q.side →
      d.StronglySeparated → d.ρ d.Q.carrierᶜ = 0 →
      d.coincidence.toReal ≤ C*(2:ℝ)^(-(d.a:ℝ)) *
        ∫ r in Icc (-((2:ℝ)^d.t)) ((2:ℝ)^d.t), ‖charFun d.weightedDistance r‖^2 := by
  obtain ⟨C,hC,hfourier⟩ := finite_measure_distance_collision_fourier
  refine ⟨2004*C,by positivity,?_⟩
  intro d _ hQ hs hcarry
  let := d.weightedDistance_isFinite hQ hs
  have hf := hfourier d.weightedDistance ((2:ℝ)^d.t) (by positivity)
  have hd := d.coincidence_le_weighted_collision hQ hs hcarry
  have hw : 100*d.width = 100/(2:ℝ)^d.t := by
    simp only [PositiveDistanceData.width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,div_eq_mul_inv]
  have hp : (2:ℝ)^((d.t:ℝ)-d.a) = (2:ℝ)^(-(d.a:ℝ)) * (2:ℝ)^d.t := by
    rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [hw,hp] at hd
  have h := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2004*(2:ℝ)^(-(d.a:ℝ)) by positivity)
  calc
    _ ≤ (2004*(2:ℝ)^(-(d.a:ℝ))) *
        (((2:ℝ)^d.t)*(d.weightedDistance.prod d.weightedDistance).real
          {z : ℝ × ℝ | |z.1-z.2| ≤ 100/(2:ℝ)^d.t}) := by
      simpa only [mul_assoc] using hd
    _ ≤ _ := h
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_Shells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set ComplexConjugate
open scoped ENNReal

theorem fourier_energy_even (μ : Measure ℝ) (r : ℝ) :
    ‖charFun μ (-r)‖^2 = ‖charFun μ r‖^2 := by
  rw [charFun_neg]
  simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierBandDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem fourier_band_split (μ : Measure ℝ) [IsFiniteMeasure μ]
    {L H : ℝ} (hL : 0 ≤ L) (hLH : L ≤ H) :
    (∫ r in Icc (-H) H, ‖charFun μ r‖^2) =
      (∫ r in Icc (-L) L, ‖charFun μ r‖^2)+2*(∫ r in Icc L H, ‖charFun μ r‖^2) := by
  have hc : Continuous (fun r : ℝ => ‖charFun μ r‖^2) := continuous_charFun.norm.pow 2
  have hset (x y : ℝ) (hxy : x ≤ y) :
      (∫ r in Icc x y, ‖charFun μ r‖^2) = ∫ r in x..y, ‖charFun μ r‖^2 := by
    rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hxy]
  have heven (u : ℝ) :
      (∫ r in -u..0, ‖charFun μ r‖^2) = ∫ r in 0..u, ‖charFun μ r‖^2 := by
    have he := intervalIntegral.integral_comp_neg (f := fun r => ‖charFun μ r‖^2) (a := 0) (b := u)
    simpa only [fourier_energy_even,neg_zero] using he.symm
  have hband (u : ℝ) : (∫ r in -u..u, ‖charFun μ r‖^2) =
      2*(∫ r in 0..u, ‖charFun μ r‖^2) := by
    have he := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) (a := -u) (b := 0)) (hc.intervalIntegrable (μ := volume) (a := 0) (b := u))
    rw [heven] at he
    linarith
  rw [hset _ _ (by linarith),hset _ _ (by linarith),hset _ _ hLH,hband,hband]
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (a := 0) (b := L)) (hc.intervalIntegrable (μ := volume) (a := L) (b := H))
  linarith

theorem fourier_dyadic_band_decomposition (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a t : ℕ} (hat : a ≤ t) :
    (∫ r in Icc (-((2:ℝ)^t)) ((2:ℝ)^t), ‖charFun μ r‖^2) =
      (∫ r in Icc (-((2:ℝ)^a)) ((2:ℝ)^a), ‖charFun μ r‖^2)+
      2*∑ v ∈ Finset.Ioc a t,
        ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2 := by
  induction t,hat using Nat.le_induction with
  | base => simp
  | succ t hat ih =>
    rw [Finset.sum_Ioc_succ_top hat]
    have hs := fourier_band_split μ (L := (2:ℝ)^t) (H := (2:ℝ)^(t+1))
      (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ t))
    rw [ih] at hs
    have he : ((t+1:ℕ):ℝ)-1 = (t:ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
    linarith

theorem fourier_shell_le_band (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℕ) :
    (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤
      ∫ r in Icc (-((2:ℝ)^v)) ((2:ℝ)^v), ‖charFun μ r‖^2 := by
  apply setIntegral_mono_set
    ((continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun r => sq_nonneg ‖charFun μ r‖)
  exact Filter.Eventually.of_forall (fun r hr => ⟨by linarith [hr.1,Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) ((v:ℝ)-1),pow_pos (by norm_num : (0:ℝ)<2) v],hr.2⟩)

theorem fourier_shell_le_expanded (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℕ) :
    (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤
      ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)), ‖charFun μ r‖^2 := by
  apply setIntegral_mono_set
    ((continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun r => sq_nonneg ‖charFun μ r‖)
  apply Filter.Eventually.of_forall
  intro r hr
  refine ⟨hr.1,hr.2.trans ?_⟩
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierBandBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem finite_fourier_band_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a t N : ℕ} (hat : a ≤ t) (htN : t ≤ N) {B : ℝ} (hB : 0 ≤ B)
    (hbase : (2:ℝ)^(-(a:ℝ))*(∫ r in Icc (-((2:ℝ)^a)) ((2:ℝ)^a), ‖charFun μ r‖^2) ≤ B)
    (hshell : ∀ v ∈ Finset.Ioc a t,
      (2:ℝ)^(-(a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) ≤ B) :
    (2:ℝ)^(-(a:ℝ))*(∫ r in Icc (-((2:ℝ)^t)) ((2:ℝ)^t), ‖charFun μ r‖^2) ≤
      (1+2*(N:ℝ))*B := by
  have hsum := Finset.sum_le_sum hshell
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : ((Finset.Ioc a t).card:ℝ) ≤ (N:ℝ) := by
    rw [Nat.card_Ioc]
    exact_mod_cast (show t-a ≤ N by omega)
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcard hB)
  rw [fourier_dyadic_band_decomposition μ hat]
  have he : (2:ℝ)^(-(a:ℝ))*(2*∑ v ∈ Finset.Ioc a t,
      ∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) =
      2*∑ v ∈ Finset.Ioc a t, (2:ℝ)^(-(a:ℝ))*
        (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v), ‖charFun μ r‖^2) := by
    rw [← Finset.mul_sum]
    ring
  rw [mul_add,he]
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_WeightedDistanceLowFrequency
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem weightedDistance_mass_le (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) :
    d.weightedDistance.real univ ≤
      ((d.ρ (d.Q.descendant d.X).carrier).toReal / d.levelMass) *
      ((d.ρ (d.Q.descendant d.Y).carrier).toReal / d.levelMass) := by
  have hm := Measure.le_iff.mp (d.weightedPair_le hQ hs) univ MeasurableSet.univ
  have h := ENNReal.toReal_mono (by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hm
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at h
  have hp : d.cellPair univ =
      d.ρ (d.Q.descendant d.X).carrier * d.ρ (d.Q.descendant d.Y).carrier := by
    unfold cellPair
    rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Measure.restrict_apply_univ]
  rw [hp,ENNReal.toReal_mul] at h
  have hw : d.weightedDistance.real univ = (d.weightedPair univ).toReal := by
    rw [measureReal_def,weightedDistance,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ]
  rw [hw]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  norm_num only [zpow_neg,zpow_ofNat]
  field_simp

theorem weightedDistance_profile_mass (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (ha : d.a ≤ d.N)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.weightedDistance.real univ ≤ ((2:ℝ)^d.N)^(6*d.lam) := by
  let := hd.probability
  have hx := hd.normalized_cell_mass_le ha hX
  have hy := hd.normalized_cell_mass_le ha hY
  have h := mul_le_mul hx hy (by positivity) (by positivity)
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N),
    show 3*d.lam+3*d.lam = 6*d.lam by ring] at h
  exact (d.weightedDistance_mass_le hQ hs).trans h

theorem weightedDistance_low_frequency (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (ha : d.a ≤ d.N)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc (-((2:ℝ)^d.a)) ((2:ℝ)^d.a), ‖charFun d.weightedDistance r‖^2) ≤
        2*((2:ℝ)^d.N)^(12*d.lam) := by
  let := hd.probability
  let := d.weightedDistance_isFinite hQ hs
  have hm := d.weightedDistance_profile_mass hd hQ hs ha hX hY
  have hb : ∀ r : ℝ, ‖charFun d.weightedDistance r‖^2 ≤ ((2:ℝ)^d.N)^(12*d.lam) := by
    intro r
    have h := pow_le_pow_left₀ (norm_nonneg _) ((norm_charFun_le r).trans hm) 2
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (2:ℝ)^d.N) (6*d.lam) 2] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have hi : IntegrableOn (fun r => ‖charFun d.weightedDistance r‖^2)
      (Icc (-((2:ℝ)^d.a)) ((2:ℝ)^d.a)) := by
    simpa only [one_mul,IntegrableOn] using charFun_sq_integrable_finite d.weightedDistance
      (volume.restrict (Icc (-((2:ℝ)^d.a)) ((2:ℝ)^d.a))) 1
  have h := integral_mono hi (integrable_const (((2:ℝ)^d.N)^(12*d.lam))) hb
  rw [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (neg_le_self (by positivity)))] at h
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ (2:ℝ)^(-(d.a:ℝ)) by positivity)
  apply h'.trans_eq
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  field_simp
  ring

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_PrefixSuccessorEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem policyCellEnergy_finite_bound (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (S : Finset PolicyDescriptor)
    (k : Fin 2 → PolicyDescriptor → ℕ) (K : ℕ) (hK : ∀ l, ∑ b ∈ S, k l b ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (p : ℕ) (v : ℝ) (hv : v ≤ d.t) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) (row : CellPath × CellPath) :
    d.policyCellEnergy S k h p v Ψ row ≠ ⊤ ∧
      (d.policyCellEnergy S k h p v Ψ row).toReal ≤ d.prefixEnergyBound K p W := by
  let β := fun l => inheritedCircleSymbol S id (k l) d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i (h l)
  let D := symbolDerivativeConstant K^K
  have hD : 0 ≤ D := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ (hh l)
  have hb (l : Fin 2) (x : Plane) (u : UnitCircle) : ‖β l x u‖ ≤ D :=
    inheritedCircleSymbol_norm_le S id (k l) d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i (h l)
      K (hK l) x (hhb l x) u
  have he := sourceAngularH_uniform_bound p v Ψ hW hw hs _ _
    (measurable_sourceAngularTransform _ _ _ _ (hm 0))
    (measurable_sourceAngularTransform _ _ _ _ (hm 1))
    (show 0 ≤ D*d.ρ.real univ/(((2:ℝ)^d.N)^(-d.mass p)) by positivity)
    (show 0 ≤ D*d.ρ.real univ/(((2:ℝ)^d.N)^(-d.mass p)) by positivity)
    (fun z => sourceAngularTransform_global_bound d.ρ (d.Q.descendant row.1).carrier
      (by positivity) (β 0) hD (hb 0) z.1 z.2)
    (fun z => sourceAngularTransform_global_bound d.ρ (d.Q.descendant row.2).carrier
      (by positivity) (β 1) hD (hb 1) z.1 z.2)
  refine ⟨he.1,he.2.trans ?_⟩
  unfold prefixEnergyBound
  dsimp only [D] at *
  gcongr
  norm_num

theorem prefixSuccessorEnergies_bddAbove (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (K p : ℕ) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) :
    BddAbove (d.prefixSuccessorEnergies K p Ψ) := by
  refine ⟨d.prefixEnergyBound K p W,?_⟩
  intro E hE
  rcases hE with rfl | ⟨v,hv,_,row,_,k,hk,h,hh,hhb,rfl⟩
  · unfold prefixEnergyBound
    positivity
  · exact (d.policyCellEnergy_finite_bound hQ _ k K hk h hh hhb p v
      (by exact_mod_cast (Finset.mem_Ioc.mp hv).2) Ψ hW hw hs row).2

theorem prefixSuccessorSupremum_majorizes (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (K p : ℕ) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) :
    0 ≤ d.prefixSuccessorSupremum K p Ψ ∧
    ∀ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-d.sig*d.N < (v:ℝ) →
    ∀ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
    ∀ k : Fin 2 → PolicyDescriptor → ℕ,
      (∀ l, ∑ b ∈ d.prefixRemainingList p, k l b ≤ K) →
    ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row ≠ ⊤ ∧
      (d.policyCellEnergy (d.prefixRemainingList p) k h p v Ψ row).toReal ≤
        d.prefixSuccessorSupremum K p Ψ := by
  have hb := d.prefixSuccessorEnergies_bddAbove hQ K p Ψ hW hw hs
  refine ⟨le_csSup hb (Or.inl rfl),?_⟩
  intro v hv hv' row hr k hk h hh hhb
  exact ⟨(d.policyCellEnergy_finite_bound hQ _ k K hk h hh hhb p v
    (by exact_mod_cast (Finset.mem_Ioc.mp hv).2) Ψ hW hw hs row).1,
    le_csSup hb (Or.inr ⟨v,hv,hv',row,hr,k,hk,h,hh,hhb,rfl⟩)⟩

end PositiveDistanceData

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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixLowMaximum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem prefixLowMaximum_nonneg (d : PositiveDistanceData) : 0 ≤ d.prefixLowMaximum :=
  finiteEnergyMaximum_nonneg _ _

theorem prefixLowMaximum_majorizes (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    {v : ℕ} (hv : v ∈ Finset.Ioc d.a d.t) (hvl : (v:ℝ) ≤ (d.t:ℝ)-d.sig*d.N) :
    ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence ≠ ⊤ ∧
    ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal ≤ d.prefixLowMaximum :=
  ⟨({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence_ne_top,
    le_finiteEnergyMaximum d.prefixLowDepths
      (fun w => ({d with t := w,i := d.i+1} : PositiveDistanceData).coincidence)
      (Finset.mem_filter.mpr ⟨hv,hvl⟩)⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixBandAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
namespace PositiveDistanceData

theorem uniform_prefix_band_oai {sig kap lam T eps : ℝ}
    (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (heps : 0 < eps) {J : ℕ} (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ C : ℝ, 0 < C ∧ ∃ K N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    d.coincidence.toReal ≤ C*(1+2*(d.N:ℝ)) *
      (((2:ℝ)^d.N)^(12*lam)+d.prefixLowMaximum+
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eps) *
        d.prefixSuccessorSupremum K p Ψ + ((2:ℝ)^d.N)^(-T)) := by
  classical
  obtain ⟨C₀,hC₀,hfourier⟩ := actual_weighted_distance_equation20
  obtain ⟨K,N₁,hhigh⟩ := uniform_prefix_high_shell hsig hgap hlam hT heps hJ hΨ hpos hs hone
  obtain ⟨N₂,hlow⟩ := uniform_actual_distance_low_band hsig hJ
  let c := 32*binKernelConstant.toReal
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨C₀*(2+c),by positivity,K,max N₁ N₂,?_⟩
  intro d hdSig hdLam hdJ hN hQ hcarry B δ hprof hq hblock hw ht hi hX hY hlo hsep A p hpref
  let := hprof.probability
  have hQpos : 0 < d.Q.side := by rw [hQ]; norm_num
  have hsep' := d.stronglySeparated_of_unit hQ hX hY hlo hsep
  let := d.weightedDistance_isFinite hQpos hsep'
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup0 := (d.prefixSuccessorSupremum_majorizes hQpos K p Ψ hW
    (fun x => (le_abs_self _).trans (hWb x)) hsupport).1
  let F := ((2:ℝ)^d.N)^(12*lam)
  let G := ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eps)*d.prefixSuccessorSupremum K p Ψ
  let Z := ((2:ℝ)^d.N)^(-T)
  let S := F+d.prefixLowMaximum+G+Z
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := mul_nonneg (by positivity) hsup0
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hD := d.prefixLowMaximum_nonneg
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hFS : F ≤ S := by dsimp [S]; linarith
  have hDS : d.prefixLowMaximum ≤ S := by dsimp [S]; linarith
  have hGS : G+Z ≤ S := by dsimp [S]; linarith
  have hseed := d.weightedDistance_low_frequency hprof hQpos hsep' (by omega) hX hY
  rw [hdLam] at hseed
  have hbase : (2:ℝ)^(-(d.a:ℝ))*(∫ r in Icc (-((2:ℝ)^d.a)) ((2:ℝ)^d.a),
      ‖charFun d.weightedDistance r‖^2) ≤ (2+c)*S :=
    hseed.trans (by change 2*F ≤ _; nlinarith [mul_nonneg hc hS])
  have hshell : ∀ v ∈ Finset.Ioc d.a d.t,
      (2:ℝ)^(-(d.a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v),
        ‖charFun d.weightedDistance r‖^2) ≤ (2+c)*S := by
    intro v hv
    by_cases hvl : (v:ℝ) ≤ (d.t:ℝ)-d.sig*d.N
    · have hb := hlow d ((le_max_right _ _).trans hN) hdSig hdJ hQ hsep' hcarry hq ht v
        (Finset.mem_Ioc.mp hv).2
      have hm := (d.prefixLowMaximum_majorizes hv hvl).2
      have hsmall := mul_le_mul_of_nonneg_left (fourier_shell_le_band d.weightedDistance v)
        (by positivity : 0 ≤ (2:ℝ)^(-(d.a:ℝ)))
      exact (hsmall.trans hb).trans (by change c*_ ≤ _; nlinarith [mul_le_mul_of_nonneg_left hm hc,mul_le_mul_of_nonneg_left hDS hc])
    · have hb := hhigh d hdSig hdLam hdJ ((le_max_left _ _).trans hN) hQ B δ hprof hq hblock
        hw ht hi hX hY hlo hsep hpref v hv (by simpa only [hdSig] using lt_of_not_ge hvl)
      have hsmall := mul_le_mul_of_nonneg_left (fourier_shell_le_expanded d.weightedDistance v)
        (by positivity : 0 ≤ (2:ℝ)^(-(d.a:ℝ)))
      exact (hsmall.trans hb).trans (by change G+Z ≤ _; nlinarith [mul_nonneg hc hS])
  have hband := finite_fourier_band_bound d.weightedDistance (by omega : d.a ≤ d.t) ht
    (mul_nonneg (by positivity) hS) hbase hshell
  have hf := hfourier d hQpos hsep' hcarry
  have hb := mul_le_mul_of_nonneg_left hband hC₀.le
  apply hf.trans
  convert hb using 1 <;> (try dsimp only [S,F,G,Z]) <;> ring

end PositiveDistanceData

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band_oai := @OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_band_oai
