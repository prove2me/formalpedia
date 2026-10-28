-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:27:23.147303+00:00
-- url     : https://prove2.me/submissions/07eb0e32-ec95-4585-a708-ea34e84a59e5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_stationary_product_radial_bound
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_four_approximant_good

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

theorem stripCount_neg {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) (ω : Plane) :
    stripCount S v W (-ω) = stripCount S v W ω := by
  classical
  have he (i : ι) : planeDot (v i) (-ω) = -planeDot (v i) ω := by simp [planeDot]; ring
  simp only [stripCount,he,abs_neg]

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

theorem parallelTestCount_neg (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    parallelTestCount Q ρ g p P W (-ω) = parallelTestCount Q ρ g p P W ω := by
  have he : quarterTurn (-ω) = -quarterTurn ω := by ext i; fin_cases i <;> simp [quarterTurn]
  unfold parallelTestCount
  rw [he,stripCount_neg]

theorem projectionTestCount_neg (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    projectionTestCount Q ρ p u P W (-ω) = projectionTestCount Q ρ p u P W ω :=
  stripCount_neg _ _ _ _

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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RegularizationSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Filter
open scoped Topology ENNReal

theorem fixed_polynomial_subpower (k : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ((4*(N:ℝ)+1)^k) ≤ ((2:ℝ)^N)^e := by
  have hb : 1 < (2:ℝ)^e := Real.one_lt_rpow (by norm_num) he
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hb).const_mul ((5:ℝ)^k)
  have hevent : ∀ᶠ N : ℕ in atTop, (5:ℝ)^k*((N:ℝ)^k/((2:ℝ)^e)^N) < 1 := by
    exact ht.eventually (gt_mem_nhds (by simp : (5:ℝ)^k*0 < (1:ℝ)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 N₀,?_⟩
  intro N hN
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast ((le_max_left 1 N₀).trans hN)
  have hh := hN₀ N ((le_max_right 1 N₀).trans hN)
  rw [← mul_div_assoc] at hh
  have hp : 0 < ((2:ℝ)^e)^N := by positivity
  have hpol : (4*(N:ℝ)+1)^k ≤ (5:ℝ)^k*(N:ℝ)^k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hbound := hpol.trans ((div_lt_one hp).mp hh).le
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm e (N:ℝ),
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hbound
  exact hbound

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskSupport
attribute [-instance] _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem circleTestMask_antipodal {G : Set UnitCircle}
    (hG : ∀ dir : UnitCircle, circleAntipode dir ∈ G ↔ dir ∈ G)
    (d : ℝ) (hd : 0 < d) (dir : UnitCircle) :
    circleTestMask G d hd (circleAntipode dir) = circleTestMask G d hd dir := by
  have hp : Function.Periodic (sourceTestMask G d hd) Real.pi := by
    apply smoothAngleMask_periodic
    intro θ
    simpa only [mem_preimage,sourceUnitDirection_add_pi] using hG (sourceUnitDirection θ)
  rw [← sourceUnitDirection_sourceAngle dir,← sourceUnitDirection_add_pi,
    circleTestMask_comp,circleTestMask_comp,hp]

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

theorem descriptorGoodSet_antipodal (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (b : PolicyDescriptor) (dir : UnitCircle) :
    circleAntipode dir ∈ descriptorGoodSet Q ρ m N lam sig J i P b ↔
      dir ∈ descriptorGoodSet Q ρ m N lam sig J i P b := by
  cases b with
  | parallel g p =>
    change (parallelTestCount Q ρ g p P _ (-(dir:Plane)):ℝ) ≤ _ ↔ _
    rw [parallelTestCount_neg]
    rfl
  | projection p u =>
    change (projectionTestCount Q ρ p u P _ (-(dir:Plane)):ℝ) ≤ _ ↔ _
    rw [projectionTestCount_neg]
    rfl

theorem spatialAnchorMask_antipodal (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d)
    (hG : ∀ P : CellPath, ∀ dir : UnitCircle, circleAntipode dir ∈ G P ↔ dir ∈ G P)
    (x : Plane) (dir : UnitCircle) :
    spatialAnchorMask Q ρ n G d hd x (circleAntipode dir) = spatialAnchorMask Q ρ n G d hd x dir := by
  classical
  unfold spatialAnchorMask
  apply Finset.sum_congr rfl
  intro P _
  rw [circleTestMask_antipodal (hG P)]

theorem descriptorSpatialMask_antipodal (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    descriptorSpatialMask Q ρ m N lam sig J i b x (circleAntipode dir) =
      descriptorSpatialMask Q ρ m N lam sig J i b x dir :=
  spatialAnchorMask_antipodal Q ρ _ _ _ _ (fun P dir => descriptorGoodSet_antipodal Q ρ m N lam sig J i P b dir) x dir

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

 theorem inheritedMaskProduct_contDiff {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane) :
    ContDiff ℝ ∞ (inheritedMaskProduct S b k Q ρ m N lam sig J i x) := by
  apply contDiff_prod
  intro a _
  exact normalizedMaskFactor_contDiff (descriptorAngleMask_contDiff Q hQ ρ m N lam sig J i (b a) (x a)) _ _

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
-- module Solutions.OAIQ038_FA.Falconer_Fourier_UniformSymbolScale
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem sourceAngularRadius_inv (N : ℕ) (sig : ℝ) (l : ℕ) :
    (sourceAngularRadius N sig l)⁻¹ = max 1 ((2:ℝ)^l*((2:ℝ)^N)^(-50*sig)) := by
  have hp : 0 < 1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig) := by positivity
  have he : (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig))⁻¹ =
      (2:ℝ)^l*((2:ℝ)^N)^(-50*sig) := by
    rw [mul_inv_rev,inv_div,div_one,show -50*sig = -(50*sig) by ring,Real.rpow_neg (by positivity)]
    ring
  unfold sourceAngularRadius
  rcases le_total 1 (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig)) with h | h
  · rw [min_eq_left h,inv_one,← he,max_eq_left (by simpa using inv_anti₀ zero_lt_one h)]
  · rw [min_eq_right h,he,← he,max_eq_right (by simpa using inv_anti₀ hp h)]

 theorem sourceAngularRadius_inv_mono (N : ℕ) (sig : ℝ) {l L : ℕ} (h : l ≤ L) :
    (sourceAngularRadius N sig l)⁻¹ ≤ (sourceAngularRadius N sig L)⁻¹ := by
  rw [sourceAngularRadius_inv,sourceAngularRadius_inv]
  apply max_le_max_left
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) (by positivity)

 theorem sourceSymbolScale_pos (N : ℕ) (sig : ℝ) (L : ℕ) : 0 < sourceSymbolScale N sig L := by
  unfold sourceSymbolScale
  positivity

 theorem uniform_inheritedMaskProduct_bound {sig : ℝ} (hsig : 0 < sig) (K j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (x : ι → Plane) (θ : ℝ),
    ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x) θ‖ ≤
      symbolDerivativeConstant (K+j)^(K+j) * sourceSymbolScale N sig L^j := by
  obtain ⟨N₁,h₁⟩ := fixed_polynomial_subpower 3 (half_pos hsig)
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed (half_pos hsig) 2
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i x θ
  have hpol : (S.card:ℝ) ≤ ((2:ℝ)^N)^sig := by
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    have hc : (S.card:ℝ) ≤ ((N:ℝ)+1)^3+1 := by exact_mod_cast hcard
    have hc' : ((N:ℝ)+1)^3+1 ≤ 2*(4*(N:ℝ)+1)^3 := by
      nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ (N:ℝ)+1)
        (by linarith : (N:ℝ)+1 ≤ 4*(N:ℝ)+1) 3,
        one_le_pow₀ (by linarith : (1:ℝ) ≤ 4*(N:ℝ)+1) (n := 3)]
    apply (hc.trans hc').trans
    calc
      _ ≤ ((2:ℝ)^N)^(sig/2)*((2:ℝ)^N)^(sig/2) :=
        mul_le_mul (h₂ N ((le_max_right _ _).trans hN))
          (h₁ N ((le_max_left _ _).trans hN)) (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hd := sourceAngularRadius_pos N sig L
  apply (inheritedMaskProduct_bound S b k Q hQ ρ m N lam sig J i x K j hK
    (sourceAngularRadius N sig L)⁻¹ (by positivity)
    (fun a ha => sourceAngularRadius_inv_mono N sig (hL a ha)) θ).trans
  have hC : 0 ≤ symbolDerivativeConstant (K+j) := zero_le_one.trans (symbolDerivativeConstant_one_le _)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
  apply pow_le_pow_left₀ (by positivity)
  rw [sourceSymbolScale,← sourceAngularRadius_inv]
  exact mul_le_mul_of_nonneg_right hpol (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedCircleRegularity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem periodic_iteratedDeriv {f : ℝ → ℝ} {p : ℝ} (hp : Function.Periodic f p) (j : ℕ) :
    Function.Periodic (iteratedDeriv j f) p := by
  have he : (fun x => f (x+p)) = f := funext hp
  have hh := iteratedDeriv_comp_add_const j f p
  rw [he] at hh
  intro x
  exact (congrFun hh x).symm

 theorem inheritedMaskProduct_periodic {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane) :
    Function.Periodic (inheritedMaskProduct S b k Q ρ m N lam sig J i x) Real.pi := by
  have hp a : Function.Periodic (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a)) Real.pi := by
    intro θ
    exact (congrArg (descriptorSpatialMask Q ρ m N lam sig J i (b a) (x a))
      (sourceUnitDirection_add_pi θ)).trans (descriptorSpatialMask_antipodal _ _ _ _ _ _ _ _ _ _ _)
  intro θ
  apply Finset.prod_congr rfl
  intro a _
  unfold normalizedMaskFactor
  rw [periodic_iteratedDeriv (hp a) (k a) θ]

 theorem periodic_sourceAngle {f : ℝ → ℝ} (hf : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    f (sourceAngle (sourceUnitDirection θ)) = f θ := by
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := hf.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

 theorem inheritedCircleSymbol_comp {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) (θ : ℝ) :
    inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection θ) =
      h x * (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x) θ : ℂ) := by
  have hp := (inheritedMaskProduct_periodic S b k Q ρ m N lam sig J i (fun _ => x)).nat_mul 2
  have hp' : Function.Periodic (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x))
      (2*Real.pi) := by simpa using hp
  unfold inheritedCircleSymbol
  rw [periodic_sourceAngle hp']

 theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    iteratedDeriv j (fun θ => (f θ : ℂ)) = fun θ => ((iteratedDeriv j f θ : ℝ) : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    have hd := (hf.differentiable_iteratedDeriv j
      (by exact_mod_cast (ENat.natCast_lt_top j))).differentiableAt (x := θ)
    simpa only [iteratedDeriv_succ] using hd.hasDerivAt.ofReal_comp.deriv

 theorem inheritedCircleSymbol_contDiff {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection θ)) := by
  simp only [inheritedCircleSymbol_comp]
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (inheritedMaskProduct_contDiff S b k Q hQ ρ m N lam sig J i (fun _ => x)))

 theorem inheritedCircleSymbol_derivative_norm {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection φ)) θ‖ =
      ‖h x‖ * ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x)) θ‖ := by
  simp only [inheritedCircleSymbol_comp, iteratedDeriv_const_mul_field,
    iteratedDeriv_ofReal (inheritedMaskProduct_contDiff S b k Q hQ ρ m N lam sig J i (fun _ => x)),
    norm_mul,Complex.norm_real]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_ActualSymbolEstimates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem uniform_actual_symbol_derivatives {sig : ℝ} (hsig : 0 < sig) (K j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane), ‖h x‖ ≤ 1 → ∀ θ : ℝ,
    ‖iteratedDeriv j (fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x
      (sourceUnitDirection φ)) θ‖ ≤
      symbolDerivativeConstant (K+j)^(K+j) * sourceSymbolScale N sig L^j := by
  obtain ⟨N₀,h₀⟩ := uniform_inheritedMaskProduct_bound hsig K j
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i h x hx θ
  rw [inheritedCircleSymbol_derivative_norm S b k Q hQ]
  apply (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans
  rw [one_mul]
  exact h₀ N hN S b k hcard hK L hL Q hQ ρ m lam J i (fun _ => x) θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualStationaryAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem sourceSymbolScale_one_le (N : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (L : ℕ) :
    1 ≤ sourceSymbolScale N sig L := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Real.one_le_rpow (one_le_pow₀ (by norm_num)) hsig
  · exact le_max_left _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualStationaryExpansion
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem uniform_actual_symbol_derivatives_upto {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane), ‖h x‖ ≤ 1 →
    ∀ j ≤ n, ∀ θ : ℝ,
    ‖iteratedDeriv j (fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x
      (sourceUnitDirection φ)) θ‖ ≤ C * sourceSymbolScale N sig L^j := by
  choose N₀ h₀ using fun j => uniform_actual_symbol_derivatives hsig K j
  let C : ℝ := ∑ j ∈ Finset.range (n+1), symbolDerivativeConstant (K+j)^(K+j)
  have hCj (j : ℕ) : 0 ≤ symbolDerivativeConstant (K+j)^(K+j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  refine ⟨C,Finset.sum_nonneg (fun j _ => hCj j),(Finset.range (n+1)).sup N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i h x hx j hj θ
  have hjmem : j ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hNj : N₀ j ≤ N := (Finset.le_sup hjmem).trans hN
  apply (h₀ j N hNj S b k hcard hK L hL Q hQ ρ m lam J i h x hx θ).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (sourceSymbolScale_pos _ _ _).le _)
  exact Finset.single_le_sum (fun l _ => hCj l) hjmem

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryOppositePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem complex_iteratedDeriv_conj {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun x => conj (f x)) = fun x => conj (iteratedDeriv n f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := (hf.differentiable_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt (x := x)
    have hh := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt
    change HasDerivAt (fun y => conj (iteratedDeriv n f y))
      (conj (deriv (iteratedDeriv n f) x)) x at hh
    simpa only [iteratedDeriv_succ] using hh.deriv

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularFarStationaryScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem sourceSymbolScale_dyadic (N : ℕ) (sig : ℝ) (L : ℕ) :
    sourceSymbolScale N sig L =
      max ((2:ℝ)^((N:ℝ)*sig)) ((2:ℝ)^((L:ℝ)-49*(N:ℝ)*sig)) := by
  unfold sourceSymbolScale
  rw [mul_max_of_nonneg _ _ (by positivity),mul_one]
  congr 1
  · exact (Real.rpow_natCast_mul (by norm_num) N sig).symm
  · rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_natCast]
    rw [← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring

 theorem sourceSymbolScale_far_square {sig L₀ : ℝ} (hsig : 0 ≤ sig)
    (N L : ℕ) (hL : (L:ℝ) ≤ L₀) (hL₀ : 10*sig*(N:ℝ) ≤ L₀) :
    sourceSymbolScale N sig L^2 ≤ (2:ℝ)^(2*L₀)*((2:ℝ)^N)^(-18*sig) := by
  have hn : 0 ≤ (N:ℝ)*sig := mul_nonneg (Nat.cast_nonneg _) hsig
  have hbase : sourceSymbolScale N sig L ≤ (2:ℝ)^(L₀-9*(N:ℝ)*sig) := by
    rw [sourceSymbolScale_dyadic]
    apply max_le
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      nlinarith
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      nlinarith
  apply (pow_le_pow_left₀ (sourceSymbolScale_pos N sig L).le hbase 2).trans_eq
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

 theorem actual_far_stationary_slack {sig L₀ Λ : ℝ} (hsig : 0 ≤ sig)
    (N L : ℕ) (hL : (L:ℝ) ≤ L₀) (hL₀ : 10*sig*(N:ℝ) ≤ L₀)
    (hΛ : (2:ℝ)^(2*L₀) ≤ Λ) :
    ((2:ℝ)^N)^(18*sig) ≤ Λ ∧
      sourceSymbolScale N sig L^2/Λ ≤ ((2:ℝ)^N)^(-18*sig) := by
  have hΛpos : 0 < Λ := (by positivity : (0:ℝ) < (2:ℝ)^(2*L₀)).trans_le hΛ
  refine ⟨?_,(div_le_iff₀ hΛpos).mpr ?_⟩
  · apply le_trans _ hΛ
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    nlinarith [mul_nonneg (Nat.cast_nonneg N) hsig]
  · exact (sourceSymbolScale_far_square hsig N L hL hL₀).trans
      (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hΛ (by positivity : 0 ≤ ((2:ℝ)^N)^(-18*sig)))

 theorem far_bump_frequency {v h L₀ d s : ℝ} (hv : v-h = 2*L₀)
    (hd : 4*(2:ℝ)^(-h) ≤ d) (hs : 1/4 ≤ s) :
    (2:ℝ)^(2*L₀) ≤ (2:ℝ)^v*s*d := by
  have hdpos : 0 < d := (by positivity : 0 < 4*(2:ℝ)^(-h)).trans_le hd
  calc
    _ = (2:ℝ)^v*(1/4)*(4*(2:ℝ)^(-h)) := by
      rw [← hv,sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hd
      (by positivity) (by positivity)

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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_SelectedBinAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem complex_mul_derivative_scale {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C B D E : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (j : ℕ) (x : ℝ)
    (hbf : ∀ k ≤ j, ‖iteratedDeriv k f x‖ ≤ C*D^k)
    (hbg : ∀ k ≤ j, ‖iteratedDeriv k g x‖ ≤ B*E^k) :
    ‖iteratedDeriv j (fun y => f y*g y) x‖ ≤ C*B*(D+E)^j := by
  have hf' : ContDiffAt ℝ j f x :=
    (hf.of_le (WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
  have hg' : ContDiffAt ℝ j g x :=
    (hg.of_le (WithTop.coe_le_coe.mpr (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
  rw [iteratedDeriv_fun_mul hf' hg', add_pow, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (j.choose k : ℝ) * (C*D^k) * (B*E^(j-k)) := by
      exact mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hbf k hk') (Nat.cast_nonneg _)
          (mul_nonneg hC (pow_nonneg hD _)))
        (hbg (j-k) (Nat.sub_le _ _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg hB (pow_nonneg hE _))
    _ = _ := by ring

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

theorem angularLengthShell_lengths (b : ℕ) {x : Fin 4 → Plane} (hx : x ∈ angularLengthShell b) :
    (256*(2:ℝ)^(-(b:ℝ)) < dist (x 0) (x 1) ∧
      dist (x 0) (x 1) ≤ 1024*(2:ℝ)^(-(b:ℝ))) ∧
    (256*(2:ℝ)^(-(b:ℝ)) < dist (x 2) (x 3) ∧
      dist (x 2) (x 3) ≤ 1024*(2:ℝ)^(-(b:ℝ))) := by
  have hc₁ : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*dist (x 0) (x 1) :=
    max_le (by linarith [dist_nonneg (x := x 0) (y := x 1)]) hx.1.2
  have hc₂ : max (dist (x 0) (x 1)) (dist (x 2) (x 3)) ≤ 2*dist (x 2) (x 3) :=
    max_le hx.1.1 (by linarith [dist_nonneg (x := x 2) (y := x 3)])
  exact ⟨⟨by linarith [hx.2.1],(le_max_left _ _).trans hx.2.2⟩,
    ⟨by linarith [hx.2.1],(le_max_right _ _).trans hx.2.2⟩⟩

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualTwoPointStationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem complex_pair_derivatives_upto {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {C B D : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D) (n : ℕ)
    (hbf : ∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k)
    (hbg : ∀ k ≤ n, ∀ x, ‖iteratedDeriv k g x‖ ≤ B*D^k) :
    ∀ j ≤ n, ∀ x, ‖iteratedDeriv j (fun y => f y*conj (g y)) x‖ ≤
      (C*B*2^n)*D^j := by
  intro j hj x
  have hbc : ∀ k ≤ j, ‖iteratedDeriv k (fun y => conj (g y)) x‖ ≤ B*D^k := by
    intro k hk
    rw [complex_iteratedDeriv_conj hg,Complex.norm_conj]
    exact hbg k (hk.trans hj) x
  apply (complex_mul_derivative_scale hf (Complex.conjCLE.contDiff.comp hg)
    hC hB hD hD j x (fun k hk => hbf k (hk.trans hj) x) hbc).trans
  calc
    _ = (C*B*2^j)*D^j := by rw [← two_mul,mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg hC hB))
      (pow_nonneg hD j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryPairGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem stationary_pair_gain_le {R l d₁ d₂ : ℝ} (hR : 0 < R) (hl : 0 < l)
    (h1 : l ≤ d₁) (h2 : l ≤ d₂) :
    (R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ) ≤ (R*l)⁻¹ := by
  have hb₁ := Real.rpow_le_rpow_of_nonpos (mul_pos hR hl)
    (mul_le_mul_of_nonneg_left h1 hR.le) (by norm_num : (-1/2:ℝ) ≤ 0)
  have hb₂ := Real.rpow_le_rpow_of_nonpos (mul_pos hR hl)
    (mul_le_mul_of_nonneg_left h2 hR.le) (by norm_num : (-1/2:ℝ) ≤ 0)
  calc
    _ ≤ (R*l)^(-1/2:ℝ)*(R*l)^(-1/2:ℝ) :=
      mul_le_mul hb₁ hb₂ (Real.rpow_nonneg (mul_nonneg hR.le (hl.le.trans h2)) _) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (mul_pos hR hl),show (-1/2:ℝ)+(-1/2) = -1 by norm_num,Real.rpow_neg_one]

 theorem stationary_pair_dyadic_gain {v b d₁ d₂ : ℝ}
    (h1 : (2:ℝ)^(-b) ≤ d₁) (h2 : (2:ℝ)^(-b) ≤ d₂) :
    ((2:ℝ)^v*d₁)^(-1/2:ℝ)*((2:ℝ)^v*d₂)^(-1/2:ℝ) ≤ (2:ℝ)^(-(v-b)) := by
  apply (stationary_pair_gain_le (by positivity : (0:ℝ) < (2:ℝ)^v)
    (by positivity : (0:ℝ) < (2:ℝ)^(-b)) h1 h2).trans_eq
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualTwoPointDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem uniform_actual_pair_derivatives {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x y : Plane),
    ‖h x‖ ≤ 1 → ‖h y‖ ≤ 1 →
    let f := fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection φ) *
      conj (inheritedCircleSymbol S b k Q ρ m N lam sig J i h y (sourceUnitDirection φ))
    ContDiff ℝ ∞ f ∧ ∀ j ≤ n, ∀ θ, ‖iteratedDeriv j f θ‖ ≤ C*sourceSymbolScale N sig L^j := by
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_symbol_derivatives_upto hsig K n
  refine ⟨C*C*2^n,by positivity,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i h x y hx hy
  have hfx := inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h x
  have hfy := inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h y
  refine ⟨hfx.mul (Complex.conjCLE.contDiff.comp hfy),?_⟩
  exact complex_pair_derivatives_upto hfx hfy hC hC (sourceSymbolScale_pos N sig L).le n
    (h₀ N hN S b k hcard hK L hL Q hQ ρ m lam J i h x hx)
    (h₀ N hN S b k hcard hK L hL Q hQ ρ m lam J i h y hy)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualStationaryProductKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_actual_stationary_product_kernel {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ) (x y : Fin 2 → Plane),
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v bdepth : ℝ, (∀ l, (2:ℝ)^(-bdepth) ≤ ‖x l-y l‖) →
    (∀ l, sourceSymbolScale N sig L^2 ≤ (2:ℝ)^v*‖x l-y l‖) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖angularStationarySpatialKernel (β 0) (β 1) n v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
      H*(2:ℝ)^(-(v-bdepth))/(1+(2:ℝ)^v*|‖x 0-y 0‖-‖x 1-y 1‖|)^2 := by
  obtain ⟨H,hH,hkernel⟩ := stationary_product_radial_bound hΨ hs n
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_pair_derivatives hsig K (2*n)
  refine ⟨H*C*C,by positivity,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i hsp x y hx hy v bdepth hd hD
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  let f := fun l t => β l (x l) (sourceUnitDirection t)*conj (β l (y l) (sourceUnitDirection t))
  have hp (l : Fin 2) := h₀ N hN (S l) (b l) (k l) (hcard l) (hK l) L (hL l)
    (Q l) (hQ l) (ρ l) (m l) (lam l) (J l) (i l) (hsp l) (x l) (y l) (hx l) (hy l)
  have hfs (l : Fin 2) : ContDiff ℝ ∞ (fun t => f l (t+angularPairAngle (x l) (y l))) :=
    (hp l).1.comp (contDiff_id.add contDiff_const)
  have hbs (l : Fin 2) (j : ℕ) (hj : j ≤ 2*n) (t : ℝ) :
      ‖iteratedDeriv j (fun u => f l (u+angularPairAngle (x l) (y l))) t‖ ≤ C*sourceSymbolScale N sig L^j := by
    rw [iteratedDeriv_comp_add_const]
    exact (hp l).2 j hj _
  have hpos (l : Fin 2) : 0 < ‖x l-y l‖ := (by positivity : (0:ℝ) < (2:ℝ)^(-bdepth)).trans_le (hd l)
  have he := hkernel (hfs 0) (hfs 1) hC hC (sourceSymbolScale_one_le N hsig.le L)
    (by positivity : (0:ℝ) < (2:ℝ)^v) (hpos 0) (hpos 1) (hD 0) (hD 1) (hbs 0) (hbs 1)
  apply he.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (stationary_pair_dyadic_gain (hd 0) (hd 1)) (by positivity)

theorem sourceSymbolScale_far_frequency_le {sig : ℝ} (hsig : 0 ≤ sig)
    (N L : ℕ) {v h L₀ d : ℝ} (hv : v-h = 2*L₀)
    (hLL : (L:ℝ) ≤ L₀) (hL₀ : 10*sig*(N:ℝ) ≤ L₀)
    (hd : 4*(2:ℝ)^(-h) ≤ d) : sourceSymbolScale N sig L^2 ≤ (2:ℝ)^v*d := by
  have hfreq : (2:ℝ)^(2*L₀) ≤ (2:ℝ)^v*d := by
    simpa only [mul_one] using far_bump_frequency hv hd (by norm_num : (1/4:ℝ) ≤ 1)
  have hp : 0 < (2:ℝ)^v*d := (by positivity : (0:ℝ) < (2:ℝ)^(2*L₀)).trans_le hfreq
  have he := (actual_far_stationary_slack hsig N L hLL hL₀ hfreq).2
  have hpow : ((2:ℝ)^N)^(-18*sig) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  simpa only [one_mul] using (div_le_iff₀ hp).mp (he.trans hpow)

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularFarSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

 theorem comparable_cells_strong_separation (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {l : ℝ} (hl : 0 < l)
    (hsP : P.side ≤ l) (hsQ : Q.side ≤ l) {x y : Plane}
    (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hlo : 256*l < dist x y) (hhi : dist x y ≤ 1024*l) :
    100*l ≤ dist P.center Q.center ∧ dist P.center Q.center ≤ 2000*l := by
  have hpx := (P.dist_le hP.le (P.center_mem hP) hx).trans (mul_le_mul_of_nonneg_left hsP (by norm_num))
  have hqy := (Q.dist_le hQ.le hy (Q.center_mem hQ)).trans (mul_le_mul_of_nonneg_left hsQ (by norm_num))
  have ht₁ := (dist_triangle P.center x Q.center).trans
    (add_le_add (le_refl _) (dist_triangle x y Q.center))
  have ht₂ := (dist_triangle x P.center y).trans
    (add_le_add (le_refl _) (dist_triangle P.center Q.center y))
  rw [dist_comm x P.center,dist_comm Q.center y] at ht₂
  constructor <;> linarith

 theorem comparable_dyadic_cells_strong_separation (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1) (b : ℕ) (P Q : CellPath)
    (hP : P.length = b) (hQ : Q.length = b) {x y : Plane}
    (hx : x ∈ (Q₁.descendant P).carrier) (hy : y ∈ (Q₂.descendant Q).carrier)
    (hlo : 256*(2:ℝ)^(-(b:ℝ)) < dist x y) (hhi : dist x y ≤ 1024*(2:ℝ)^(-(b:ℝ))) :
    100*(2:ℝ)^(-(b:ℝ)) ≤ dist (Q₁.descendant P).center (Q₂.descendant Q).center ∧
      dist (Q₁.descendant P).center (Q₂.descendant Q).center ≤ 2000*(2:ℝ)^(-(b:ℝ)) := by
  have hp : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hq : 0 < Q₂.side := by rw [hQ₂]; norm_num
  apply comparable_cells_strong_separation (Q₁.descendant P) (Q₂.descendant Q)
    (Q₁.descendant_side_pos hp P) (Q₂.descendant_side_pos hq Q) (by positivity) _ _ hx hy hlo hhi
  · rw [Q₁.descendant_side,hP,hQ₁,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simp
  · rw [Q₂.descendant_side,hQ,hQ₂,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasureSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

 theorem DyadicSquare.measure_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) :
    ρ.restrict Q.carrier =
      ∑ P ∈ occupiedAnchorPaths Q ρ n, ρ.restrict (Q.descendant P).carrier := by
  classical
  have hall : ρ.restrict Q.carrier =
      ∑ P ∈ dyadicPaths n, ρ.restrict (Q.descendant P).carrier := by
    rw [← Q.biUnion_descendants hQ n]
    rw [Measure.restrict_biUnion_finset]
    · rw [Measure.sum_fintype]
      exact Finset.sum_coe_sort (dyadicPaths n) (fun P => ρ.restrict (Q.descendant P).carrier)
    · intro P hP S hS hne
      exact Q.descendants_disjoint hQ
        (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
    · exact fun P => (Q.descendant P).measurable
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  apply Measure.restrict_eq_zero.mpr
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨hP,bot_lt_iff_ne_bot.mpr hne⟩)

 theorem occupied_absolute_measure_sum (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (A : CellPath) (n : ℕ) :
    (∑ P ∈ (occupiedAnchorPaths (Q.descendant A) ρ n).image (fun c => A++c),
      ρ.restrict (Q.descendant P).carrier) = ρ.restrict (Q.descendant A).carrier := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ he => List.append_cancel_left he)]
  simp only [DyadicSquare.descendant_append]
  exact ((Q.descendant A).measure_split_occupied (Q.descendant_side_pos hQ A) ρ n).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_FourCellMeasureSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem angularFourCellMeasure_pi (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (row col : CellPath × CellPath)
    (s : Fin 4 → Set Plane) :
    angularFourCellMeasure Q₁ Q₂ ρ ν row col (Set.pi univ s) =
      (ρ.restrict (Q₁.descendant row.1).carrier (s 0) *
       ν.restrict (Q₂.descendant row.2).carrier (s 2)) *
      (ρ.restrict (Q₁.descendant col.1).carrier (s 1) *
       ν.restrict (Q₂.descendant col.2).carrier (s 3)) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  change Measure.pi (fun i => (ρs i).restrict _) (Set.pi univ s) = _
  rw [Measure.pi_pi,Fin.prod_univ_four]
  dsimp [ρs]
  ring

theorem angularFourCellMeasure_split (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) :
    angularFourCellMeasure Q₁ Q₂ ρ ν (A,B) (A,B) =
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  change Measure.pi (fun i => (ρs i).restrict _) = _
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.finsetSum_apply,angularFourCellMeasure_pi]
  simp only [sourceProductVertices,Finset.sum_product,← Finset.mul_sum,← Finset.sum_mul]
  have he (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane) (P : CellPath)
      (t : Set Plane) :
      (∑ c ∈ (occupiedAnchorPaths (Q.descendant P) μ n).image (fun c => P++c),
        μ.restrict (Q.descendant c).carrier t) = μ.restrict (Q.descendant P).carrier t := by
    rw [← Measure.finsetSum_apply,occupied_absolute_measure_sum Q hQ]
  simp only [he Q₁ hQ₁,he Q₂ hQ₂,Fin.prod_univ_four]
  dsimp [ρs]
  ring

theorem angularFourCellMeasure_lintegral_split (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) (F : (Fin 4 → Plane) → ℝ≥0∞) :
    (∫⁻ x, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν (A,B) (A,B)) =
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ∫⁻ x, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
  rw [angularFourCellMeasure_split Q₁ Q₂ hQ₁ hQ₂ ρ ν A B n]
  simp only [lintegral_finsetSum_measure]

theorem angularFourCellMeasure_positive_rebin (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (h b : ℕ) (F : (Fin 4 → Plane) → ℝ≥0∞) :
    (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        ∫⁻ x, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col) =
    ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B b,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B b,
        ∫⁻ x, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
  rw [← angularFourCellMeasure_lintegral_split Q₁ Q₂ hQ₁ hQ₂,
    ← angularFourCellMeasure_lintegral_split Q₁ Q₂ hQ₁ hQ₂]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ComparablePositiveRebin
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem angular_shell_lintegral_zero_of_not_separated (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (b : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths b) ×ˢ (dyadicPaths b))
    (hc : col ∈ (dyadicPaths b) ×ˢ (dyadicPaths b))
    (hn : ¬ angularSeparated Q₁ Q₂ b row col) (F : (Fin 4 → Plane) → ℝ≥0∞) :
    (∫⁻ x in angularLengthShell b, F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col) = 0 := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  have hae := graph_four_spatial_ae_carrier ρs X
    (by intro i; fin_cases i <;> exact DyadicSquare.measurable _)
  rw [← lintegral_indicator (measurable_angularLengthShell b)]
  calc
    _ = ∫⁻ _ : Fin 4 → Plane, 0 ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
      apply lintegral_congr_ae
      filter_upwards [hae] with x hx
      apply Set.indicator_of_notMem
      intro hs
      have hl := angularLengthShell_lengths b hs
      apply hn
      constructor
      · exact comparable_dyadic_cells_strong_separation Q₁ Q₁ hQ₁ hQ₁ b row.1 col.1
          ((mem_dyadicPaths b _).mp (Finset.mem_product.mp hr).1)
          ((mem_dyadicPaths b _).mp (Finset.mem_product.mp hc).1)
          (hx 0) (hx 1) hl.1.1 hl.1.2
      · exact comparable_dyadic_cells_strong_separation Q₂ Q₂ hQ₂ hQ₂ b row.2 col.2
          ((mem_dyadicPaths b _).mp (Finset.mem_product.mp hr).2)
          ((mem_dyadicPaths b _).mp (Finset.mem_product.mp hc).2)
          (hx 2) (hx 3) hl.2.1 hl.2.2
    _ = 0 := by simp

theorem angular_shell_positive_rebin (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a h n : ℕ) (hA : A.length = a) (hB : B.length = a)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (F : (Fin 4 → Plane) → ℝ≥0∞) :
    (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        if G row col then
          ∫⁻ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0) ≤
    ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        if angularSeparated Q₁ Q₂ (a+n) row col then
          ∫⁻ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0 := by
  have hp₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hp₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  calc
    _ ≤ ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
          ∫⁻ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
      apply Finset.sum_le_sum
      intro row _
      apply Finset.sum_le_sum
      intro col _
      split_ifs <;> simp
    _ = ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ∫⁻ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col := by
      simp_rw [← lintegral_indicator (measurable_angularLengthShell (a+n))]
      exact angularFourCellMeasure_positive_rebin Q₁ Q₂ hp₁ hp₂ ρ ν A B h n _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro row hr
      apply Finset.sum_congr rfl
      intro col hc
      by_cases hs : angularSeparated Q₁ Q₂ (a+n) row col
      · simp [hs]
      · simp only [hs,↓reduceIte]
        exact angular_shell_lintegral_zero_of_not_separated Q₁ Q₂ hQ₁ hQ₂ ρ ν (a+n) row col
          (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB hr)
          (sourceProductVertices_subset Q₁ Q₂ ρ ν A B a n hA hB hc) hs F

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

theorem enorm_setIntegral_le_good_kernel (μ : Measure (Fin 4 → Plane))
    (S G : Set (Fin 4 → Plane)) (hG : MeasurableSet G)
    (F : (Fin 4 → Plane) → ℂ) (K : (Fin 4 → Plane) → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hb : ∀ᵐ x ∂μ.restrict S, ‖F x‖ₑ ≤ c*K x)
    (hs : ∀ᵐ x ∂μ.restrict S, F x ≠ 0 → x ∈ G) :
    ‖∫ x in S, F x ∂μ‖ₑ ≤ c*(∫⁻ x in S ∩ G, K x ∂μ) := by
  apply (enorm_integral_le_lintegral_enorm F).trans
  calc
    (∫⁻ x in S, ‖F x‖ₑ ∂μ) ≤ ∫⁻ x in S, c*G.indicator K x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hb,hs] with x hx hxs
      by_cases h : F x = 0
      · simp only [h,enorm_zero]; exact zero_le
      · rw [Set.indicator_of_mem (hxs h)]
        exact hx
    _ = c*(∫⁻ x in S ∩ G, K x ∂μ) := by
      rw [lintegral_const_mul' c _ hc,lintegral_indicator hG,Measure.restrict_restrict hG]
      rw [inter_comm]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ComparableComplexRebin
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

theorem angular_complex_shell_rebin (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a h n : ℕ) (hA : A.length = a) (hB : B.length = a)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (F : (Fin 4 → Plane) → ℂ) (K : (Fin 4 → Plane) → ℝ≥0∞)
    (T : Set (Fin 4 → Plane)) (hT : MeasurableSet T) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hb : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h, G row col →
      ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict (angularLengthShell (a+n)),
        ‖F x‖ₑ ≤ c*K x)
    (hs : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h, G row col →
      ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict (angularLengthShell (a+n)),
        F x ≠ 0 → x ∈ T) :
    ‖∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        if G row col then
          ∫ x in angularLengthShell (a+n), F x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0‖ₑ ≤
    c * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        if angularSeparated Q₁ Q₂ (a+n) row col then
          ∫⁻ x in angularLengthShell (a+n), T.indicator K x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
        else 0 := by
  apply (enorm_sum_le _ _).trans
  calc
    _ ≤ ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
          if G row col then c *
            ∫⁻ x in angularLengthShell (a+n), T.indicator K x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
          else 0 := by
      apply Finset.sum_le_sum
      intro row hr
      apply (enorm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro col hcol
      by_cases hg : G row col
      · simp only [hg,↓reduceIte]
        have he := enorm_setIntegral_le_good_kernel (angularFourCellMeasure Q₁ Q₂ ρ ν row col)
          (angularLengthShell (a+n)) T hT F K c hc (hb row hr col hcol hg) (hs row hr col hcol hg)
        rw [lintegral_indicator hT,Measure.restrict_restrict hT,inter_comm]
        exact he
      · simp [hg]
    _ = c * ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B h,
          if G row col then
            ∫⁻ x in angularLengthShell (a+n), T.indicator K x ∂angularFourCellMeasure Q₁ Q₂ ρ ν row col
          else 0 := by simp only [Finset.mul_sum,mul_ite,mul_zero]
    _ ≤ _ := mul_le_mul_right
      (angular_shell_positive_rebin Q₁ Q₂ hQ₁ hQ₂ ρ ν A B a h n hA hB G (T.indicator K)) c

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ActualComparableShellRebin
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

theorem uniform_actual_comparable_shell_rebin_oai {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) {J : ℕ} (hJ : 0 < J) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : Fin 2 → ℝ → ℝ) (q a₀ t₀ a d n v : ℕ),
    0 < q → a₀ ≤ a+n → v ≤ t₀ → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun t => m l t-(t:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength t ≤ L) →
    ∀ L₀ : ℝ, (v:ℝ)-(a+d:ℕ) = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (lam : Fin 2 → ℝ) (i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l)
      N (lam l) sig J (i l) (hsp l)
    let good := fun l => positiveDistanceGoodSet (Q l) (ρ l) (m l) N q (a+n) v (lam l) sig J (i l+1)
    ‖∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
      ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B d,
        if ¬ angularNear (Q 0) (Q 1) (a+d) row col then
          ∫ x in angularLengthShell (a+n), angularStationarySpatialKernel (β 0) (β 1) o v Ψ x
            ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
        else 0‖ₑ ≤
    (ENNReal.ofReal H * ENNReal.ofReal ((2:ℝ)^(-((v:ℝ)-(a+n:ℕ))))) *
      ∑ row ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
        ∑ col ∈ sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n,
          if angularSeparated (Q 0) (Q 1) (a+n) row col then
            ∫⁻ x in angularLengthShell (a+n),
              (fourPairGood (good 0) (good 1)).indicator (distanceDifferenceKernel v) x
                ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col
          else 0 := by
  obtain ⟨H,hH,N₁,h₁⟩ := uniform_actual_stationary_product_kernel hΨ hsΨ hsig K o
  obtain ⟨N₂,h₂⟩ := uniform_actual_four_approximant_good hsig hJ
  refine ⟨H,hH,max N₁ N₂,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a d n v hq ha₀ ht hv S k hS hcard hK L hL
    L₀ hvh hLL hL₀ lam i hsp hspb A B hA hB
  let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l)
    N (lam l) sig J (i l) (hsp l)
  let good := fun l => positiveDistanceGoodSet (Q l) (ρ l) (m l) N q (a+n) v (lam l) sig J (i l+1)
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  dsimp only
  convert angular_complex_shell_rebin (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) A B a d n hA hB
    (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)
    (angularStationarySpatialKernel (β 0) (β 1) o v Ψ) (distanceDifferenceKernel v)
    (fourPairGood (good 0) (good 1))
    (measurable_fourPairGood (measurable_positiveDistanceGoodSet _ _ _ _ _ _ _ _ _ _ _)
      (measurable_positiveDistanceGoodSet _ _ _ _ _ _ _ _ _ _ _))
    (ENNReal.ofReal H * ENNReal.ofReal ((2:ℝ)^(-((v:ℝ)-(a+n:ℕ))))) (by finiteness) ?_ ?_ using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro row hr
    apply Finset.sum_congr rfl
    intro col hc
    by_cases hg : ¬ angularNear (Q 0) (Q 1) (a+d) row col <;> simp only [hg,↓reduceIte,β]
  · intro row hr col hc hfar
    have hf := angular_comparable_far_ae (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) (a+d) row col
      (sourceProductVertices_subset _ _ _ _ _ _ a d hA hB hr)
      (sourceProductVertices_subset _ _ _ _ _ _ a d hA hB hc) hfar
    have hf' := ae_restrict_of_ae_restrict_of_subset (show angularLengthShell (a+n) ⊆
      angularLengthComparable from inter_subset_left) hf
    filter_upwards [hf',ae_restrict_mem (measurable_angularLengthShell (a+n))] with x hx hs
    have hl := angularLengthShell_lengths (a+n) hs
    have hd : ∀ l : Fin 2, (2:ℝ)^(-(a+n:ℕ):ℝ) ≤ ‖(![x 0,x 2] : Fin 2 → Plane) l-(![x 1,x 3] : Fin 2 → Plane) l‖ := by
      intro l
      have hp : 0 < (2:ℝ)^(-(a+n:ℕ):ℝ) := by positivity
      fin_cases l
      · change (2:ℝ)^(-((a+n:ℕ):ℝ)) ≤ ‖x 0-x 1‖
        rw [← dist_eq_norm]
        linarith [hl.1.1]
      · change (2:ℝ)^(-((a+n:ℕ):ℝ)) ≤ ‖x 2-x 3‖
        rw [← dist_eq_norm]
        linarith [hl.2.1]
    have hD : ∀ l : Fin 2, sourceSymbolScale N sig L^2 ≤
        (2:ℝ)^(v:ℝ)*‖(![x 0,x 2] : Fin 2 → Plane) l-(![x 1,x 3] : Fin 2 → Plane) l‖ := by
      intro l
      apply sourceSymbolScale_far_frequency_le hsig.le N L hvh hLL hL₀
      fin_cases l
      · exact hx.1
      · exact hx.2
    have he := h₁ N ((le_max_left _ _).trans hN) S (fun _ => id) k hcard hK L hL
      Q hQp ρ m lam (fun _ => J) i hsp ![x 0,x 2] ![x 1,x 3]
      (fun l => hspb l _) (fun l => hspb l _) v (a+n:ℕ) hd hD
    have hxvec : (![x 0,x 1,x 2,x 3] : Fin 4 → Plane) = x := by ext j; fin_cases j <;> rfl
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,hxvec,← dist_eq_norm] at he
    rw [← ofReal_norm]
    have he' := ENNReal.ofReal_le_ofReal he
    convert he' using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [distanceDifferenceKernel]
    rw [← ENNReal.ofReal_mul hH,← ENNReal.ofReal_mul (mul_nonneg hH (by positivity))]
    congr 1
    ring
  · intro row hr col hc hfar
    let X : Fin 4 → Set Plane := ![((Q 0).descendant row.1).carrier,((Q 0).descendant col.1).carrier,
      ((Q 1).descendant row.2).carrier,((Q 1).descendant col.2).carrier]
    have hs := h₂ N ((le_max_right _ _).trans hN) Q hQ ρ hcarry m q a₀ t₀ a (a+n) v
      hq ha₀ ht (Nat.le_add_right _ _) hv S k hS lam i hsp X
    have hs' : ∀ᵐ x ∂(angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col).restrict
        (angularLengthShell (a+n)), ∀ (o : ℕ) (w : ℝ) (Ψ : ℝ → ℝ),
        (∀ t, Ψ t ≠ 0 → 0 < t) → x 0 ≠ x 1 → x 2 ≠ x 3 →
        angularStationarySpatialKernel (β 0) (β 1) o w Ψ x ≠ 0 →
        (x 0,x 1) ∈ good 0 ∧ (x 2,x 3) ∈ good 1 := ae_restrict_of_ae hs
    filter_upwards [hs',ae_restrict_mem (measurable_angularLengthShell (a+n))] with x hx hshell
    have hl := angularLengthShell_lengths (a+n) hshell
    have hp : 0 < 256*(2:ℝ)^(-(a+n:ℕ):ℝ) := by positivity
    exact hx o v Ψ (fun t ht => lt_trans (by norm_num) (hsΨ t ht).1)
      (dist_pos.mp (hp.trans hl.1.1)) (dist_pos.mp (hp.trans hl.2.1))

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin_oai := @OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin_oai
