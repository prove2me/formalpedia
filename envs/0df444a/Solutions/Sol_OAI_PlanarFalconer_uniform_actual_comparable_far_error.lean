-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_comparable_far_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:12:30.305998+00:00
-- url     : https://prove2.me/submissions/03d4cdd3-f4c8-4b03-924d-f29bbca1e9a6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_far_radial_error

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

theorem stripCount_neg {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) (ω : Plane) :
    stripCount S v W (-ω) = stripCount S v W ω := by
  classical
  have he (i : ι) : planeDot (v i) (-ω) = -planeDot (v i) ω := by simp [planeDot]; ring
  simp only [stripCount,he,abs_neg]

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

 theorem inheritedCircleSymbol_contDiff {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection θ)) := by
  simp only [inheritedCircleSymbol_comp]
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (inheritedMaskProduct_contDiff S b k Q hQ ρ m N lam sig J i (fun _ => x)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationarySineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationarySineInverse_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineInverse u := by
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => x/2) u := contDiffAt_id.div_const 2
  have hh : ContDiffAt ℝ ∞ Real.arcsin (u/2) :=
    Real.contDiffAt_arcsin (by linarith [hu.1]) (by linarith [hu.2])
  have ht : ContDiffAt ℝ ∞ (fun x : ℝ => Real.arcsin (x/2)) u :=
    ContDiffAt.comp (f := fun x : ℝ => x/2) (g := Real.arcsin) u hh hi
  exact contDiffAt_const.mul ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem stationaryCutoff_tsupport : tsupport (stationaryCutoff : ℝ → ℝ) = Icc (-1:ℝ) 1 := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryCutoff]

 theorem stationaryChartCutoff_tsupport :
    tsupport (stationaryChartCutoff : ℝ → ℝ) = Icc (-3/2:ℝ) (3/2) := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryChartCutoff]

 theorem contDiff_localized_real {χ f : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf x hx)
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

 theorem stationarySineJacobian_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineJacobian u := by
  have hp : 0 < 1-u^2/4 := by nlinarith [hu.1,hu.2]
  have hf : ContDiffAt ℝ ∞ (fun u : ℝ => 1-u^2/4) u :=
    contDiffAt_const.sub ((contDiffAt_id.pow 2).div_const 4)
  exact (hf.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'

 theorem extendedStationaryInverse_contDiff : ContDiff ℝ ∞ extendedStationaryInverse := by
  apply contDiff_localized_real stationaryChartCutoff.contDiff
  intro u hu
  rw [stationaryChartCutoff_tsupport] at hu
  exact stationarySineInverse_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem stationaryWeight_contDiff : ContDiff ℝ ∞ stationaryWeight := by
  apply contDiff_localized_real stationaryCutoff.contDiff
  intro u hu
  rw [stationaryCutoff_tsupport] at hu
  exact stationarySineJacobian_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff SchwartzMap

 theorem stationaryAmplitude_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (stationaryAmplitude f) := by
  exact (Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff).mul
    (hf.comp extendedStationaryInverse_contDiff)

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

namespace AngularDifferentialExpr

theorem smooth_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

end AngularDifferentialExpr
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

theorem DyadicSquare.mass_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) :
    ρ Q.carrier = ∑ P ∈ occupiedAnchorPaths Q ρ n, ρ (Q.descendant P).carrier := by
  classical
  have hall : ρ Q.carrier = ∑ P ∈ dyadicPaths n, ρ (Q.descendant P).carrier := by
    rw [← Q.biUnion_descendants hQ n]
    apply measure_biUnion_finset
    · intro P hP S hS hne
      exact Q.descendants_disjoint hQ
        (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
    · exact fun P _ => (Q.descendant P).measurable
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨hP, bot_lt_iff_ne_bot.mpr hne⟩)

theorem DyadicSquare.normalized_mass_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (n : ℕ) (M : ℝ) :
    (∑ P ∈ occupiedAnchorPaths Q ρ n, (ρ (Q.descendant P).carrier).toReal / M) =
      (ρ Q.carrier).toReal / M := by
  rw [← Finset.sum_div, Q.mass_split_occupied hQ ρ n, ENNReal.toReal_sum]
  exact fun P _ => measure_ne_top ρ _

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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ENNReal

theorem sourcePlaneWave_norm (r : ℝ) (ω : UnitCircle) (x : Plane) :
    ‖sourcePlaneWave r ω x‖ = 1 := by
  simpa only [sourcePlaneWave, mul_one, norm_one] using angular_integrand_norm r ω x (fun _ _ => 1)

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

theorem graphFourKernel_norm_le (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (B : Fin 4 → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hb : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hW : ∀ p, ‖W p‖ ≤ 1) (x : Fin 4 → Plane) (r : ℝ) (u v : UnitCircle) :
    ‖graphFourKernel b W x r u v‖ ≤ (B 0*B 1)*(B 2*B 3) := by
  simp only [graphFourKernel, graphFourAmplitude, norm_mul, sourcePlaneWave_norm,
    one_mul, Complex.norm_conj]
  exact (mul_le_mul
    (mul_le_mul (hW (u,v))
      (mul_le_mul (hb 0 _ _) (hb 1 _ _) (norm_nonneg _) (hB 0))
      (by positivity) zero_le_one)
    (mul_le_mul (hb 2 _ _) (hb 3 _ _) (norm_nonneg _) (hB 2))
    (by positivity) (mul_nonneg zero_le_one (mul_nonneg (hB 0) (hB 1)))).trans_eq (by ring)

theorem graphFourKernel_measurable (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hW : Measurable W) :
    Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphFourKernel b W p.2 p.1.1 p.1.2.1 p.1.2.2) := by
  unfold graphFourKernel graphFourAmplitude sourcePlaneWave
  have h0 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 0 (p.2 0) p.1.2.1) := (hb 0).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 0, p.1.2.1)) from by fun_prop)
  have h1 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 1 (p.2 1) p.1.2.1) := (hb 1).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 1, p.1.2.1)) from by fun_prop)
  have h2 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 2 (p.2 2) p.1.2.2) := (hb 2).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 2, p.1.2.2)) from by fun_prop)
  have h3 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 3 (p.2 3) p.1.2.2) := (hb 3).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 3, p.1.2.2)) from by fun_prop)
  apply Measurable.mul
  · fun_prop
  · exact (((hW.comp (measurable_snd.comp measurable_fst)).mul
      (h0.mul (Complex.continuous_conj.measurable.comp h1))).mul
      (h2.mul (Complex.continuous_conj.measurable.comp h3)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSpatialFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem compact_finite_spatial_integrable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (ν : Measure α) (μ : Measure β)
    [IsFiniteMeasure μ] {K : Set α} (hK : MeasurableSet K) (hfinite : ν K < ∞)
    {f : α × β → ℂ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ p, ‖f p‖ ≤ C) (hsupp : ∀ p, f p ≠ 0 → p.1 ∈ K) :
    Integrable f (ν.prod μ) := by
  have hi : Integrable (K.indicator (fun _ : α => C)) ν :=
    (integrableOn_const hfinite.ne).integrable_indicator hK
  apply (hi.comp_fst μ).mono hf.aestronglyMeasurable
  filter_upwards with p
  by_cases hp : p.1 ∈ K
  · simpa only [indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg hC] using hbound p
  · have hz : f p = 0 := by by_contra hn; exact hp (hsupp p hn)
    simp [indicator_of_notMem hp, hz]

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

theorem graphOriginalKernel_measurable
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (R : ℝ) :
    Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphOriginalKernel b W Ψ R p.1 p.2) := by
  unfold graphOriginalKernel
  simp only [Complex.real_smul]
  apply Measurable.mul
  · fun_prop
  · exact graphFourKernel_measurable b W hb hW

theorem graphOriginalKernel_norm_le
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) (R : ℝ)
    (p : ℝ × (UnitCircle × UnitCircle)) (x : Fin 4 → Plane) :
    ‖graphOriginalKernel b W Ψ R p x‖ ≤ C*((B 0*B 1)*(B 2*B 3)) := by
  simp only [graphOriginalKernel, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hc _) (graphFourKernel_norm_le b W B hB hbound hw x _ _ _)
    (norm_nonneg _) hC

theorem graphOriginalKernel_integrable
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) :
    Integrable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphOriginalKernel b W Ψ R p.1 p.2)
      ((volume.prod (sourceArcLength.prod sourceArcLength)).prod μ) := by
  have hK : IsCompact (Icc (R/4) (4*R) ×ˢ (univ : Set (UnitCircle × UnitCircle))) :=
    isCompact_Icc.prod isCompact_univ
  apply compact_finite_spatial_integrable _ μ hK.measurableSet hK.measure_lt_top
    (graphOriginalKernel_measurable b W hb hW hΨ R)
    (mul_nonneg hC (mul_nonneg (mul_nonneg (hB 0) (hB 1)) (mul_nonneg (hB 2) (hB 3))))
  · intro p
    exact graphOriginalKernel_norm_le b W B hB hbound hw hC hc R p.1 p.2
  · intro p hp
    have hn : Ψ (p.1.1/R) ≠ 0 := by
      intro hz; exact hp (by simp [graphOriginalKernel, hz])
    have hh := hsupp _ hn
    refine ⟨⟨?_,?_⟩,mem_univ _⟩
    · have := (lt_div_iff₀ hR).mp hh.1; linarith
    · have := (div_lt_iff₀ hR).mp hh.2; linarith

theorem circle_pair_integral (F : UnitCircle × UnitCircle → ℂ)
    (hF : Measurable F) {C : ℝ} (hb : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, F p ∂sourceArcLength.prod sourceArcLength) =
      ∫ u, ∫ v, F (u,v) ∂sourceArcLength ∂sourceArcLength :=
  integral_prod _ (Integrable.of_bound hF.aestronglyMeasurable C (Filter.Eventually.of_forall hb))

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularPairCircleIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem angular_four_kernel_pair_integral (β γ : Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (r : ℝ) :
    (∫ u, ∫ w, graphFourKernel ![β,β,γ,γ] (fun _ => 1) x r u w
      ∂sourceArcLength ∂sourceArcLength) =
      angularPairCircleIntegral β (x 0) (x 1) r * angularPairCircleIntegral γ (x 2) (x 3) r := by
  have he (u w : UnitCircle) : graphFourKernel ![β,β,γ,γ] (fun _ => 1) x r u w =
      (sourcePlaneWave r u (x 0-x 1)*(β (x 0) u*conj (β (x 1) u))) *
      (sourcePlaneWave r w (x 2-x 3)*(γ (x 2) w*conj (γ (x 3) w))) := by
    simp only [graphFourKernel,graphFourAmplitude,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    ring
  simp_rw [he,integral_const_mul,integral_mul_const]
  rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularOriginalIntegrability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angularOriginalSpatialKernel_integrable
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) :
    Integrable (angularOriginalSpatialKernel β γ v Ψ) μ := by
  let bs : Fin 4 → Plane → UnitCircle → ℂ := ![β,β,γ,γ]
  let B : Fin 4 → ℝ := ![D₁,D₁,D₂,D₂]
  have hbs : ∀ i, Measurable (fun p : Plane × UnitCircle => bs i p.1 p.2) := by
    intro i; fin_cases i <;> assumption
  have hB : ∀ i, 0 ≤ B i := by intro i; fin_cases i <;> assumption
  have hb : ∀ i x u, ‖bs i x u‖ ≤ B i := by intro i; fin_cases i <;> assumption
  have hi := graphOriginalKernel_integrable μ bs (fun _ => 1) hbs measurable_const B hB hb
    (by intro p; simp) hΨ hs hC hc (by positivity : (0:ℝ) < (2:ℝ)^v)
  have hsli (x : Fin 4 → Plane) : Integrable
      (fun p => graphOriginalKernel bs (fun _ => 1) Ψ ((2:ℝ)^v) p x)
      (volume.prod (sourceArcLength.prod sourceArcLength)) := by
    have hh := graphOriginalKernel_integrable (Measure.dirac x) bs (fun _ => 1)
      hbs measurable_const B hB hb (by intro p; simp) hΨ hs hC hc
      (by positivity : (0:ℝ) < (2:ℝ)^v)
    simpa only [integral_dirac] using hh.integral_prod_left
  have he (x : Fin 4 → Plane) :
      (∫ p, graphOriginalKernel bs (fun _ => 1) Ψ ((2:ℝ)^v) p x
        ∂volume.prod (sourceArcLength.prod sourceArcLength)) =
      ∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
        (angularPairCircleIntegral β (x 0) (x 1) r *
         angularPairCircleIntegral γ (x 2) (x 3) r) := by
    rw [integral_prod _ (hsli x)]
    apply integral_congr_ae
    filter_upwards with r
    rw [circle_pair_integral (fun p => graphOriginalKernel bs (fun _ => 1) Ψ ((2:ℝ)^v) (r,p) x)
      ((graphOriginalKernel_measurable bs (fun _ => 1) hbs measurable_const hΨ _).comp
        (show Measurable (fun p : UnitCircle × UnitCircle => ((r,p),x)) from by fun_prop))
      (fun p => graphOriginalKernel_norm_le bs (fun _ => 1) B hB hb (by intro p; simp)
        hC hc _ (r,p) x)]
    simp only [graphOriginalKernel,integral_smul,bs,angular_four_kernel_pair_integral]
  have hh := hi.integral_prod_right.smul (((2:ℝ)^v)⁻¹)
  change Integrable (fun x => ((2:ℝ)^v)⁻¹ • (∫ p,
    graphOriginalKernel bs (fun _ => 1) Ψ ((2:ℝ)^v) p x
      ∂volume.prod (sourceArcLength.prod sourceArcLength))) μ at hh
  simp_rw [he] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularFourCellMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angularFourCellMeasure_real (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (row col : CellPath × CellPath) :
    (angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ =
      ((ρ (Q₁.descendant row.1).carrier).toReal*(ν (Q₂.descendant row.2).carrier).toReal)*
      ((ρ (Q₁.descendant col.1).carrier).toReal*(ν (Q₂.descendant col.2).carrier).toReal) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  change (Measure.pi (fun i => (ρs i).restrict _)).real univ = _
  simp only [Measure.real,Measure.pi_univ,Measure.restrict_apply_univ,ENNReal.toReal_mul,
    Fin.prod_univ_four,ρs,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

theorem occupied_absolute_mass_sum (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (A : CellPath) (n : ℕ) :
    (∑ P ∈ (occupiedAnchorPaths (Q.descendant A) ρ n).image (fun c => A++c),
      (ρ (Q.descendant P).carrier).toReal) = (ρ (Q.descendant A).carrier).toReal := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ he => List.append_cancel_left he)]
  simp only [DyadicSquare.descendant_append]
  simpa only [div_one] using (Q.descendant A).normalized_mass_split (Q.descendant_side_pos hQ A) ρ n 1

theorem angularFourCellMeasure_mass_sum (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) :
    (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        (angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ) =
      (ρ (Q₁.descendant A).carrier).toReal^2*(ν (Q₂.descendant B).carrier).toReal^2 := by
  simp_rw [angularFourCellMeasure_real,← Finset.mul_sum,← Finset.sum_mul]
  simp only [sourceProductVertices,Finset.sum_product,← Finset.mul_sum,← Finset.sum_mul]
  rw [occupied_absolute_mass_sum Q₁ hQ₁,occupied_absolute_mass_sum Q₂ hQ₂]
  ring

theorem angular_four_sum_error (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    [DecidableRel G] (F E : (CellPath × CellPath) → (CellPath × CellPath) → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, G row col →
      ‖F row col-E row col‖ ≤ ε*(angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ) :
    ‖(∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, if G row col then F row col else 0) -
      (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, if G row col then E row col else 0)‖ ≤
      ε*((ρ (Q₁.descendant A).carrier).toReal^2*(ν (Q₂.descendant B).carrier).toReal^2) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ε*(angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ := by
      apply Finset.sum_le_sum
      intro row hr
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro col hc
      by_cases hg : G row col
      · simpa only [hg,↓reduceIte] using he row hr col hc hg
      · simp only [hg,↓reduceIte,sub_self,norm_zero]
        positivity
    _ = _ := by simp only [← Finset.mul_sum,angularFourCellMeasure_mass_sum Q₁ Q₂ hQ₁ hQ₂]

theorem angular_four_sum_error_power (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n N : ℕ) (lam U c Ma₁ Ma₂ : ℝ)
    (hc : 0 ≤ c) (hcR : c ≤ ((2:ℝ)^N)^2) (hM₁ : 0 < Ma₁) (hM₂ : 0 < Ma₂)
    (hm₁ : (ρ (Q₁.descendant A).carrier).toReal/Ma₁ ≤ ((2:ℝ)^N)^(3*lam))
    (hm₂ : (ν (Q₂.descendant B).carrier).toReal/Ma₂ ≤ ((2:ℝ)^N)^(3*lam))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) [DecidableRel G]
    (F E : (CellPath × CellPath) → (CellPath × CellPath) → ℂ)
    (he : ∀ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∀ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, G row col →
      ‖F row col-E row col‖ ≤ ((2:ℝ)^N)^(-U)*(angularFourCellMeasure Q₁ Q₂ ρ ν row col).real univ) :
    ‖(c/(Ma₁^2*Ma₂^2)) •
      ((∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, if G row col then F row col else 0) -
      (∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
        ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, if G row col then E row col else 0))‖ ≤
      ((2:ℝ)^N)^(-U+12*lam+2) := by
  have hε : 0 ≤ ((2:ℝ)^N)^(-U) := by positivity
  have hp := angular_four_sum_error Q₁ Q₂ hQ₁ hQ₂ ρ ν A B n G F E hε he
  have hscale : 0 ≤ c/(Ma₁^2*Ma₂^2) := by positivity
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hscale]
  apply (mul_le_mul_of_nonneg_left hp hscale).trans
  calc
    _ = c*((2:ℝ)^N)^(-U)*
        (((ρ (Q₁.descendant A).carrier).toReal/Ma₁)^2*((ν (Q₂.descendant B).carrier).toReal/Ma₂)^2) := by
      field_simp
    _ ≤ ((2:ℝ)^N)^2*((2:ℝ)^N)^(-U)*
        ((((2:ℝ)^N)^(3*lam))^2*(((2:ℝ)^N)^(3*lam))^2) := by
      gcongr
    _ = _ := by
      simp only [← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
      rw [← Real.rpow_natCast ((2:ℝ)^N) 2]
      simp only [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_MeasurableAngularJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate

theorem measurable_angular_deriv {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hm : Measurable (fun p : α × ℝ => f p.1 p.2))
    (hd : ∀ x, Differentiable ℝ (f x)) :
    Measurable (fun p : α × ℝ => deriv (f p.1) p.2) := by
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε : Tendsto ε atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun n => show 0 < 1/((n:ℝ)+1) by positivity)⟩
  apply measurable_of_tendsto_metrizable
    (f := fun n => fun p : α × ℝ => (ε n)⁻¹ • (f p.1 (p.2+ε n)-f p.1 p.2))
  · intro n
    exact (show Measurable (fun _ : α × ℝ => (ε n)⁻¹) from measurable_const).smul
      ((hm.comp (measurable_fst.prodMk (measurable_snd.add_const (ε n)))).sub hm)
  · apply tendsto_pi_nhds.mpr
    intro p
    exact (hd p.1 p.2).hasDerivAt.tendsto_slope_zero_right.comp hε

theorem measurable_angular_iteratedDeriv {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hm : Measurable (fun p : α × ℝ => f p.1 p.2))
    (hd : ∀ x, ContDiff ℝ ∞ (f x)) (n : ℕ) :
    Measurable (fun p : α × ℝ => iteratedDeriv n (f p.1) p.2) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hm
  | succ n ih =>
    simp only [iteratedDeriv_succ]
    exact measurable_angular_deriv (fun x => iteratedDeriv n (f x)) ih (fun x => (AngularDifferentialExpr.smooth_iteratedDeriv (f := f x) (hd x) n).differentiable (by simp))

theorem measurable_stationary_family {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hm : Measurable (fun p : α × ℝ => f p.1 p.2))
    (hd : ∀ x, ContDiff ℝ ∞ (f x)) (n : ℕ) :
    Measurable (fun p : α × ℝ => fullCircleStationaryExpansion p.2 (f p.1) n) := by
  have hjet (g : α → ℝ → ℂ)
      (hg : Measurable (fun p : α × ℝ => g p.1 p.2))
      (hgd : ∀ x, ContDiff ℝ ∞ (g x)) (k : ℕ) :
      Measurable (fun x => iteratedDeriv k (stationaryAmplitude (g x)) 0) := by
    have hma : Measurable (fun p : α × ℝ => stationaryAmplitude (g p.1) p.2) := by
      unfold stationaryAmplitude
      exact ((stationaryWeight_contDiff.continuous.measurable.comp measurable_snd).complex_ofReal).mul
        (hg.comp (measurable_fst.prodMk (extendedStationaryInverse_contDiff.continuous.measurable.comp measurable_snd)))
    exact (measurable_angular_iteratedDeriv _ hma (fun x => stationaryAmplitude_contDiff (hgd x)) k).comp
      (measurable_id.prodMk measurable_const)
  have hopp : Measurable (fun p : α × ℝ => conj (f p.1 (p.2+Real.pi))) :=
    Complex.continuous_conj.measurable.comp (hm.comp (measurable_fst.prodMk (measurable_snd.add_const _)))
  have hdopp (x : α) : ContDiff ℝ ∞ (fun t => conj (f x (t+Real.pi))) :=
    Complex.conjCLE.contDiff.comp ((hd x).comp (contDiff_id.add contDiff_const))
  have h1 (k : ℕ) := (hjet f hm hd k).comp (measurable_fst : Measurable (Prod.fst : α × ℝ → α))
  have h2 (k : ℕ) := (hjet _ hopp hdopp k).comp (measurable_fst : Measurable (Prod.fst : α × ℝ → α))
  unfold fullCircleStationaryExpansion fresnelCoefficient stationaryDerivativeExpansion
  fun_prop

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStationarySpatial
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem angularPairAngle_measurable :
    Measurable (fun z : Plane × Plane => angularPairAngle z.1 z.2) :=
  measurable_sourceAngle.comp (measurable_sourceRadialUnit_joint.comp measurable_swap)

theorem angularPairAngle_represents (x y : Plane) :
    x-y = ‖x-y‖ • sourceDirection (angularPairAngle x y) := by
  have he := congrArg (fun u : UnitCircle => (u:Plane))
    (sourceUnitDirection_sourceAngle (sourceRadialUnit y x))
  change sourceDirection (angularPairAngle x y) = sourceRadialVector y x at he
  rw [he]
  by_cases hx : x=y
  · simp [hx]
  · simp only [sourceRadialVector,hx,↓reduceIte,smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)),one_smul]

theorem angularPairStationary_measurable (β : Plane → UnitCircle → ℂ)
    (hm : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hd : ∀ x, ContDiff ℝ ∞ (fun t => β x (sourceUnitDirection t))) (n : ℕ) :
    Measurable (fun p : (Plane × Plane) × ℝ => angularPairStationary β n p.1.1 p.1.2 p.2) := by
  let f := fun z : Plane × Plane => fun t =>
    β z.1 (sourceUnitDirection (t+angularPairAngle z.1 z.2))*
      conj (β z.2 (sourceUnitDirection (t+angularPairAngle z.1 z.2)))
  have hf : Measurable (fun p : (Plane × Plane) × ℝ => f p.1 p.2) := by
    have ha := angularPairAngle_measurable.comp (measurable_fst : Measurable (Prod.fst : (Plane × Plane) × ℝ → _))
    have hu := continuous_sourceUnitDirection.measurable.comp (measurable_snd.add ha)
    exact (hm.comp ((measurable_fst.comp measurable_fst).prodMk hu)).mul
      (Complex.continuous_conj.measurable.comp (hm.comp ((measurable_snd.comp measurable_fst).prodMk hu)))
  have hdf (z : Plane × Plane) : ContDiff ℝ ∞ (f z) :=
    ((hd z.1).comp (contDiff_id.add contDiff_const)).mul
      (Complex.conjCLE.contDiff.comp ((hd z.2).comp (contDiff_id.add contDiff_const)))
  exact (measurable_stationary_family f hf hdf n).comp
    (show Measurable (fun p : (Plane × Plane) × ℝ => (p.1,p.2*‖p.1.1-p.1.2‖)) from by fun_prop)

theorem angularStationarySpatialKernel_measurable (β γ : Plane → UnitCircle → ℂ)
    (hmβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hmγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    (hdβ : ∀ x, ContDiff ℝ ∞ (fun t => β x (sourceUnitDirection t)))
    (hdγ : ∀ x, ContDiff ℝ ∞ (fun t => γ x (sourceUnitDirection t)))
    (n : ℕ) (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) :
    Measurable (angularStationarySpatialKernel β γ n v Ψ) := by
  have h1 := (angularPairStationary_measurable β hmβ hdβ n).comp
    (show Measurable (fun p : (Fin 4 → Plane) × ℝ => ((p.1 0,p.1 1),p.2)) from by fun_prop)
  have h2 := (angularPairStationary_measurable γ hmγ hdγ n).comp
    (show Measurable (fun p : (Fin 4 → Plane) × ℝ => ((p.1 2,p.1 3),p.2)) from by fun_prop)
  have hi : Measurable (fun p : (Fin 4 → Plane) × ℝ => Ψ (p.2/(2:ℝ)^v) •
      (angularPairStationary β n (p.1 0) (p.1 1) p.2 * angularPairStationary γ n (p.1 2) (p.1 3) p.2)) :=
    (hΨ.comp (by fun_prop)).smul (h1.mul h2)
  exact (show Measurable (fun _ : Fin 4 → Plane => ((2:ℝ)^v)⁻¹) from measurable_const).smul
    (hi.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem spatial_replacement_integral_bound_ae (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (S : Set (Fin 4 → Plane)) (F G : (Fin 4 → Plane) → ℂ)
    (hF : IntegrableOn F S μ) (hG : Measurable G) {ε : ℝ}
    (hb : ∀ᵐ x ∂μ.restrict S, ‖F x-G x‖ ≤ ε) :
    ‖(∫ x in S, F x ∂μ)-(∫ x in S, G x ∂μ)‖ ≤ ε*μ.real S := by
  have hi : Integrable G (μ.restrict S) := by
    apply (hF.norm.add (integrable_const ε)).mono' hG.aestronglyMeasurable
    filter_upwards [hb] with x hx
    have ht := norm_add_le (F x) (G x-F x)
    rw [add_sub_cancel,norm_sub_rev (G x) (F x)] at ht
    change ‖G x‖ ≤ ‖F x‖+ε
    exact ht.trans (add_le_add (le_refl _) hx)
  rw [← integral_sub hF hi]
  simpa only [Measure.real,Measure.restrict_apply_univ] using norm_integral_le_of_norm_le_const hb

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualFarSpatialError
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_far_spatial_error {sig T : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ],
    ∀ Z : Set (Fin 4 → Plane), MeasurableSet Z →
    (∀ᵐ x ∂μ.restrict Z, 4*(2:ℝ)^(-h) ≤ ‖x 0-x 1‖ ∧ 4*(2:ℝ)^(-h) ≤ ‖x 2-x 3‖) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖(∫ x in Z, angularOriginalSpatialKernel (β 0) (β 1) v Ψ x ∂μ) -
      (∫ x in Z, angularStationarySpatialKernel (β 0) (β 1) n v Ψ x ∂μ)‖ ≤
      ((2:ℝ)^N)^(-T)*μ.real Z := by
  obtain ⟨n,N₀,h₀⟩ := uniform_actual_far_radial_error (T := T) hsig K hΨ hpos hs hW hw
  refine ⟨n,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm hb
    v h L₀ hv hLL hL₀ μ instμ Z hZ hgeom
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  have hβ (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ (hm l)
  have hbd (l : Fin 2) (x : Plane) := inheritedCircleSymbol_norm_le
    (S l) (b l) (k l) (Q l) (hQ l) (ρ l) (m l) N (lam l) sig (J l) (i l) (hsp l) K (hK l) x (hb l x)
  have hD : 0 ≤ symbolDerivativeConstant K^K := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hF := angularOriginalSpatialKernel_integrable μ (β 0) (β 1) (hβ 0) (hβ 1)
    hD hD (hbd 0) (hbd 1) v hΨ hs hW (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t)
  have hG := angularStationarySpatialKernel_measurable (β 0) (β 1) (hβ 0) (hβ 1)
    (inheritedCircleSymbol_contDiff _ _ _ _ (hQ 0) _ _ _ _ _ _ _ _)
    (inheritedCircleSymbol_contDiff _ _ _ _ (hQ 1) _ _ _ _ _ _ _ _) n v hΨ
  apply spatial_replacement_integral_bound_ae μ Z _ _ hF.integrableOn hG
  filter_upwards [hgeom] with z hz
  have he := h₀ N hN S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm
    ![z 0,z 2] ![z 1,z 3] (fun l => hb l _) (fun l => hb l _)
    v h L₀ hv hLL hL₀ (by
        intro l
        fin_cases l
        · exact hz.1
        · exact hz.2)
    ![angularPairAngle (z 0) (z 1),angularPairAngle (z 2) (z 3)]
    (by intro l; fin_cases l <;> exact angularPairAngle_represents _ _)
  exact he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualComparableFarError
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem uniform_actual_comparable_far_error_oai {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (m l)) →
    ∀ (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ a ≤ N, ∀ A : Fin 2 → CellPath, (∀ l, (A l).length = a) →
    ∀ d : ℕ, ∀ v L₀ : ℝ, v ≤ N → v-(a+d:ℕ) = 2*L₀ →
    (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N lam sig (J l) (i l) (hsp l)
    let M := fun l => ((2:ℝ)^N)^(-m l a)
    ‖angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v (M 0) (M 1)
        (angularOriginalSpatialKernel (β 0) (β 1) v Ψ) -
      angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v (M 0) (M 1)
        (angularStationarySpatialKernel (β 0) (β 1) n v Ψ)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_actual_far_spatial_error (T := T+12*lam+2) hsig K hΨ hpos hs hW hw
  refine ⟨n,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m B δ hd J i hsp hm hb a ha A hA
    d v L₀ hvN hv hLL hL₀
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N lam sig (J l) (i l) (hsp l)
  let M := fun l => ((2:ℝ)^N)^(-m l a)
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  have hc : (2:ℝ)^(2*(v-a)) ≤ ((2:ℝ)^N)^2 := by
    rw [← Real.rpow_natCast ((2:ℝ)^N) 2,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (0:ℝ) ≤ a := Nat.cast_nonneg a
    norm_num
    linarith
  have he := angular_four_sum_error_power (Q 0) (Q 1) (hQp 0) (hQp 1) (ρ 0) (ρ 1)
    (A 0) (A 1) d N lam (T+12*lam+2) ((2:ℝ)^(2*(v-a))) (M 0) (M 1)
    (by positivity) hc (by dsimp [M]; positivity) (by dsimp [M]; positivity)
    ((hd 0).normalized_cell_mass_le ha (hA 0)) ((hd 1).normalized_cell_mass_le ha (hA 1))
    (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col)
    (fun row col => ∫ x in angularLengthComparable, angularOriginalSpatialKernel (β 0) (β 1) v Ψ x
      ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col)
    (fun row col => ∫ x in angularLengthComparable, angularStationarySpatialKernel (β 0) (β 1) n v Ψ x
      ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col) (by
      intro row hr col hcol hfar
      have hp := h₀ N hN S b k hcard hK L hLN hL Q hQp ρ m (fun _ => lam) J i hsp hm hb
        v (a+d:ℕ) L₀ hv hLL hL₀ (angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col)
        angularLengthComparable measurable_angularLengthComparable
        (angular_comparable_far_ae (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) (a+d) row col
          (sourceProductVertices_subset _ _ _ _ _ _ a d (hA 0) (hA 1) hr)
          (sourceProductVertices_subset _ _ _ _ _ _ a d (hA 0) (hA 1) hcol) hfar)
      apply hp.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _)))
  dsimp only [angularComparableFarContribution]
  rw [← smul_sub]
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_comparable_far_error_oai := @OAI.PlanarFalconer.uniform_actual_comparable_far_error_oai
