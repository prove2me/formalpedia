-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_far_stationary_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:14:49.753337+00:00
-- url     : https://prove2.me/submissions/bad973d7-109d-44de-a4e9-66170347c6da

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_comparable_far_error
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_noncomparable_radial_either

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

theorem sourcePlaneWave_sub (r : ℝ) (ω : UnitCircle) (x y : Plane) :
    sourcePlaneWave r ω x * conj (sourcePlaneWave r ω y) =
      sourcePlaneWave r ω (x-y) := by
  simp only [sourcePlaneWave, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal, ← Complex.exp_add, inner_sub_right, Complex.ofReal_sub]
  congr 1
  ring

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

theorem graphOriginalKernel_spatial_swap
    (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ]
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2)) (hW : Measurable W)
    (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hw : ∀ p, ‖W p‖ ≤ 1) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ r : ℝ, ∫ u, ∫ v, ∫ x, graphOriginalKernel b W Ψ R (r,(u,v)) x ∂μ
      ∂sourceArcLength ∂sourceArcLength) =
      ∫ x, ∫ r : ℝ, ∫ u, ∫ v, graphOriginalKernel b W Ψ R (r,(u,v)) x
        ∂sourceArcLength ∂sourceArcLength ∂volume ∂μ := by
  let G := graphOriginalKernel b W Ψ R
  have hg := graphOriginalKernel_measurable b W hb hW hΨ R
  have hd := graphOriginalKernel_norm_le b W B hB hbound hw hC hc R
  have hi := graphOriginalKernel_integrable μ b W hb hW B hB hbound hw hΨ hsupp hC hc hR
  have hslice (x : Fin 4 → Plane) : Integrable (fun p => G p x)
      (volume.prod (sourceArcLength.prod sourceArcLength)) := by
    have hh := graphOriginalKernel_integrable (Measure.dirac x) b W hb hW B hB hbound hw
      hΨ hsupp hC hc hR
    have he := hh.integral_prod_left
    simpa only [integral_dirac] using he
  have hcircle (r : ℝ) :
      (∫ p, ∫ x, G (r,p) x ∂μ ∂sourceArcLength.prod sourceArcLength) =
        ∫ u, ∫ v, ∫ x, G (r,(u,v)) x ∂μ ∂sourceArcLength ∂sourceArcLength := by
    have hm : Measurable (fun p : (UnitCircle × UnitCircle) × (Fin 4 → Plane) => G (r,p.1) p.2) :=
      hg.comp (show Measurable (fun p : (UnitCircle × UnitCircle) × (Fin 4 → Plane) =>
        ((r,p.1),p.2)) from by fun_prop)
    exact circle_pair_integral _ hm.stronglyMeasurable.integral_prod_right'.measurable
      (fun p => norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (hd (r,p))))
  calc
    _ = ∫ r : ℝ, ∫ p, ∫ x, G (r,p) x ∂μ ∂sourceArcLength.prod sourceArcLength := by
      simp_rw [hcircle]
      rfl
    _ = ∫ p, ∫ x, G p x ∂μ ∂volume.prod (sourceArcLength.prod sourceArcLength) :=
      (integral_prod _ hi.integral_prod_left).symm
    _ = ∫ x, ∫ p, G p x ∂volume.prod (sourceArcLength.prod sourceArcLength) ∂μ :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_prod _ (hslice x)]
      apply integral_congr_ae
      filter_upwards with r
      exact circle_pair_integral _
        (hg.comp (show Measurable (fun p : UnitCircle × UnitCircle => ((r,p),x)) from by fun_prop))
        (fun p => hd (r,p) x)

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFourTransformExpansion
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphFourKernel_endpoint_product
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) (x : Fin 4 → Plane) :
    graphFourKernel b W x r u v = W (u,v) *
      ∏ i : Fin 4, (![fun y => sourcePlaneWave r u y * b 0 y u,
        fun y => conj (sourcePlaneWave r u y * b 1 y u),
        fun y => sourcePlaneWave r v y * b 2 y v,
        fun y => conj (sourcePlaneWave r v y * b 3 y v)] i) (x i) := by
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, graphFourKernel, graphFourAmplitude,
    ← sourcePlaneWave_sub, map_mul]
  ring

theorem sourceGraphFourTransform_endpoint_integral
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (r : ℝ) (u v : UnitCircle) :
    sourceGraphFourTransform ρ X M b W r u v =
      ((M 0*M 1)*(M 2*M 3))⁻¹ •
        (∫ x, graphFourKernel b W x r u v ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  simp_rw [graphFourKernel_endpoint_product, integral_const_mul]
  rw [integral_fintype_prod_eq_prod]
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [integral_conj]
  simp only [sourceGraphFourTransform, sourceAngularTransform, sourcePlaneWave,
    Complex.real_smul, map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv,
    Complex.ofReal_mul, mul_inv_rev]
  ring

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularFourSpatialIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceGraphFourTransform_original_spatial
    (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hW : Measurable W) (B : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hbound : ∀ i x ω, ‖b i x ω‖ ≤ B i) (hw : ∀ p, ‖W p‖ ≤ 1)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ t, |Ψ t| ≤ C) {R : ℝ} (hR : 0 < R) :
    R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • sourceGraphFourTransform ρ X M b W r u v
      ∂sourceArcLength ∂sourceArcLength) =
      ((M 0*M 1)*(M 2*M 3))⁻¹ •
        (∫ x, R⁻¹ • (∫ r : ℝ, ∫ u, ∫ v, Ψ (r/R) • graphFourKernel b W x r u v
          ∂sourceArcLength ∂sourceArcLength)
          ∂Measure.pi (fun i => (ρ i).restrict (X i))) := by
  let μ := Measure.pi (fun i => (ρ i).restrict (X i))
  let c := ((M 0*M 1)*(M 2*M 3))⁻¹
  have he (r : ℝ) (u v : UnitCircle) :
      Ψ (r/R) • sourceGraphFourTransform ρ X M b W r u v =
        c • (∫ x, graphOriginalKernel b W Ψ R (r,(u,v)) x ∂μ) := by
    rw [sourceGraphFourTransform_endpoint_integral]
    change Ψ (r/R) • (c • (∫ x, graphFourKernel b W x r u v ∂μ)) = _
    rw [smul_comm]
    congr 1
    exact (integral_smul _ _).symm
  simp_rw [he, integral_smul]
  rw [smul_comm (R⁻¹) c]
  congr 1
  rw [graphOriginalKernel_spatial_swap μ b W hb hW B hB hbound hw hΨ hsupp hC hc hR]
  simp only [graphOriginalKernel, integral_smul, μ]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularCellSpatialIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem angular_pair_spatial_integral (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (row col : CellPath × CellPath) (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    angularKernelIntegral a v Ψ (fun z => angularPairTerm
      (fun P => angularCellTransform Q₁ ρ M₁ β P (z.1,z.2.1))
      (fun Q => angularCellTransform Q₂ ν M₂ γ Q (z.1,z.2.2)) row col) =
      ((2:ℝ)^(2*(v-a))) • ((M₁^2*M₂^2)⁻¹ •
        angularCellSpatialIntegral Q₁ Q₂ ρ ν β γ row col v Ψ) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hz : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  let U := angularCellTransform Q₁ ρ M₁ β
  let V := angularCellTransform Q₂ ν M₂ γ
  have hu := angularCellTransform_measurable Q₁ ρ M₁ β hβ
  have hv := angularCellTransform_measurable Q₂ ν M₂ γ hγ
  have hm : Measurable (fun z : ℝ × (UnitCircle × UnitCircle) =>
      angularPairTerm (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col) := by
    unfold angularPairTerm
    fun_prop
  have hb : ∀ z : ℝ × (UnitCircle × UnitCircle),
      ‖angularPairTerm (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col‖ ≤
        (D₁*(ρ univ).toReal/M₁)^2*(D₂*(ν univ).toReal/M₂)^2 := by
    intro z
    simp only [angularPairTerm,norm_mul,Complex.norm_conj,pow_two]
    apply mul_le_mul
      (mul_le_mul (sourceAngularTransform_global_bound ρ _ hM₁ β hD₁ hbβ _ _)
        (sourceAngularTransform_global_bound ρ _ hM₁ β hD₁ hbβ _ _) (norm_nonneg _) (by positivity))
      (mul_le_mul (sourceAngularTransform_global_bound ν _ hM₂ γ hD₂ hbγ _ _)
        (sourceAngularTransform_global_bound ν _ hM₂ γ hD₂ hbγ _ _) (norm_nonneg _) (by positivity))
      (by positivity) (by positivity)
  rw [angularKernelIntegral_original a v hΨ hpos hz _ hm hb]
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let bs : Fin 4 → Plane → UnitCircle → ℂ := ![β,β,γ,γ]
  let Ds : Fin 4 → ℝ := ![D₁,D₁,D₂,D₂]
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier, (Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier, (Q₂.descendant col.2).carrier]
  let : ∀ index, IsFiniteMeasure (ρs index) := by
    intro index
    fin_cases index <;> dsimp [ρs] <;> infer_instance
  have he := sourceGraphFourTransform_original_spatial ρs X ![M₁,M₁,M₂,M₂] bs (fun _ => 1)
    (by intro l; fin_cases l <;> assumption) measurable_const Ds
    (by intro l; fin_cases l <;> assumption)
    (by intro l; fin_cases l <;> assumption) (by intro p; simp)
    hΨ hs hW (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t)
    (by positivity : (0:ℝ) < (2:ℝ)^v)
  congr 1
  simpa only [sourceGraphFourTransform,angularPairTerm,angularCellTransform,
    angularCellSpatialIntegral,ρs,bs,Ds,X,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    one_mul,pow_two,U,V,angularCellTransform] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularRestrictedIntegralSum
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

theorem angularRestrictedIntegral_sum (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (C : Finset (CellPath × CellPath))
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop)
    (U V : CellPath → ℝ × UnitCircle → ℂ)
    (hU : ∀ P, Measurable (U P)) (hV : ∀ Q, Measurable (V Q))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbU : ∀ P z, ‖U P z‖ ≤ B) (hbV : ∀ Q z, ‖V Q z‖ ≤ D) :
    angularKernelIntegral a v Ψ (angularRestrictedKernel C G U V) =
      ∑ row ∈ C, ∑ col ∈ C, if G row col then
        angularKernelIntegral a v Ψ (fun z => angularPairTerm
          (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col) else 0 := by
  let F := fun (row col : CellPath × CellPath) (z : ℝ × (UnitCircle × UnitCircle)) =>
    if G row col then angularPairTerm
      (fun P => U P (z.1,z.2.1)) (fun Q => V Q (z.1,z.2.2)) row col else 0
  have hi (row col : CellPath × CellPath) : Integrable (F row col)
      ((sourceAngularShellMeasure v Ψ).prod (sourceArcLength.prod sourceArcLength)) := by
    by_cases hg : G row col
    · have hm : Measurable (F row col) := by dsimp [F]; simp only [hg,↓reduceIte,angularPairTerm]; fun_prop
      apply Integrable.of_bound hm.aestronglyMeasurable (B^2*D^2)
      apply Filter.Eventually.of_forall
      intro z
      dsimp [F]
      simp only [hg,↓reduceIte,angularPairTerm,norm_mul,Complex.norm_conj,pow_two]
      exact mul_le_mul
        (mul_le_mul (hbU row.1 _) (hbU col.1 _) (norm_nonneg _) hB)
        (mul_le_mul (hbV row.2 _) (hbV col.2 _) (norm_nonneg _) hD)
        (by positivity) (by positivity)
    · simp only [F,hg,↓reduceIte]
      exact integrable_zero _ _ _
  change ((2:ℝ)^(2*(v-a))) • (∫ z, ∑ row ∈ C, ∑ col ∈ C, F row col z ∂_) = _
  rw [integral_finsetSum C (fun row _ => integrable_finsetSum C (fun col _ => hi row col))]
  simp_rw [integral_finsetSum C (fun col _ => hi _ col),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  by_cases hg : G row col <;> simp [F,hg,angularKernelIntegral]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularFarSpatialSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem angular_contribution_spatial_sum (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (n : ℕ) (a v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (Ma₁ Ma₂ : ℝ) {Mp₁ Mp₂ : ℝ} (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) :
    angularCellContribution Q₁ Q₂ ρ ν A B n a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ G =
      (((2:ℝ)^(2*(v-a)))/(Ma₁^2*Ma₂^2)) •
        ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
          ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
            if G row col then angularCellSpatialIntegral Q₁ Q₂ ρ ν β γ row col v Ψ else 0 := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  unfold angularCellContribution
  rw [angularRestrictedIntegral_sum a v Ψ _ G _ _
    (angularCellTransform_measurable Q₁ ρ Mp₁ β hβ)
    (angularCellTransform_measurable Q₂ ν Mp₂ γ hγ)
    (B := D₁*(ρ univ).toReal/Mp₁) (D := D₂*(ν univ).toReal/Mp₂) (by positivity) (by positivity)
    (fun P z => sourceAngularTransform_global_bound ρ _ hMp₁ β hD₁ hbβ z.1 z.2)
    (fun P z => sourceAngularTransform_global_bound ν _ hMp₂ γ hD₂ hbγ z.1 z.2)]
  simp_rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  by_cases hg : G row col
  · simp only [hg,↓reduceIte]
    rw [angular_pair_spatial_integral Q₁ Q₂ ρ ν hMp₁ hMp₂ β γ hβ hγ hD₁ hD₂ hbβ hbγ
      row col a v hΨ hpos hs hW hw,smul_smul,smul_smul]
    congr 1
    simp only [mul_inv_rev,pow_two,div_eq_mul_inv]
    field_simp
  · simp [hg]

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

theorem measurable_angularLengthLeft : MeasurableSet angularLengthLeft := by
  unfold angularLengthLeft
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem measurable_angularLengthRight : MeasurableSet angularLengthRight := by
  unfold angularLengthRight
  exact measurableSet_lt (by fun_prop) (by fun_prop)

theorem measurable_angularLengthComparable : MeasurableSet angularLengthComparable := by
  change MeasurableSet ({x : Fin 4 → Plane | dist (x 0) (x 1) ≤ 2*dist (x 2) (x 3)} ∩
    {x | dist (x 2) (x 3) ≤ 2*dist (x 0) (x 1)})
  apply MeasurableSet.inter <;> exact measurableSet_le (by fun_prop) (by fun_prop)

theorem angular_length_trichotomy (x : Fin 4 → Plane) :
    x ∈ angularLengthLeft ∨ x ∈ angularLengthRight ∨ x ∈ angularLengthComparable := by
  by_cases h1 : x ∈ angularLengthLeft
  · exact Or.inl h1
  by_cases h2 : x ∈ angularLengthRight
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr ⟨le_of_not_gt h1,le_of_not_gt h2⟩)

theorem angular_length_left_comparable_disjoint :
    Disjoint angularLengthLeft angularLengthComparable := by
  exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h2.1 h1)

theorem angular_length_right_comparable_disjoint :
    Disjoint angularLengthRight angularLengthComparable := by
  exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h2.2 h1)

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

 theorem angularCellSpatialIntegral_pair (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) (β γ : Plane → UnitCircle → ℂ)
    (row col : CellPath × CellPath) (v : ℝ) (Ψ : ℝ → ℝ) :
    angularCellSpatialIntegral Q₁ Q₂ ρ ν β γ row col v Ψ =
      ∫ x, ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
        (angularPairCircleIntegral β (x 0) (x 1) r * angularPairCircleIntegral γ (x 2) (x 3) r))
      ∂Measure.pi (fun i => (![ρ,ρ,ν,ν] i).restrict
        (![ (Q₁.descendant row.1).carrier, (Q₁.descendant col.1).carrier,
            (Q₂.descendant row.2).carrier, (Q₂.descendant col.2).carrier] i)) := by
  simp only [angularCellSpatialIntegral,integral_smul,angular_four_kernel_pair_integral]

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNoncomparableCarrier
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angular_noncomparable_far_ae (Q₁ Q₂ : DyadicSquare)
    (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (h : ℕ) (row col : CellPath × CellPath)
    (hr : row ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hc : col ∈ (dyadicPaths h) ×ˢ (dyadicPaths h))
    (hfar : ¬ angularNear Q₁ Q₂ h row col) :
    ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict (angularLengthLeft ∪ angularLengthRight),
      (4*(2:ℝ)^(-(h:ℝ)) ≤ ‖x 0-x 1‖ ∧ 2*‖x 2-x 3‖ ≤ ‖x 0-x 1‖) ∨
      (4*(2:ℝ)^(-(h:ℝ)) ≤ ‖x 2-x 3‖ ∧ 2*‖x 0-x 1‖ ≤ ‖x 2-x 3‖) := by
  let ρs : Fin 4 → Measure Plane := ![ρ,ρ,ν,ν]
  let : ∀ i, IsFiniteMeasure (ρs i) := by intro i; fin_cases i <;> dsimp [ρs] <;> infer_instance
  let X : Fin 4 → Set Plane := ![(Q₁.descendant row.1).carrier,(Q₁.descendant col.1).carrier,
    (Q₂.descendant row.2).carrier,(Q₂.descendant col.2).carrier]
  have hae := graph_four_spatial_ae_carrier ρs X
    (by intro i; fin_cases i <;> exact DyadicSquare.measurable _)
  have haer : ∀ᵐ x ∂(angularFourCellMeasure Q₁ Q₂ ρ ν row col).restrict (angularLengthLeft ∪ angularLengthRight),
      ∀ i, x i ∈ X i := ae_restrict_of_ae hae
  filter_upwards [haer,ae_restrict_mem (measurable_angularLengthLeft.union measurable_angularLengthRight)] with x hx hnc
  have hf := angular_far_max_displacement Q₁ Q₂ hQ₁ hQ₂ h row col hr hc hfar x
    (hx 0) (hx 1) (hx 2) (hx 3)
  simp only [dist_eq_norm] at hf
  rcases hnc with hn | hn
  · change 2*dist (x 2) (x 3) < dist (x 0) (x 1) at hn
    simp only [dist_eq_norm] at hn
    have hmax : max ‖x 0-x 1‖ ‖x 2-x 3‖ = ‖x 0-x 1‖ := max_eq_left (by linarith [norm_nonneg (x 2-x 3)])
    rw [hmax] at hf
    exact Or.inl ⟨by linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-(h:ℝ))],hn.le⟩
  · change 2*dist (x 0) (x 1) < dist (x 2) (x 3) at hn
    simp only [dist_eq_norm] at hn
    have hmax : max ‖x 0-x 1‖ ‖x 2-x 3‖ = ‖x 2-x 3‖ := max_eq_right (by linarith [norm_nonneg (x 0-x 1)])
    rw [hmax] at hf
    exact Or.inr ⟨by linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-(h:ℝ))],hn.le⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualNoncomparableSpatial
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_noncomparable_spatial {sig T : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
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
    (∀ᵐ x ∂μ.restrict Z,
      (4*(2:ℝ)^(-h) ≤ ‖x 0-x 1‖ ∧ 2*‖x 2-x 3‖ ≤ ‖x 0-x 1‖) ∨
      (4*(2:ℝ)^(-h) ≤ ‖x 2-x 3‖ ∧ 2*‖x 0-x 1‖ ≤ ‖x 2-x 3‖)) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    IntegrableOn (angularOriginalSpatialKernel (β 0) (β 1) v Ψ) Z μ ∧
    ‖∫ x in Z, angularOriginalSpatialKernel (β 0) (β 1) v Ψ x ∂μ‖ ≤
      ((2:ℝ)^N)^(-T)*μ.real Z := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_noncomparable_radial_either (T := T) hsig K hΨ hpos hs hW hw
  refine ⟨N₀,?_⟩
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
    hD hD (hbd 0) (hbd 1) v hΨ.continuous.measurable hs hW
    (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t)
  refine ⟨hF.integrableOn,?_⟩
  have he : ∀ᵐ z ∂μ.restrict Z, ‖angularOriginalSpatialKernel (β 0) (β 1) v Ψ z‖ ≤ ((2:ℝ)^N)^(-T) := by
    filter_upwards [hgeom] with z hz
    have hh := h₀ N hN S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm
      ![z 0,z 2] ![z 1,z 3] (fun l => hb l _) (fun l => hb l _)
      v h L₀ hv hLL hL₀ hz
    have hzeta : (![z 0,z 1,z 2,z 3] : Fin 4 → Plane) = z := by
      funext l; fin_cases l <;> rfl
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons,hzeta] using hh
  simpa only [Measure.real,Measure.restrict_apply_univ] using norm_integral_le_of_norm_le_const he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualNoncomparableFar
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_noncomparable_far {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
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
    ‖angularNoncomparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v (M 0) (M 1)
        (angularOriginalSpatialKernel (β 0) (β 1) v Ψ)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_noncomparable_spatial (T := T+12*lam+2) hsig K hΨ hpos hs hW hw
  refine ⟨N₀,?_⟩
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
    (fun row col => ∫ x in (angularLengthLeft ∪ angularLengthRight), angularOriginalSpatialKernel (β 0) (β 1) v Ψ x
      ∂angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col)
    (fun _ _ => 0) (by
      intro row hr col hcol hfar
      have hp := h₀ N hN S b k hcard hK L hLN hL Q hQp ρ m (fun _ => lam) J i hsp hm hb
        v (a+d:ℕ) L₀ hv hLL hL₀ (angularFourCellMeasure (Q 0) (Q 1) (ρ 0) (ρ 1) row col)
        (angularLengthLeft ∪ angularLengthRight) (measurable_angularLengthLeft.union measurable_angularLengthRight)
        (angular_noncomparable_far_ae (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1) (a+d) row col
          (sourceProductVertices_subset _ _ _ _ _ _ a d (hA 0) (hA 1) hr)
          (sourceProductVertices_subset _ _ _ _ _ _ a d (hA 0) (hA 1) hcol) hfar)
      simp only [sub_zero]
      apply hp.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _)))
  dsimp only [angularNoncomparableFarContribution]
  simp only [ite_self,Finset.sum_const_zero,sub_zero] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_FarComparableSplit
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem integral_noncomparable_comparable (μ : Measure (Fin 4 → Plane))
    (F : (Fin 4 → Plane) → ℂ) (hF : Integrable F μ) :
    (∫ x, F x ∂μ) = (∫ x in angularLengthLeft ∪ angularLengthRight, F x ∂μ) +
      (∫ x in angularLengthComparable, F x ∂μ) := by
  have hu : (angularLengthLeft ∪ angularLengthRight) ∪ angularLengthComparable = univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases angular_length_trichotomy x with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hd : Disjoint (angularLengthLeft ∪ angularLengthRight) angularLengthComparable :=
    disjoint_union_left.mpr ⟨angular_length_left_comparable_disjoint,angular_length_right_comparable_disjoint⟩
  have hh := setIntegral_union hd measurable_angularLengthComparable hF.integrableOn hF.integrableOn
  simpa only [hu,Measure.restrict_univ] using hh

theorem angular_far_comparable_split (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a d : ℕ) (v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (Ma₁ Ma₂ : ℝ) {Mp₁ Mp₂ : ℝ} (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂) :
    angularCellContribution Q₁ Q₂ ρ ν A B d a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ
      (fun row col => ¬ angularNear Q₁ Q₂ (a+d) row col) =
    angularNoncomparableFarContribution Q₁ Q₂ ρ ν A B a d v Ma₁ Ma₂
      (angularOriginalSpatialKernel β γ v Ψ) +
    angularComparableFarContribution Q₁ Q₂ ρ ν A B a d v Ma₁ Ma₂
      (angularOriginalSpatialKernel β γ v Ψ) := by
  rw [angular_contribution_spatial_sum Q₁ Q₂ ρ ν A B d a v hΨ hpos hs hW hw
    Ma₁ Ma₂ hMp₁ hMp₂ β γ hβ hγ hD₁ hD₂ hbβ hbγ]
  unfold angularNoncomparableFarContribution angularComparableFarContribution
  rw [← smul_add,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro row hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro col hc
  by_cases hf : ¬ angularNear Q₁ Q₂ (a+d) row col
  · simp only [hf,not_false_eq_true,↓reduceIte]
    rw [angularCellSpatialIntegral_pair]
    exact integral_noncomparable_comparable (angularFourCellMeasure Q₁ Q₂ ρ ν row col) _
      (angularOriginalSpatialKernel_integrable _ β γ hβ hγ hD₁ hD₂ hbβ hbγ v hΨ hs hW
        (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t))
  · simp [hf]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualFarStationaryReduction
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem uniform_actual_far_stationary_reduction_oai {sig T lam : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
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
    ‖angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) d a v Ψ
        (M 0) (M 1) (((2:ℝ)^N)^(-m 0 (a+d))) (((2:ℝ)^N)^(-m 1 (a+d))) (β 0) (β 1)
        (fun row col => ¬ angularNear (Q 0) (Q 1) (a+d) row col) -
      angularComparableFarContribution (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v (M 0) (M 1)
        (angularStationarySpatialKernel (β 0) (β 1) n v Ψ)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₁,h₁⟩ := uniform_actual_noncomparable_far (T := T+1) (lam := lam) hsig K hΨ hpos hs hW hw
  obtain ⟨n,N₂,h₂⟩ := uniform_actual_comparable_far_error (T := T+1) (lam := lam) hsig K
    hΨ.continuous.measurable hpos hs hW hw
  refine ⟨n,max 1 (max N₁ N₂),?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m B δ hd J i hsp hm hb a ha A hA
    d v L₀ hvN hv hLL hL₀
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N lam sig (J l) (i l) (hsp l)
  let M := fun l => ((2:ℝ)^N)^(-m l a)
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  have hβ (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ (hm l)
  have hbd (l : Fin 2) (x : Plane) := inheritedCircleSymbol_norm_le
    (S l) (b l) (k l) (Q l) (hQp l) (ρ l) (m l) N lam sig (J l) (i l) (hsp l) K (hK l) x (hb l x)
  have hD : 0 ≤ symbolDerivativeConstant K^K := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have he₁ := h₁ N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) S b k hcard hK
    L hLN hL Q hQ ρ m B δ hd J i hsp hm hb a ha A hA d v L₀ hvN hv hLL hL₀
  have he₂ := h₂ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN)) S b k hcard hK
    L hLN hL Q hQ ρ m B δ hd J i hsp hm hb a ha A hA d v L₀ hvN hv hLL hL₀
  dsimp only
  rw [angular_far_comparable_split (Q 0) (Q 1) (ρ 0) (ρ 1) (A 0) (A 1) a d v
    hΨ.continuous.measurable hpos hs hW hw (M 0) (M 1) (by positivity) (by positivity)
    (β 0) (β 1) (hβ 0) (hβ 1) hD hD (hbd 0) (hbd 1),add_sub_assoc]
  apply ((norm_add_le _ _).trans (add_le_add he₁ he₂)).trans
  have hR : (2:ℝ) ≤ (2:ℝ)^N := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) ((le_max_left _ _).trans hN)
  calc
    _ = 2*((2:ℝ)^N)^(-(T+1)) := by ring
    _ ≤ (2:ℝ)^N*((2:ℝ)^N)^(-(T+1)) := mul_le_mul_of_nonneg_right hR (by positivity)
    _ = _ := by
      nth_rw 1 [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_far_stationary_reduction_oai := @OAI.PlanarFalconer.uniform_actual_far_stationary_reduction_oai
