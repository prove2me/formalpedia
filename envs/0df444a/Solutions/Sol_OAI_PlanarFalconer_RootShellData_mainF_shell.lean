-- Prove2me | solution 1 for OAI.PlanarFalconer.RootShellData.mainF_shell
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:06:15.077458+00:00
-- url     : https://prove2.me/submissions/6a069f67-1b05-42a9-a79c-5edebca4b298

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_RootShellData_inverseOrderForm_shell

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

namespace AngularDifferentialExpr

theorem sum_order_le (ps : List AngularDifferentialExpr) (n : ℕ)
    (h : ∀ p ∈ ps, p.order ≤ n) : (sum ps).order ≤ n := by
  induction ps with
  | nil => exact Nat.zero_le n
  | cons p ps ih =>
    exact max_le (h p (by simp)) (ih (fun q hq => h q (by simp [hq])))

end AngularDifferentialExpr
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryJetOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem stationaryJet_order {n k : ℕ} (_hk : k ∈ Finset.range (n+1))
    (c : OrderedFinpartition (n-k)) : c.length ≤ n := by
  exact c.length_le.trans (Nat.sub_le _ _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem angularFiniteSum_order {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (n : ℕ) (h : ∀ a ∈ s, (p a).order ≤ n) :
    (angularFiniteSum s p).order ≤ n := by
  apply AngularDifferentialExpr.sum_order_le
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact h a (Finset.mem_toList.mp ha)

theorem stationaryJetExpr_order (n : ℕ) : (stationaryJetExpr n).order ≤ n := by
  apply angularFiniteSum_order
  intro k hk
  apply angularFiniteSum_order
  intro c _
  exact stationaryJet_order hk c

theorem directStationaryExpr_order (j : ℕ) : (directStationaryExpr j).order ≤ 2*j := by
  simpa [directStationaryExpr, AngularDifferentialExpr.order] using stationaryJetExpr_order (2*j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem inverseStationaryExpr_order (n : ℕ) : (inverseStationaryExpr n).order ≤ 2*n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [inverseStationaryExpr, AngularDifferentialExpr.order]
    | succ n =>
      simp only [inverseStationaryExpr, AngularDifferentialExpr.order, zero_add]
      apply angularFiniteSum_order
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hi := ih (n-k) (by omega)
      have hd := directStationaryExpr_order (k+1)
      change (directStationaryExpr (k+1)).order + (inverseStationaryExpr (n-k)).order ≤ _
      omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OrderedLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem orderedDerivAssignments_budget {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (n : ℕ) {k : ι → ℕ} (hk : k ∈ orderedDerivAssignments S n) :
    ∑ i ∈ S, k i = n := by
  induction n generalizing k with
  | zero => simp only [orderedDerivAssignments,List.mem_singleton] at hk; subst k; simp
  | succ n ih =>
    obtain ⟨l,hl,hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    have hi : i ∈ S := Finset.mem_toList.mp hi
    rw [Finset.sum_update_of_mem hi,Finset.sdiff_singleton_eq_erase]
    have he := Finset.add_sum_erase S l hi
    rw [ih hl] at he
    omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularOperatorTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff
namespace AngularDifferentialExpr

theorem terms_order (p : AngularDifferentialExpr) {a : ℂ × ℕ} (ha : a ∈ p.terms) :
    a.2 ≤ p.order := by
  induction p generalizing a with
  | term c k =>
    have he : a = (c,k) := List.mem_singleton.mp ha
    subst a
    exact le_rfl
  | add p q hp hq =>
    obtain ha | ha := List.mem_append.mp ha
    · exact (hp ha).trans (le_max_left _ _)
    · exact (hq ha).trans (le_max_right _ _)
  | comp p q hp hq =>
    obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    exact Nat.add_le_add (hp hb) (hq hc)

end AngularDifferentialExpr

theorem inverseStationaryOperator_terms_order (j : ℕ) {a : ℂ × ℕ}
    (ha : a ∈ (inverseStationaryExpr j).terms) : a.2 ≤ 2*j :=
  ((inverseStationaryExpr j).terms_order ha).trans (inverseStationaryExpr_order j)

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

theorem sourceAngularTransform_product (ρ ν : Measure Plane) (X Y : Set Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ X M₁ b₁ r ω *
      conj (sourceAngularTransform ν Y M₂ b₂ r ω) =
    (M₁*M₂)⁻¹ • (∫ x in X, ∫ y in Y,
      sourcePlaneWave r ω (x-y) * (b₁ x ω * conj (b₂ y ω)) ∂ν ∂ρ) := by
  have he (x y : Plane) :
      sourcePlaneWave r ω (x-y) * (b₁ x ω * conj (b₂ y ω)) =
      (sourcePlaneWave r ω x * b₁ x ω) * conj (sourcePlaneWave r ω y * b₂ y ω) := by
    rw [← sourcePlaneWave_sub, map_mul]
    ring
  simp_rw [he, integral_const_mul, integral_mul_const, integral_conj]
  simp only [sourceAngularTransform, sourcePlaneWave, Complex.real_smul,
    map_mul, Complex.conj_ofReal, mul_inv_rev, Complex.ofReal_mul]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_DistanceFormFubini
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem finite_three_integral_swap {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (τ : Measure γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure τ]
    (f : α → β → γ → ℂ)
    (hf : Measurable (fun z : (α × β) × γ => f z.1.1 z.1.2 z.2))
    (C : ℝ) (hC : ∀ a b c, ‖f a b c‖ ≤ C) :
    (∫ a, ∫ b, ∫ c, f a b c ∂τ ∂ν ∂μ) =
      ∫ b, ∫ c, ∫ a, f a b c ∂μ ∂τ ∂ν := by
  have hi : Integrable (fun z : (α × β) × γ => f z.1.1 z.1.2 z.2)
      ((μ.prod ν).prod τ) :=
    (integrable_const C).mono hf.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun point =>
        (hC point.1.1 point.1.2 point.2).trans (le_abs_self C)))
  rw [integral_integral_swap hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards with b
  apply integral_integral_swap
  apply (integrable_const C).mono
  · exact (hf.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aestronglyMeasurable
  · filter_upwards with z
    exact (hC z.1 b z.2).trans (le_abs_self C)

theorem measurable_distance_integrand (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) (r : ℝ) :
    Measurable (fun z : (UnitCircle × Plane) × Plane =>
      sourcePlaneWave r z.1.1 (z.1.2-z.2) *
        (ψ z.1.1 * b₁ z.1.2 z.1.1 * conj (b₂ z.2 z.1.1))) := by
  apply Measurable.mul
  · unfold sourcePlaneWave
    fun_prop
  · exact ((hψ.comp (measurable_fst.comp measurable_fst)).mul
      (h₁.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst)))).mul
      (Complex.continuous_conj.measurable.comp
        (h₂.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))))

theorem distance_integrand_norm_le (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) {P B₁ B₂ : ℝ}
    (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (_ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) (ω : UnitCircle) (x y : Plane) :
    ‖sourcePlaneWave r ω (x-y) * (ψ ω * b₁ x ω * conj (b₂ y ω))‖ ≤ P*B₁*B₂ := by
  simp only [norm_mul, sourcePlaneWave_norm, Complex.norm_conj, one_mul]
  exact mul_le_mul (mul_le_mul (hp ω) (hb₁ x ω) (norm_nonneg _) hP)
    (hb₂ y ω) (norm_nonneg _) (mul_nonneg hP hB₁)

theorem sourceDistanceF_endpoint_integral (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    sourceDistanceF ψ (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2) r =
      (M₁*M₂)⁻¹ • (∫ x in X, ∫ y in Y, sourceDistanceKernel ψ b₁ b₂ r x y ∂ν ∂ρ) := by
  unfold sourceDistanceF
  simp_rw [mul_assoc, sourceAngularTransform_product, mul_smul_comm,
    ← integral_const_mul]
  have he (ω : UnitCircle) (x y : Plane) :
      ψ ω * (sourcePlaneWave r ω (x-y) * (b₁ x ω * conj (b₂ y ω))) =
        sourcePlaneWave r ω (x-y) * (ψ ω * b₁ x ω * conj (b₂ y ω)) := by ring
  simp_rw [he]
  rw [integral_smul]
  congr 1
  exact finite_three_integral_swap sourceArcLength (ρ.restrict X) (ν.restrict Y) _
    (measurable_distance_integrand ψ b₁ b₂ hψ h₁ h₂ r) (P*B₁*B₂)
    (distance_integrand_norm_le ψ b₁ b₂ hP hB₁ hB₂ hp hb₁ hb₂ r)

theorem sourceDistanceF_norm_le (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (_ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ∈ X, ∀ ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ∈ Y, ∀ ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    ‖sourceDistanceF ψ (fun z => sourceAngularTransform ρ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ b₂ z.1 z.2) r‖ ≤
      (P*B₁*B₂*sourceArcLength.real univ) *
        ((ρ X).toReal/M₁) * ((ν Y).toReal/M₂) := by
  have hh := norm_integral_le_of_norm_le_const (μ := sourceArcLength)
    (f := fun ω => ψ ω * sourceAngularTransform ρ X M₁ b₁ r ω *
      conj (sourceAngularTransform ν Y M₂ b₂ r ω))
    (C := P*(B₁*(ρ X).toReal/M₁)*(B₂*(ν Y).toReal/M₂))
    (Filter.Eventually.of_forall (fun ω => by
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul
        (mul_le_mul (hp ω) (sourceAngularTransform_norm_le ρ X M₁ hM₁ b₁ B₁ hb₁ r ω)
          (norm_nonneg _) hP)
        (sourceAngularTransform_norm_le ν Y M₂ hM₂ b₂ B₂ hb₂ r ω)
        (norm_nonneg _) (by positivity)))
  apply hh.trans_eq
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphConeCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem graphConeCutoff_contDiff : ContDiff ℝ ∞ graphConeCutoff :=
  Complex.ofRealCLM.contDiff.comp graphConeBump.contDiff

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedConeKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

theorem measurable_sourceConeCircle (axis : ℝ) : Measurable (sourceConeCircle axis) :=
  graphConeCutoff_contDiff.continuous.measurable.comp
    (measurable_sourceAngle.comp (sourceCircleRotate_isometry (-axis)).continuous.measurable)

theorem sourceConeCircle_norm_le (axis : ℝ) (dir : UnitCircle) :
    ‖sourceConeCircle axis dir‖ ≤ 1 := by
  simp only [sourceConeCircle, graphConeCutoff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg graphConeBump.nonneg]
  exact graphConeBump.le_one

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialAnnulusKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric Filter
open scoped ContDiff Topology SchwartzMap

theorem spatialAnnulusKernel_eq (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {z : Plane} (hz₁ : δ ≤ ‖z‖) (hz₂ : ‖z‖ ≤ L) :
    spatialAnnulusKernel δ L hδ hL j z = ↑((‖z‖^j)⁻¹) := by
  have hi : spatialInnerBump δ hδ z = 0 :=
    (spatialInnerBump δ hδ).zero_of_le_dist (by simpa [spatialInnerBump] using hz₁)
  have ho : spatialOuterBump L hL z = 1 :=
    (spatialOuterBump L hL).one_of_mem_closedBall (by simpa [spatialOuterBump] using hz₂)
  simp [spatialAnnulusKernel, hi, ho]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialFourierSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate

theorem spatialFourierCost_nonneg (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 0 ≤ spatialFourierCost δ L hδ hL j :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem spatialFourierPhase_norm (s : ℝ) (ξ x : Plane) :
    ‖spatialFourierPhase s ξ x‖ = 1 := by
  simp [spatialFourierPhase, Complex.norm_exp, Complex.mul_re]

theorem spatialFourierPhase_sub (s : ℝ) (ξ x y : Plane) :
    spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y) =
      Complex.exp (↑(2*Real.pi*inner ℝ ξ (s⁻¹ • (x-y)))*Complex.I) := by
  simp only [spatialFourierPhase, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, smul_sub,
    inner_sub_right, mul_sub, Complex.ofReal_sub]
  congr 1
  ring

theorem spatialFourierCoeff_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : Integrable (spatialFourierCoeff δ L hδ hL j) :=
  (spatialFourierCoeff δ L hδ hL j).integrable

theorem spatialFourierSeparation (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (x y : Plane) :
    (∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
      (spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y))) =
      spatialAnnulusKernel δ L hδ hL j (s⁻¹ • (x-y)) := by
  have he := congrArg (fun f : 𝓢(Plane, ℂ) => f (s⁻¹ • (x-y)))
    (show (𝓕⁻ (𝓕 (spatialAnnulusSchwartz δ L hδ hL j) : 𝓢(Plane, ℂ)) :
      𝓢(Plane, ℂ)) = spatialAnnulusSchwartz δ L hδ hL j from
      FourierTransform.fourierInv_fourier_eq _)
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', smul_eq_mul] at he
  refine Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards with ξ
  rw [spatialFourierPhase_sub]
  exact mul_comm _ _

theorem spatialInverseDistance_separation (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {s : ℝ} (hs : 0 < s) {x y : Plane}
    (hd₁ : δ ≤ dist x y / s) (hd₂ : dist x y / s ≤ L) :
    (↑((dist x y / s)^j)⁻¹ : ℂ) =
      ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
        (spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y)) := by
  have hn : ‖s⁻¹ • (x-y)‖ = dist x y / s := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, dist_eq_norm, div_eq_inv_mul]
  rw [spatialFourierSeparation, spatialAnnulusKernel_eq δ L hδ hL j
    (by rwa [hn]) (by rwa [hn]), hn, Complex.ofReal_inv]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ContinuousCoefficientShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

 theorem integrable_coeff_norm_power {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c F : α → ℂ) (hic : Integrable c μ) (hF : Measurable F)
    {C : ℝ} (_ : 0 ≤ C) (hb : ∀ x, ‖F x‖ ≤ C) (n : ℕ) :
    Integrable (fun x => ‖c x‖ * ‖F x‖^n) μ := by
  apply (hic.norm.mul_const (C^n)).mono'
    (hic.aestronglyMeasurable.norm.mul (hF.aestronglyMeasurable.norm.pow n))
  filter_upwards with x
  change ‖‖c x‖ * ‖F x‖^n‖ ≤ ‖c x‖ * C^n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb x) n) (norm_nonneg _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_FiniteWeightedShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem finite_weighted_shell_square {ι : Type*} (s : Finset ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hi : ∀ i ∈ s, Integrable (fun r => ‖F i r‖^2) μ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (F i) μ)
    (hB : ∀ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) ≤ (w i)^2*B) :
    (∫ r, ‖∑ i ∈ s, F i r‖^2 ∂μ) ≤ (∑ i ∈ s, w i)^2*B := by
  classical
  have hz (i : ι) (his : i ∈ s) (hwi : w i = 0) :
      ∀ᵐ r ∂μ, F i r = 0 := by
    have he : (∫ r, ‖F i r‖^2 ∂μ) = 0 :=
      le_antisymm (by simpa [hwi] using hB i his)
        (integral_nonneg (fun _ => sq_nonneg _))
    have hh := (integral_eq_zero_iff_of_nonneg (fun r => sq_nonneg (‖F i r‖)) (hi i his)).mp he
    filter_upwards [hh] with r hr
    simpa using hr
  have hae : ∀ᵐ r ∂μ, ∀ i ∈ s, w i = 0 → F i r = 0 := by
    exact (eventually_all_finset s).mpr (fun i his =>
      (ae_all_iff).mpr (fun hwi => hz i his hwi))
  let G : ℝ → ℝ := fun r => ∑ i ∈ s, ‖F i r‖^2 / w i
  let W : ℝ := ∑ i ∈ s, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hgi : Integrable G μ := integrable_finsetSum s
    (fun i his => (hi i his).div_const (w i))
  have hpoint : ∀ᵐ r ∂μ, ‖∑ i ∈ s, F i r‖^2 ≤ W*G r := by
    filter_upwards [hae] with r hr
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2).trans
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i his => div_nonneg (sq_nonneg _) (hw i his))
    intro i his
    by_cases hwi : w i = 0
    · simp [hwi,hr i his hwi]
    · rw [mul_div_cancel₀ _ hwi]
  have hsi : Integrable (fun r => ‖∑ i ∈ s, F i r‖^2) μ := by
    have hsm : AEStronglyMeasurable (fun r => ∑ i ∈ s, F i r) μ := by
      convert Finset.aestronglyMeasurable_sum s hm using 1
      all_goals try with_reducible_and_instances rfl
      ext r
      simp
    apply (hgi.const_mul W).mono' (hsm.norm.pow 2)
    filter_upwards [hpoint] with r hr
    change ‖‖∑ i ∈ s, F i r‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hr
  have hBi (i : ι) (his : i ∈ s) :
      (∫ r, ‖F i r‖^2 ∂μ) / w i ≤ w i*B := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · apply (div_le_iff₀ (lt_of_le_of_ne (hw i his) (Ne.symm hwi))).mpr
      nlinarith [hB i his]
  calc
    _ ≤ ∫ r, W*G r ∂μ := integral_mono_ae hsi (hgi.const_mul W) hpoint
    _ = W * ∑ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) / w i := by
      rw [integral_const_mul,integral_finsetSum s (fun i his => (hi i his).div_const (w i))]
      simp only [integral_div]
    _ ≤ W * ∑ i ∈ s, w i*B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hBi) hW
    _ = _ := by rw [← Finset.sum_mul]; dsimp [W]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_FiniteSquareIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem finite_sum_square_integrable {ι : Type*} (s : Finset ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ)
    (hm : ∀ i ∈ s, Measurable (F i))
    (hi : ∀ i ∈ s, Integrable (fun r => ‖F i r‖^2) μ) :
    Integrable (fun r => ‖∑ i ∈ s, F i r‖^2) μ := by
  have hsm : Measurable (fun r => ∑ i ∈ s, F i r) := by
    exact Finset.measurable_sum s hm
  have hb := (integrable_finsetSum s hi).const_mul (∑ _i ∈ s, (1:ℝ))
  apply hb.mono' (hsm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with r
  change ‖‖∑ i ∈ s, F i r‖^2‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2).trans
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun _ => (1:ℝ)) (g := fun i => ‖F i r‖^2) (r := fun i => ‖F i r‖)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_InverseLeibniz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem inverseLeibnizTerms_budget {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι)
    {a : ℂ × (ι → ℕ)} (ha : a ∈ inverseLeibnizTerms j S) :
    ∑ i ∈ S, a.2 i ≤ 2*j := by
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  rw [orderedDerivAssignments_budget S b.2 hk]
  exact inverseStationaryOperator_terms_order j hb

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceKernelSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem measurable_sourceDistanceKernel (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) :
    Measurable (fun z : ℝ × (Plane × Plane) => sourceDistanceKernel ψ b₁ b₂ z.1 z.2.1 z.2.2) := by
  have hf : Measurable (fun z : (ℝ × (Plane × Plane)) × UnitCircle =>
      sourcePlaneWave z.1.1 z.2 (z.1.2.1-z.1.2.2) *
        (ψ z.2 * b₁ z.1.2.1 z.2 * conj (b₂ z.1.2.2 z.2))) := by
    apply Measurable.mul
    · unfold sourcePlaneWave
      fun_prop
    · exact (((hψ.comp measurable_snd).mul
        (h₁.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))).mul
        (Complex.continuous_conj.measurable.comp
          (h₂.comp ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

theorem sourceDistanceKernel_norm_le (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) {P B₁ B₂ : ℝ}
    (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁)
    (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂) (r : ℝ) (x y : Plane) :
    ‖sourceDistanceKernel ψ b₁ b₂ r x y‖ ≤ P*B₁*B₂*sourceArcLength.real univ :=
  norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall (fun dir =>
    distance_integrand_norm_le ψ b₁ b₂ hP hB₁ hB₂ hp hb₁ hb₂ r dir x y))

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
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellKernelTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

 theorem integrable_list_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : List ι) (f : ι → α → ℂ) (hf : ∀ i ∈ L, Integrable (f i) μ) :
    Integrable (fun x => (L.map (fun i => f i x)).sum) μ := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hf i (by simp)).add (ih (fun a ha => hf a (by simp [ha])))

 theorem integral_list_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (L : List ι) (f : ι → α → ℂ) (hf : ∀ i ∈ L, Integrable (f i) μ) :
    (∫ x, (L.map (fun i => f i x)).sum ∂μ) = (L.map (fun i => ∫ x, f i x ∂μ)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hf i (by simp)) (integrable_list_sum μ L f (fun a ha => hf a (by simp [ha]))),
      ih (fun a ha => hf a (by simp [ha]))]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ListBoundedFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem list_sum_measurable_bounded {ι : Type*} (L : List ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ L, Measurable (F i) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖F i r‖ ≤ C) :
    Measurable (fun r => (L.map (fun i => F i r)).sum) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖(L.map (fun i => F i r)).sum‖ ≤ C := by
  induction L with
  | nil => exact ⟨by simp,
      0,le_rfl,by simp⟩
  | cons a L ih =>
    obtain ⟨ha,A,hA,hAb⟩ := hF a (by simp)
    obtain ⟨hl,D,hD,hDb⟩ := ih (fun i hi => hF i (by simp [hi]))
    refine ⟨?_,A+D,add_nonneg hA hD,?_⟩
    · exact ha.add hl
    intro r
    simpa using (norm_add_le (F a r) ((L.map (fun i => F i r)).sum)).trans
      (add_le_add (hAb r) (hDb r))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootLeibnizBounds
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem root_assignment_budgets (d e : RootEndpointData) (k : RootMaskIndex → ℕ)
    (K : ℕ) (hk : ∑ b ∈ rootMaskIndices d e, k b ≤ K) :
    (∑ b ∈ d.S, k (.inl b)) ≤ K ∧ (∑ b ∈ e.S, k (.inr b)) ≤ K := by
  simp only [rootMaskIndices,Finset.sum_disjSum] at hk
  constructor <;> omega

namespace RootEndpointData

theorem symbol_measurable (d : RootEndpointData) (N : ℕ) (sig : ℝ) (k : PolicyDescriptor → ℕ) :
    Measurable (fun z : Plane × UnitCircle => d.symbol N sig k (fun _ => 1) z.1 z.2) :=
  measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ measurable_const

theorem symbol_norm (d : RootEndpointData) (hd : 0 < d.Q.side) (N : ℕ) (sig : ℝ)
    (k : PolicyDescriptor → ℕ) (K : ℕ) (hk : ∑ b ∈ d.S, k b ≤ K) (x : Plane) (dir : UnitCircle) :
    ‖d.symbol N sig k (fun _ => 1) x dir‖ ≤ symbolDerivativeConstant K^K :=
  inheritedCircleSymbol_norm_le _ _ _ _ hd _ _ _ _ _ _ _ _ K hk x (by simp) dir

end RootEndpointData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootEndpointTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem rootLeftSymbol_measurable (d : RootEndpointData) (N : ℕ) (sig : ℝ) (k : RootMaskIndex → ℕ) :
    Measurable (fun z : Plane × UnitCircle => rootLeftSymbol d N sig k z.1 z.2) :=
  d.symbol_measurable N sig _

theorem rootRightSymbol_measurable (e : RootEndpointData) (N : ℕ) (sig : ℝ) (k : RootMaskIndex → ℕ) :
    Measurable (fun z : Plane × UnitCircle => rootRightSymbol e N sig k z.1 z.2) :=
  e.symbol_measurable N sig _

theorem rootLeftSymbol_norm (d e : RootEndpointData) (hd : 0 < d.Q.side) (N j : ℕ) (sig : ℝ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e))
    (x : Plane) (dir : UnitCircle) :
    ‖rootLeftSymbol d N sig b.2 x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) :=
  d.symbol_norm hd N sig _ (2*j)
    (root_assignment_budgets d e _ _ (inverseLeibnizTerms_budget j _ hb)).1 x dir

theorem rootRightSymbol_norm (d e : RootEndpointData) (he : 0 < e.Q.side) (N j : ℕ) (sig : ℝ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e))
    (y : Plane) (dir : UnitCircle) :
    ‖rootRightSymbol e N sig b.2 y dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) :=
  e.symbol_norm he N sig _ (2*j)
    (root_assignment_budgets d e _ _ (inverseLeibnizTerms_budget j _ hb)).2 y dir

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootFourierError
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

theorem root_pair_ae_patches (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (U V : DyadicSquare)
    (hU : ∀ᵐ x ∂d.ρ, x ∈ U.carrier) (hV : ∀ᵐ y ∂e.ρ, y ∈ V.carrier) :
    ∀ᵐ z ∂d.ρ.prod e.ρ, z.1 ∈ U.carrier ∧ z.2 ∈ V.carrier :=
  (Measure.quasiMeasurePreserving_fst.ae hU).and (Measure.quasiMeasurePreserving_snd.ae hV)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialFourierIntegration
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter
open scoped ComplexConjugate

theorem spatialPairPhase_norm (s : ℝ) (ξ : Plane) (z : Plane × Plane) :
    ‖spatialPairPhase s ξ z‖ = 1 := by
  simp [spatialPairPhase, spatialFourierPhase_norm]

theorem spatialFourier_joint_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure (Plane × Plane)) [IsFiniteMeasure μ]
    (A : Plane × Plane → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    Integrable (fun p : Plane × (Plane × Plane) =>
      spatialFourierCoeff δ L hδ hL j p.1 * (spatialPairPhase s p.1 p.2 * A p.2))
      (volume.prod μ) := by
  have hm : AEStronglyMeasurable (fun p : Plane × (Plane × Plane) =>
      spatialFourierCoeff δ L hδ hL j p.1 * (spatialPairPhase s p.1 p.2 * A p.2))
      (volume.prod μ) :=
    (spatialFourierCoeff δ L hδ hL j).continuous.aestronglyMeasurable.comp_fst.mul
      ((spatialPairPhase_continuous s).aestronglyMeasurable.mul
        hA.aestronglyMeasurable.comp_snd)
  apply (((spatialFourierCoeff_integrable δ L hδ hL j).norm.comp_fst μ).mul_const C).mono' hm
  filter_upwards with p
  simp only [norm_mul, spatialPairPhase_norm, one_mul]
  exact mul_le_mul_of_nonneg_left (hb p.2) (norm_nonneg _)

theorem spatialFourier_integral_swap (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (μ : Measure (Plane × Plane)) [IsFiniteMeasure μ]
    (A : Plane × Plane → ℂ) (hA : Measurable A) {C : ℝ}
    (hb : ∀ z, ‖A z‖ ≤ C) :
    (∫ z, spatialAnnulusKernel δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z ∂μ) =
      ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
        ∫ z, spatialPairPhase s ξ z * A z ∂μ := by
  have he (z : Plane × Plane) :
      spatialAnnulusKernel δ L hδ hL j (s⁻¹ • (z.1-z.2)) * A z =
        ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ * (spatialPairPhase s ξ z * A z) := by
    rw [← spatialFourierSeparation, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp [spatialPairPhase]
    ring
  simp_rw [he]
  simpa only [integral_const_mul] using
    (integral_integral_swap (f := fun ξ z => spatialFourierCoeff δ L hδ hL j ξ *
      (spatialPairPhase s ξ z * A z))
      (spatialFourier_joint_integrable δ L hδ hL j s μ A hA hb)).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SpatialPhasedSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ComplexConjugate

theorem spatialPhasedSymbol_norm (s : ℝ) (ξ : Plane)
    (b : Plane → UnitCircle → ℂ) (x : Plane) (ω : UnitCircle) :
    ‖spatialPhasedSymbol s ξ b x ω‖ = ‖b x ω‖ := by
  simp [spatialPhasedSymbol, spatialFourierPhase_norm]

theorem spatialPhasedSymbol_measurable (s : ℝ) (ξ : Plane)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2)) :
    Measurable (fun z : Plane × UnitCircle => spatialPhasedSymbol s ξ b z.1 z.2) := by
  apply Measurable.mul _ hb
  unfold spatialFourierPhase
  fun_prop

theorem sourceDistanceKernel_phased (s : ℝ) (ξ : Plane) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) (x y : Plane) :
    sourceDistanceKernel ψ (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r x y =
      spatialPairPhase s ξ (x,y) * sourceDistanceKernel ψ b₁ b₂ r x y := by
  simp only [sourceDistanceKernel, spatialPhasedSymbol, spatialPairPhase, map_mul,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialDistanceFormSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ComplexConjugate

 theorem spatialDistanceForm_separation (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    (M₁*M₂)⁻¹ • (∫ z, spatialAnnulusKernel δ L hδ hL j (s⁻¹ • (z.1-z.2)) *
      sourceDistanceKernel ψ b₁ b₂ r z.1 z.2 ∂((ρ.restrict X).prod (ν.restrict Y))) =
      ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
        sourceDistanceF ψ
          (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s ξ b₁) z.1 z.2)
          (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s ξ b₂) z.1 z.2) r := by
  have hmk : Measurable (fun z : Plane × Plane => sourceDistanceKernel ψ b₁ b₂ r z.1 z.2) :=
    (measurable_sourceDistanceKernel ψ b₁ b₂ hψ h₁ h₂).comp (f := fun z : Plane × Plane => (r,z))
      (show Measurable (fun z : Plane × Plane => (r,z)) from measurable_const.prodMk measurable_id)
  have hbk := sourceDistanceKernel_norm_le ψ b₁ b₂ hP hB₁ hB₂ hp hb₁ hb₂ r
  rw [spatialFourier_integral_swap δ L hδ hL j s _ _ hmk (fun z => hbk z.1 z.2),
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards with ξ
  have hm₁ := spatialPhasedSymbol_measurable s ξ b₁ h₁
  have hm₂ := spatialPhasedSymbol_measurable s ξ b₂ h₂
  have hb₁' : ∀ x ω, ‖spatialPhasedSymbol s ξ b₁ x ω‖ ≤ B₁ := by
    intro x ω
    rw [spatialPhasedSymbol_norm]
    exact hb₁ x ω
  have hb₂' : ∀ x ω, ‖spatialPhasedSymbol s ξ b₂ x ω‖ ≤ B₂ := by
    intro x ω
    rw [spatialPhasedSymbol_norm]
    exact hb₂ x ω
  rw [sourceDistanceF_endpoint_integral ρ ν X Y M₁ M₂ ψ _ _ hψ hm₁ hm₂
    hP hB₁ hB₂ hp hb₁' hb₂']
  have hm : Measurable (fun z : Plane × Plane => sourceDistanceKernel ψ
      (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r z.1 z.2) :=
    (measurable_sourceDistanceKernel ψ _ _ hψ hm₁ hm₂).comp (f := fun z : Plane × Plane => (r,z)) (show Measurable (fun z : Plane × Plane => (r,z)) from measurable_const.prodMk measurable_id)
  have hi : Integrable (fun z : Plane × Plane => sourceDistanceKernel ψ
      (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r z.1 z.2)
      ((ρ.restrict X).prod (ν.restrict Y)) :=
    Integrable.of_bound hm.aestronglyMeasurable (P*B₁*B₂*sourceArcLength.real univ)
      (Eventually.of_forall (fun z => sourceDistanceKernel_norm_le ψ _ _ hP hB₁ hB₂
        hp hb₁' hb₂' r z.1 z.2))
  rw [← integral_prod _ hi]
  simp_rw [sourceDistanceKernel_phased]
  simp only [Complex.real_smul]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_SeparatedSpatialDistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

 theorem separatedSpatialDistanceForm (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {s : ℝ} (hs : 0 < s) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (X Y : Set Plane)
    (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ dist x y / s ∧ dist x y / s ≤ L)
    (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    (M₁*M₂)⁻¹ • (∫ z, (↑((dist z.1 z.2 / s)^j)⁻¹ : ℂ) *
      sourceDistanceKernel ψ b₁ b₂ r z.1 z.2 ∂((ρ.restrict X).prod (ν.restrict Y))) =
      ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
        sourceDistanceF ψ
          (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s ξ b₁) z.1 z.2)
          (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s ξ b₂) z.1 z.2) r := by
  rw [← spatialDistanceForm_separation δ L hδ hL j s ρ ν X Y M₁ M₂ ψ b₁ b₂
    hψ h₁ h₂ hP hB₁ hB₂ hp hb₁ hb₂]
  congr 1
  apply integral_congr_ae
  have hx : ∀ᵐ z ∂((ρ.restrict X).prod (ν.restrict Y)), z.1 ∈ X :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hX)
  have hy : ∀ᵐ z ∂((ρ.restrict X).prod (ν.restrict Y)), z.2 ∈ Y :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hY)
  filter_upwards [hx,hy] with z hz₁ hz₂
  have hd := hsep z.1 hz₁ z.2 hz₂
  have he := spatialInverseDistance_separation δ L hδ hL j hs hd.1 hd.2
  rw [spatialFourierSeparation] at he
  rw [he]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialDistanceError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem integrable_norm_square_bounded (μ : Measure ℝ) [IsFiniteMeasure μ]
    (F : ℝ → ℂ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ r ∂μ, ‖F r‖ ≤ B) : Integrable (fun r => ‖F r‖^2) μ := by
  apply (integrable_const (B^2)).mono (hF.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [hb] with r hr
  simp only [norm_pow, Real.norm_eq_abs, abs_of_nonneg hB, abs_of_nonneg (norm_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hr 2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootSpatialTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

theorem rootDistanceEndpointKernel_measurable (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (U V : DyadicSquare) (j : ℕ) (k : RootMaskIndex → ℕ) (r : ℝ) :
    Measurable (rootDistanceEndpointKernel d e N sig U V j k r) := by
  unfold rootDistanceEndpointKernel
  apply Measurable.mul
  · fun_prop
  · exact (measurable_sourceDistanceKernel _ _ _ (measurable_sourceConeCircle _)
      (rootLeftSymbol_measurable d N sig k) (rootRightSymbol_measurable e N sig k)).comp
      (f := fun z : Plane × Plane => (r,z)) (measurable_const.prodMk measurable_id)

theorem rootDistanceEndpointKernel_integrable (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (N : ℕ) (sig : ℝ)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (U V : DyadicSquare)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2)
    (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e)) (r : ℝ) :
    Integrable (rootDistanceEndpointKernel d e N sig U V j b.2 r) (d.ρ.prod e.ρ) := by
  let C := symbolDerivativeConstant (2*j)^(2*j)
  have hC : 0 ≤ C := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  refine Integrable.of_bound (rootDistanceEndpointKernel_measurable d e N sig U V j b.2 r).aestronglyMeasurable
    (δ⁻¹^j*(1*C*C*sourceArcLength.real univ)) ?_
  filter_upwards [hsep] with z hz
  have hinv := inv_anti₀ hδ hz
  have hn : ‖((((dist z.1 z.2)⁻¹)^j:ℝ):ℂ)‖ ≤ δ⁻¹^j := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) hinv j
  have hk := sourceDistanceKernel_norm_le (sourceConeCircle (sourceParentAxis U V)) _ _ (by norm_num : (0:ℝ) ≤ 1) hC hC
    (sourceConeCircle_norm_le (sourceParentAxis U V)) (rootLeftSymbol_norm d e hd N j sig hb)
    (rootRightSymbol_norm d e he N j sig hb) r z.1 z.2
  change ‖_ * _‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul hn hk (norm_nonneg _) (by positivity)

theorem rootDistanceEndpointKernel_form (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (U V : DyadicSquare)
    (hcarry₁ : ∀ᵐ x ∂d.ρ, x ∈ U.carrier) (hcarry₂ : ∀ᵐ y ∂e.ρ, y ∈ V.carrier)
    (hsep : ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y ∧ dist x y ≤ L)
    (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e)) (r : ℝ) :
    (∫ z, rootDistanceEndpointKernel d e N sig U V j b.2 r z ∂d.ρ.prod e.ρ) =
      ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
        sourceParentDistanceF U V d.ρ e.ρ 1 1
          (spatialPhasedSymbol 1 ξ (rootLeftSymbol d N sig b.2))
          (spatialPhasedSymbol 1 ξ (rootRightSymbol e N sig b.2)) r := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  have hh := separatedSpatialDistanceForm δ L hδ hL j (s := 1) (by norm_num)
    d.ρ e.ρ U.carrier V.carrier U.measurable V.measurable
    (fun x hx y hy => by simpa only [div_one] using hsep x hx y hy)
    1 1 _ _ _ (measurable_sourceConeCircle (sourceParentAxis U V))
    (rootLeftSymbol_measurable d N sig b.2) (rootRightSymbol_measurable e N sig b.2)
    (by norm_num : (0:ℝ) ≤ 1) hC hC (sourceConeCircle_norm_le _)
    (rootLeftSymbol_norm d e hd N j sig hb) (rootRightSymbol_norm d e he N j sig hb) r
  rw [Measure.restrict_eq_self_of_ae_mem hcarry₁,Measure.restrict_eq_self_of_ae_mem hcarry₂] at hh
  simpa only [one_mul,inv_one,one_smul,div_one,inv_pow,rootDistanceEndpointKernel,sourceParentDistanceF] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootFiniteSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

theorem rootNormalizedF_finite_separation (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (U V : DyadicSquare)
    (hcarry₁ : ∀ᵐ x ∂d.ρ, x ∈ U.carrier) (hcarry₂ : ∀ᵐ y ∂e.ρ, y ∈ V.carrier)
    (hsep : ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y ∧ dist x y ≤ L)
    (n : ℕ) (r : ℝ) :
    rootNormalizedF d e N sig n U V r =
      (((r^(1/2:ℝ)):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        ((((r/(2:ℝ)^(N:ℝ))⁻¹)^j:ℝ):ℂ) *
          ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
            rootAbsorbedCoefficient d e N sig j b *
              ∫ ξ, spatialFourierCoeff δ L hδ hL j ξ *
                sourceParentDistanceF U V d.ρ e.ρ 1 1
                  (spatialPhasedSymbol 1 ξ (rootLeftSymbol d N sig b.2))
                  (spatialPhasedSymbol 1 ξ (rootRightSymbol e N sig b.2)) r)).sum := by
  let I := fun j => inverseLeibnizTerms j (rootMaskIndices d e)
  let R := fun j => ((((r/(2:ℝ)^(N:ℝ))⁻¹)^j:ℝ):ℂ)
  let A := (((r^(1/2:ℝ)):ℝ):ℂ)
  let K := fun j (b : ℂ × (RootMaskIndex → ℕ)) => rootDistanceEndpointKernel d e N sig U V j b.2 r
  let c := fun j b => rootAbsorbedCoefficient d e N sig j b
  have hdist : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2 := by
    filter_upwards [root_pair_ae_patches d e U V hcarry₁ hcarry₂] with z hz
    exact (hsep z.1 hz.1 z.2 hz.2).1
  have hi (j : ℕ) (b : ℂ × (RootMaskIndex → ℕ)) (hb : b ∈ I j) :
      Integrable (fun z => c j b * K j b z) (d.ρ.prod e.ρ) :=
    (rootDistanceEndpointKernel_integrable d e N sig hd he U V hδ hdist j hb r).const_mul (c j b)
  have hiJ (j : ℕ) : Integrable (fun z => R j * ((I j).map (fun b => c j b * K j b z)).sum) (d.ρ.prod e.ρ) :=
    (integrable_list_sum (d.ρ.prod e.ρ) (I j) (fun b z => c j b * K j b z) (hi j)).const_mul (R j)
  have heJ (j : ℕ) :
      (∫ z, R j * ((I j).map (fun b => c j b * K j b z)).sum ∂d.ρ.prod e.ρ) =
        R j * ((I j).map (fun b => c j b * ∫ z, K j b z ∂d.ρ.prod e.ρ)).sum := by
    rw [integral_const_mul,integral_list_sum (d.ρ.prod e.ρ) (I j) _ (hi j)]
    simp_rw [integral_const_mul]
  have hk (z : Plane × Plane) : rootNormalizedKernel d e N sig n r
      (sourceConeCircle (sourceParentAxis U V)) z =
      A * ∑ j ∈ Finset.range (n+1), R j * ((I j).map (fun b => c j b * K j b z)).sum := by
    simp only [rootNormalizedKernel,neg_zero,Real.rpow_zero,mul_one,div_one,
      A,R,I,c,K,rootDistanceEndpointKernel]
  unfold rootNormalizedF
  simp_rw [hk]
  rw [integral_const_mul,integral_finsetSum (Finset.range (n+1)) (fun j _ => hiJ j)]
  simp_rw [heJ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  rw [show (∫ z, K j b z ∂d.ρ.prod e.ρ) = _ from
    rootDistanceEndpointKernel_form δ L hδ hL d e N sig hd he U V hcarry₁ hcarry₂ hsep j hb r]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialPhasedDistanceForm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

 theorem spatialPhasedDistanceF_formula (s : ℝ) (ξ : Plane)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) :
    sourceDistanceF ψ
      (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s ξ b₁) z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s ξ b₂) z.1 z.2) r =
      (M₁*M₂)⁻¹ • (∫ z, spatialPairPhase s ξ z * sourceDistanceKernel ψ b₁ b₂ r z.1 z.2
        ∂((ρ.restrict X).prod (ν.restrict Y))) := by
  have hm₁ := spatialPhasedSymbol_measurable s ξ b₁ h₁
  have hm₂ := spatialPhasedSymbol_measurable s ξ b₂ h₂
  have hb₁' : ∀ x ω, ‖spatialPhasedSymbol s ξ b₁ x ω‖ ≤ B₁ := by
    intro x ω; rw [spatialPhasedSymbol_norm]; exact hb₁ x ω
  have hb₂' : ∀ x ω, ‖spatialPhasedSymbol s ξ b₂ x ω‖ ≤ B₂ := by
    intro x ω; rw [spatialPhasedSymbol_norm]; exact hb₂ x ω
  rw [sourceDistanceF_endpoint_integral ρ ν X Y M₁ M₂ ψ _ _ hψ hm₁ hm₂
    hP hB₁ hB₂ hp hb₁' hb₂']
  have hm : Measurable (fun z : Plane × Plane => sourceDistanceKernel ψ
      (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r z.1 z.2) :=
    (measurable_sourceDistanceKernel ψ _ _ hψ hm₁ hm₂).comp (f := fun z : Plane × Plane => (r,z))
      (show Measurable (fun z : Plane × Plane => (r,z)) from measurable_const.prodMk measurable_id)
  have hi : Integrable (fun z : Plane × Plane => sourceDistanceKernel ψ
      (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r z.1 z.2)
      ((ρ.restrict X).prod (ν.restrict Y)) :=
    Integrable.of_bound hm.aestronglyMeasurable (P*B₁*B₂*sourceArcLength.real univ)
      (Eventually.of_forall (fun z => sourceDistanceKernel_norm_le ψ _ _ hP hB₁ hB₂
        hp hb₁' hb₂' r z.1 z.2))
  rw [← integral_prod _ hi]
  simp_rw [sourceDistanceKernel_phased]

 theorem spatialPhasedDistanceF_joint_measurable (s : ℝ)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set Plane) (M₁ M₂ : ℝ) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (hψ : Measurable ψ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {P B₁ B₂ : ℝ} (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) :
    Measurable (fun p : Plane × ℝ => sourceDistanceF ψ
      (fun z => sourceAngularTransform ρ X M₁ (spatialPhasedSymbol s p.1 b₁) z.1 z.2)
      (fun z => sourceAngularTransform ν Y M₂ (spatialPhasedSymbol s p.1 b₂) z.1 z.2) p.2) := by
  simp_rw [spatialPhasedDistanceF_formula s _ ρ ν X Y M₁ M₂ ψ b₁ b₂ hψ h₁ h₂
    hP hB₁ hB₂ hp hb₁ hb₂]
  have hphase : Measurable (fun p : (Plane × ℝ) × (Plane × Plane) =>
      spatialPairPhase s p.1.1 p.2) :=
    (spatialPairPhase_continuous s).measurable.comp (f := fun p : (Plane × ℝ) × (Plane × Plane) => (p.1.1,p.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hkernel : Measurable (fun p : (Plane × ℝ) × (Plane × Plane) =>
      sourceDistanceKernel ψ b₁ b₂ p.1.2 p.2.1 p.2.2) :=
    (measurable_sourceDistanceKernel ψ b₁ b₂ hψ h₁ h₂).comp (f := fun p : (Plane × ℝ) × (Plane × Plane) => (p.1.2,p.2))
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : Plane × ℝ =>
      ∫ z, spatialPairPhase s p.1 z * sourceDistanceKernel ψ b₁ b₂ p.2 z.1 z.2
        ∂((ρ.restrict X).prod (ν.restrict Y))) :=
    (hphase.mul hkernel).stronglyMeasurable.integral_prod_right'.measurable
  exact hm.const_smul ((M₁*M₂)⁻¹ : ℝ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellMultipliers
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem shell_multiplier_square (μ : Measure ℝ) (u F : ℝ → ℂ)
    (hu : Measurable u) (hF : Measurable F)
    (hi : Integrable (fun r => ‖F r‖^2) μ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ᵐ r ∂μ, ‖u r‖ ≤ A) :
    Integrable (fun r => ‖u r*F r‖^2) μ ∧
      (∫ r, ‖u r*F r‖^2 ∂μ) ≤ A^2*(∫ r, ‖F r‖^2 ∂μ) := by
  have hp : ∀ᵐ r ∂μ, ‖u r*F r‖^2 ≤ A^2*‖F r‖^2 := by
    filter_upwards [hb] with r hr
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hA).mpr hr) (sq_nonneg _)
  have hi' : Integrable (fun r => ‖u r*F r‖^2) μ := by
    apply (hi.const_mul (A^2)).mono' ((hu.mul hF).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hp] with r hr
    change ‖‖u r*F r‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hr
  exact ⟨hi', (integral_mono_ae hi' (hi.const_mul (A^2)) hp).trans_eq (integral_const_mul _ _)⟩

theorem continuous_shell_mixture_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : Plane → ℂ) (hc : Measurable c) (hic : Integrable c)
    (F : Plane × ℝ → ℂ) (hF : Measurable F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ p, ‖F p‖ ≤ C) :
    Measurable (fun r => ∫ ξ, c ξ*F (ξ,r)) ∧
    (∀ r, ‖∫ ξ, c ξ*F (ξ,r)‖ ≤ (∫ ξ, ‖c ξ‖)*C) ∧
    Integrable (fun r => ‖∫ ξ, c ξ*F (ξ,r)‖^2) μ := by
  have hm : Measurable (fun r => ∫ ξ, c ξ*F (ξ,r)) :=
    ((hc.comp measurable_fst).mul hF).stronglyMeasurable.integral_prod_left'.measurable
  have hn (r : ℝ) : ‖∫ ξ, c ξ*F (ξ,r)‖ ≤ (∫ ξ, ‖c ξ‖)*C := by
    apply (norm_integral_le_integral_norm _).trans
    simp only [norm_mul]
    have hi := integrable_coeff_norm_power volume c (fun ξ => F (ξ,r)) hic
      (hF.comp (measurable_id.prodMk measurable_const)) hC (fun ξ => hb (ξ,r)) 1
    apply (integral_mono (by simpa using hi) (hic.norm.mul_const C)
      (fun ξ => mul_le_mul_of_nonneg_left (hb (ξ,r)) (norm_nonneg _))).trans_eq
    exact integral_mul_const _ _
  refine ⟨hm,hn,?_⟩
  apply Integrable.of_bound (hm.norm.pow_const 2).aestronglyMeasurable
    (((∫ ξ, ‖c ξ‖)*C)^2)
  filter_upwards with r
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hn r) 2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellRadialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem high_shell_radial_inverse {v r : ℝ} (hr : (2:ℝ)^(v-1) ≤ r) (j : ℕ) :
    ‖((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ)‖ ≤ (2:ℝ)^j := by
  have hp : 0 < r := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hr
  have he : (2:ℝ)^(v-1) = (2:ℝ)^v/2 := by rw [Real.rpow_sub (by norm_num)]; norm_num
  have hi : (r/(2:ℝ)^v)⁻¹ ≤ 2 := by
    rw [inv_div,div_le_iff₀ hp]
    rw [he] at hr
    linarith
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (by positivity) hi j

theorem high_shell_radial_sqrt {a v r : ℝ}
    (hr : r ∈ Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) :
    ‖(((r*(2:ℝ)^(-a))^(1/2:ℝ):ℝ):ℂ)‖ ≤ Real.sqrt (2*(2:ℝ)^(v-a)) := by
  have hp : 0 ≤ r := (Real.rpow_pos_of_pos (by norm_num) _).le.trans hr.1
  have he : (2:ℝ)^(v+1)*(2:ℝ)^(-a) = 2*(2:ℝ)^(v-a) := by
    rw [Real.rpow_add (by norm_num),Real.rpow_one]
    have hh : (2:ℝ)^v*(2:ℝ)^(-a) = (2:ℝ)^(v-a) := by
      rw [← Real.rpow_add (by norm_num)]; rfl
    calc
      _ = 2*((2:ℝ)^v*(2:ℝ)^(-a)) := by ring
      _ = _ := by rw [hh]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_right hr.2 (by positivity)).trans_eq he)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootShellData
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

namespace RootShellData

theorem endpointLeft_measurable (d : RootShellData) (k : RootMaskIndex → ℕ) :
    Measurable (fun z : Plane × UnitCircle => d.endpointLeft k z.1 z.2) :=
  rootLeftSymbol_measurable d.left d.N d.sig k

theorem endpointRight_measurable (d : RootShellData) (k : RootMaskIndex → ℕ) :
    Measurable (fun z : Plane × UnitCircle => d.endpointRight k z.1 z.2) :=
  rootRightSymbol_measurable d.right d.N d.sig k

theorem endpointLeft_norm (d : RootShellData) (hd : 0 < d.left.Q.side) (j : ℕ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j d.indices) (x : Plane) (dir : UnitCircle) :
    ‖d.endpointLeft b.2 x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) :=
  rootLeftSymbol_norm d.left d.right hd d.N j d.sig hb x dir

theorem endpointRight_norm (d : RootShellData) (he : 0 < d.right.Q.side) (j : ℕ)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j d.indices) (x : Plane) (dir : UnitCircle) :
    ‖d.endpointRight b.2 x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) :=
  rootRightSymbol_norm d.left d.right he d.N j d.sig hb x dir

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootShellMixture
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace RootShellData

theorem inversePhasedBound_nonneg (d : RootShellData) (j : ℕ) :
    0 ≤ d.inversePhasedBound j := by
  have hC := zero_le_one.trans (symbolDerivativeConstant_one_le (2*j))
  unfold inversePhasedBound
  positivity

theorem inversePhasedForm_data (d : RootShellData) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (d.indices)) :
    Measurable (fun p : Plane × ℝ => d.inversePhasedForm b.2 p.1 p.2) ∧
      ∀ p : Plane × ℝ, ‖d.inversePhasedForm b.2 p.1 p.2‖ ≤ d.inversePhasedBound j := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  constructor
  · exact spatialPhasedDistanceF_joint_measurable 1 d.left.ρ d.right.ρ d.U.carrier d.V.carrier 1 1
      _ _ _ (measurable_sourceConeCircle _) (d.endpointLeft_measurable b.2)
      (d.endpointRight_measurable b.2) (by norm_num) hC hC
      (sourceConeCircle_norm_le _) (d.endpointLeft_norm hd j hb)
      (d.endpointRight_norm he j hb)
  · intro p
    apply sourceDistanceF_norm_le d.left.ρ d.right.ρ d.U.carrier d.V.carrier
      (show (0:ℝ) < 1 by norm_num)
      (show (0:ℝ) < 1 by norm_num)
      _ _ _ (by norm_num) hC hC (sourceConeCircle_norm_le _)
    · intro x hx ω
      rw [spatialPhasedSymbol_norm]
      exact d.endpointLeft_norm hd j hb x ω
    · intro y hy ω
      rw [spatialPhasedSymbol_norm]
      exact d.endpointRight_norm he j hb y ω

theorem inverseSpatialMixture_data (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (d.indices))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable (d.inverseSpatialMixture δ L hδ hL j b.2) ∧
    (∀ r, ‖d.inverseSpatialMixture δ L hδ hL j b.2 r‖ ≤
      spatialFourierCost δ L hδ hL j*d.inversePhasedBound j) ∧
    Integrable (fun r => ‖d.inverseSpatialMixture δ L hδ hL j b.2 r‖^2) μ := by
  have hd := d.inversePhasedForm_data hd he j hb
  exact continuous_shell_mixture_bound μ _
    (spatialFourierCoeff δ L hδ hL j).continuous.measurable
    (spatialFourierCoeff_integrable _ _ _ _ _) _ hd.1 (d.inversePhasedBound_nonneg j) hd.2

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootShellOrder
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace RootShellData

theorem inverseOrderForm_data (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) :
    Measurable (d.inverseOrderForm δ L hδ hL j) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖d.inverseOrderForm δ L hδ hL j r‖ ≤ C := by
  apply list_sum_measurable_bounded
  intro b hb
  have hmdata := d.inverseSpatialMixture_data δ L hδ hL hd he j hb (Measure.dirac (0:ℝ))
  refine ⟨hmdata.1.const_mul _,
    ‖d.coefficient j b‖*
      (spatialFourierCost δ L hδ hL j*d.inversePhasedBound j),?_,?_⟩
  · exact mul_nonneg (norm_nonneg _) (mul_nonneg (spatialFourierCost_nonneg ..) (d.inversePhasedBound_nonneg j))
  · intro r
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hmdata.2.1 r) (norm_nonneg _)

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootShellMain
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace RootShellData

theorem mainF_shell_oai (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
    (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
    (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2)
    (hcarry₁ : ∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) (hcarry₂ : ∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier)
    (hsep : ∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) (n : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (d.indices), ∀ ξ,
      (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.inversePhasedForm b.2 ξ r‖^2) ≤ B) :
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.mainF n r‖^2) ≤
      2*(2:ℝ)^((d.N:ℝ)) *
        (∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j)^2*B := by
  let μ := volume.restrict (Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)))
  let u := fun j (r : ℝ) => ((((r/(2:ℝ)^(d.N:ℝ))⁻¹)^j:ℝ):ℂ)
  let F := fun j r => u j r*d.inverseOrderForm δ L hδ hL j r
  let w := fun j => d.cost δ L hδ hL j
  have hu (j : ℕ) : Measurable (u j) := by dsimp [u]; fun_prop
  have huw (j : ℕ) : ∀ᵐ r ∂μ, ‖u j r‖ ≤ (2:ℝ)^j := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact high_shell_radial_inverse hr.1 j
  have hwn (j : ℕ) : 0 ≤ w j := by
    apply mul_nonneg (spatialFourierCost_nonneg ..)
    apply mul_nonneg _ (by positivity)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    positivity
  have hm (j : ℕ) : Measurable (F j) := (hu j).mul (d.inverseOrderForm_data δ L hδ hL hd he j).1
  have hi (j : ℕ) : Integrable (fun r => ‖F j r‖^2) μ := by
    obtain ⟨hm,C,hC,hCb⟩ := d.inverseOrderForm_data δ L hδ hL hd he j
    exact (shell_multiplier_square μ (u j) _ (hu j) hm
      (integrable_norm_square_bounded μ _ hm hC (Eventually.of_forall hCb))
      (by positivity) (huw j)).1
  have hE (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∫ r, ‖F j r‖^2 ∂μ) ≤ (w j)^2*B := by
    obtain ⟨hm,C,hC,hCb⟩ := d.inverseOrderForm_data δ L hδ hL hd he j
    have hmul := (shell_multiplier_square μ (u j) _ (hu j) hm
      (integrable_norm_square_bounded μ _ hm hC (Eventually.of_forall hCb))
      (by positivity) (huw j)).2
    apply hmul.trans
    apply (mul_le_mul_of_nonneg_left
      (d.inverseOrderForm_shell δ L hδ hL hd he hsig hL₁ hL₂ j μ hB0 (hB j hj))
      (sq_nonneg ((2:ℝ)^j))).trans_eq
    dsimp [w,cost,rootSpatialLeibnizCost,indices]
    ring
  let G := fun r => ∑ j ∈ Finset.range (n+1), F j r
  have hGm : Measurable G := Finset.measurable_sum _ (fun j _ => hm j)
  have hGi : Integrable (fun r => ‖G r‖^2) μ :=
    finite_sum_square_integrable _ μ F (fun j _ => hm j) (fun j _ => hi j)
  have hGE := finite_weighted_shell_square (Finset.range (n+1)) μ F w
    (fun j _ => hwn j) (fun j _ => hi j) (fun j _ => (hm j).aestronglyMeasurable) hE
  let p := fun r : ℝ => (((r)^(1/2:ℝ):ℝ):ℂ)
  have hpm : Measurable p := by dsimp [p]; fun_prop
  have hp : ∀ᵐ r ∂μ, ‖p r‖ ≤ Real.sqrt (2*(2:ℝ)^((d.N:ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    simpa only [sub_zero,neg_zero,Real.rpow_zero,mul_one] using (high_shell_radial_sqrt (a := 0) hr)
  have hE' := (shell_multiplier_square μ p G hpm hGm hGi (Real.sqrt_nonneg _) hp).2
  rw [Real.sq_sqrt (by positivity)] at hE'
  have he (r : ℝ) : d.mainF n r = p r*G r :=
    by
      simpa only [p,G,F,u,mainF,indices,coefficient,endpointLeft,endpointRight,inverseOrderForm,
        inverseSpatialMixture,inversePhasedForm] using
        rootNormalizedF_finite_separation δ L hδ hL d.left d.right d.N d.sig hd he d.U d.V
          hcarry₁ hcarry₂ hsep n r
  simp_rw [he]
  exact hE'.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hGE
      (show 0 ≤ 2*(2:ℝ)^((d.N:ℝ)) by positivity))

end RootShellData

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.RootShellData.mainF_shell_oai := @OAI.PlanarFalconer.RootShellData.mainF_shell_oai
