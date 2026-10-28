-- Prove2me | solution 1 for OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_high_shell
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:05:48.781644+00:00
-- url     : https://prove2.me/submissions/b85426d0-4c7e-49e5-9843-936def594259

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_high_shell_parent_bound
import Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_prefix_inverse_supremum

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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
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

theorem measurable_sourceDistanceF (ψ : UnitCircle → ℂ)
    (U V : ℝ × UnitCircle → ℂ) (hψ : Measurable ψ)
    (hU : Measurable U) (hV : Measurable V) :
    Measurable (sourceDistanceF ψ U V) := by
  exact (((hψ.comp measurable_snd).mul hU).mul
    (Complex.continuous_conj.measurable.comp hV)).stronglyMeasurable.integral_prod_right'.measurable

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

theorem sourceDistanceHF_eq_ofReal (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (ψ : UnitCircle → ℂ) (U V : ℝ × UnitCircle → ℂ)
    (hF : Measurable (sourceDistanceF ψ U V)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ r ∂sourceAngularShellMeasure v Ψ, ‖sourceDistanceF ψ U V r‖ ≤ B) :
    sourceDistanceHF a v Ψ ψ U V =
      ENNReal.ofReal (sourceRadialSquareEnergy a v Ψ (sourceDistanceF ψ U V)) := by
  have hi := integrable_norm_square_bounded (sourceAngularShellMeasure v Ψ) _ hF hB hb
  have he : (∫⁻ r, ‖sourceDistanceF ψ U V r‖ₑ^2 ∂sourceAngularShellMeasure v Ψ) =
      ENNReal.ofReal (∫ r, ‖sourceDistanceF ψ U V r‖^2 ∂sourceAngularShellMeasure v Ψ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun r => sq_nonneg _))]
    apply lintegral_congr
    intro r
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [sourceDistanceHF, he, ← ENNReal.ofReal_mul (by positivity)]
  rfl

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

end PositiveDistanceData

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

theorem spatialFourierPhase_norm (s : ℝ) (ξ x : Plane) :
    ‖spatialFourierPhase s ξ x‖ = 1 := by
  simp [spatialFourierPhase, Complex.norm_exp, Complex.mul_re]

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_ParentRetainedEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceParentDistanceF_measurable (X Y : DyadicSquare) (ρ ν : Measure Plane)
    [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) :
    Measurable (sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂) :=
  measurable_sourceDistanceF _ _ _ (measurable_sourceConeCircle _)
    (measurable_sourceAngularTransform ρ _ _ b₁ h₁)
    (measurable_sourceAngularTransform ν _ _ b₂ h₂)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem pair_assignment_endpoint_budget (S : Finset PolicyDescriptor) (k : PairMaskIndex → ℕ)
    (K : ℕ) (hk : ∑ a ∈ pairMaskIndices S, k a ≤ K) (l : Fin 2) :
    ∑ b ∈ S, k (b,l) ≤ K := by
  apply le_trans _ hk
  change (∑ b ∈ S, k (b,l)) ≤ ∑ a ∈ S.product (Finset.univ : Finset (Fin 2)), k a
  rw [Finset.product_eq_sprod,Finset.sum_product S (Finset.univ : Finset (Fin 2)) k]
  apply Finset.sum_le_sum
  intro b hb
  exact Finset.single_le_sum (f := fun y : Fin 2 => k (b,y)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellEndpointTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ComplexConjugate
namespace PositiveDistanceData

 theorem inverseEndpointSymbol_measurable (d : PositiveDistanceData) (k : PairMaskIndex → ℕ)
    (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => d.inverseEndpointSymbol k l z.1 z.2) :=
  measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ measurable_const

 theorem inverseEndpointSymbol_norm (d : PositiveDistanceData) (hQ : 0 < d.Q.side) (j : ℕ)
    {b : ℂ × (PairMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (l : Fin 2) (x : Plane) (dir : UnitCircle) :
    ‖d.inverseEndpointSymbol b.2 l x dir‖ ≤ symbolDerivativeConstant (2*j)^(2*j) := by
  exact inheritedCircleSymbol_norm_le _ _ _ _ hQ _ _ _ _ _ _ _ _ (2*j)
    (pair_assignment_endpoint_budget _ _ _ (inverseLeibnizTerms_budget j _ hb) l) x (by simp) dir

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentHFBridge
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceParentHF_finite_eq (a v : ℝ) (Ψ : ℝ → ℝ) (X Y : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b₁ b₂ : Plane → UnitCircle → ℂ)
    (h₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (h₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2))
    {B₁ B₂ W : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hW : 0 ≤ W)
    (hb₁ : ∀ x dir, ‖b₁ x dir‖ ≤ B₁) (hb₂ : ∀ y dir, ‖b₂ y dir‖ ≤ B₂)
    (hΨW : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceParentHF a v Ψ X Y ρ ν M₁ M₂ b₁ b₂ ≠ ⊤ ∧
      (sourceParentHF a v Ψ X Y ρ ν M₁ M₂ b₁ b₂).toReal =
        sourceRadialSquareEnergy a v Ψ (sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂) := by
  let := sourceAngularShellMeasure_finite v Ψ hW hΨW hs
  have hh := sourceDistanceHF_eq_ofReal a v Ψ (sourceConeCircle (sourceParentAxis X Y)) _ _
    (sourceParentDistanceF_measurable X Y ρ ν M₁ M₂ b₁ b₂ h₁ h₂)
    (show 0 ≤ (1*B₁*B₂*sourceArcLength.real univ)*((ρ X.carrier).toReal/M₁)*((ν Y.carrier).toReal/M₂) by positivity)
    (Filter.Eventually.of_forall (sourceDistanceF_norm_le ρ ν X.carrier Y.carrier hM₁ hM₂
      _ b₁ b₂ (by norm_num) hB₁ hB₂ (sourceConeCircle_norm_le _) (fun x _ => hb₁ x) (fun y _ => hb₂ y)))
  change sourceParentHF a v Ψ X Y ρ ν M₁ M₂ b₁ b₂ =
    ENNReal.ofReal (sourceRadialSquareEnergy a v Ψ (sourceParentDistanceF X Y ρ ν M₁ M₂ b₁ b₂)) at hh
  rw [hh]
  refine ⟨ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ?_⟩
  unfold sourceRadialSquareEnergy
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (integral_nonneg (fun _ => sq_nonneg _))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellMixture
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem inversePhasedBound_nonneg (d : PositiveDistanceData) (j : ℕ) :
    0 ≤ d.inversePhasedBound j := by
  have hC := zero_le_one.trans (symbolDerivativeConstant_one_le (2*j))
  unfold inversePhasedBound levelMass
  positivity

theorem inversePhasedForm_data (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)) :
    Measurable (fun p : Plane × ℝ => d.inversePhasedForm b.2 p.1 p.2) ∧
      ∀ p : Plane × ℝ, ‖d.inversePhasedForm b.2 p.1 p.2‖ ≤ d.inversePhasedBound j := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  constructor
  · exact spatialPhasedDistanceF_joint_measurable _ d.ρ d.ρ _ _ d.levelMass d.levelMass
      _ _ _ (measurable_sourceConeCircle _) (d.inverseEndpointSymbol_measurable b.2 0)
      (d.inverseEndpointSymbol_measurable b.2 1) (by norm_num) hC hC
      (sourceConeCircle_norm_le _) (d.inverseEndpointSymbol_norm hQ j hb 0)
      (d.inverseEndpointSymbol_norm hQ j hb 1)
  · intro p
    apply sourceDistanceF_norm_le d.ρ d.ρ _ _
      (show 0 < d.levelMass by unfold levelMass; positivity)
      (show 0 < d.levelMass by unfold levelMass; positivity)
      _ _ _ (by norm_num) hC hC (sourceConeCircle_norm_le _)
    · intro x hx ω
      rw [spatialPhasedSymbol_norm]
      exact d.inverseEndpointSymbol_norm hQ j hb 0 x ω
    · intro y hy ω
      rw [spatialPhasedSymbol_norm]
      exact d.inverseEndpointSymbol_norm hQ j hb 1 y ω

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellParentEnergy
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

theorem inversePhasedHF_finite_eq (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList))
    (v : ℝ) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hΨW : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) (ξ : Plane) :
    d.inversePhasedHF v Ψ b.2 ξ ≠ ⊤ ∧
      (d.inversePhasedHF v Ψ b.2 ξ).toReal =
        sourceRadialSquareEnergy d.a v Ψ (d.inversePhasedForm b.2 ξ) := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  apply sourceParentHF_finite_eq _ _ _ _ _ d.ρ d.ρ
    (show 0 < d.levelMass by unfold levelMass; positivity)
    (show 0 < d.levelMass by unfold levelMass; positivity) _ _
    (spatialPhasedSymbol_measurable _ _ _ (d.inverseEndpointSymbol_measurable b.2 0))
    (spatialPhasedSymbol_measurable _ _ _ (d.inverseEndpointSymbol_measurable b.2 1)) hC hC hW
    _ _ hΨW hs
  · intro x dir
    rw [spatialPhasedSymbol_norm]
    exact d.inverseEndpointSymbol_norm hQ j hb 0 x dir
  · intro x dir
    rw [spatialPhasedSymbol_norm]
    exact d.inverseEndpointSymbol_norm hQ j hb 1 x dir

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellSupremum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem inverseShellEnergies_bddAbove (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (n : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hs : ∀ x, 4 < x → Ψ x = 0) : BddAbove (d.inverseShellEnergies n v Ψ) := by
  let μ := sourceAngularShellMeasure v Ψ
  let : IsFiniteMeasure μ := sourceAngularShellMeasure_finite v Ψ hW hΨW hs
  let E : ℝ := (2:ℝ)^(2*(v-d.a))
  let C := ∑ j ∈ Finset.range (n+1), (d.inversePhasedBound j)^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨E*μ.real univ*C,?_⟩
  intro x hx
  rcases hx with rfl | ⟨j,hj,b,hb,ξ,rfl⟩
  · exact mul_nonneg (mul_nonneg (by dsimp [E]; positivity) measureReal_nonneg) hC
  · rw [(d.inversePhasedHF_finite_eq hQ j hb v Ψ hW hΨW hs ξ).2]
    have hd := d.inversePhasedForm_data hQ j hb
    have hm : Measurable (d.inversePhasedForm b.2 ξ) :=
      hd.1.comp (f := fun r : ℝ => (ξ,r)) (measurable_const.prodMk measurable_id)
    have hi := integrable_norm_square_bounded μ _ hm (d.inversePhasedBound_nonneg j)
      (Filter.Eventually.of_forall (fun r => hd.2 (ξ,r)))
    have hbnd := integral_mono hi (integrable_const ((d.inversePhasedBound j)^2))
      (fun r => pow_le_pow_left₀ (norm_nonneg _) (hd.2 (ξ,r)) 2)
    rw [integral_const,smul_eq_mul] at hbnd
    have hjC : (d.inversePhasedBound j)^2 ≤ C :=
      Finset.single_le_sum (fun i _ => sq_nonneg (d.inversePhasedBound i)) hj
    change E*(∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ _
    calc
      _ ≤ E*(μ.real univ*(d.inversePhasedBound j)^2) :=
        mul_le_mul_of_nonneg_left hbnd (by dsimp [E]; positivity)
      _ ≤ E*(μ.real univ*C) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hjC measureReal_nonneg) (by dsimp [E]; positivity)
      _ = _ := by ring

theorem inverseShellSupremum_majorizes (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (n : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hs : ∀ x, 4 < x → Ψ x = 0) :
    0 ≤ d.inverseShellSupremum n v Ψ ∧
    ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
        (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ d.inverseShellSupremum n v Ψ := by
  have hb := d.inverseShellEnergies_bddAbove hQ n v Ψ hW hΨW hs
  refine ⟨le_csSup hb (Or.inl rfl),?_⟩
  intro j hj b hb' ξ
  exact le_csSup hb (Or.inr ⟨j,hj,b,hb',ξ,rfl⟩)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ActualHighShellEquation21
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem uniform_high_shell_equation21 {sig lam eps T : ℝ}
    (hsig : 0 < sig) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, ∀ (B : ℕ) (δ : ℝ),
    RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    N₀ ≤ d.N → d.sig = sig → d.lam = lam →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    d.X.length = d.a → d.Y.length = d.a →
    ∀ v : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → v ≤ d.t →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) →
    (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖charFun d.weightedDistance r‖^2) ≤
        ((2:ℝ)^d.N)^eps*d.inverseShellSupremum n v Ψ+((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_high_shell_parent_bound (lam := lam) (T := T) hsig heps
  refine ⟨n,N₀,?_⟩
  intro d B δ hd hN hdSig hdLam hQ hsep hq hqs hw ht hX hY v hv hvt Ψ hΨ hpos hs W hW hΨW hone
  let := hd.probability
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup := d.inverseShellSupremum_majorizes hQ n v Ψ hW hΨW hsupport
  exact h₀ d B δ hd hN hdSig hdLam hQ hsep hq hqs hw ht hX hY v hv hvt
    Ψ hΨ hpos hs W hW hΨW hone _ hsup.1 hsup.2

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_PrefixHighShell
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem prefix_shell_power_absorption {R eta E T C H : ℝ}
    (hR : 2 ≤ R) (heta : 0 < eta) (hC : C ≤ R^eta) (hH : 0 ≤ H) :
    R^eta*(C*R^(E+eta)*H+R^(-(T+eta+1)))+R^(-(T+eta+1)) ≤
      R^(E+3*eta)*H+R^(-T) := by
  have hRp : 0 < R := by linarith
  have hp : 1 ≤ R^eta := Real.one_le_rpow (by linarith) heta.le
  have herr : R^eta*R^(-(T+eta+1))+R^(-(T+eta+1)) ≤ R^(-T) := by
    have hsmall : R^(-(T+eta+1)) ≤ R^eta*R^(-(T+eta+1)) := by nlinarith [Real.rpow_pos_of_pos hRp (-(T+eta+1))]
    have he : R^eta*R^(-(T+eta+1)) = R^(-T)/R := by
      rw [← Real.rpow_add hRp]
      rw [show eta+ -(T+eta+1) = -T-1 by ring,Real.rpow_sub hRp,Real.rpow_one]
    rw [he] at hsmall ⊢
    have hdiv : 2*(R^(-T)/R) ≤ R^(-T) := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hRp).mpr
      nlinarith [Real.rpow_pos_of_pos hRp (-T)]
    linarith
  calc
    _ ≤ R^eta*(R^eta*R^(E+eta)*H+R^(-(T+eta+1)))+R^(-(T+eta+1)) := by gcongr
    _ = R^(E+3*eta)*H+(R^eta*R^(-(T+eta+1))+R^(-(T+eta+1))) := by
      have he : R^eta*(R^eta*R^(E+eta)) = R^(E+3*eta) := by
        rw [← mul_assoc,← Real.rpow_add hRp,← Real.rpow_add hRp]
        congr 1
        ring
      nlinarith [he]
    _ ≤ _ := add_le_add (le_refl _) herr

namespace PositiveDistanceData

theorem uniform_prefix_high_shell_oai {sig kap lam T eps : ℝ}
    (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (heps : 0 < eps) {J : ℕ} (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ K N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    ∀ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-sig*d.N < (v:ℝ) →
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)), ‖charFun d.weightedDistance r‖^2) ≤
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eps) *
        d.prefixSuccessorSupremum K p Ψ + ((2:ℝ)^d.N)^(-T) := by
  let eta := eps/3
  have heta : 0 < eta := by dsimp [eta]; positivity
  let U := T+eta+1
  obtain ⟨n,N₁,h₁⟩ := uniform_high_shell_equation21 (lam := lam) (T := U) hsig heta
  obtain ⟨N₂,h₂⟩ := uniform_prefix_inverse_supremum hsig hgap hlam
    (show 0 ≤ U by dsimp [U]; linarith) heta n hJ hΨ hpos hs
  obtain ⟨N₃,h₃⟩ := fixed_constant_absorbed heta ((symbolDerivativeConstant (2*n)^(2*n))^4)
  refine ⟨2*n,max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro d hdSig hdLam hdJ hN hQ B δ hprof hq hblock hw ht hi hX hY hlo hsep A p hpref v hv hvhigh
  have hN1 : N₁ ≤ d.N := by omega
  have hN2 : N₂ ≤ d.N := by omega
  have hN3 : N₃ ≤ d.N := by omega
  let := hprof.probability
  have hQpos : 0 < d.Q.side := by rw [hQ]; norm_num
  have hsep' := d.stronglySeparated_of_unit hQ hX hY hlo hsep
  have hqs : d.sig*d.N ≤ (d.q:ℝ) := by
    rw [hdSig]
    exact (mul_le_mul_of_nonneg_right (by linarith : sig ≤ kap) (Nat.cast_nonneg _)).trans hblock
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hvt : (v:ℝ) ≤ d.t := by exact_mod_cast (Finset.mem_Ioc.mp hv).2
  have hlow := h₁ d B δ hprof hN1 hdSig hdLam hQpos hsep' hq hqs hw ht hX hY
    v (by simpa only [hdSig] using hvhigh.le) hvt Ψ hΨ.continuous.measurable hpos hs W hW
    (fun x => (le_abs_self _).trans (hWb x)) hone
  have hhigh := h₂ d hdSig hdLam hdJ hN2 hQ B δ hprof hq hblock hw ht hi hX hY hlo hsep hpref v hv hvhigh
  have hsup0 := (d.prefixSuccessorSupremum_majorizes hQpos (2*n) p Ψ hW
    (fun x => (le_abs_self _).trans (hWb x)) hsupport).1
  have hR : 2 ≤ (2:ℝ)^d.N := by
    calc
      (2:ℝ) = (2:ℝ)^1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have habs := prefix_shell_power_absorption
    (E := -2*(A p-A d.a)+height A d.a p+4000*(lam+sig)) (T := T)
    hR heta (h₃ d.N hN3) hsup0
  have h := hlow.trans ((add_le_add
    (mul_le_mul_of_nonneg_left hhigh (by positivity : 0 ≤ ((2:ℝ)^d.N)^eta)) (le_refl _)).trans habs)
  simpa only [show 3*eta = eps by dsimp [eta]; ring] using h

end PositiveDistanceData

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_high_shell_oai := @OAI.PlanarFalconer.PositiveDistanceData.uniform_prefix_high_shell_oai
