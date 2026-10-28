-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_root_fourier_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:34:02.429006+00:00
-- url     : https://prove2.me/submissions/1df8e423-a306-4ff0-bd2c-f22f1b292786

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_root_weighted_inverse

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

theorem apply_contDiff (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (p.apply f) := by
  induction p generalizing f with
  | term c k => exact contDiff_const.mul (smooth_iteratedDeriv hf k)
  | add p q hp hq => exact (hp hf).add (hq hf)
  | comp p q hp hq => exact hp (hq hf)

theorem iteratedDeriv_iterated (m k : ℕ) (f : ℝ → ℂ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m+k) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology
namespace AngularDifferentialExpr

theorem smooth_finite {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    ContDiffAt ℝ m f x :=
  (hf.of_le (WithTop.coe_le_coe.mpr (show (m:ℕ∞) ≤ ⊤ from le_top))).contDiffAt

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

theorem assignedDerivProduct_contDiff {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℂ) (k : ι → ℕ) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (assignedDerivProduct S f k) :=
  contDiff_prod (fun i hi => AngularDifferentialExpr.smooth_iteratedDeriv (hf i hi) (k i))

theorem assignedDerivProduct_deriv {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℂ) (k : ι → ℕ) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (x : ℝ) :
    deriv (assignedDerivProduct S f k) x =
      ∑ i ∈ S, assignedDerivProduct S f (Function.update k i (k i+1)) x := by
  unfold assignedDerivProduct
  rw [deriv_fun_finsetProd (fun i hi =>
    (AngularDifferentialExpr.smooth_iteratedDeriv (hf i hi) _).differentiable (by simp) |>.differentiableAt)]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (fun j => iteratedDeriv (Function.update k i (k i+1) j) (f j) x) =
      Function.update (fun j => iteratedDeriv (k j) (f j) x) i (iteratedDeriv (k i+1) (f i) x) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [he,Finset.prod_update_of_mem hi]
  simp [iteratedDeriv_succ,smul_eq_mul,mul_comm,Finset.sdiff_singleton_eq_erase]

theorem contDiff_list_sum {α : Type*} (L : List α) (g : α → ℝ → ℂ)
    (hg : ∀ i ∈ L, ContDiff ℝ ∞ (g i)) :
    ContDiff ℝ ∞ (fun x => (L.map (fun i => g i x)).sum) := by
  induction L with
  | nil => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0:ℂ)))
  | cons a L ih =>
    simpa using (hg a (by simp)).add (ih (fun i hi => hg i (by simp [hi])))

theorem deriv_list_sum {α : Type*} (L : List α) (g : α → ℝ → ℂ)
    (hg : ∀ i ∈ L, ContDiff ℝ ∞ (g i)) (x : ℝ) :
    deriv (fun x => (L.map (fun i => g i x)).sum) x =
      (L.map (fun i => deriv (g i) x)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [deriv_fun_add ((hg a (by simp)).differentiable (by simp)).differentiableAt
      ((contDiff_list_sum L g (fun i hi => hg i (by simp [hi]))).differentiable (by simp)).differentiableAt]
    rw [ih (fun i hi => hg i (by simp [hi]))]

theorem iteratedDeriv_ordered_product {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (n : ℕ) :
    iteratedDeriv n (fun x => ∏ i ∈ S, f i x) =
      fun x => ((orderedDerivAssignments S n).map (fun k => assignedDerivProduct S f k x)).sum := by
  induction n with
  | zero => simp [orderedDerivAssignments,assignedDerivProduct]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    rw [deriv_list_sum _ _ (fun k _ => assignedDerivProduct_contDiff S f k hf)]
    simp only [orderedDerivAssignments,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [assignedDerivProduct_deriv S f k hf]
    simp

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

theorem terms_derivative (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (p.apply f) x =
      (p.terms.map (fun a => a.1*iteratedDeriv (n+a.2) f x)).sum := by
  induction p generalizing f n with
  | term c k => simp [terms,apply,iteratedDeriv_const_mul_field,iteratedDeriv_iterated]
  | add p q hp hq =>
    simp only [terms,List.map_append,List.sum_append,apply]
    rw [iteratedDeriv_fun_add (smooth_finite (p.apply_contDiff hf) n x)
      (smooth_finite (q.apply_contDiff hf) n x),hp hf,hq hf]
  | comp p q hp hq =>
    change iteratedDeriv n (p.apply (q.apply f)) x = _
    rw [hp (q.apply_contDiff hf)]
    simp only [terms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    rw [hq hf,← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    simp [Nat.add_assoc,mul_assoc]

theorem terms_apply (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    p.apply f x = (p.terms.map (fun a => a.1*iteratedDeriv a.2 f x)).sum := by
  simpa using p.terms_derivative hf 0 x

end AngularDifferentialExpr

theorem inverseStationaryOperator_terms (j : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    inverseStationaryOperator j f x =
      ((inverseStationaryExpr j).terms.map (fun a => a.1*iteratedDeriv a.2 f x)).sum :=
  (inverseStationaryExpr j).terms_apply hf x

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

theorem distance_integrand_norm_le (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) {P B₁ B₂ : ℝ}
    (hP : 0 ≤ P) (hB₁ : 0 ≤ B₁) (_ : 0 ≤ B₂)
    (hp : ∀ ω, ‖ψ ω‖ ≤ P) (hb₁ : ∀ x ω, ‖b₁ x ω‖ ≤ B₁)
    (hb₂ : ∀ y ω, ‖b₂ y ω‖ ≤ B₂) (r : ℝ) (ω : UnitCircle) (x y : Plane) :
    ‖sourcePlaneWave r ω (x-y) * (ψ ω * b₁ x ω * conj (b₂ y ω))‖ ≤ P*B₁*B₂ := by
  simp only [norm_mul, sourcePlaneWave_norm, Complex.norm_conj, one_mul]
  exact mul_le_mul (mul_le_mul (hp ω) (hb₁ x ω) (norm_nonneg _) hP)
    (hb₂ y ω) (norm_nonneg _) (mul_nonneg hP hB₁)

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

theorem inverseLeibnizTerms_expansion {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (x : ℝ) :
    inverseStationaryOperator j (fun x => ∏ i ∈ S, f i x) x =
      ((inverseLeibnizTerms j S).map (fun a => a.1*assignedDerivProduct S f a.2 x)).sum := by
  rw [inverseStationaryOperator_terms j (contDiff_prod hf)]
  simp only [inverseLeibnizTerms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [iteratedDeriv_ordered_product S f hf a.2]
  exact (List.sum_map_mul_left _ _ _).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootEndpointData
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

namespace RootEndpointData

theorem mask_bounds (d : RootEndpointData) (hQ : 0 < d.Q.side)
    (N : ℕ) (sig : ℝ) (x : Plane) (dir : UnitCircle) :
    0 ≤ d.mask N sig x dir ∧ d.mask N sig x dir ≤ 1 :=
  descriptorListMask_bounds _ hQ _ _ _ _ _ _ _ _ _ _

theorem mask_measurable (d : RootEndpointData) (N : ℕ) (sig : ℝ) :
    Measurable (fun z : Plane × UnitCircle => d.mask N sig z.1 z.2) :=
  measurable_descriptorListMask _ _ _ _ _ _ _ _ _

end RootEndpointData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootPairSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem rootPairMask_measurable (d e : RootEndpointData) (N : ℕ) (sig : ℝ) :
    Measurable (rootPairMask d e N sig) := by
  have h₁ := (d.mask_measurable N sig).comp
    (f := fun z : Plane × Plane => (z.1,sourceRadialUnit z.2 z.1))
    (measurable_fst.prodMk measurable_pairRadialUnit)
  have h₂ := (e.mask_measurable N sig).comp
    (f := fun z : Plane × Plane => (z.2,sourceRadialUnit z.2 z.1))
    (measurable_snd.prodMk measurable_pairRadialUnit)
  exact h₁.mul h₂

theorem rootPairMask_bounds (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) (z : Plane × Plane) :
    0 ≤ rootPairMask d e N sig z ∧ rootPairMask d e N sig z ≤ 1 := by
  have h₁ := d.mask_bounds hd N sig z.1 (sourceRadialUnit z.2 z.1)
  have h₂ := e.mask_bounds he N sig z.2 (sourceRadialUnit z.2 z.1)
  exact ⟨mul_nonneg h₁.1 h₂.1,(mul_le_of_le_one_left h₂.1 h₁.2).trans h₂.2⟩

theorem rootSpatialWeight_measurable (d e : RootEndpointData) (N : ℕ) (sig : ℝ) :
    Measurable (rootSpatialWeight d e N sig) :=
  ((continuous_fst.dist continuous_snd).measurable.pow_const _).mul (rootPairMask_measurable d e N sig)

theorem rootSpatialWeight_nonneg (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) (z : Plane × Plane) : 0 ≤ rootSpatialWeight d e N sig z :=
  mul_nonneg (Real.rpow_nonneg dist_nonneg _) (rootPairMask_bounds d e hd he N sig z).1

theorem rootSpatialWeight_le (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) {δ : ℝ} (hδ : 0 < δ) {z : Plane × Plane} (hz : δ ≤ dist z.1 z.2) :
    rootSpatialWeight d e N sig z ≤ δ^(-(1/2:ℝ)) := by
  apply (mul_le_of_le_one_right (Real.rpow_nonneg dist_nonneg _)
    (rootPairMask_bounds d e hd he N sig z).2).trans
  exact Real.rpow_le_rpow_of_nonpos hδ hz (by norm_num)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem high_shell_inverse_power_split (a v r d : ℝ) (j : ℕ) :
    ((r*d)⁻¹)^j = ((2:ℝ)^(-(j:ℝ)*(v-a))) *
      ((r/(2:ℝ)^v)⁻¹)^j * ((d/(2:ℝ)^(-a))⁻¹)^j := by
  have hp : (2:ℝ)^(v-a) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have he : (2:ℝ)^(-(j:ℝ)*(v-a)) = (((2:ℝ)^(v-a))⁻¹)^j := by
    rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [he,← mul_pow,← mul_pow]
  congr 1
  rw [inv_div,inv_div,mul_inv_rev]
  have he : (2:ℝ)^v*(2:ℝ)^(-a) = (2:ℝ)^(v-a) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; rfl
  symm
  calc
    _ = r⁻¹*d⁻¹*(((2:ℝ)^(v-a))⁻¹*((2:ℝ)^v*(2:ℝ)^(-a))) := by ring
    _ = _ := by rw [he,inv_mul_cancel₀ hp]; ring

theorem high_shell_weight_cancellation {r d s : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hs : 0 < s) :
    (d/s)^(-(1/2:ℝ))*(r*d)^(1/2:ℝ) = (r*s)^(1/2:ℝ) := by
  rw [Real.div_rpow hd.le hs.le, Real.mul_rpow hr.le hd.le,
    Real.mul_rpow hr.le hs.le]
  have he : d^(-(1/2:ℝ))*d^(1/2:ℝ) = 1 := by
    rw [← Real.rpow_add hd]; norm_num
  have hs' : s^(-(1/2:ℝ)) = (s^(1/2:ℝ))⁻¹ := Real.rpow_neg hs.le _
  rw [hs',div_inv_eq_mul]
  calc
    _ = r^(1/2:ℝ)*s^(1/2:ℝ)*(d^(-(1/2:ℝ))*d^(1/2:ℝ)) := by ring
    _ = _ := by rw [he,mul_one]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_NormalizedLeibnizAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem normalizedMaskFactor_extract {w : ℝ → ℝ} {d : ℝ} (hd : d ≠ 0)
    (k : ℕ) (θ : ℝ) :
    (d⁻¹)^k * normalizedMaskFactor w d k θ = iteratedDeriv k w θ := by
  unfold normalizedMaskFactor
  rw [← mul_assoc,← mul_pow,inv_mul_cancel₀ hd,one_pow,one_mul]

theorem assignedDerivProduct_normalized {ι : Type*} (S : Finset ι)
    (w : ι → ℝ → ℝ) (d : ι → ℝ) (k : ι → ℕ)
    (hw : ∀ i ∈ S, ContDiff ℝ ∞ (w i)) (hd : ∀ i ∈ S, d i ≠ 0) (θ : ℝ) :
    assignedDerivProduct S (fun i t => (w i t : ℂ)) k θ =
      ((∏ i ∈ S, (d i)⁻¹^(k i) : ℝ):ℂ) *
        ((∏ i ∈ S, normalizedMaskFactor (w i) (d i) (k i) θ : ℝ):ℂ) := by
  simp only [assignedDerivProduct,← Complex.ofReal_mul,← Finset.prod_mul_distrib,Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalizedMaskFactor_extract (hd i hi),iteratedDeriv_ofReal (hw i hi)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootLeibniz
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem rootAngleFactor_contDiff (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) (z : Plane × Plane) (b : RootMaskIndex) :
    ContDiff ℝ ∞ (rootAngleFactor d e N sig z b) := by
  cases b with
  | inl b => exact descriptorAngleMask_contDiff _ hd _ _ _ _ _ _ _ _ _
  | inr b => exact descriptorAngleMask_contDiff _ he _ _ _ _ _ _ _ _ _

theorem rootPairSymbol_product (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (θ : ℝ) :
    rootPairSymbol d e N sig z (sourceUnitDirection θ) =
      ∏ b ∈ rootMaskIndices d e, (rootAngleFactor d e N sig z b θ : ℂ) := by
  simp [rootPairSymbol,RootEndpointData.mask,descriptorListMask,rootMaskIndices,
    Finset.prod_disjSum,rootAngleFactor,descriptorAngleMask,Complex.ofReal_prod]

theorem root_assignment_normalized (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (k : RootMaskIndex → ℕ) (z : Plane × Plane) (θ : ℝ) :
    assignedDerivProduct (rootMaskIndices d e) (fun b t => (rootAngleFactor d e N sig z b t : ℂ)) k θ =
      (rootAssignmentScale d e N sig k : ℂ) *
        (d.symbol N sig (fun b => k (.inl b)) (fun _ => 1) z.1 (sourceUnitDirection θ) *
          conj (e.symbol N sig (fun b => k (.inr b)) (fun _ => 1) z.2 (sourceUnitDirection θ))) := by
  rw [assignedDerivProduct_normalized _ _ _ k
    (fun b _ => rootAngleFactor_contDiff d e hd he N sig z b)
    (fun b _ => (sourceAngularRadius_pos N sig (descriptorLength (rootMaskDescriptor b))).ne') θ]
  congr 1
  simp only [RootEndpointData.symbol,inheritedCircleSymbol_comp,one_mul,Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  congr 1
  simp [rootMaskIndices,Finset.prod_disjSum,rootAngleFactor,rootMaskDescriptor,inheritedMaskProduct]

theorem rootPairSymbol_inverse_leibniz (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (j : ℕ) (θ : ℝ) :
    inverseStationaryOperator j (fun t => rootPairSymbol d e N sig z (sourceUnitDirection t)) θ =
      ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun a =>
        a.1 * ((rootAssignmentScale d e N sig a.2 : ℂ) *
          (d.symbol N sig (fun b => a.2 (.inl b)) (fun _ => 1) z.1 (sourceUnitDirection θ) *
            conj (e.symbol N sig (fun b => a.2 (.inr b)) (fun _ => 1) z.2 (sourceUnitDirection θ)))))).sum := by
  simp_rw [rootPairSymbol_product]
  rw [inverseLeibnizTerms_expansion j (rootMaskIndices d e)
    (fun b t => (rootAngleFactor d e N sig z b t : ℂ))
    (fun b _ => Complex.ofRealCLM.contDiff.comp (rootAngleFactor_contDiff d e hd he N sig z b))]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [root_assignment_normalized d e hd he N sig a.2 z θ]

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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootWeightedDistance
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal

theorem integral_rootWeightedDistance (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (F : ℝ → ℂ) (hF : AEStronglyMeasurable F (rootWeightedDistance d e N sig)) :
    (∫ t, F t ∂rootWeightedDistance d e N sig) =
      ∫ z, rootSpatialWeight d e N sig z • F (dist z.1 z.2) ∂d.ρ.prod e.ρ := by
  rw [rootWeightedDistance,integral_map (by fun_prop) hF,rootWeightedPair]
  calc
    _ = ∫ z, (ENNReal.ofReal (rootSpatialWeight d e N sig z)).toReal • F (dist z.1 z.2) ∂d.ρ.prod e.ρ :=
      integral_withDensity_eq_integral_toReal_smul
        (rootSpatialWeight_measurable d e N sig).ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [ENNReal.toReal_ofReal (rootSpatialWeight_nonneg d e hd he N sig z)]

theorem rootWeightedDistance_fourier (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig r : ℝ) :
    charFun (rootWeightedDistance d e N sig) r =
      ∫ z, (rootSpatialWeight d e N sig z : ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ))
        ∂d.ρ.prod e.ρ := by
  rw [charFun_apply_real,integral_rootWeightedDistance d e hd he N sig _ (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Complex.real_smul,Complex.ofReal_mul]
  ring_nf

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

theorem root_inverseCircleOperator_terms (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (j : ℕ) (dir : UnitCircle) :
    inverseCircleOperator j (rootPairSymbol d e N sig z) dir =
      ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
        b.1 * ((rootAssignmentScale d e N sig b.2:ℂ) *
          (rootLeftSymbol d N sig b.2 z.1 dir * conj (rootRightSymbol e N sig b.2 z.2 dir))))).sum := by
  simpa only [inverseCircleOperator,sourceUnitDirection_sourceAngle,rootLeftSymbol,rootRightSymbol] using
    rootPairSymbol_inverse_leibniz d e hd he N sig z j (sourceAngle dir)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootKernelTerms
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

 theorem root_inverse_angular_kernel_terms (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (j : ℕ) (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (r : ℝ) (z : Plane × Plane) :
    (∫ dir, sourcePlaneWave r dir (z.1-z.2) *
      (ψ dir * inverseCircleOperator j (rootPairSymbol d e N sig z) dir) ∂sourceArcLength) =
      ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
        b.1 * ((rootAssignmentScale d e N sig b.2:ℂ) *
          sourceDistanceKernel ψ (rootLeftSymbol d N sig b.2)
            (rootRightSymbol e N sig b.2) r z.1 z.2))).sum := by
  let L := inverseLeibnizTerms j (rootMaskIndices d e)
  let f := fun (b : ℂ × (RootMaskIndex → ℕ)) (dir : UnitCircle) =>
    b.1 * ((rootAssignmentScale d e N sig b.2:ℂ) *
      (sourcePlaneWave r dir (z.1-z.2) * (ψ dir * rootLeftSymbol d N sig b.2 z.1 dir *
        conj (rootRightSymbol e N sig b.2 z.2 dir))))
  have heq (dir : UnitCircle) : sourcePlaneWave r dir (z.1-z.2) *
      (ψ dir * inverseCircleOperator j (rootPairSymbol d e N sig z) dir) = (L.map (fun b => f b dir)).sum := by
    rw [root_inverseCircleOperator_terms d e hd he N sig]
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    dsimp [f]
    ring
  have hi : ∀ b ∈ L, Integrable (f b) sourceArcLength := by
    intro b hb
    have hm₁ : Measurable (fun dir => rootLeftSymbol d N sig b.2 z.1 dir) :=
      (rootLeftSymbol_measurable d N sig b.2).comp
        (f := fun dir : UnitCircle => (z.1,dir)) (measurable_const.prodMk measurable_id)
    have hm₂ : Measurable (fun dir => rootRightSymbol e N sig b.2 z.2 dir) :=
      (rootRightSymbol_measurable e N sig b.2).comp
        (f := fun dir : UnitCircle => (z.2,dir)) (measurable_const.prodMk measurable_id)
    apply Integrable.const_mul
    apply Integrable.const_mul
    refine Integrable.of_bound ?_
      (P*(symbolDerivativeConstant (2*j)^(2*j))*(symbolDerivativeConstant (2*j)^(2*j))) ?_
    · apply Measurable.aestronglyMeasurable
      apply Measurable.mul
      · unfold sourcePlaneWave; fun_prop
      · exact (hψ.mul hm₁).mul (Complex.continuous_conj.measurable.comp hm₂)
    · filter_upwards with dir
      exact distance_integrand_norm_le ψ _ _ hP
        (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)
        (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _) hp
        (rootLeftSymbol_norm d e hd N j sig hb) (rootRightSymbol_norm d e he N j sig hb) r dir z.1 z.2
  simp_rw [heq]
  rw [integral_list_sum sourceArcLength L f hi]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  simp only [f, integral_const_mul, sourceDistanceKernel]

 theorem root_inverseCircleIntegral_kernel_terms (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (n : ℕ) (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) (r : ℝ) (z : Plane × Plane) :
    sourceInverseCircleIntegral n r (z.1-z.2) ψ (rootPairSymbol d e N sig z) =
      (((r*dist z.1 z.2)^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        (((r*dist z.1 z.2)⁻¹:ℝ):ℂ)^j *
          ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b =>
            b.1 * ((rootAssignmentScale d e N sig b.2:ℂ) *
              sourceDistanceKernel ψ (rootLeftSymbol d N sig b.2)
                (rootRightSymbol e N sig b.2) r z.1 z.2))).sum := by
  unfold sourceInverseCircleIntegral
  simp only [← dist_eq_norm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact root_inverse_angular_kernel_terms d e hd he N sig j ψ hψ hP hp r z

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootNormalizedKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

 theorem root_weightedInverseCircle_normalized (d e : RootEndpointData)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) {z : Plane × Plane} (hz : 0 < dist z.1 z.2)
    (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) {P : ℝ} (hP : 0 ≤ P)
    (hp : ∀ dir, ‖ψ dir‖ ≤ P) :
    (((dist z.1 z.2/(2:ℝ)^(-(0:ℝ)))^(-(1/2:ℝ)):ℝ):ℂ) *
      sourceInverseCircleIntegral n r (z.1-z.2) ψ (rootPairSymbol d e N sig z) =
      rootNormalizedKernel d e N sig n r ψ z := by
  rw [root_inverseCircleIntegral_kernel_terms d e hd he N sig n ψ hψ hP hp r z,
    ← mul_assoc, ← Complex.ofReal_mul,
    high_shell_weight_cancellation hr hz (by positivity)]
  unfold rootNormalizedKernel
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.ofReal_pow, high_shell_inverse_power_split]
  simp only [Complex.ofReal_mul, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  simp only [rootAbsorbedCoefficient, Complex.ofReal_mul]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_NormalizedHighShellError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

 theorem measurable_list_sum {α ι : Type*} [MeasurableSpace α] (L : List ι)
    (f : ι → α → ℂ) (hf : ∀ i ∈ L, Measurable (f i)) :
    Measurable (fun x => (L.map (fun i => f i x)).sum) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hf i (by simp)).add (ih (fun a ha => hf a (by simp [ha])))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_RootNormalizedError
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem rootNormalizedKernel_measurable (d e : RootEndpointData) (N : ℕ) (sig : ℝ) (n : ℕ)
    (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × (Plane × Plane) => rootNormalizedKernel d e N sig n p.1 ψ p.2) := by
  unfold rootNormalizedKernel
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_sum
    intro j _hj
    apply Measurable.mul
    · fun_prop
    · apply measurable_list_sum
      intro b _hb
      apply Measurable.const_mul
      apply Measurable.mul
      · fun_prop
      · exact measurable_sourceDistanceKernel ψ _ _ hψ
          (rootLeftSymbol_measurable d N sig b.2) (rootRightSymbol_measurable e N sig b.2)

theorem uniform_root_normalized_error {sig δ T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
    (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
    ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
    ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
    ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
    ∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y →
    ‖(rootSpatialWeight d e N sig (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)) (x,y)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_root_weighted_inverse (T := T) hsig hsmall hδ
  refine ⟨n,N₀,?_⟩
  intro N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hb := h₀ N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hrp : 0 < r := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hr
  have hdist : 0 < dist x y := hδ.trans_le hxy
  have heq := root_weightedInverseCircle_normalized d e hd he N sig n (r := r) hrp (z := (x,y)) hdist
    (sourceConeCircle (sourceParentAxis U V)) (measurable_sourceConeCircle _)
    (by norm_num : (0:ℝ) ≤ 1) (sourceConeCircle_norm_le _)
  simp only [neg_zero,Real.rpow_zero,div_one] at heq
  rw [heq] at hb
  exact hb

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

theorem rootNormalizedF_error_of_pointwise (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) (N : ℕ) (sig : ℝ)
    (n : ℕ) (U V : DyadicSquare) (r ε : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2)
    (herr : ∀ᵐ z ∂d.ρ.prod e.ρ,
      ‖(rootSpatialWeight d e N sig z:ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ)) -
        rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)) z‖ ≤ ε) :
    Integrable (rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)))
      (d.ρ.prod e.ρ) ∧
    ‖charFun (rootWeightedDistance d e N sig) r - rootNormalizedF d e N sig n U V r‖ ≤
      (d.ρ.prod e.ρ).real univ * ε := by
  let μ := d.ρ.prod e.ρ
  let ψ := sourceConeCircle (sourceParentAxis U V)
  let K := rootNormalizedKernel d e N sig n r ψ
  let f := fun z : Plane × Plane =>
    (rootSpatialWeight d e N sig z:ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ))
  have hfm : Measurable f := by
    apply Measurable.mul (Complex.measurable_ofReal.comp (rootSpatialWeight_measurable d e N sig))
    fun_prop
  have hfb : ∀ᵐ z ∂μ, ‖f z‖ ≤ δ^(-(1/2:ℝ)) := by
    filter_upwards [hsep] with z hz
    have hw := rootSpatialWeight_le d e hd he N sig hδ hz
    have hw0 := rootSpatialWeight_nonneg d e hd he N sig z
    simpa [f,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw0] using hw
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable _ hfb
  have hkm : Measurable K := (rootNormalizedKernel_measurable d e N sig n ψ
    (measurable_sourceConeCircle _)).comp (f := fun z : Plane × Plane => (r,z))
      (measurable_const.prodMk measurable_id)
  have hki : Integrable K μ := by
    refine Integrable.of_bound hkm.aestronglyMeasurable (ε+δ^(-(1/2:ℝ))) ?_
    filter_upwards [herr,hfb] with z hz hb
    calc
      ‖K z‖ = ‖(K z-f z)+f z‖ := by rw [sub_add_cancel]
      _ ≤ ‖K z-f z‖+‖f z‖ := norm_add_le _ _
      _ ≤ ε+δ^(-(1/2:ℝ)) := add_le_add (by simpa only [norm_sub_rev] using hz) hb
  refine ⟨hki,?_⟩
  rw [rootWeightedDistance_fourier d e hd he N sig r,rootNormalizedF]
  change ‖(∫ z, f z ∂μ)-(∫ z, K z ∂μ)‖ ≤ _
  rw [← integral_sub hfi hki]
  exact (norm_integral_le_of_norm_le_const herr).trans_eq (mul_comm _ _)

theorem root_pair_ae_patches (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (U V : DyadicSquare)
    (hU : ∀ᵐ x ∂d.ρ, x ∈ U.carrier) (hV : ∀ᵐ y ∂e.ρ, y ∈ V.carrier) :
    ∀ᵐ z ∂d.ρ.prod e.ρ, z.1 ∈ U.carrier ∧ z.2 ∈ V.carrier :=
  (Measure.quasiMeasurePreserving_fst.ae hU).and (Measure.quasiMeasurePreserving_snd.ae hV)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootUniformFourier
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

theorem uniform_root_fourier_error_oai {sig δ T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    ∀ [IsProbabilityMeasure d.ρ] [IsProbabilityMeasure e.ρ],
    0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∀ b ∈ d.S, descriptorLength b ≤ N/2) →
    (∀ b ∈ e.S, descriptorLength b ≤ N/2) →
    ∀ U V : DyadicSquare, 0 < U.side → 0 < V.side →
    (∀ᵐ x ∂d.ρ, x ∈ U.carrier) → (∀ᵐ y ∂e.ρ, y ∈ V.carrier) →
    (∀ x ∈ U.carrier, ∀ y ∈ V.carrier, δ ≤ dist x y) →
    ∀ s : ℝ, U.side ≤ s → V.side ≤ s → 100*s ≤ dist U.center V.center →
    ∀ r : ℝ, (2:ℝ)^((N:ℝ)-1) ≤ r →
    Integrable (rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)))
      (d.ρ.prod e.ρ) ∧
    ‖charFun (rootWeightedDistance d e N sig) r - rootNormalizedF d e N sig n U V r‖ ≤
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_root_normalized_error (T := T) hsig hsmall hδ
  refine ⟨n,N₀,?_⟩
  intro N hN d e instd inste hd he hc₁ hc₂ hL₁ hL₂ U V hU hV hcarry₁ hcarry₂ hdist s hUs hVs hsep r hr
  have hmem := root_pair_ae_patches d e U V hcarry₁ hcarry₂
  have hdist' : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2 := by
    filter_upwards [hmem] with z hz
    exact hdist z.1 hz.1 z.2 hz.2
  have herr : ∀ᵐ z ∂d.ρ.prod e.ρ,
      ‖(rootSpatialWeight d e N sig z:ℂ)*Complex.exp (Complex.I*((r*dist z.1 z.2:ℝ):ℂ)) -
        rootNormalizedKernel d e N sig n r (sourceConeCircle (sourceParentAxis U V)) z‖ ≤ ((2:ℝ)^N)^(-T) := by
    filter_upwards [hmem] with z hz
    exact h₀ N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr
      z.1 hz.1 z.2 hz.2 (hdist z.1 hz.1 z.2 hz.2)
  have hh := rootNormalizedF_error_of_pointwise d e hd he N sig n U V r _ hδ hdist' herr
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,one_mul] using hh

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_root_fourier_error_oai := @OAI.PlanarFalconer.uniform_root_fourier_error_oai
