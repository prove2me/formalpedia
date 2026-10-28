-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_recursive_energy_rules
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:19:27.352506+00:00
-- url     : https://prove2.me/submissions/f3a08ce6-0e6f-484a-b64f-52ab1d441844

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_prefix_band
import Theorems.Thm_OAI_PlanarFalconer_source_positive_distance_suffix
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_angular_recursion_bound

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularUniformAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem fixed_linear_subpower (C : ℝ) (hC : 0 ≤ C) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C*(1+2*(N:ℝ)) ≤ ((2:ℝ)^N)^e := by
  obtain ⟨N₁,hN₁⟩ := fixed_constant_absorbed (half_pos he) C
  obtain ⟨N₂,hN₂⟩ := fixed_polynomial_subpower 1 (half_pos he)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hc := hN₁ N ((le_max_left _ _).trans hN)
  have hp := hN₂ N ((le_max_right _ _).trans hN)
  simp only [pow_one] at hp
  have hlin : 1+2*(N:ℝ) ≤ ((2:ℝ)^N)^(e/2) := by
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    linarith
  calc
    _ ≤ C*((2:ℝ)^N)^(e/2) := mul_le_mul_of_nonneg_left hlin hC
    _ ≤ ((2:ℝ)^N)^(e/2)*((2:ℝ)^N)^(e/2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularTerminal
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem actual_inherited_angular_terminal
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (N B : ℕ) (δ lam sig : ℝ)
    (hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l))
    (J i : ℕ) (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (a q : ℕ) (ha : a ≤ N) (A : Fin 2 → CellPath) (hA : ∀ l, (A l).length = a)
    (v : ℝ) (hv : v-a ≤ 100*q) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0) :
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let U := fun l => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ l) ((Q l).descendant (A l)).carrier (((2:ℝ)^N)^(-mass l a)) (β l) z.1 z.2
    sourceAngularH a v Ψ (U 0) (U 1) ≠ ⊤ ∧
    (sourceAngularH a v Ψ (U 0) (U 1)).toReal ≤
      (4*W*(symbolDerivativeConstant K^K)^4*(sourceArcLength.real univ)^2) *
        (2:ℝ)^(200*(q:ℝ)) * ((2:ℝ)^N)^(12*lam) := by
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let U := fun l => fun z : ℝ × UnitCircle =>
    sourceAngularTransform (ρ l) ((Q l).descendant (A l)).carrier (((2:ℝ)^N)^(-mass l a)) (β l) z.1 z.2
  let C := symbolDerivativeConstant K^K
  have hC : 0 ≤ C := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hm (l : Fin 2) : Measurable (U l) := measurable_sourceAngularTransform _ _ _ _
    (measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l))
  have hb (l : Fin 2) (z : ℝ × UnitCircle) : ‖U l z‖ ≤ C*((2:ℝ)^N)^(3*lam) := by
    have ht := sourceAngularTransform_norm_le (ρ l) ((Q l).descendant (A l)).carrier
      (((2:ℝ)^N)^(-mass l a)) (by positivity) (β l) C
      (fun x _ dir => inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l)
        (mass l) N lam sig J i (h l) K (hK l) x (hhb l x) dir) z.1 z.2
    apply ht.trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((hd l).normalized_cell_mass_le ha (hA l)) hC
  have he := sourceAngularH_uniform_bound a v Ψ hW hw hs (U 0) (U 1) (hm 0) (hm 1)
    (by positivity) (by positivity) (hb 0) (hb 1)
  have hp : (((2:ℝ)^N)^(3*lam))^4 = ((2:ℝ)^N)^(12*lam) := by
    rw [← Real.rpow_natCast _ 4,← Real.rpow_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
    congr 1
    norm_num
    ring
  have houter : (2:ℝ)^(2*(v-a)) ≤ (2:ℝ)^(200*(q:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  refine ⟨he.1,he.2.trans ?_⟩
  calc
    _ = (4*W*C^4*(sourceArcLength.real univ)^2) * (2:ℝ)^(2*(v-a)) * (((2:ℝ)^N)^(3*lam))^4 := by ring
    _ ≤ (4*W*C^4*(sourceArcLength.real univ)^2) * (2:ℝ)^(200*(q:ℝ)) * (((2:ℝ)^N)^(3*lam))^4 := by
      gcongr
    _ = _ := by rw [hp]

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InheritedPolicyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem remainingPolicyDescriptors_mono (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    remainingPolicyDescriptors A N q a₀ t₀ p ⊆ remainingPolicyDescriptors A N q a₀ t₀ a := by
  intro d hd
  obtain ⟨hd,hp⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd,hap.trans_lt hp⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStateData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace AngularStateData

theorem child_budget (d : AngularStateData) {a p K : ℕ} (hap : a ≤ p)
    (k : PolicyDescriptor → ℕ) (hk : ∑ b ∈ d.retainedList a, k b ≤ K) :
    ∑ b ∈ d.retainedList p, k b ≤ K := by
  exact (Finset.sum_le_sum_of_subset (remainingPolicyDescriptors_mono
    d.profile d.N d.q d.a₀ d.t₀ hap)).trans hk

end AngularStateData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStateSuccessor
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace AngularStateData

theorem children_lengths (d : AngularStateData) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    {row : CellPath × CellPath} (hr : row ∈ d.children p) :
    row.1.length = p ∧ row.2.length = p := by
  have hd := sourceProductVertices_subset d.Q d.Q d.ρ d.ρ d.X d.Y d.a (p-d.a) hX hY hr
  have hl := Finset.mem_product.mp hd
  constructor
  · simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.1
  · simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hl.2

end AngularStateData

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

theorem coincidence_four_point (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence = d.normalization * (d.cellPair.prod d.cellPair)
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width ∧
        z.1 ∈ d.good ∧ z.2 ∈ d.good} := by
  rw [coincidence,pair,Measure.prod_restrict,Measure.restrict_apply (by measurability)]
  rfl

end PositiveDistanceData

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
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellProfileMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem normalized_cellPair_mass (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.levelMass^(-2:ℤ)*d.cellPair.real univ =
      ((d.ρ (d.Q.descendant d.X).carrier).toReal/d.levelMass)*
      ((d.ρ (d.Q.descendant d.Y).carrier).toReal/d.levelMass) := by
  have hp : d.cellPair univ =
      d.ρ (d.Q.descendant d.X).carrier*d.ρ (d.Q.descendant d.Y).carrier := by
    unfold cellPair
    rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
  rw [measureReal_def,hp,ENNReal.toReal_mul]
  simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv]
  ring

theorem normalized_cellPair_profile_mass (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.levelMass^(-2:ℤ)*d.cellPair.real univ ≤ ((2:ℝ)^d.N)^(6*d.lam) := by
  let := hd.probability
  rw [d.normalized_cellPair_mass]
  have h := mul_le_mul (hd.normalized_cell_mass_le ha hX)
    (hd.normalized_cell_mass_le ha hY) (by positivity) (by positivity)
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N)] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring_nf

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualDistanceTerminal
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem coincidence_trivial_profile_bound (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.coincidence.toReal ≤ (2:ℝ)^((d.t:ℝ)-d.a)*((2:ℝ)^d.N)^(12*d.lam) := by
  let := hd.probability
  have hmass := d.normalized_cellPair_profile_mass hd ha hX hY
  have hquad : (d.cellPair.prod d.cellPair) univ = d.cellPair univ*d.cellPair univ := by
    rw [← univ_prod_univ,Measure.prod_prod]
  have hc : d.coincidence.toReal ≤ d.normalization.toReal*(d.cellPair.real univ)^2 := by
    rw [d.coincidence_four_point,ENNReal.toReal_mul]
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc
      _ ≤ ((d.cellPair.prod d.cellPair) univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top (d.cellPair.prod d.cellPair) univ)
          (measure_mono (subset_univ _))
      _ = _ := by rw [hquad,ENNReal.toReal_mul]; simp only [pow_two,measureReal_def]
  have he : d.normalization.toReal*(d.cellPair.real univ)^2 =
      (2:ℝ)^((d.t:ℝ)-d.a)*(d.levelMass^(-2:ℤ)*d.cellPair.real univ)^2 := by
    rw [normalization,ENNReal.toReal_ofReal (by positivity)]
    simp only [zpow_neg,zpow_ofNat]
    field_simp
  have hp := pow_le_pow_left₀ (show 0 ≤ d.levelMass^(-2:ℤ)*d.cellPair.real univ by positivity) hmass 2
  have hr : (((2:ℝ)^d.N)^(6*d.lam))^2 = ((2:ℝ)^d.N)^(12*d.lam) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (2:ℝ)^d.N)]
    congr 1
    norm_num
    ring
  rw [hr] at hp
  exact hc.trans (he.trans_le (mul_le_mul_of_nonneg_left hp (by positivity)))

theorem actual_distance_terminal (d : PositiveDistanceData) {B : ℕ} {δ : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (ht : d.t ≤ d.a+100*d.q) :
    d.coincidence.toReal ≤ (2:ℝ)^(200*(d.q:ℝ))*((2:ℝ)^d.N)^(12*d.lam) := by
  have htR : (d.t:ℝ) ≤ (d.a:ℝ)+100*d.q := by exact_mod_cast ht
  have he : (2:ℝ)^((d.t:ℝ)-d.a) ≤ (2:ℝ)^(200*(d.q:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [show (0:ℝ) ≤ d.q by positivity])
  exact (d.coincidence_trivial_profile_bound hd ha hX hY).trans
    (mul_le_mul_of_nonneg_right he (by positivity))

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualOuterMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourceSmoothingLevels_pos {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    0 < sourceSmoothingLevels sig kap := by
  unfold sourceSmoothingLevels
  exact Nat.ceil_pos.mpr (by positivity)

theorem sourcePolicyBlock_pos {N : ℕ} (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) :
    0 < sourcePolicyBlock N kap := by
  unfold sourcePolicyBlock
  exact Nat.ceil_pos.mpr (by positivity)

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixPolicyGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem source_policy_block_lower (N : ℕ) (kap : ℝ) :
    kap*(N:ℝ) ≤ (sourcePolicyBlock N kap:ℝ) := Nat.le_ceil _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchTransitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

namespace BranchStep
variable {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
variable {s u : BranchState} {label : BranchLabel}

theorem nested (h : BranchStep A N q sig s label u) (hq : 0 < q)
    (hv : s.Valid N sig) : s.start ≤ u.start ∧ u.finish ≤ s.finish := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    simp only [BranchState.start,BranchState.finish]
    omega
  | low _ hm _ =>
    have hm := Finset.mem_Ioc.mp hm
    exact ⟨le_rfl,hm.2⟩
  | high hw _ hm _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    have hm := Finset.mem_Ioc.mp hm
    exact ⟨by dsimp [BranchState.start]; omega,hm.2⟩
  | near _ hs => exact ⟨hs.le,le_rfl⟩
  | far _ _ hm =>
    have hm := Finset.mem_Icc.mp hm
    exact ⟨by dsimp [BranchState.start]; omega,le_rfl⟩
  | direct _ hw => exact ⟨hw.anchor_gt.le,le_rfl⟩

end BranchStep

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixLowMaximum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SourcePrefixReduction
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem prefix_band_power_absorption {R eps E T C F D H : ℝ}
    (hR : 1 ≤ R) (heps : 0 < eps) (hC : C ≤ R^(eps/2))
    (hF : 0 ≤ F) (hD : 0 ≤ D) (hH : 0 ≤ H) :
    C*(F+D+R^(E+eps/2)*H+R^(-T)) ≤
      R^eps*(F+D+R^E*H+R^(-T)) := by
  have hRp : 0 < R := by linarith
  have hhalf : 1 ≤ R^(eps/2) := Real.one_le_rpow hR (by positivity)
  have he : R^eps = R^(eps/2)*R^(eps/2) := by
    rw [← Real.rpow_add hRp]
    congr 1
    ring
  apply (mul_le_mul_of_nonneg_right hC (by positivity)).trans
  rw [Real.rpow_add hRp,he]
  nlinarith [mul_nonneg (show 0 ≤ R^(eps/2)-1 by linarith)
    (show 0 ≤ R^(eps/2)*(F+D+R^(-T)) by positivity)]

theorem source_positive_distance_prefix {lam sig kap eps T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (hT : 0 < T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ K N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
    d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    d.a+100*d.q < d.t → d.t ≤ d.N → d.i+1 ≤ d.J →
    let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    d.coincidence.toReal ≤ ((2:ℝ)^d.N)^eps *
      (((2:ℝ)^d.N)^(12*lam)+d.prefixLowMaximum+
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)) *
        d.prefixSuccessorSupremum K p Ψ + ((2:ℝ)^d.N)^(-T)) := by
  obtain ⟨C,hC,K,N₁,h₁⟩ := PositiveDistanceData.uniform_prefix_band hsig
    (by linarith : 10*sig < kap) hlam hT.le (half_pos heps)
    (sourceSmoothingLevels_pos hsig hkap) hΨ hpos hs hone
  obtain ⟨N₂,h₂⟩ := fixed_linear_subpower C hC.le (half_pos heps)
  refine ⟨K,max N₁ N₂,?_⟩
  intro d hdLam hdSig hdq hdJ hN hQ hcarry hX hY hlo hsep B δ hprof hw ht hi A p hpref
  have hq : 0 < d.q := by
    rw [hdq]
    exact sourcePolicyBlock_pos (by omega : 0 < d.N) hkap
  have hblock : kap*d.N ≤ (d.q:ℝ) := by rw [hdq]; exact source_policy_block_lower _ _
  have hband := h₁ d hdSig hdLam hdJ ((le_max_left _ _).trans hN) hQ hcarry B δ hprof
    hq hblock hw ht (by omega) hX hY hlo hsep hpref
  let := hprof.probability
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup0 := (d.prefixSuccessorSupremum_majorizes (by rw [hQ]; norm_num) K p Ψ hW
    (fun x => (le_abs_self _).trans (hWb x)) hsupport).1
  exact hband.trans (prefix_band_power_absorption (one_le_pow₀ (by norm_num)) heps
    (h₂ d.N ((le_max_right _ _).trans hN)) (by positivity) d.prefixLowMaximum_nonneg hsup0)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_BranchAnalyticSuccessors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

namespace PositiveDistanceData

theorem low_branch_transition (d : PositiveDistanceData) (hw : d.a+100*d.q < d.t)
    {v : ℕ} (hv : v ∈ d.prefixLowDepths) :
    BranchStep d.branchProfile d.N d.q d.sig d.branchState .low
      (({d with t := v,i := d.i+1} : PositiveDistanceData).branchState) := by
  obtain ⟨hm,hg⟩ := Finset.mem_filter.mp hv
  exact BranchStep.low hw hm (by linarith)

theorem high_branch_transition (d : PositiveDistanceData) (hw : d.a+100*d.q < d.t)
    (hs : 2*policyDepth d.branchProfile d.N d.q d.a d.t ≤ d.a+d.t)
    {v : ℕ} (hv : v ∈ Finset.Ioc d.a d.t) (hg : (d.t:ℝ)-d.sig*d.N < (v:ℝ))
    (row : CellPath × CellPath) :
    BranchStep d.branchProfile d.N d.q d.sig d.branchState .high
      ((d.angularSuccessor (policyDepth d.branchProfile d.N d.q d.a d.t) v row).branchState) :=
  BranchStep.high hw hs hv (by change (d.t:ℝ)-v < d.sig*d.N; linarith)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualSuccessorUpperBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem finiteEnergyMaximum_le {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ i ∈ S, (E i).toReal ≤ B) :
    finiteEnergyMaximum S E ≤ B := by
  change ((S.sup (fun i => (E i).toNNReal) : ℝ≥0) : ℝ) ≤ B
  lift B to ℝ≥0 using hB
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro i hi
  exact NNReal.coe_le_coe.mp (h i hi)

namespace PositiveDistanceData

theorem prefixLowMaximum_le (d : PositiveDistanceData) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v ∈ d.prefixLowDepths,
      ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal ≤ B) :
    d.prefixLowMaximum ≤ B := finiteEnergyMaximum_le _ _ hB h

theorem prefixSuccessorSupremum_le (d : PositiveDistanceData) (K p : ℕ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v ∈ Finset.Ioc d.a d.t, (d.t:ℝ)-d.sig*d.N < (v:ℝ) →
      ∀ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
      ∀ k : Fin 2 → PolicyDescriptor → ℕ,
        (∀ l, ∑ e ∈ d.prefixRemainingList p, k l e ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) →
        (∀ l x, ‖h l x‖ ≤ 1) →
        ((d.angularSuccessor p v row).energy k h Ψ).toReal ≤ B) :
    d.prefixSuccessorSupremum K p Ψ ≤ B := by
  apply csSup_le (show (d.prefixSuccessorEnergies K p Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro E hE
  rcases hE with rfl | ⟨v,hv,hg,row,hr,k,hk,h',hh,hhb,rfl⟩
  · exact hB
  · exact h v hv hg row hr k hk h' hh hhb

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SourceStateTerminal
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem PositiveDistanceData.terminal_power (d : PositiveDistanceData) {B : ℕ} {δ eps : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (hN : 0 < d.N) (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (ht : d.t ≤ d.a+100*d.q) (heps : 0 ≤ eps) :
    d.coincidence ≠ ⊤ ∧
    d.coincidence.toReal ≤ ((2:ℝ)^d.N)^(200*(d.q:ℝ)/d.N+12*d.lam+eps) := by
  let := hd.probability
  refine ⟨d.coincidence_ne_top,(d.actual_distance_terminal hd ha hX hY ht).trans ?_⟩
  rw [two_rpow_as_scale d.N hN,← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

theorem AngularStateData.terminal_bound (d : AngularStateData) {B : ℕ} {δ W : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (hQ : 0 < d.Q.side) (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (ht : d.v ≤ d.a+100*d.q) (K : ℕ)
    (k : Fin 2 → PolicyDescriptor → ℕ) (hk : ∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (Ψ : ℝ → ℝ) (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0) :
    d.energy k h Ψ ≠ ⊤ ∧ (d.energy k h Ψ).toReal ≤
      (4*W*(symbolDerivativeConstant K^K)^4*(sourceArcLength.real univ)^2)*
        (2:ℝ)^(200*(d.q:ℝ))*((2:ℝ)^d.N)^(12*d.lam) := by
  have htR : (d.v:ℝ) ≤ (d.a:ℝ)+100*d.q := by exact_mod_cast ht
  have hp : ∀ l : Fin 2, (![d.X,d.Y] l).length = d.a := by
    intro l
    fin_cases l <;> simp [hX,hY]
  exact actual_inherited_angular_terminal (fun _ => d.retainedList d.a) (fun _ => id) k K hk
    (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass) d.N B δ d.lam d.sig
    (fun _ => hd) d.J d.i h hh hhb d.a d.q ha ![d.X,d.Y] hp d.v (by linarith) Ψ hW hw hs

theorem uniform_angular_state_terminal (K : ℕ) {eps W : ℝ} (heps : 0 < eps) (hW : 0 ≤ W)
    (Ψ : ℝ → ℝ) (hw : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ d : AngularStateData, N₀ ≤ d.N →
      0 < d.Q.side → d.a ≤ d.N → d.X.length = d.a → d.Y.length = d.a →
      d.v ≤ d.a+100*d.q → ∀ B : ℕ, ∀ δ : ℝ,
      RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.energy k h Ψ ≠ ⊤ ∧
      (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^(200*(d.q:ℝ)/d.N+12*d.lam+eps) := by
  let C := 4*W*(symbolDerivativeConstant K^K)^4*(sourceArcLength.real univ)^2
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed heps C
  refine ⟨max 1 N₁,by omega,?_⟩
  intro d hN hQ ha hX hY ht B δ hd k hk h hh hhb
  have hb := d.terminal_bound hd hQ ha hX hY ht K k hk h hh hhb Ψ hW hw hs
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hc := h₁ d.N (by omega)
  change C*(2:ℝ)^(200*(d.q:ℝ))*((2:ℝ)^d.N)^(12*d.lam) ≤ _
  calc
    _ ≤ ((2:ℝ)^d.N)^eps*(2:ℝ)^(200*(d.q:ℝ))*((2:ℝ)^d.N)^(12*d.lam) := by
      gcongr
    _ = _ := by
      rw [two_rpow_as_scale d.N (by omega),← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N),
        ← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N)]
      congr 1
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_RecursiveCellInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

namespace PositiveDistanceData

theorem RecursiveCells.stronglySeparated {d : PositiveDistanceData}
    (h : d.RecursiveCells) (hQ : d.Q.side = 1) : d.StronglySeparated :=
  d.stronglySeparated_of_unit hQ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem RecursiveCells.update {d : PositiveDistanceData} (h : d.RecursiveCells) (t i : ℕ) :
    ({d with t := t,i := i} : PositiveDistanceData).RecursiveCells := h

theorem angularSuccessor_lengths (d : PositiveDistanceData) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) (v : ℕ)
    {row : CellPath × CellPath}
    (hr : row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a)) :
    (d.angularSuccessor p v row).X.length = p ∧
      (d.angularSuccessor p v row).Y.length = p := by
  change row.1.length = p ∧ row.2.length = p
  have hm := sourceProductVertices_subset d.Q d.Q d.ρ d.ρ d.X d.Y d.a (p-d.a) hX hY hr
  have hm := Finset.mem_product.mp hm
  exact ⟨by simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hm.1,
    by simpa only [Nat.add_sub_of_le hap] using (mem_dyadicPaths _ _).mp hm.2⟩

end PositiveDistanceData

namespace AngularStateData

theorem successor_budget (d : AngularStateData) {p K : ℕ} (hap : d.a ≤ p)
    (row : CellPath × CellPath) (k : Fin 2 → PolicyDescriptor → ℕ)
    (hk : ∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K) :
    ∀ l, ∑ e ∈ (d.successor p row).retainedList p, k l e ≤ K :=
  fun l => d.child_budget hap (k l) (hk l)

theorem far_recursive_cells (d : AngularStateData) {b : ℕ} (hab : d.a ≤ b)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    {row col : CellPath × CellPath} (hr : row ∈ d.children b) (hc : col ∈ d.children b)
    (hs : angularSeparated d.Q d.Q b row col) :
    ((d.distanceSuccessor b).atCells row.1 col.1).RecursiveCells ∧
      ((d.distanceSuccessor b).atCells row.2 col.2).RecursiveCells := by
  have hr' := d.children_lengths hab hX hY hr
  have hc' := d.children_lengths hab hX hY hc
  exact ⟨⟨hr'.1,hc'.1,hs.1⟩,⟨hr'.2,hc'.2,hs.2⟩⟩

end AngularStateData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ActualDistanceRecursionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem PositiveDistanceData.mul_prefixLowMaximum_le (d : PositiveDistanceData)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hb : ∀ v ∈ d.prefixLowDepths,
      c*({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal ≤ M) :
    c*d.prefixLowMaximum ≤ M := by
  have hh := d.prefixLowMaximum_le (div_nonneg hM hc.le)
    (fun v hv => (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb v hv))
  exact (mul_le_mul_of_nonneg_left hh hc.le).trans_eq (by field_simp)

theorem uniform_actual_distance_recursion_bound {lam sig kap eps T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (hT : 0 < T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ Kinv N₀ : ℕ, ∀ K ≥ Kinv, ∀ d : PositiveDistanceData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N →
      d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 → d.RecursiveCells →
      d.branchState.Valid d.N d.sig → d.a+100*d.q < d.t → d.i+1 ≤ d.J →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ M : ℝ, 0 ≤ M → ((2:ℝ)^d.N)^(12*lam+eps) ≤ M →
      (∀ t i l, BranchStep d.branchProfile d.N d.q d.sig d.branchState l (.D d.a t i) →
        ((2:ℝ)^d.N)^(branchExponent d.branchProfile lam sig eps d.branchState l (.D d.a t i)) *
          ({d with t := t,i := i} : PositiveDistanceData).coincidence.toReal ≤ M) →
      (∀ p v, ∀ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
        BranchStep d.branchProfile d.N d.q d.sig d.branchState .high (.H d.a d.t p v d.i) →
        ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ e ∈ d.prefixRemainingList p, k l e ≤ K) →
        ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
        ((2:ℝ)^d.N)^(branchExponent d.branchProfile lam sig eps d.branchState .high (.H d.a d.t p v d.i)) *
          ((d.angularSuccessor p v row).energy k h Ψ).toReal ≤ M) →
      d.coincidence ≠ ⊤ ∧ d.coincidence.toReal ≤ 3*M+((2:ℝ)^d.N)^(eps-T) := by
  obtain ⟨N₁,h₁⟩ := source_positive_distance_suffix hlam hsig hkap heps
  obtain ⟨Kinv,N₂,h₂⟩ := source_positive_distance_prefix hlam hsig hkap hgap heps hT hΨ hpos hs hone
  refine ⟨Kinv,max N₁ N₂,?_⟩
  intro K hK d hdlam hdsig hdq hdJ hN hQ hcarry hcells hv hw hi B δ hprof M hM hfloor hD hH
  let := hprof.probability
  have hfinite := d.coincidence_ne_top
  change d.a ≤ d.t ∧ d.t ≤ d.N at hv
  let p := policyDepth d.branchProfile d.N d.q d.a d.t
  have hRp : 0 < (2:ℝ)^d.N := by positivity
  by_cases hp : d.a+d.t < 2*p
  · have hbound := h₁ d hdlam hdsig hdq hdJ (by omega) hQ
      (hcells.stronglySeparated hQ) hcells.1 hcells.2.1 B δ hprof hw hv.2 hi hp
    have hstep : BranchStep d.branchProfile d.N d.q d.sig d.branchState .suffix (.D d.a p (d.i+1)) :=
      BranchStep.suffix hw hp
    have hm := hD p (d.i+1) .suffix hstep
    have hboundR := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence_ne_top) hbound
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hboundR
    simp only [branchExponent,branchCost,PositiveDistanceData.branchState,BranchState.start,BranchState.finish,
      sub_self,mul_zero,zero_add,reduceCtorEq,ite_false] at hm
    have hboundM : d.coincidence.toReal ≤ M := hboundR.trans hm
    refine ⟨hfinite,hboundM.trans ?_⟩
    linarith [Real.rpow_pos_of_pos hRp (eps-T)]
  · have hp' : 2*p ≤ d.a+d.t := by omega
    have hbound := h₂ d hdlam hdsig hdq hdJ (by omega) hQ hcarry hcells.1 hcells.2.1
      hcells.2.2.1 hcells.2.2.2 B δ hprof hw hv.2 hi hp'
    have hlow : ((2:ℝ)^d.N)^eps*d.prefixLowMaximum ≤ M := by
      apply d.mul_prefixLowMaximum_le (by positivity) hM
      intro v hv
      have hm := hD v (d.i+1) .low (d.low_branch_transition hw hv)
      simpa only [branchExponent,branchCost,PositiveDistanceData.branchState,BranchState.start,sub_self,mul_zero,
        neg_zero,zero_add,ite_true] using hm
    let E := -2*(d.branchProfile p-d.branchProfile d.a)+height d.branchProfile d.a p+4000*(lam+sig)
    have hhigh : ((2:ℝ)^d.N)^(E+eps)*d.prefixSuccessorSupremum Kinv p Ψ ≤ M := by
      have hsup := d.prefixSuccessorSupremum_le Kinv p Ψ
        (div_nonneg hM (by positivity : 0 ≤ ((2:ℝ)^d.N)^(E+eps))) (by
          intro v hv hg row hr k hk h hh hhb
          have hm := hH p v row hr (d.high_branch_transition hw hp' hv hg row) k
            (fun l => (hk l).trans hK) h hh hhb
          apply (le_div_iff₀ (by positivity : 0 < ((2:ℝ)^d.N)^(E+eps))).mpr
          simpa only [branchExponent,branchCost,PositiveDistanceData.branchState,BranchState.start,
            reduceCtorEq,ite_false,E,mul_comm] using hm)
      exact (mul_le_mul_of_nonneg_left hsup (by positivity)).trans_eq (by field_simp)
    have hfloor' : ((2:ℝ)^d.N)^eps*((2:ℝ)^d.N)^(12*lam) ≤ M := by
      rw [← Real.rpow_add hRp,add_comm eps]
      exact hfloor
    have hhigh' : ((2:ℝ)^d.N)^eps*(((2:ℝ)^d.N)^E*d.prefixSuccessorSupremum Kinv p Ψ) ≤ M := by
      rw [← mul_assoc,← Real.rpow_add hRp,add_comm eps]
      exact hhigh
    have herr : ((2:ℝ)^d.N)^eps*((2:ℝ)^d.N)^(-T) = ((2:ℝ)^d.N)^(eps-T) := by
      rw [← Real.rpow_add hRp,sub_eq_add_neg]
    refine ⟨hfinite,hbound.trans ?_⟩
    change ((2:ℝ)^d.N)^eps * (((2:ℝ)^d.N)^(12*lam)+d.prefixLowMaximum+
      ((2:ℝ)^d.N)^E*d.prefixSuccessorSupremum Kinv p Ψ+((2:ℝ)^d.N)^(-T)) ≤ _
    simp only [mul_add]
    rw [herr]
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_RecursiveEnergyFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_recursive_energy_rules_oai {lam sig kap eps tau T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (htau : 0 < tau) (hT : 0 < T) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ K : ℕ, K₀ ≤ K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
      e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
      e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
      (∀ s : BranchState, s.Valid e.N e.sig → s.finish ≤ s.start+100*e.q → ∀ x, e.energies K Ψ s x →
        x ≤ ((2:ℝ)^e.N)^(200*(e.q:ℝ)/e.N+12*lam+tau)) ∧
      (∀ s : BranchState, s.Valid e.N e.sig → s.index+1 ≤ e.J → s.start+100*e.q < s.finish →
        ∀ M : ℝ, 0 ≤ M → ((2:ℝ)^e.N)^(12*lam+eps) ≤ M →
        (∀ u l, BranchStep e.profile e.N e.q e.sig s l u → ∀ x, e.energies K Ψ u x →
          ((2:ℝ)^e.N)^(branchExponent e.profile lam sig eps s l u)*x ≤ M) →
        ∀ x, e.energies K Ψ s x → x ≤ ((e.N:ℝ)+3)*M+((2:ℝ)^e.N)^(-T)) := by
  obtain ⟨Kinv,N₁,h₁⟩ := uniform_actual_distance_recursion_bound hlam hsig hkap hgap heps
    (add_pos hT heps) hΨ hpos hs hone
  let K := max K₀ Kinv
  obtain ⟨N₂,h₂⟩ := uniform_actual_angular_recursion_bound hlam hsig hkap hgap heps T K hΨ hpos hs
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hWupper : ∀ x, Ψ x ≤ W := fun x => (le_abs_self _).trans (hWb x)
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  obtain ⟨N₃,hN₃,h₃⟩ := uniform_angular_state_terminal K htau hW Ψ hWupper hsupport
  refine ⟨K,le_max_left _ _,max N₁ (max N₂ N₃),by omega,?_⟩
  intro e hdlam hdsig hdq hdJ hN hQ hcarry B δ hprof
  have hNp : 0 < e.N := by omega
  have hQp : 0 < e.Q.side := by rw [hQ]; norm_num
  have heqp : 0 < e.q := by rw [hdq]; exact sourcePolicyBlock_pos hNp hkap
  constructor
  · intro s hv ht x hx
    cases s with
    | D a t i =>
      obtain ⟨X,Y,hcells,rfl⟩ := hx
      let d := e.distanceData a t i X Y
      have hb := d.terminal_power hprof hNp (hv.1.trans hv.2) hcells.1 hcells.2.1 ht htau.le
      simpa only [d,RecursiveEnvironment.distanceData,hdlam] using hb.2
    | H a₀ t₀ a v i =>
      obtain ⟨X,Y,hX,hY,k,hk,h,hh,hhb,rfl⟩ := hx
      have hb := h₃ (e.angularData a₀ t₀ a v i X Y) (show N₃ ≤ e.N by omega)
        hQp (hv.2.1.trans (hv.2.2.1.trans hv.2.2.2.1)) hX hY ht B δ hprof k hk h hh hhb
      simpa only [RecursiveEnvironment.angularData,hdlam] using hb.2
  · intro s hv hi hw M hM hfloor hchildren x hx
    cases s with
    | D a t i =>
      obtain ⟨X,Y,hcells,rfl⟩ := hx
      let d := e.distanceData a t i X Y
      have hb := h₁ K (le_max_right _ _) d hdlam hdsig hdq hdJ (show N₁ ≤ e.N by omega)
        hQ hcarry hcells hv hw hi B δ hprof M hM hfloor
      have hDc : ∀ t' i' l, BranchStep d.branchProfile d.N d.q d.sig d.branchState l (.D d.a t' i') →
          ((2:ℝ)^d.N)^(branchExponent d.branchProfile lam sig eps d.branchState l (.D d.a t' i')) *
            ({d with t := t',i := i'} : PositiveDistanceData).coincidence.toReal ≤ M := by
        intro t' i' l hstep
        exact hchildren _ l hstep _ ⟨X,Y,hcells.update t' i',rfl⟩
      have hHc : ∀ p v, ∀ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
          BranchStep d.branchProfile d.N d.q d.sig d.branchState .high (.H d.a d.t p v d.i) →
          ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.prefixRemainingList p, k l b ≤ K) →
          ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l y, ‖h l y‖ ≤ 1) →
          ((2:ℝ)^d.N)^(branchExponent d.branchProfile lam sig eps d.branchState .high (.H d.a d.t p v d.i)) *
            ((d.angularSuccessor p v row).energy k h Ψ).toReal ≤ M := by
        intro p v row hr hstep k hk h hh hhb
        have hap := (hstep.nested heqp hv).1
        have hl := d.angularSuccessor_lengths hap hcells.1 hcells.2.1 v hr
        exact hchildren _ .high hstep _ ⟨row.1,row.2,hl.1,hl.2,k,hk,h,hh,hhb,rfl⟩
      have hb := (hb hDc hHc).2
      have he : eps-(T+eps) = -T := by ring
      rw [he] at hb
      change _ ≤ ((e.N:ℝ)+3)*M+_
      exact hb.trans (by dsimp only [d,RecursiveEnvironment.distanceData]; nlinarith [Nat.cast_nonneg (α := ℝ) e.N])
    | H a₀ t₀ a v i =>
      obtain ⟨X,Y,hX,hY,k,hk,h,hh,hhb,rfl⟩ := hx
      let d := e.angularData a₀ t₀ a v i X Y
      have hb := h₂ d hdlam hdsig hdq hdJ (show N₂ ≤ e.N by omega) hQ hcarry hv hw hi
        hX hY B δ hprof k hk h hh hhb M hM
      have hHc : ∀ p l, BranchStep d.profile d.N d.q d.sig d.branchState l (.H d.a₀ d.t₀ p d.v d.i) →
          ∀ row ∈ d.children p,
          ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState l (.H d.a₀ d.t₀ p d.v d.i)) *
            ((d.successor p row).energy k h Ψ).toReal ≤ M := by
        intro p l hstep row hr
        have hap := (hstep.nested heqp hv).1
        have hl := d.children_lengths hap hX hY hr
        exact hchildren _ l hstep _ ⟨row.1,row.2,hl.1,hl.2,k,d.successor_budget hap row k hk,h,hh,hhb,rfl⟩
      have hDc : ∀ b, BranchStep d.profile d.N d.q d.sig d.branchState .far (.D b d.v (d.i+1)) →
          ∀ row ∈ d.children b, ∀ col ∈ d.children b, angularSeparated d.Q d.Q b row col →
          ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
            ((d.distanceSuccessor b).atCells row.1 col.1).coincidence.toReal ≤ M ∧
          ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
            ((d.distanceSuccessor b).atCells row.2 col.2).coincidence.toReal ≤ M := by
        intro b hstep row hr col hc hs
        have hab := (hstep.nested heqp hv).1
        have hcells := d.far_recursive_cells hab hX hY hr hc hs
        exact ⟨hchildren _ .far hstep _ ⟨row.1,col.1,hcells.1,rfl⟩,
          hchildren _ .far hstep _ ⟨row.2,col.2,hcells.2,rfl⟩⟩
      have hb := (hb hHc hDc).2
      exact hb.trans (by dsimp only [d,RecursiveEnvironment.angularData]; nlinarith)

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_recursive_energy_rules_oai := @OAI.PlanarFalconer.uniform_recursive_energy_rules_oai
