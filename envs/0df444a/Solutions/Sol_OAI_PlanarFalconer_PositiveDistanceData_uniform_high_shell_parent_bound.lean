-- Prove2me | solution 1 for OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:20:35.849727+00:00
-- url     : https://prove2.me/submissions/36a5dd8e-c59f-4e95-bce8-bd230f374b4a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_normalizedHighShellF_measurable
import Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_normalizedHighShellF_shell
import Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_uniform_high_shell_profile_error

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

namespace AngularDifferentialExpr

theorem cost_nonneg (p : AngularDifferentialExpr) : 0 ≤ p.cost := by
  induction p with
  | term c k => exact norm_nonneg c
  | add p q hp hq => exact add_nonneg hp hq
  | comp p q hp hq => exact mul_nonneg hp hq

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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptors_card (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) : (originDescriptors A N q b u).card ≤ N+1 := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  unfold originDescriptors
  apply (Finset.card_union_le _ _).trans
  have hfirst : ((Finset.Ico (policyDepth A N q b u-min (policyDepth A N q b u-b)
      (u-policyDepth A N q b u)) (policyDepth A N q b u)).image
      (fun g => PolicyDescriptor.parallel g (policyDepth A N q b u))).card ≤ N := by
    apply Finset.card_image_le.trans
    rw [Nat.card_Ico]
    omega
  split_ifs <;> simp only [Finset.card_singleton,Finset.card_empty] <;> omega

theorem policyDescriptorList_card (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) :
    (policyDescriptorList A N q a t).card ≤ (N+1)^3 := by
  classical
  calc
    _ ≤ ∑ z ∈ policyOrigins N q a t, (originDescriptors A N q z.1 z.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ policyOrigins N q a t, (N+1) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
      have huN := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
      exact originDescriptors_card A hq huN hwide
    _ = (policyOrigins N q a t).card*(N+1) := by simp
    _ ≤ ((N+1)*(N+1))*(N+1) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = (N+1)^3 := by ring

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

theorem orderedDerivAssignments_length {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (n : ℕ) : (orderedDerivAssignments S n).length = S.card^n := by
  induction n with
  | zero => simp [orderedDerivAssignments]
  | succ n ih => simp [orderedDerivAssignments,List.length_flatMap,ih,pow_succ]

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

theorem terms_cost (p : AngularDifferentialExpr) :
    (p.terms.map (fun a => ‖a.1‖)).sum = p.cost := by
  induction p with
  | term c k => simp [terms,cost]
  | add p q hp hq => simp [terms,cost,hp,hq]
  | comp p q hp hq =>
    simp only [terms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def,norm_mul,List.sum_map_mul_left,List.sum_map_mul_right,hp,hq,cost]

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_FiniteAngularSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem bounded_shell_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, |Ψ t| ≤ W)
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) (hf : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ r, ‖f r‖ ≤ C) :
    Integrable (fun r => Ψ (r/R) • f r) := by
  have hb : Integrable (Set.indicator (Icc (R/4) (4*R)) (fun _ : ℝ => W*C)) :=
    (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  apply hb.mono ((hΨ.comp (measurable_id.div_const R)).aestronglyMeasurable.smul hf)
  filter_upwards with r
  by_cases hn : Ψ (r/R) = 0
  · simp [hn]
  · have hh := hs _ hn
    have hr : r ∈ Icc (R/4) (4*R) := by
      constructor
      · have := (lt_div_iff₀ hR).mp hh.1; linarith
      · have := (div_lt_iff₀ hR).mp hh.2; linarith
    change ‖Ψ (r/R) • f r‖ ≤ ‖Set.indicator (Icc (R/4) (4*R)) (fun _ : ℝ => W*C) r‖
    rw [Set.indicator_of_mem hr, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hW hC),
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hw _) (hc r) (norm_nonneg _) hW

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

theorem inverseLeibnizTerms_cost {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι) :
    ((inverseLeibnizTerms j S).map (fun a => ‖a.1‖)).sum ≤
      (inverseStationaryExpr j).cost * (max 1 (S.card:ℝ))^(2*j) := by
  simp only [inverseLeibnizTerms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  calc
    _ ≤ ((inverseStationaryExpr j).terms.map
        (fun a => ‖a.1‖*(max 1 (S.card:ℝ))^(2*j))).sum := by
      apply List.sum_le_sum
      intro a ha
      simp only [List.map_const',List.sum_replicate,orderedDerivAssignments_length,nsmul_eq_mul,
        Nat.cast_pow]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right 1 (S.card:ℝ)) a.2).trans
        (pow_le_pow_right₀ (le_max_left _ _) (inverseStationaryOperator_terms_order j ha))
    _ = _ := by rw [List.sum_map_mul_right,AngularDifferentialExpr.terms_cost]

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

theorem ae_cellPair_mem (d : PositiveDistanceData) [SFinite d.ρ] :
    ∀ᵐ z ∂d.cellPair, z.1 ∈ (d.Q.descendant d.X).carrier ∧
      z.2 ∈ (d.Q.descendant d.Y).carrier := by
  exact (Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem (d.Q.descendant d.X).measurable)).and
    (Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (d.Q.descendant d.Y).measurable))

end PositiveDistanceData

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

end PositiveDistanceData

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

theorem high_shell_energy_prefactor (a v : ℝ) :
    (2:ℝ)^(-a)*(2:ℝ)^v*(2:ℝ)^(v-a) = (2:ℝ)^(2*(v-a)) := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

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

theorem minimal_inverseLeibniz_cost (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) (j : ℕ) :
    ((inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))).map
      (fun b => ‖b.1‖)).sum ≤
    (inverseStationaryExpr j).cost * (2*((N:ℝ)+1)^3)^(2*j) := by
  apply (inverseLeibnizTerms_cost j _).trans
  apply mul_le_mul_of_nonneg_left _ (inverseStationaryExpr j).cost_nonneg
  apply pow_le_pow_left₀ (by positivity)
  apply max_le
  · have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    nlinarith [one_le_pow₀ (by linarith : (1:ℝ) ≤ (N:ℝ)+1) (n := 3)]
  · have hc : ((policyDescriptorList A N q a t).card:ℝ) ≤ ((N:ℝ)+1)^3 := by
      exact_mod_cast policyDescriptorList_card A hq
    change ((Finset.product (policyDescriptorList A N q a t) (Finset.univ : Finset (Fin 2))).card:ℝ) ≤ _
    rw [Finset.product_eq_sprod,Finset.card_product (policyDescriptorList A N q a t) (Finset.univ : Finset (Fin 2))]
    simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem uniform_minimal_inverseLeibniz_subpower {eps : ℝ} (heps : 0 < eps) (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0 < q →
    ((inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))).map
      (fun b => ‖b.1‖)).sum * (2:ℝ)^j ≤ ((2:ℝ)^N)^eps := by
  let C := (inverseStationaryExpr j).cost * (2:ℝ)^(2*j) * (2:ℝ)^j
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) C
  obtain ⟨N₂,h₂⟩ := fixed_polynomial_subpower (6*j) (half_pos heps)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN A q a t hq
  have hpoly : (((N:ℝ)+1)^3)^(2*j) = ((N:ℝ)+1)^(6*j) := by
    rw [← pow_mul]
    congr 1
    omega
  have hbound := mul_le_mul_of_nonneg_right (minimal_inverseLeibniz_cost A (N := N) (a := a) (t := t) hq j)
    (by positivity : 0 ≤ (2:ℝ)^j)
  apply hbound.trans
  calc
    _ = C*((N:ℝ)+1)^(6*j) := by rw [mul_pow,hpoly]; dsimp [C]; ring
    _ ≤ C*(4*(N:ℝ)+1)^(6*j) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by have := Nat.cast_nonneg (α := ℝ) N; linarith) _)
      (by dsimp [C]; exact mul_nonneg (mul_nonneg (inverseStationaryExpr j).cost_nonneg (by positivity)) (by positivity))
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul (h₁ N ((le_max_left _ _).trans hN)) (h₂ N ((le_max_right _ _).trans hN))
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialLeibnizSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem uniform_spatialLeibniz_subpower (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    {eps : ℝ} (heps : 0 < eps) (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0 < q →
      spatialLeibnizCost δ L hδ hL j A N q a t ≤ ((2:ℝ)^N)^eps := by
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) (spatialFourierCost δ L hδ hL j)
  obtain ⟨N₂,h₂⟩ := uniform_minimal_inverseLeibniz_subpower (half_pos heps) j
  refine ⟨max N₁ N₂,?_⟩
  intro N hN A q a t hq
  unfold spatialLeibnizCost
  calc
    _ ≤ spatialFourierCost δ L hδ hL j * ((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_left (h₂ N ((le_max_right _ _).trans hN) A q a t hq)
        (spatialFourierCost_nonneg δ L hδ hL j)
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_right (h₁ N ((le_max_left _ _).trans hN)) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem uniform_spatialLeibniz_sum_subpower (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0 < q →
      (∑ j ∈ Finset.range (n+1), spatialLeibnizCost δ L hδ hL j A N q a t) ≤
        ((2:ℝ)^N)^eps := by
  classical
  choose K hK using (fun j => uniform_spatialLeibniz_subpower δ L hδ hL (half_pos heps) j)
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) ((n:ℝ)+1)
  refine ⟨max N₁ ((Finset.range (n+1)).sup K),?_⟩
  intro N hN A q a t hq
  have hb : ∀ j ∈ Finset.range (n+1), spatialLeibnizCost δ L hδ hL j A N q a t ≤
      ((2:ℝ)^N)^(eps/2) := by
    intro j hj
    exact hK j N ((Finset.le_sup hj).trans ((le_max_right _ _).trans hN)) A q a t hq
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((2:ℝ)^N)^(eps/2) := Finset.sum_le_sum hb
    _ = ((n:ℝ)+1)*((2:ℝ)^N)^(eps/2) := by simp
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_right (h₁ N ((le_max_left _ _).trans hN)) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

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
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellErrorPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem high_shell_error_power (N a : ℕ) (hN : 1 ≤ N) {v : ℝ} (hv : v ≤ N) (T : ℝ) :
    (2:ℝ)^(-(a:ℝ)) * (2*(((2:ℝ)^N)^(-((T+3)/2)))^2 *
      (volume.restrict (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)))).real univ) ≤
        ((2:ℝ)^N)^(-T) := by
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR2 : 2 ≤ R := by
    dsimp [R]
    exact_mod_cast (show 2^1 ≤ 2^N from Nat.pow_le_pow_right (by omega) hN)
  have houter : (2:ℝ)^(-(a:ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show -(a:ℝ) ≤ 0 from neg_nonpos.mpr (Nat.cast_nonneg a))
  have hlength : (volume.restrict (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)))).real univ ≤ 2*R := by
    rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)))]
    have hp : (2:ℝ)^(v+1) ≤ 2*R := by
      rw [Real.rpow_add (by norm_num),Real.rpow_one,mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hv
    linarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (v-1)]
  have he : (R^(-((T+3)/2)))^2 = R^(-(T+3)) := by
    rw [← Real.rpow_mul_natCast hR.le]
    congr 1
    norm_num
  change (2:ℝ)^(-(a:ℝ))*(2*(R^(-((T+3)/2)))^2*_) ≤ R^(-T)
  rw [he]
  calc
    _ ≤ 1*(2*R^(-(T+3))*(2*R)) :=
      mul_le_mul houter (mul_le_mul_of_nonneg_left hlength (by positivity))
        (by positivity) (by norm_num)
    _ = 4*R*R^(-(T+3)) := by ring
    _ ≤ R^3*R^(-(T+3)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (R-2)]
    _ = R^(-T) := by
      rw [← Real.rpow_natCast R 3,← Real.rpow_add hR]
      congr 1
      norm_num

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
-- module Solutions.OAIQ038_FA.Falconer_Shells_SmoothShellDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem dyadic_shell_smooth_domination (v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hb : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hCbound : ∀ r, ‖F r‖ ≤ C) :
    (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
      (2:ℝ)^v * ∫ r, ‖F r‖^2 ∂sourceAngularShellMeasure v Ψ := by
  have hR : 0 < (2:ℝ)^v := by positivity
  have hzero : ∀ x ≤ 0, Ψ x = 0 := by
    intro x hx
    by_contra hn
    have := (hs x hn).1
    linarith
  rw [sourceAngularShellMeasure_integral v hΨ hpos hzero,smul_eq_mul,
    ← mul_assoc,mul_inv_cancel₀ hR.ne',one_mul]
  have hi : Integrable (fun r => Ψ (r/(2:ℝ)^v)*‖F r‖^2) := by
    exact bounded_shell_integrable hΨ hs hW
      (fun x => by rw [abs_of_nonneg (hpos x)]; exact hb x) hR _
      (hF.norm.pow_const 2).aestronglyMeasurable (sq_nonneg C) (fun r => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hCbound r) 2)
  have hfi : IntegrableOn (fun r => ‖F r‖^2)
      (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) :=
    integrable_norm_square_bounded _ F hF hC (Filter.Eventually.of_forall hCbound)
  rw [← integral_indicator measurableSet_Icc]
  apply integral_mono (hfi.integrable_indicator measurableSet_Icc) hi
  intro r
  by_cases hr : r ∈ Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))
  · rw [indicator_of_mem hr]
    have he₁ : (2:ℝ)^(v-1) = (2:ℝ)^v/2 := by
      rw [Real.rpow_sub (by norm_num)]; norm_num
    have he₂ : (2:ℝ)^(v+1) = 2*(2:ℝ)^v := by
      rw [Real.rpow_add (by norm_num)]; norm_num; ring
    have hh : r/(2:ℝ)^v ∈ Icc (1/2:ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ hR).mpr
        rw [he₁] at hr
        linarith [hr.1]
      · apply (div_le_iff₀ hR).mpr
        simpa only [he₂] using hr.2
    exact le_mul_of_one_le_left (sq_nonneg _) (hone _ hh)
  · rw [indicator_of_notMem hr]
    exact mul_nonneg (hpos _) (sq_nonneg _)

theorem dyadic_shell_le_radial_energy (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hb : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    (F : ℝ → ℂ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hCbound : ∀ r, ‖F r‖ ≤ C) {H : ℝ}
    (hH : sourceRadialSquareEnergy a v Ψ F ≤ H) :
    (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
      ((2:ℝ)^v/(2:ℝ)^(2*(v-a)))*H := by
  apply (dyadic_shell_smooth_domination v Ψ hΨ hpos hs hW hb hone F hF hC hCbound).trans
  have hh := (le_div_iff₀ (show 0 < (2:ℝ)^(2*(v-a)) by positivity)).mpr
    (show (∫ r, ‖F r‖^2 ∂sourceAngularShellMeasure v Ψ)*(2:ℝ)^(2*(v-a)) ≤ H by
      simpa only [sourceRadialSquareEnergy,mul_comm] using hH)
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

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

theorem normalizedHighShellF_parent_energy (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hsep : d.StronglySeparated) (hsig : 0 ≤ d.sig)
    (hq : 0 < d.q) (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
    {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (n : ℕ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
        (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ H) :
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖d.normalizedHighShellF n v r‖^2) ≤
      2*(∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
        (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)^2*H := by
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hE := d.normalizedHighShellF_shell hQ hsep hsig hq hqs hw hv n
    (B := ((2:ℝ)^v/(2:ℝ)^(2*(v-d.a)))*H) (by positivity) (by
      intro j hj b hb ξ
      have hd := d.inversePhasedForm_data hQ j hb
      have hm : Measurable (d.inversePhasedForm b.2 ξ) :=
        hd.1.comp (f := fun r : ℝ => (ξ,r)) (measurable_const.prodMk measurable_id)
      apply dyadic_shell_le_radial_energy d.a v Ψ hΨ hpos hs hW hΨW hone _ hm
        (d.inversePhasedBound_nonneg j) (fun r => hd.2 (ξ,r))
      rw [← (d.inversePhasedHF_finite_eq hQ j hb v Ψ hW hΨW hsupport ξ).2]
      exact hH j hj b hb ξ)
  apply (mul_le_mul_of_nonneg_left hE (show 0 ≤ (2:ℝ)^(-(d.a:ℝ)) by positivity)).trans_eq
  let S := ∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
    (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
  change (2:ℝ)^(-(d.a:ℝ))*(2*(2:ℝ)^(v-d.a)*S^2*
    (((2:ℝ)^v/(2:ℝ)^(2*(v-d.a)))*H)) = 2*S^2*H
  calc
    _ = 2*S^2*H*((2:ℝ)^(-(d.a:ℝ))*(2:ℝ)^v*(2:ℝ)^(v-d.a)/(2:ℝ)^(2*(v-d.a))) := by ring
    _ = _ := by rw [high_shell_energy_prefactor,div_self (by positivity),mul_one]

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellApproximationError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Filter

theorem norm_square_of_error {z w : ℂ} {e : ℝ} (he : 0 ≤ e) (h : ‖z-w‖ ≤ e) :
    ‖z‖^2 ≤ 2*‖w‖^2+2*e^2 := by
  have hn : ‖z‖ ≤ ‖w‖+e := by
    calc
      _ = ‖(z-w)+w‖ := by rw [sub_add_cancel]
      _ ≤ ‖z-w‖+‖w‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  nlinarith [sq_nonneg (‖w‖-e),
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) he)).2 hn]

theorem shell_square_approximation (μ : Measure ℝ) [IsFiniteMeasure μ]
    (F G : ℝ → ℂ) (hG : Measurable G)
    (hiF : Integrable (fun r => ‖F r‖^2) μ) {e : ℝ} (he : 0 ≤ e)
    (herr : ∀ᵐ r ∂μ, ‖F r-G r‖ ≤ e) :
    Integrable (fun r => ‖G r‖^2) μ ∧
      (∫ r, ‖F r‖^2 ∂μ) ≤ 2*(∫ r, ‖G r‖^2 ∂μ)+2*e^2*μ.real Set.univ := by
  have hGi : Integrable (fun r => ‖G r‖^2) μ := by
    apply ((hiF.const_mul 2).add (integrable_const (2*e^2))).mono'
      (hG.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [herr] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact norm_square_of_error he (by simpa only [norm_sub_rev] using hr)
  refine ⟨hGi,?_⟩
  calc
    _ ≤ ∫ r, 2*‖G r‖^2+2*e^2 ∂μ :=
      integral_mono_ae hiF ((hGi.const_mul 2).add (integrable_const (2*e^2)))
        (herr.mono (fun r hr => norm_square_of_error he hr))
    _ = _ := by
      rw [integral_add (hGi.const_mul 2) (integrable_const (2*e^2)),integral_const_mul,integral_const]
      simp only [smul_eq_mul]
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellEquation21
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

theorem uniform_high_shell_parent_bound_oai {sig lam eps T : ℝ}
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
    ∀ H : ℝ, 0 ≤ H →
    (∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
        (d.inversePhasedHF v Ψ b.2 ξ).toReal ≤ H) →
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖charFun d.weightedDistance r‖^2) ≤
        ((2:ℝ)^d.N)^eps*H+((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₁,h₁⟩ := uniform_high_shell_profile_error (lam := lam) (T := (T+3)/2) hsig
  obtain ⟨N₂,h₂⟩ := uniform_spatialLeibniz_sum_subpower 96 2004 (by norm_num) (by norm_num)
    (show 0 < eps/4 by linarith) n
  obtain ⟨N₃,h₃⟩ := fixed_constant_absorbed (half_pos heps) 4
  refine ⟨n,max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro d B δ hd hN hsig' hlam hQ hsep hq hqs hw ht hX hY v hv hvt Ψ hΨ hpos hs W hW hΨW hone H hH0 hH
  let := hd.probability
  let := d.weightedDistance_isFinite hQ hsep
  have hN1 : N₁ ≤ d.N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : N₂ ≤ d.N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : N₃ ≤ d.N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  let R : ℝ := (2:ℝ)^d.N
  let μ := volume.restrict (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)))
  let e := R^(-((T+3)/2))
  have herr : ∀ᵐ r ∂μ, ‖charFun d.weightedDistance r-d.normalizedHighShellF n v r‖ ≤ e := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact h₁ d B δ hd hN1 hsig' hlam hQ hsep hq hqs hw ht hX hY v r hv hr.1
  have hi : Integrable (fun r => ‖charFun d.weightedDistance r‖^2) μ :=
    integrable_norm_square_bounded μ _ measurable_charFun measureReal_nonneg
      (Eventually.of_forall (fun r => norm_charFun_le r))
  have hsq := (shell_square_approximation μ _ _ (d.normalizedHighShellF_measurable hQ hsep n v)
    hi (show 0 ≤ e by dsimp [e]; positivity) herr).2
  have hmain := d.normalizedHighShellF_parent_energy hQ hsep (by rw [hsig']; exact hsig.le)
    hq hqs hw hv n Ψ hΨ hpos hs hW hΨW hone hH0 hH
  let S := ∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
    (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
  have hS : S ≤ R^(eps/4) := h₂ d.N hN2 _ d.q d.a d.t hq
  have hS0 : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (spatialFourierCost_nonneg ..)
    apply mul_nonneg _ (by positivity)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    positivity
  have hcost : 4*S^2 ≤ R^eps := by
    calc
      _ ≤ R^(eps/2)*(R^(eps/4))^2 :=
        mul_le_mul (h₃ d.N hN3) (pow_le_pow_left₀ hS0 hS 2) (sq_nonneg _) (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul_natCast (show 0 ≤ R by dsimp [R]; positivity),
          ← Real.rpow_add (show 0 < R by dsimp [R]; positivity)]
        congr 1
        ring
  have herror := high_shell_error_power d.N d.a ((le_max_left _ _).trans hN)
    (hvt.trans (Nat.cast_le.mpr ht)) T
  calc
    _ ≤ (2:ℝ)^(-(d.a:ℝ)) * (2*(∫ r, ‖d.normalizedHighShellF n v r‖^2 ∂μ)+2*e^2*μ.real univ) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2*((2:ℝ)^(-(d.a:ℝ))*(∫ r, ‖d.normalizedHighShellF n v r‖^2 ∂μ))+
        (2:ℝ)^(-(d.a:ℝ))*(2*e^2*μ.real univ) := by ring
    _ ≤ 2*(2*S^2*H)+R^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num)) herror
    _ ≤ R^eps*H+R^(-T) := by nlinarith [mul_le_mul_of_nonneg_right hcost hH0]

end PositiveDistanceData

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound_oai := @OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound_oai
