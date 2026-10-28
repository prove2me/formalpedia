-- Prove2me | solution 1 for OAI.PlanarFalconer.RootShellData.uniform_parent_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:07:48.012905+00:00
-- url     : https://prove2.me/submissions/3c28fb5d-e3ac-420a-ba33-20328d8328d6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_RootShellData_mainF_shell
import Theorems.Thm_OAI_PlanarFalconer_uniform_root_fourier_error

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

theorem rootPairMask_bounds (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) (z : Plane × Plane) :
    0 ≤ rootPairMask d e N sig z ∧ rootPairMask d e N sig z ≤ 1 := by
  have h₁ := d.mask_bounds hd N sig z.1 (sourceRadialUnit z.2 z.1)
  have h₂ := e.mask_bounds he N sig z.2 (sourceRadialUnit z.2 z.1)
  exact ⟨mul_nonneg h₁.1 h₂.1,(mul_le_of_le_one_left h₂.1 h₁.2).trans h₂.2⟩

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

theorem root_inverseLeibniz_cost (d e : RootEndpointData) (N j : ℕ)
    (hd : d.S.card ≤ (N+1)^3+1) (he : e.S.card ≤ (N+1)^3+1) :
    ((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b => ‖b.1‖)).sum ≤
      (inverseStationaryExpr j).cost * (4*((N:ℝ)+1)^3)^(2*j) := by
  apply (inverseLeibnizTerms_cost j _).trans
  apply mul_le_mul_of_nonneg_left _ (inverseStationaryExpr j).cost_nonneg
  apply pow_le_pow_left₀ (by positivity)
  have hd' : (d.S.card:ℝ) ≤ ((N:ℝ)+1)^3+1 := by exact_mod_cast hd
  have he' : (e.S.card:ℝ) ≤ ((N:ℝ)+1)^3+1 := by exact_mod_cast he
  have hp : 1 ≤ ((N:ℝ)+1)^3 := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
  simp only [rootMaskIndices,Finset.card_disjSum,Nat.cast_add]
  apply max_le <;> linarith

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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootCoefficientSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem uniform_root_inverseLeibniz_subpower {eps : ℝ} (heps : 0 < eps) (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
      d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    ((inverseLeibnizTerms j (rootMaskIndices d e)).map
      (fun b => ‖b.1‖)).sum * (2:ℝ)^j ≤ ((2:ℝ)^N)^eps := by
  let C := (inverseStationaryExpr j).cost * (4:ℝ)^(2*j) * (2:ℝ)^j
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) C
  obtain ⟨N₂,h₂⟩ := fixed_polynomial_subpower (6*j) (half_pos heps)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN d e hd he
  have hpoly : (((N:ℝ)+1)^3)^(2*j) = ((N:ℝ)+1)^(6*j) := by
    rw [← pow_mul]
    congr 1
    omega
  have hbound := mul_le_mul_of_nonneg_right (root_inverseLeibniz_cost d e N j hd he)
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

theorem rootWeightedPair_le (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    rootWeightedPair d e N sig ≤ ENNReal.ofReal (δ^(-(1/2:ℝ))) • d.ρ.prod e.ρ := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [hsep] with z hz
  exact ENNReal.ofReal_le_ofReal (rootSpatialWeight_le d e hd he N sig hδ hz)

theorem rootWeightedPair_isFinite (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    IsFiniteMeasure (rootWeightedPair d e N sig) := by
  constructor
  apply (Measure.le_iff.mp (rootWeightedPair_le d e N sig hd he hδ hsep) univ MeasurableSet.univ).trans_lt
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem rootWeightedDistance_isFinite (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    IsFiniteMeasure (rootWeightedDistance d e N sig) := by
  let := rootWeightedPair_isFinite d e N sig hd he hδ hsep
  unfold rootWeightedDistance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

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

theorem rootNormalizedF_measurable (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (N : ℕ) (sig : ℝ)
    (n : ℕ) (U V : DyadicSquare) : Measurable (rootNormalizedF d e N sig n U V) :=
  (rootNormalizedKernel_measurable d e N sig n _ (measurable_sourceConeCircle _)).stronglyMeasurable.integral_prod_right'.measurable

theorem root_pair_ae_patches (d e : RootEndpointData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (U V : DyadicSquare)
    (hU : ∀ᵐ x ∂d.ρ, x ∈ U.carrier) (hV : ∀ᵐ y ∂e.ρ, y ∈ V.carrier) :
    ∀ᵐ z ∂d.ρ.prod e.ρ, z.1 ∈ U.carrier ∧ z.2 ∈ V.carrier :=
  (Measure.quasiMeasurePreserving_fst.ae hU).and (Measure.quasiMeasurePreserving_snd.ae hV)

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
-- module Solutions.OAIQ038_FA.Falconer_Measures_RootNormalizedCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem uniform_root_spatialLeibniz_subpower (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    {eps : ℝ} (heps : 0 < eps) (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    rootSpatialLeibnizCost δ L hδ hL d e j ≤ ((2:ℝ)^N)^eps := by
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) (spatialFourierCost δ L hδ hL j)
  obtain ⟨N₂,h₂⟩ := uniform_root_inverseLeibniz_subpower (half_pos heps) j
  refine ⟨max N₁ N₂,?_⟩
  intro N hN d e hd he
  unfold rootSpatialLeibnizCost
  calc
    _ ≤ spatialFourierCost δ L hδ hL j * ((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_left (h₂ N ((le_max_right _ _).trans hN) d e hd he)
        (spatialFourierCost_nonneg δ L hδ hL j)
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_right (h₁ N ((le_max_left _ _).trans hN)) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem uniform_root_spatialLeibniz_sum_subpower (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∑ j ∈ Finset.range (n+1), rootSpatialLeibnizCost δ L hδ hL d e j) ≤ ((2:ℝ)^N)^eps := by
  classical
  choose K hK using (fun j => uniform_root_spatialLeibniz_subpower δ L hδ hL (half_pos heps) j)
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) ((n:ℝ)+1)
  refine ⟨max N₁ ((Finset.range (n+1)).sup K),?_⟩
  intro N hN d e hd he
  have hb : ∀ j ∈ Finset.range (n+1), rootSpatialLeibnizCost δ L hδ hL d e j ≤ ((2:ℝ)^N)^(eps/2) := by
    intro j hj
    exact hK j N ((Finset.le_sup hj).trans ((le_max_right _ _).trans hN)) d e hd he
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

end RootShellData

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_RootParentEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace RootShellData

theorem inversePhasedHF_finite_eq (d : RootShellData) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) {b : ℂ × (RootMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (d.indices))
    (v : ℝ) (Ψ : ℝ → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hΨW : ∀ x, Ψ x ≤ W) (hs : ∀ x, 4 < x → Ψ x = 0) (ξ : Plane) :
    d.inversePhasedHF v Ψ b.2 ξ ≠ ⊤ ∧
      (d.inversePhasedHF v Ψ b.2 ξ).toReal =
        sourceRadialSquareEnergy (0:ℝ) v Ψ (d.inversePhasedForm b.2 ξ) := by
  have hC : 0 ≤ symbolDerivativeConstant (2*j)^(2*j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  apply sourceParentHF_finite_eq _ _ _ _ _ d.left.ρ d.right.ρ
    (show (0:ℝ) < 1 by norm_num)
    (show (0:ℝ) < 1 by norm_num) _ _
    (spatialPhasedSymbol_measurable _ _ _ (d.endpointLeft_measurable b.2))
    (spatialPhasedSymbol_measurable _ _ _ (d.endpointRight_measurable b.2)) hC hC hW
    _ _ hΨW hs
  · intro x dir
    rw [spatialPhasedSymbol_norm]
    exact d.endpointLeft_norm hd j hb x dir
  · intro x dir
    rw [spatialPhasedSymbol_norm]
    exact d.endpointRight_norm he j hb x dir

theorem mainF_parent_energy (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
    (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
    (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2)
    (hcarry₁ : ∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) (hcarry₂ : ∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier)
    (hsep : ∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) (n : ℕ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ x, Ψ x ≤ W)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
      (d.inversePhasedHF d.N Ψ b.2 ξ).toReal ≤ H) :
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖d.mainF n r‖^2) ≤
      2*(∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j)^2*H := by
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hE := d.mainF_shell δ L hδ hL hd he hsig hL₁ hL₂ hcarry₁ hcarry₂ hsep n
    (B := ((2:ℝ)^(d.N:ℝ)/(2:ℝ)^(2*(d.N:ℝ)))*H) (by positivity) (by
      intro j hj b hb ξ
      have hdata := d.inversePhasedForm_data hd he j hb
      have hm : Measurable (d.inversePhasedForm b.2 ξ) :=
        hdata.1.comp (f := fun r : ℝ => (ξ,r)) (measurable_const.prodMk measurable_id)
      have hrad : sourceRadialSquareEnergy 0 d.N Ψ (d.inversePhasedForm b.2 ξ) ≤ H := by
        rw [← (d.inversePhasedHF_finite_eq hd he j hb d.N Ψ hW hΨW hsupport ξ).2]
        exact hH j hj b hb ξ
      simpa only [sub_zero] using dyadic_shell_le_radial_energy 0 d.N Ψ hΨ hpos hs hW hΨW hone _ hm
        (d.inversePhasedBound_nonneg j) (fun r => hdata.2 (ξ,r)) hrad)
  apply hE.trans_eq
  let S := ∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j
  change 2*(2:ℝ)^(d.N:ℝ)*S^2*(((2:ℝ)^(d.N:ℝ)/(2:ℝ)^(2*(d.N:ℝ)))*H) = 2*S^2*H
  have hp : (2:ℝ)^(d.N:ℝ)*(2:ℝ)^(d.N:ℝ) = (2:ℝ)^(2*(d.N:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  calc
    _ = 2*S^2*H*((2:ℝ)^(d.N:ℝ)*(2:ℝ)^(d.N:ℝ)/(2:ℝ)^(2*(d.N:ℝ))) := by ring
    _ = _ := by rw [hp,div_self (by positivity),mul_one]

end RootShellData

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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootEquation21
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace RootShellData

theorem uniform_parent_bound_oai {sig δ L eps T : ℝ}
    (hsig : 0 < sig) (hsmall : sig ≤ 1/4) (hδ : 0 < δ) (hL : 0 < L) (heps : 0 < eps) :
    ∃ n N₀ : ℕ, ∀ d : RootShellData,
    ∀ [IsProbabilityMeasure d.left.ρ] [IsProbabilityMeasure d.right.ρ],
    N₀ ≤ d.N → d.sig = sig → 0 < d.left.Q.side → 0 < d.right.Q.side →
    d.left.S.card ≤ (d.N+1)^3+1 → d.right.S.card ≤ (d.N+1)^3+1 →
    (∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2) →
    (∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) →
    0 < d.U.side → 0 < d.V.side →
    (∀ᵐ x ∂d.left.ρ, x ∈ d.U.carrier) → (∀ᵐ y ∂d.right.ρ, y ∈ d.V.carrier) →
    (∀ x ∈ d.U.carrier, ∀ y ∈ d.V.carrier, δ ≤ dist x y ∧ dist x y ≤ L) →
    ∀ s : ℝ, d.U.side ≤ s → d.V.side ≤ s → 100*s ≤ dist d.U.center d.V.center →
    ∀ Ψ : ℝ → ℝ, Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
    (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) →
    ∀ W : ℝ, 0 ≤ W → (∀ x, Ψ x ≤ W) → (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
    ∀ H : ℝ, 0 ≤ H →
    (∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
      (d.inversePhasedHF d.N Ψ b.2 ξ).toReal ≤ H) →
    (∫ r in Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
      ((2:ℝ)^d.N)^eps*H+((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₁,h₁⟩ := uniform_root_fourier_error (T := (T+3)/2) hsig hsmall hδ
  obtain ⟨N₂,h₂⟩ := uniform_root_spatialLeibniz_sum_subpower δ L hδ hL
    (show 0 < eps/4 by linarith) n
  obtain ⟨N₃,h₃⟩ := fixed_constant_absorbed (half_pos heps) 4
  refine ⟨n,max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro d inst₁ inst₂ hN hsig' hd he hc₁ hc₂ hl₁ hl₂ hU hV hcarry₁ hcarry₂ hsep s hUs hVs hstrong Ψ hΨ hpos hs W hW hΨW hone H hH0 hH
  subst sig
  have hN1 : N₁ ≤ d.N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : N₂ ≤ d.N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hN3 : N₃ ≤ d.N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hdist : ∀ᵐ z ∂d.left.ρ.prod d.right.ρ, δ ≤ dist z.1 z.2 := by
    filter_upwards [root_pair_ae_patches d.left d.right d.U d.V hcarry₁ hcarry₂] with z hz
    exact (hsep z.1 hz.1 z.2 hz.2).1
  let : IsFiniteMeasure d.measure := rootWeightedDistance_isFinite d.left d.right d.N d.sig hd he hδ hdist
  let R : ℝ := (2:ℝ)^d.N
  let μ := volume.restrict (Icc ((2:ℝ)^((d.N:ℝ)-1)) ((2:ℝ)^((d.N:ℝ)+1)))
  let err := R^(-((T+3)/2))
  have herr : ∀ᵐ r ∂μ, ‖charFun d.measure r-d.mainF n r‖ ≤ err := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (h₁ d.N hN1 d.left d.right hd he hc₁ hc₂ hl₁ hl₂ d.U d.V hU hV hcarry₁ hcarry₂
      (fun x hx y hy => (hsep x hx y hy).1) s hUs hVs hstrong r hr.1).2
  have hi : Integrable (fun r => ‖charFun d.measure r‖^2) μ :=
    integrable_norm_square_bounded μ _ measurable_charFun measureReal_nonneg
      (Eventually.of_forall (fun r => norm_charFun_le r))
  have hsq := (shell_square_approximation μ _ _
    (rootNormalizedF_measurable d.left d.right d.N d.sig n d.U d.V)
    hi (show 0 ≤ err by dsimp [err]; positivity) herr).2
  have hmain := d.mainF_parent_energy δ L hδ hL hd he hsig.le hl₁ hl₂ hcarry₁ hcarry₂ hsep n
    Ψ hΨ hpos hs hW hΨW hone hH0 hH
  let S := ∑ j ∈ Finset.range (n+1), d.cost δ L hδ hL j
  have hS : S ≤ R^(eps/4) := h₂ d.N hN2 d.left d.right hc₁ hc₂
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
        norm_num
        ring
  have herror : 2*err^2*μ.real univ ≤ R^(-T) := by
    simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] using
      high_shell_error_power d.N 0 ((le_max_left _ _).trans hN) (v := (d.N:ℝ)) le_rfl T
  calc
    _ ≤ 2*(∫ r, ‖d.mainF n r‖^2 ∂μ)+2*err^2*μ.real univ := hsq
    _ ≤ 2*(2*S^2*H)+R^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num)) herror
    _ ≤ R^eps*H+R^(-T) := by nlinarith [mul_le_mul_of_nonneg_right hcost hH0]

end RootShellData

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.RootShellData.uniform_parent_bound_oai := @OAI.PlanarFalconer.RootShellData.uniform_parent_bound_oai
