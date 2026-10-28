-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_single_stationary_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:17:09.37701+00:00
-- url     : https://prove2.me/submissions/df879c3c-ce75-4336-bc92-a897aac3e25d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

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
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SchwartzFourierMomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace

 theorem schwartz_iteratedDeriv_integrable (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    Integrable (iteratedDeriv n (φ : ℝ → ℂ)) := by
  apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 n).mono'
    ((φ.smooth ⊤).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).aestronglyMeasurable
  filter_upwards with x
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

 theorem schwartz_fourier_weighted_pointwise (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (ξ : ℝ) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤ fourierDerivativeL1 φ n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤)
    (fun k _ => schwartz_iteratedDeriv_integrable φ k) (n := n) (by simp)) ξ
  have hh := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n (φ : ℝ → ℂ)) ξ
  have hh' : ‖𝓕 (iteratedDeriv n (φ : ℝ → ℂ)) ξ‖ ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    simpa using! hh
  rw [he] at hh'
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one] at hh'
  have hh'' : (2*Real.pi)^n * (‖ξ‖^n*‖𝓕 φ ξ‖) ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_pow,Real.norm_eq_abs,SchwartzMap.fourier_coe]
    ring
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n)).mpr (by simpa [mul_comm] using hh'')

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CompactStationaryAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem complex_iteratedDeriv_tsupport (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset).trans ih

 theorem compact_derivative_integral_bound (φ : 𝓢(ℝ,ℂ)) {a b C : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C) :
    (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) ≤ C*(b-a) := by
  have he : (∫ x in Icc a b, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) =
      ∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply norm_eq_zero.mpr
    by_contra hn
    exact hx (hs (complex_iteratedDeriv_tsupport _ n (subset_closure hn)))
  have hh := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun x : ℝ => ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)
    (s := Icc a b) (C := C) (by simp) (Filter.Eventually.of_forall (fun x => by simpa using hC x))
  rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hh
  simpa [Real.volume_Icc,Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr hab] using hh

 theorem compact_fourierDerivativeL1_bound (φ : 𝓢(ℝ,ℂ)) {a b C D : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n) :
    fourierDerivativeL1 φ n ≤ C*(b-a)*D^n/(2*Real.pi)^n := by
  unfold fourierDerivativeL1
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (C*D^n)*(b-a) := compact_derivative_integral_bound φ hab hs n hC
    _ = _ := by ring

 theorem compact_smooth_to_schwartz {f : ℝ → ℂ} {a b : ℝ}
    (hs : tsupport f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = f := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  exact ⟨hc.toSchwartzMap hf,rfl⟩

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

 theorem stationaryChartCutoff_one {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    stationaryChartCutoff u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa [Real.closedBall_eq_Icc,stationaryChartCutoff] using hu

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

 theorem extendedStationaryInverse_eq {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    extendedStationaryInverse u = stationarySineInverse u := by
  simp [extendedStationaryInverse,stationaryChartCutoff_one hu]

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryJetOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem extendedStationaryInverse_zero : extendedStationaryInverse 0 = 0 := by
  rw [extendedStationaryInverse_eq (by norm_num)]
  simp [stationarySineInverse]

 theorem stationaryJet_order {n k : ℕ} (_hk : k ∈ Finset.range (n+1))
    (c : OrderedFinpartition (n-k)) : c.length ≤ n := by
  exact c.length_le.trans (Nat.sub_le _ _)

 theorem stationaryAmplitude_jet (n : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (stationaryAmplitude f) 0 = stationaryJet n f := by
  have hw : ContDiff ℝ ∞ (fun u => (stationaryWeight u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff
  have hfn : ContDiffAt ℝ n (f ∘ extendedStationaryInverse) 0 :=
    ((hf.comp extendedStationaryInverse_contDiff).of_le
      (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  have hwn : ContDiffAt ℝ n (fun u => (stationaryWeight u : ℂ)) 0 :=
    (hw.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  change iteratedDeriv n (fun u => (stationaryWeight u : ℂ) *
    (f ∘ extendedStationaryInverse) u) 0 = _
  rw [iteratedDeriv_fun_mul hwn hfn]
  unfold stationaryJet
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt
    extendedStationaryInverse_contDiff.contDiffAt
      (WithTop.coe_le_coe.mpr (show ((n-k:ℕ):ℕ∞) ≤ ⊤ from le_top))]
  simp only [extendedStationaryInverse_zero,Complex.real_smul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleDirectCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem fresnelCoefficient_half {Λ : ℝ} (hΛ : 0 < Λ) :
    fresnelCoefficient (Λ/2) = ((Λ^(-1/2:ℝ):ℝ):ℂ) *
      ((Real.sqrt (2*Real.pi):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) := by
  have he : Real.pi/(Λ/2) = (2*Real.pi)/Λ := by ring
  have hp : (Real.pi/(Λ/2))^(1/2:ℝ) = Λ^(-1/2:ℝ)*Real.sqrt (2*Real.pi) := by
    rw [he,Real.div_rpow (by positivity) hΛ.le,Real.sqrt_eq_rpow]
    rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring,Real.rpow_neg hΛ.le]
    ring
  simp only [fresnelCoefficient,hp,Complex.ofReal_mul]
  ring

 theorem quadratic_coefficient_normalization (k : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (d : ℂ) :
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/(Λ/2))^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹*d) =
    ((Λ⁻¹:ℝ):ℂ)^k * (((k.factorial:ℝ)⁻¹:ℝ):ℂ) * (-Complex.I/2)^k*d := by
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΛ' : (Λ:ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
  have he : (((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹) =
      ((Λ⁻¹:ℝ):ℂ)*(-Complex.I/2) := by
    push_cast
    field_simp
    simp [Complex.I_sq]
  calc
    _ = (((k.factorial:ℝ)⁻¹:ℝ):ℂ) *
        ((((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹)^k) * d := by
      simp only [Complex.ofReal_mul,Complex.ofReal_pow,mul_pow,inv_pow,pow_mul]
      ring
    _ = _ := by rw [he,mul_pow]; ring

 theorem stationary_expansion_direct_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ =
      ((Λ^(-1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        ((Λ⁻¹:ℝ):ℂ)^j * directStationaryOperator j f 0 := by
  rw [fresnelCoefficient_half hΛ,stationaryDerivativeExpansion,mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [quadratic_coefficient_normalization j hΛ,stationaryAmplitude_jet (2*j) hf]
  simp only [directStationaryOperator,add_zero]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FullCircleStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem fullCircleStationaryExpansion_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      Complex.exp (Complex.I*(Λ:ℂ))*((Λ^(-1/2:ℝ):ℝ):ℂ)*
        (∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j*directStationaryOperator j f 0) +
      conj (Complex.exp (Complex.I*(Λ:ℂ))*((Λ^(-1/2:ℝ):ℝ):ℂ)*
        (∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j*
          directStationaryOperator j (fun θ => conj (f (θ+Real.pi))) 0)) := by
  have hfs : ContDiff ℝ ∞ (fun θ => conj (f (θ+Real.pi))) :=
    Complex.conjCLE.contDiff.comp (hf.comp (contDiff_id.add contDiff_const))
  unfold fullCircleStationaryExpansion
  rw [stationary_expansion_direct_operators hΛ hf,stationary_expansion_direct_operators hΛ hfs]
  simp only [mul_assoc]

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

theorem sum_apply (ps : List AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (sum ps).apply f x = (ps.map (fun p => p.apply f x)).sum := by
  induction ps with
  | nil => simp [sum, apply]
  | cons p ps ih => simp [sum, apply, ih]

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

theorem derivative_bound (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ m+p.order, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (p.apply f) x‖ ≤ p.cost * (C*D^(m+p.order)) := by
  induction p generalizing f C m with
  | term c k =>
    simp only [apply, cost, order, iteratedDeriv_const_mul_field, iteratedDeriv_iterated,
      norm_mul]
    exact mul_le_mul_of_nonneg_left (hb (m+k) le_rfl) (norm_nonneg c)
  | add p q hp hq =>
    have hpord : m+p.order ≤ m+max p.order q.order := Nat.add_le_add_left (le_max_left _ _) _
    have hqord : m+q.order ≤ m+max p.order q.order := Nat.add_le_add_left (le_max_right _ _) _
    have hp' := hp hf hC m (fun k hk => hb k (hk.trans hpord))
    have hq' := hq hf hC m (fun k hk => hb k (hk.trans hqord))
    change ‖iteratedDeriv m (fun y => p.apply f y + q.apply f y) x‖ ≤ _
    rw [iteratedDeriv_fun_add (smooth_finite (p.apply_contDiff hf) m x)
      (smooth_finite (q.apply_contDiff hf) m x)]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ p.cost * (C*D^(m+max p.order q.order)) +
          q.cost * (C*D^(m+max p.order q.order)) := add_le_add
        (hp'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hpord) hC) p.cost_nonneg))
        (hq'.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hqord) hC) q.cost_nonneg))
      _ = _ := by simp only [cost, order]; ring
  | comp p q hp hq =>
    have hCq : 0 ≤ q.cost*C*D^q.order := by
      exact mul_nonneg (mul_nonneg q.cost_nonneg hC) (pow_nonneg (zero_le_one.trans hD) _)
    have hbq : ∀ k ≤ m+p.order,
        ‖iteratedDeriv k (q.apply f) x‖ ≤ (q.cost*C*D^q.order)*D^k := by
      intro k hk
      have h := hq hf hC k (fun l hl => hb l (by
        simp only [order]; omega))
      apply h.trans_eq
      rw [pow_add]
      ring
    have h := hp (q.apply_contDiff hf) hCq m hbq
    apply h.trans_eq
    simp only [cost, order, pow_add]
    ring

theorem derivative_bound_of_order_le (p : AngularDifferentialExpr) {n : ℕ}
    (hn : p.order ≤ n) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ m+n, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (p.apply f) x‖ ≤ p.cost * (C*D^(m+n)) := by
  have hm := Nat.add_le_add_left hn m
  exact (p.derivative_bound hf hC hD m x (fun k hk => hb k (hk.trans hm))).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hm) hC) p.cost_nonneg)

end AngularDifferentialExpr
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

theorem angularFiniteSum_apply {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (angularFiniteSum s p).apply f x = ∑ a ∈ s, (p a).apply f x := by
  simp [angularFiniteSum, AngularDifferentialExpr.sum_apply, List.map_map,
    Finset.sum_map_toList, Function.comp_def]

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

theorem stationaryJetExpr_apply (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (stationaryJetExpr n).apply f x = stationaryJet n (fun u => f (u+x)) := by
  simp only [stationaryJetExpr, angularFiniteSum_apply, AngularDifferentialExpr.apply,
    stationaryJet, iteratedDeriv_comp_add_const, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem directStationaryExpr_order (j : ℕ) : (directStationaryExpr j).order ≤ 2*j := by
  simpa [directStationaryExpr, AngularDifferentialExpr.order] using stationaryJetExpr_order (2*j)

theorem directStationaryExpr_apply (j : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (directStationaryExpr j).apply f x = directStationaryOperator j f x := by
  simp [directStationaryExpr, AngularDifferentialExpr.apply, stationaryJetExpr_apply,
    directStationaryOperator, stationaryLeadingConstant]

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphEndpointContinuity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem continuous_circle_of_direction {E : Type*} [TopologicalSpace E]
    (f : UnitCircle → E) (hf : Continuous (fun θ => f (sourceUnitDirection θ))) :
    Continuous f := by
  let A := Icc (-Real.pi) Real.pi
  let : CompactSpace A := isCompact_iff_compactSpace.mp (show IsCompact A from isCompact_Icc)
  let q : A → UnitCircle := fun θ => sourceUnitDirection θ
  have hq : Continuous q := continuous_sourceUnitDirection.comp continuous_subtype_val
  have hs : Function.Surjective q := by
    intro ω
    exact ⟨⟨sourceAngle ω, (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩,
      sourceUnitDirection_sourceAngle ω⟩
  exact (hq.isClosedMap.isQuotientMap hq hs).continuous_iff.mpr
    (hf.comp continuous_subtype_val)

theorem inheritedCircleSymbol_continuous {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Plane → ℂ) (x : Plane) :
    Continuous (inheritedCircleSymbol S b k Q ρ m N lam sig J i h x) :=
  continuous_circle_of_direction _
    (inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h x).continuous

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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_LinearNonstationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff RealInnerProductSpace

 theorem compact_fourier_nonstationary {f : ℝ → ℂ} {a z C D ξ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a z) (haz : a ≤ z)
    (hξ : ξ ≠ 0) (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n f x‖ ≤ C*D^n) :
    ‖𝓕 f ξ‖ ≤ C*(z-a)*D^n/((2*Real.pi)^n*‖ξ‖^n) := by
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hs hf
  have hs' : tsupport (φ : ℝ → ℂ) ⊆ Icc a z := by simpa [hφ] using hs
  have hC' : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n := by simpa [hφ] using hC
  have hh := (schwartz_fourier_weighted_pointwise φ n ξ).trans
    (compact_fourierDerivativeL1_bound φ haz hs' n hC')
  rw [SchwartzMap.fourier_coe,hφ] at hh
  have hpos : 0 < ‖ξ‖^n := pow_pos (norm_pos_iff.mpr hξ) _
  have hi : ‖𝓕 f ξ‖ ≤ (C*(z-a)*D^n/(2*Real.pi)^n)/‖ξ‖^n :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm (‖𝓕 f ξ‖)] using hh)
  simpa [div_div] using hi

 theorem compact_linear_phase_bound {f : ℝ → ℂ} {a z C D ξ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a z) (haz : a ≤ z)
    (hξ : ξ ≠ 0) (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n f x‖ ≤ C*D^n) :
    ‖∫ x : ℝ, Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(x:ℂ)*(ξ:ℂ))*f x‖ ≤
      C*(z-a)*D^n/((2*Real.pi)^n*‖ξ‖^n) := by
  have he : 𝓕 f ξ = ∫ x : ℝ,
      Complex.exp (-(2:ℂ)*(Real.pi:ℂ)*Complex.I*(x:ℂ)*(ξ:ℂ))*f x := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with x
    simp only [Real.inner_apply, smul_eq_mul]
    push_cast
    congr 2
    ring
  rw [← he]
  exact compact_fourier_nonstationary hf hs haz hξ n hC

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
-- module Solutions.OAIQ038_FA.Falconer_Radial_LinearRadialDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

theorem radialPhaseIntegral_nonzero {f : ℝ → ℂ} {a b C xi : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a b) (hab : a ≤ b)
    (hxi : xi ≠ 0) (n : ℕ) (hb : ∀ s, ‖iteratedDeriv n f s‖ ≤ C) :
    ‖radialPhaseIntegral f xi‖ ≤ C*(b-a)/|xi|^n := by
  have hp : (2:ℝ)*Real.pi ≠ 0 := by positivity
  have hh := compact_linear_phase_bound (ξ := -xi/(2*Real.pi)) (C := C) (D := 1)
    hf hs hab (div_ne_zero (neg_ne_zero.mpr hxi) hp) n (by simpa using hb)
  have he (s : ℝ) : -(2:ℂ)*(Real.pi:ℂ)*Complex.I*(s:ℂ)*((-xi/(2*Real.pi):ℝ):ℂ) =
      Complex.I*(xi:ℂ)*(s:ℂ) := by
    push_cast
    have hpc : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  simp_rw [he] at hh
  have hd : (2*Real.pi)^n*‖-xi/(2*Real.pi)‖^n = |xi|^n := by
    rw [Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos (by positivity : 0 < 2*Real.pi),div_pow]
    field_simp
  simpa only [radialPhaseIntegral,one_pow,mul_one,hd] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularRadialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem noncomparable_radial_frequency {dlarge dsmall t s : ℝ}
    (hsep : 2*dsmall ≤ dlarge) (ht : |t| ≤ dsmall) (hs : s = 1 ∨ s = -1) :
    dlarge/2 ≤ |s*dlarge+t| := by
  obtain ⟨ht1,ht2⟩ := abs_le.mp ht
  rcases hs with rfl | rfl
  · simp only [one_mul]
    linarith only [hsep, ht1, le_abs_self (dlarge+t)]
  · simp only [neg_one_mul]
    linarith only [hsep, ht2, neg_le_abs (-dlarge+t)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RadialStationaryProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem radialStationaryProfile_contDiff {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (p : ℝ) :
    ContDiff ℝ ∞ (radialStationaryProfile Ψ p) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hz : s = 0
  · subst s
    have he : radialStationaryProfile Ψ p =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0:ℝ) < 1/4)] with t ht
      have ht0 : Ψ t = 0 := by
        by_contra hn
        exact (not_lt_of_ge (hs t hn).1.le) ht
      simp [radialStationaryProfile,ht0]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp s
      (hΨ.contDiffAt.mul (contDiffAt_id.rpow_const_of_ne hz))

theorem radialStationaryProfile_tsupport {Ψ : ℝ → ℝ}
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (p : ℝ) :
    tsupport (radialStationaryProfile Ψ p) ⊆ Icc (1/4:ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hn : Ψ t ≠ 0 := by
    intro hz
    exact ht (by simp [radialStationaryProfile,hz])
  exact Ioo_subset_Icc_self (hs t hn)

theorem compact_complex_derivatives_bounded {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {K : Set ℝ} (hK : IsCompact K) (hs : tsupport f ⊆ K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s, ‖iteratedDeriv j f s‖ ≤ C := by
  have hc (j : ℕ) : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j (WithTop.coe_le_coe.mpr (show (j:ℕ∞) ≤ ⊤ from le_top))
  choose C hC using fun j => hK.exists_bound_of_continuousOn (hc j).continuousOn
  let B := ∑ j ∈ Finset.range (n+1), max 0 (C j)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨B,hB,?_⟩
  intro j hj s
  by_cases hmem : s ∈ K
  · apply (hC j s hmem).trans
    apply (le_max_right 0 (C j)).trans
    exact Finset.single_le_sum (fun _ _ => le_max_left _ _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · have hz : iteratedDeriv j f s = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hmem (hs (complex_iteratedDeriv_tsupport f j ht)))
    simpa only [hz,norm_zero] using hB

theorem radialStationaryProfile_derivatives {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (p : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s, ‖iteratedDeriv j (radialStationaryProfile Ψ p) s‖ ≤ C :=
  compact_complex_derivatives_bounded (radialStationaryProfile_contDiff hΨ hs p)
    isCompact_Icc (radialStationaryProfile_tsupport hs p) n

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_NormalizedStationaryJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem directStationaryOperator_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (j : ℕ) (θ : ℝ)
    (hb : ∀ k ≤ 2*j, ‖iteratedDeriv k f θ‖ ≤ C*D^k) :
    ‖directStationaryOperator j f θ‖ ≤ (directStationaryExpr j).cost*C*D^(2*j) := by
  have hh := (directStationaryExpr j).derivative_bound_of_order_le (directStationaryExpr_order j)
    hf hC hD 0 θ (by simpa only [zero_add] using hb)
  simpa only [iteratedDeriv_zero,zero_add,directStationaryExpr_apply,mul_assoc] using hh

theorem normalizedStationaryJet_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D Λ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hΛ : 0 < Λ) (hscale : D^2 ≤ Λ)
    (j : ℕ) (θ : ℝ) (hb : ∀ k ≤ 2*j, ‖iteratedDeriv k f θ‖ ≤ C*D^k) :
    ‖normalizedStationaryJet j f θ Λ‖ ≤ (directStationaryExpr j).cost*C := by
  have hp : (D^2/Λ)^j ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hΛ).mpr hscale)
  have hcost := (directStationaryExpr j).cost_nonneg
  calc
    _ = (Λ⁻¹)^j*‖directStationaryOperator j f θ‖ := by
      simp only [normalizedStationaryJet,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hΛ)]
    _ ≤ (Λ⁻¹)^j*((directStationaryExpr j).cost*C*D^(2*j)) :=
      mul_le_mul_of_nonneg_left (directStationaryOperator_bound hf hC hD j θ hb) (by positivity)
    _ = ((directStationaryExpr j).cost*C)*(D^2/Λ)^j := by
      rw [div_pow,pow_mul]
      ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg hcost hC)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

 theorem signedStationaryJet_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D Λ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hΛ : 0 < Λ) (hscale : D^2 ≤ Λ)
    (plus : Bool) (j : ℕ) (θ : ℝ)
    (hb : ∀ k ≤ 2*j, ∀ t, ‖iteratedDeriv k f t‖ ≤ C*D^k) :
    ‖signedStationaryJet plus j f θ Λ‖ ≤ (directStationaryExpr j).cost*C := by
  cases plus
  · simp only [signedStationaryJet,Bool.false_eq_true,↓reduceIte,Complex.norm_conj]
    have hfs : ContDiff ℝ ∞ (fun t => f (t+Real.pi)) := hf.comp (contDiff_id.add contDiff_const)
    apply normalizedStationaryJet_bound (Complex.conjCLE.contDiff.comp hfs) hC hD hΛ hscale
    intro k hk
    change ‖iteratedDeriv k (fun t => conj (f (t+Real.pi))) θ‖ ≤ _
    rw [complex_iteratedDeriv_conj hfs,Complex.norm_conj,iteratedDeriv_comp_add_const]
    exact hb k hk _
  · simp only [signedStationaryJet,↓reduceIte]
    exact normalizedStationaryJet_bound hf hC hD hΛ hscale j θ (fun k hk => hb k hk θ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

 theorem fullCircleStationaryExpansion_signed {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      (∑ j ∈ Finset.range (n+1), signedStationaryTerm true j f Λ) +
      (∑ j ∈ Finset.range (n+1), signedStationaryTerm false j f Λ) := by
  rw [fullCircleStationaryExpansion_operators hΛ hf]
  simp only [signedStationaryTerm,stationarySign,signedStationaryJet,normalizedStationaryJet,
    ↓reduceIte,Bool.false_eq_true,one_mul,neg_one_mul,
    map_mul,map_sum,map_pow,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I,
    Complex.ofReal_neg,Finset.mul_sum,mul_assoc]
  simp [neg_mul,mul_neg]

 theorem signedStationaryJet_scale (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ A s : ℝ) :
    signedStationaryJet plus j f θ (A*s) = ((s⁻¹:ℝ):ℂ)^j * signedStationaryJet plus j f θ A := by
  cases plus <;> simp only [signedStationaryJet,normalizedStationaryJet,↓reduceIte,
    Bool.false_eq_true,mul_inv_rev,Complex.ofReal_mul,mul_pow,map_mul,map_pow,Complex.conj_ofReal]
  all_goals ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryProductIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem fullCircleStationaryExpansion_sum {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      ∑ p ∈ stationarySignedIndices n, signedStationaryTerm p.1 p.2 f Λ := by
  rw [fullCircleStationaryExpansion_signed hΛ hf]
  simp [stationarySignedIndices,Finset.sum_product,add_comm]

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_SingleStationaryRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem singleStationaryRadial_derivatives {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (j n : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {C D A : ℝ}, 0 ≤ C → 1 ≤ D → 0 < A →
    D^2 ≤ A → ∀ plus : Bool, ∀ θ : ℝ,
    (∀ l ≤ 2*j, ∀ t, ‖iteratedDeriv l f t‖ ≤ C*D^l) →
    ContDiff ℝ ∞ (singleStationaryRadialCoefficient Ψ plus j f θ A) ∧
    tsupport (singleStationaryRadialCoefficient Ψ plus j f θ A) ⊆ Icc (1/4:ℝ) 4 ∧
    ∀ l ≤ n, ∀ s, ‖iteratedDeriv l (singleStationaryRadialCoefficient Ψ plus j f θ A) s‖ ≤
      H*C*A^(-1/2:ℝ) := by
  obtain ⟨P,hP,hp⟩ := radialStationaryProfile_derivatives hΨ hs (-((j:ℝ)+1/2)) n
  have hj := (directStationaryExpr j).cost_nonneg
  refine ⟨P*(directStationaryExpr j).cost,by positivity,?_⟩
  intro f hf C D A hC hD hA hDA plus θ hb
  refine ⟨contDiff_const.mul (radialStationaryProfile_contDiff hΨ hs _),
    tsupport_mul_subset_right.trans (radialStationaryProfile_tsupport hs _),?_⟩
  intro l hl s
  change ‖iteratedDeriv l (fun t =>
    (((A^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus j f θ A) *
      radialStationaryProfile Ψ (-((j:ℝ)+1/2)) t) s‖ ≤ _
  rw [iteratedDeriv_const_mul_field]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hA _)]
  calc
    _ ≤ A^(-1/2:ℝ)*((directStationaryExpr j).cost*C)*P := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left (signedStationaryJet_bound hf hC hD hA hDA plus j θ hb)
          (by positivity)) (hp l hl s) (norm_nonneg _) (by positivity)
    _ = _ := by ring

 theorem singleStationaryRadial_noncomparable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (j n : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {C D R large small t sign : ℝ},
    0 ≤ C → 1 ≤ D → 0 < R → 0 < large → 2*small ≤ large → |t| ≤ small →
    (sign = 1 ∨ sign = -1) → D^2 ≤ R*large → ∀ plus : Bool, ∀ θ : ℝ,
    (∀ l ≤ 2*j, ∀ u, ‖iteratedDeriv l f u‖ ≤ C*D^l) →
    ‖radialPhaseIntegral (singleStationaryRadialCoefficient Ψ plus j f θ (R*large))
      (R*(sign*large+t))‖ ≤ H*C*(R*large)^(-1/2:ℝ)/(R*large/2)^n := by
  obtain ⟨H,hH,hh⟩ := singleStationaryRadial_derivatives hΨ hs j n
  refine ⟨H*(15/4),by positivity,?_⟩
  intro f hf C D R large small t sign hC hD hR hl hsep ht hsign hDA plus θ hb
  obtain ⟨ha,hsa,hba⟩ := hh hf hC hD (mul_pos hR hl) hDA plus θ hb
  have hfreq : R*large/2 ≤ |R*(sign*large+t)| := by
    rw [abs_mul,abs_of_pos hR]
    have hx := mul_le_mul_of_nonneg_left (noncomparable_radial_frequency hsep ht hsign) hR.le
    linarith
  have hpos : 0 < R*large/2 := by positivity
  have hne : R*(sign*large+t) ≠ 0 := abs_pos.mp (hpos.trans_le hfreq)
  have hx := radialPhaseIntegral_nonzero ha hsa (by norm_num) hne n (hba n le_rfl)
  apply hx.trans
  have hnum : H*C*(R*large)^(-1/2:ℝ)*((4:ℝ)-1/4) =
      (H*(15/4))*C*(R*large)^(-1/2:ℝ) := by ring
  rw [hnum]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hpos n)
    (pow_le_pow_left₀ hpos.le hfreq n)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SingleStationaryIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem singleStationaryRadialCoefficient_eq (Ψ : ℝ → ℝ) (plus : Bool)
    (j : ℕ) (f : ℝ → ℂ) (θ : ℝ) {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    singleStationaryRadialCoefficient Ψ plus j f θ A s =
      (Ψ s : ℂ) * (((A*s)^(-1/2:ℝ):ℝ):ℂ) * signedStationaryJet plus j f θ (A*s) := by
  have hj : (s⁻¹)^j = s^(-(j:ℝ)) := by
    rw [Real.rpow_neg hs.le,Real.rpow_natCast,inv_pow]
  have hp : s^(-((j:ℝ)+1/2)) = s^(-1/2:ℝ)*(s⁻¹)^j := by
    rw [hj,← Real.rpow_add hs]
    congr 1
    ring
  simp only [singleStationaryRadialCoefficient,radialStationaryProfile,
    signedStationaryJet_scale,Real.mul_rpow hA.le hs.le,Complex.ofReal_mul,hp]
  push_cast
  ring

theorem singleStationaryRadial_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ A ξ : ℝ) :
    Integrable (fun s : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(s:ℂ))*
      singleStationaryRadialCoefficient Ψ plus j f θ A s) := by
  have hc : HasCompactSupport (radialStationaryProfile Ψ (-((j:ℝ)+1/2))) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (radialStationaryProfile_tsupport hs _)
  have hcont : Continuous (singleStationaryRadialCoefficient Ψ plus j f θ A) :=
    continuous_const.mul (radialStationaryProfile_contDiff hΨ hs _).continuous
  exact ((by fun_prop : Continuous (fun s : ℝ => Complex.exp (Complex.I*(ξ:ℂ)*(s:ℂ)))).mul
    hcont).integrable_of_hasCompactSupport hc.mul_left.mul_left

theorem stationary_single_radial_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) {R large : ℝ}
    (hR : 0 < R) (hl : 0 < large) (t : ℝ) :
    R⁻¹ • (∫ r : ℝ, Ψ (r/R) • (fullCircleStationaryExpansion (r*large) f n *
      Complex.exp (Complex.I*(r:ℂ)*(t:ℂ)))) =
    ∑ p ∈ stationarySignedIndices n,
      radialPhaseIntegral (singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large))
        (R*(stationarySign p.1*large+t)) := by
  let H := fun (p : Bool × ℕ) (s : ℝ) =>
    Complex.exp (Complex.I*((R*(stationarySign p.1*large+t):ℝ):ℂ)*(s:ℂ))*
      singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large) s
  have he (s : ℝ) : Ψ s • (fullCircleStationaryExpansion (R*s*large) f n *
      Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t:ℂ))) =
      ∑ p ∈ stationarySignedIndices n, H p s := by
    by_cases hn : Ψ s = 0
    · simp [hn,H,singleStationaryRadialCoefficient,radialStationaryProfile]
    · have hsp : 0 < s := lt_trans (by norm_num : (0:ℝ) < 1/4) (hs s hn).1
      rw [fullCircleStationaryExpansion_sum hf (by positivity)]
      simp only [Complex.real_smul,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [H]
      rw [singleStationaryRadialCoefficient_eq Ψ p.1 p.2 f 0 (mul_pos hR hl) hsp]
      have hex : Complex.exp (Complex.I*((stationarySign p.1*(R*s*large):ℝ):ℂ)) *
          Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t:ℂ)) =
          Complex.exp (Complex.I*((R*(stationarySign p.1*large+t):ℝ):ℂ)*(s:ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      unfold signedStationaryTerm
      rw [← hex]
      simp only [mul_assoc]
      ring_nf
  calc
    _ = ∫ s : ℝ, Ψ s • (fullCircleStationaryExpansion (R*s*large) f n *
        Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t:ℂ))) := by
      have hh := Measure.integral_comp_mul_left (fun r : ℝ => Ψ (r/R) •
        (fullCircleStationaryExpansion (r*large) f n * Complex.exp (Complex.I*(r:ℂ)*(t:ℂ)))) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,abs_of_pos (inv_pos.mpr hR)] using hh.symm
    _ = ∫ s : ℝ, ∑ p ∈ stationarySignedIndices n, H p s := by simp_rw [he]
    _ = _ := by
      rw [integral_finsetSum _ (fun p _ => singleStationaryRadial_integrable hΨ hs p.1 p.2 f 0 (R*large) _)]
      rfl

theorem stationary_single_radial_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {C D R large small t : ℝ}, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
    2*small ≤ large → |t| ≤ small → D^2 ≤ R*large →
    (∀ l ≤ 2*n, ∀ u, ‖iteratedDeriv l f u‖ ≤ C*D^l) →
    ‖R⁻¹ • (∫ r : ℝ, Ψ (r/R) • (fullCircleStationaryExpansion (r*large) f n *
      Complex.exp (Complex.I*(r:ℂ)*(t:ℂ))))‖ ≤
      H*C*(R*large)^(-1/2:ℝ)/(R*large/2)^q := by
  choose H hH hb using fun j => singleStationaryRadial_noncomparable hΨ hs j q
  refine ⟨∑ p ∈ stationarySignedIndices n, H p.2,
    Finset.sum_nonneg (fun p _ => hH p.2),?_⟩
  intro f hf C D R large small t hC hD hR hl hsep ht hDA hbf
  rw [stationary_single_radial_integral hΨ hs hf n hR hl t]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ stationarySignedIndices n, H p.2*C*(R*large)^(-1/2:ℝ)/(R*large/2)^q := by
      apply Finset.sum_le_sum
      intro p hp
      have hj : p.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      exact hb p.2 hf hC hD hR hl hsep ht
        (by cases p.1 <;> simp [stationarySign]) hDA p.1 0
        (fun l hl => hbf l (hl.trans (Nat.mul_le_mul_left 2 hj)))
    _ = _ := by simp only [Finset.sum_mul,Finset.sum_div]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SingleStationaryAngular
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem stationary_single_angular_integral {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) {R large : ℝ}
    (hR : 0 < R) (hl : 0 < large) (g : UnitCircle → ℂ)
    (hg : Measurable g) {E : ℝ} (hE : 0 ≤ E) (hb : ∀ u, ‖g u‖ ≤ E)
    (t : UnitCircle → ℝ) (ht : Measurable t) :
    R⁻¹ • (∫ r : ℝ, Ψ (r/R) • (fullCircleStationaryExpansion (r*large) f n *
      (∫ u, Complex.exp (Complex.I*(r:ℂ)*(t u:ℂ))*g u ∂sourceArcLength))) =
    ∫ u, (∑ p ∈ stationarySignedIndices n,
      radialPhaseIntegral (singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large))
        (R*(stationarySign p.1*large+t u)))*g u ∂sourceArcLength := by
  let a := fun p : Bool × ℕ => singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large)
  let H := fun (p : Bool × ℕ) (s : ℝ) (u : UnitCircle) =>
    (Complex.exp (Complex.I*((R*(stationarySign p.1*large+t u):ℝ):ℂ)*(s:ℂ))*a p s)*g u
  have ha (p : Bool × ℕ) : Continuous (a p) :=
    continuous_const.mul (radialStationaryProfile_contDiff hΨ hs _).continuous
  have hsa (p : Bool × ℕ) : tsupport (a p) ⊆ Icc (1/4:ℝ) 4 :=
    tsupport_mul_subset_right.trans (radialStationaryProfile_tsupport hs _)
  have hi (p : Bool × ℕ) : Integrable (fun z : ℝ × UnitCircle => H p z.1 z.2)
      (volume.prod sourceArcLength) := by
    have hc : HasCompactSupport (a p) := isCompact_Icc.of_isClosed_subset isClosed_closure (hsa p)
    obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous (ha p)
    apply compact_finite_spatial_integrable volume sourceArcLength measurableSet_Icc
      isCompact_Icc.measure_lt_top (by dsimp [H]; fun_prop)
      (mul_nonneg ((norm_nonneg (a p 0)).trans (hC 0)) hE)
    · intro z
      have hn : ‖Complex.exp (Complex.I*((R*(stationarySign p.1*large+t z.2):ℝ):ℂ)*(z.1:ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      dsimp [H]
      simp only [norm_mul,hn,one_mul]
      exact mul_le_mul (hC z.1) (hb z.2) (norm_nonneg _) ((norm_nonneg (a p 0)).trans (hC 0))
    · intro z hz
      apply hsa p
      apply subset_closure
      change a p z.1 ≠ 0
      intro he
      exact hz (by simp [H,he])
  have he (s : ℝ) (u : UnitCircle) :
      Ψ s • (fullCircleStationaryExpansion (R*s*large) f n *
        (Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t u:ℂ))*g u)) =
      ∑ p ∈ stationarySignedIndices n, H p s u := by
    by_cases hn : Ψ s = 0
    · simp [hn,H,a,singleStationaryRadialCoefficient,radialStationaryProfile]
    · have hsp : 0 < s := lt_trans (by norm_num : (0:ℝ) < 1/4) (hs s hn).1
      rw [fullCircleStationaryExpansion_sum hf (by positivity)]
      simp only [Complex.real_smul,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [H,a]
      rw [singleStationaryRadialCoefficient_eq Ψ p.1 p.2 f 0 (mul_pos hR hl) hsp]
      have hex : Complex.exp (Complex.I*((stationarySign p.1*(R*s*large):ℝ):ℂ)) *
          Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t u:ℂ)) =
          Complex.exp (Complex.I*((R*(stationarySign p.1*large+t u):ℝ):ℂ)*(s:ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      unfold signedStationaryTerm
      rw [← hex]
      simp only [mul_assoc]
      ring_nf
  calc
    _ = ∫ s : ℝ, Ψ s • (fullCircleStationaryExpansion (R*s*large) f n *
        (∫ u, Complex.exp (Complex.I*((R*s:ℝ):ℂ)*(t u:ℂ))*g u ∂sourceArcLength)) := by
      have hh := Measure.integral_comp_mul_left (fun r : ℝ => Ψ (r/R) •
        (fullCircleStationaryExpansion (r*large) f n *
          (∫ u, Complex.exp (Complex.I*(r:ℂ)*(t u:ℂ))*g u ∂sourceArcLength))) R
      simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,abs_of_pos (inv_pos.mpr hR)] using hh.symm
    _ = ∫ s : ℝ, ∫ u, ∑ p ∈ stationarySignedIndices n, H p s u ∂sourceArcLength := by
      simp_rw [← he,integral_smul,integral_const_mul]
    _ = ∫ u, (∫ s : ℝ, ∑ p ∈ stationarySignedIndices n, H p s u) ∂sourceArcLength :=
      integral_integral_swap (integrable_finsetSum _ (fun p _ => hi p))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [integral_finsetSum _ (fun p _ =>
        (singleStationaryRadial_integrable hΨ hs p.1 p.2 f 0 (R*large) _).mul_const (g u))]
      simp only [H,integral_mul_const,Finset.sum_mul]
      rfl

theorem stationary_single_angular_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {C D R large small : ℝ}, 0 ≤ C → 1 ≤ D → 0 < R → 0 < large →
    2*small ≤ large → D^2 ≤ R*large →
    (∀ l ≤ 2*n, ∀ u, ‖iteratedDeriv l f u‖ ≤ C*D^l) →
    ∀ (g : UnitCircle → ℂ), Measurable g → ∀ {E : ℝ}, 0 ≤ E → (∀ u, ‖g u‖ ≤ E) →
    ∀ (t : UnitCircle → ℝ), Measurable t → (∀ u, |t u| ≤ small) →
    ‖R⁻¹ • (∫ r : ℝ, Ψ (r/R) • (fullCircleStationaryExpansion (r*large) f n *
      (∫ u, Complex.exp (Complex.I*(r:ℂ)*(t u:ℂ))*g u ∂sourceArcLength)))‖ ≤
      H*C*E*(R*large)^(-1/2:ℝ)/(R*large/2)^q := by
  obtain ⟨H,hH,hb⟩ := stationary_single_radial_bound hΨ hs n q
  refine ⟨H*sourceArcLength.real univ,by positivity,?_⟩
  intro f hf C D R large small hC hD hR hl hsep hDA hbf g hg E hE hbg t ht hbt
  rw [stationary_single_angular_integral hΨ hs hf n hR hl g hg hE hbg t ht]
  have hbound (u : UnitCircle) :
      ‖(∑ p ∈ stationarySignedIndices n,
        radialPhaseIntegral (singleStationaryRadialCoefficient Ψ p.1 p.2 f 0 (R*large))
          (R*(stationarySign p.1*large+t u)))*g u‖ ≤
        (H*C*(R*large)^(-1/2:ℝ)/(R*large/2)^q)*E := by
    rw [norm_mul,← stationary_single_radial_integral hΨ hs hf n hR hl (t u)]
    exact mul_le_mul (hb hf hC hD hR hl hsep (hbt u) hDA hbf) (hbg u) (norm_nonneg _) (by positivity)
  have hh := norm_integral_le_of_norm_le_const (μ := sourceArcLength) (Filter.Eventually.of_forall hbound)
  apply hh.trans_eq
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualSingleStationaryKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem unit_direction_inner_bound (u : UnitCircle) (z : Plane) :
    |inner ℝ (u:Plane) z| ≤ ‖z‖ := by
  simpa only [u.property,one_mul] using abs_real_inner_le_norm (u:Plane) z

theorem uniform_actual_single_stationary_kernel_oai {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K n q : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ) (x y : Fin 2 → Plane),
    (∀ l, ‖hsp l (x l)‖ ≤ 1) → (∀ l, ‖hsp l (y l)‖ ≤ 1) →
    ∀ v : ℝ, 0 < ‖x 0-y 0‖ → 2*‖x 1-y 1‖ ≤ ‖x 0-y 0‖ →
    sourceSymbolScale N sig L^2 ≤ (2:ℝ)^v*‖x 0-y 0‖ →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    ‖angularSingleStationaryKernel (β 0) (β 1) n v Ψ ![x 0,y 0,x 1,y 1]‖ ≤
      H*((2:ℝ)^v*‖x 0-y 0‖)^(-1/2:ℝ)/((2:ℝ)^v*‖x 0-y 0‖/2)^q := by
  obtain ⟨H,hH,hkernel⟩ := stationary_single_angular_bound hΨ hs n q
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_pair_derivatives hsig K (2*n)
  let B := symbolDerivativeConstant K^K
  have hB : 0 ≤ B := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  refine ⟨H*C*B^2,by positivity,N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i hsp x y hx hy v hl hsep hD
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  let f := fun t => β 0 (x 0) (sourceUnitDirection t)*conj (β 0 (y 0) (sourceUnitDirection t))
  have hp := h₀ N hN (S 0) (b 0) (k 0) (hcard 0) (hK 0) L (hL 0)
    (Q 0) (hQ 0) (ρ 0) (m 0) (lam 0) (J 0) (i 0) (hsp 0) (x 0) (y 0) (hx 0) (hy 0)
  have hfs : ContDiff ℝ ∞ (fun t => f (t+angularPairAngle (x 0) (y 0))) :=
    hp.1.comp (contDiff_id.add contDiff_const)
  have hbs (j : ℕ) (hj : j ≤ 2*n) (t : ℝ) :
      ‖iteratedDeriv j (fun u => f (u+angularPairAngle (x 0) (y 0))) t‖ ≤ C*sourceSymbolScale N sig L^j := by
    rw [iteratedDeriv_comp_add_const]
    exact hp.2 j hj _
  let g := fun u => β 1 (x 1) u*conj (β 1 (y 1) u)
  have hg : Measurable g := by
    have hc (z : Plane) : Continuous (β 1 z) :=
      inheritedCircleSymbol_continuous _ _ _ _ (hQ 1) _ _ _ _ _ _ _ _ z
    exact ((hc (x 1)).mul (Complex.continuous_conj.comp (hc (y 1)))).measurable
  have hbg (u : UnitCircle) : ‖g u‖ ≤ B^2 := by
    have hbx := inheritedCircleSymbol_norm_le (S 1) (b 1) (k 1) (Q 1) (hQ 1)
      (ρ 1) (m 1) N (lam 1) sig (J 1) (i 1) (hsp 1) K (hK 1) (x 1) (hx 1) u
    have hby := inheritedCircleSymbol_norm_le (S 1) (b 1) (k 1) (Q 1) (hQ 1)
      (ρ 1) (m 1) N (lam 1) sig (J 1) (i 1) (hsp 1) K (hK 1) (y 1) (hy 1) u
    simpa only [g,norm_mul,Complex.norm_conj,pow_two] using
      mul_le_mul hbx hby (norm_nonneg _) hB
  exact hkernel hfs hC (sourceSymbolScale_one_le N hsig.le L)
    (by positivity : (0:ℝ) < (2:ℝ)^v) hl hsep hD hbs g hg (sq_nonneg B) hbg
    (fun u : UnitCircle => inner ℝ (u:Plane) (x 1-y 1)) (by fun_prop)
    (fun u => unit_direction_inner_bound u _)

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_single_stationary_kernel_oai := @OAI.PlanarFalconer.uniform_actual_single_stationary_kernel_oai
