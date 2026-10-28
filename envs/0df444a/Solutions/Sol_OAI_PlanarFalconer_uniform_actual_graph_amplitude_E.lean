-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_graph_amplitude_E
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:29:38.489491+00:00
-- url     : https://prove2.me/submissions/b44621db-ed6e-4d2d-a466-dd92a9988450

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

 theorem iteratedDeriv_tsupport {f : ℝ → ℝ} (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularBinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff Topology

theorem angularBinKernel_contDiff : ContDiff ℝ ∞ angularBinKernel :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem angularBinKernel_compact : HasCompactSupport angularBinKernel :=
  isCompact_Icc.of_isClosed_subset isClosed_closure angularBinKernel_tsupport

theorem angularBinKernel_translate_zero (t : ℝ) (k : ℤ)
    (hk : k ≠ ⌊t⌋ ∧ k ≠ ⌊t⌋+1) : angularBinKernel (t-k) = 0 := by
  have hlow := Int.floor_le t
  have hhigh := Int.lt_floor_add_one t
  by_cases h : k ≤ ⌊t⌋-1
  · apply angularBinKernel_zero_right
    have hh : (k : ℝ) ≤ (⌊t⌋ : ℝ)-1 := by exact_mod_cast h
    linarith
  · apply angularBinKernel_zero_left
    have hh : ⌊t⌋+2 ≤ k := by omega
    have hh : (⌊t⌋ : ℝ)+2 ≤ (k : ℝ) := by exact_mod_cast hh
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularBinSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Filter
open scoped ContDiff Topology

theorem angularBinSelection_two_terms (p : ℤ → Prop) (t : ℝ) :
    angularBinSelection p t =
      (if p ⌊t⌋ then angularBinKernel (t-(⌊t⌋ : ℤ)) else 0) +
      (if p (⌊t⌋+1) then angularBinKernel (t-(⌊t⌋+1 : ℤ)) else 0) := by
  classical
  unfold angularBinSelection
  rw [tsum_eq_sum (s := {⌊t⌋, ⌊t⌋+1})]
  · simp [show ⌊t⌋ ≠ ⌊t⌋+1 by omega]
  · intro k hk
    have hz := angularBinKernel_translate_zero t k (by simpa using hk)
    simp [hz]

theorem angularBinSelection_local (p : ℤ → Prop) (t : ℝ) :
    angularBinSelection p =ᶠ[𝓝 t] (fun u =>
      ∑ k ∈ Finset.Icc (⌊t⌋-2) (⌊t⌋+3), if p k then angularBinKernel (u-k) else 0) := by
  classical
  filter_upwards [Ioo_mem_nhds (show t-1 < t by linarith) (show t < t+1 by linarith)] with u hu
  unfold angularBinSelection
  apply tsum_eq_sum
  intro k hk
  have hz : angularBinKernel (u-k) = 0 := by
    have hk : k < ⌊t⌋-2 ∨ ⌊t⌋+3 < k := by simpa only [Finset.mem_Icc, not_and_or, not_le] using hk
    rcases hk with hk | hk
    · apply angularBinKernel_zero_right
      have hc : (k : ℝ) < (⌊t⌋ : ℝ)-2 := by exact_mod_cast hk
      linarith [Int.floor_le t, hu.1]
    · apply angularBinKernel_zero_left
      have hc : (⌊t⌋ : ℝ)+3 < (k : ℝ) := by exact_mod_cast hk
      linarith [Int.lt_floor_add_one t, hu.2]
  simp [hz]

theorem angularBinSelection_contDiff (p : ℤ → Prop) : ContDiff ℝ ∞ (angularBinSelection p) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro t
  apply ContDiffAt.congr_of_eventuallyEq _ (angularBinSelection_local p t)
  apply ContDiff.contDiffAt
  apply ContDiff.sum
  intro k _
  by_cases hk : p k
  · simp only [hk, ↓reduceIte]
    exact angularBinKernel_contDiff.comp (contDiff_id.sub contDiff_const)
  · simp only [hk, ↓reduceIte]
    exact contDiff_const

theorem angularBinKernel_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv j angularBinKernel t‖ ≤ C := by
  have hc : HasCompactSupport (iteratedDeriv j angularBinKernel) :=
    angularBinKernel_compact.of_isClosed_subset isClosed_closure (iteratedDeriv_tsupport j)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous
    (angularBinKernel_contDiff.continuous_iteratedDeriv j (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

theorem angularBinSelection_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℤ → Prop) (t : ℝ),
      ‖iteratedDeriv j (angularBinSelection p) t‖ ≤ C := by
  classical
  obtain ⟨C, hC0, hC⟩ := angularBinKernel_derivative_bound j
  refine ⟨6*C, by positivity, ?_⟩
  intro p t
  rw [EventuallyEq.iteratedDeriv_eq j (angularBinSelection_local p t)]
  have hf (k : ℤ) : ContDiff ℝ ∞ (fun u => if p k then angularBinKernel (u-k) else 0) := by
    by_cases hk : p k
    · simp only [hk, ↓reduceIte]
      exact angularBinKernel_contDiff.comp (contDiff_id.sub contDiff_const)
    · simp only [hk, ↓reduceIte]
      exact contDiff_const
  rw [iteratedDeriv_fun_sum (fun k _ => ((hf k).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt)]
  calc
    _ ≤ ∑ k ∈ Finset.Icc (⌊t⌋-2) (⌊t⌋+3), C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : p k
      · simp only [hk, ↓reduceIte, iteratedDeriv_comp_sub_const]
        exact hC _
      · simpa only [hk, ↓reduceIte, iteratedDeriv_fun_const_zero, norm_zero] using hC0
    _ = _ := by
      have hcard : (Finset.Icc (⌊t⌋-2) (⌊t⌋+3)).card = 6 := by
        rw [Int.card_Icc]
        omega
      simp [hcard]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_PeriodicAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set
open scoped ContDiff Topology

theorem angularBinSelection_periodic (p : ℤ → Prop) (n : ℤ)
    (hp : ∀ k, p (k+n) ↔ p k) : Function.Periodic (angularBinSelection p) (n : ℝ) := by
  intro t
  unfold angularBinSelection
  rw [← (Equiv.addRight n).tsum_eq]
  apply tsum_congr
  intro k
  change (if p (k+n) then angularBinKernel (t+(n:ℝ)-(k+n : ℤ)) else 0) = _
  rw [show t+(n:ℝ)-(k+n : ℤ) = t-k by push_cast; ring]
  simp only [hp]

theorem periodicAngularBin_periodic (n j : ℕ) :
    Function.Periodic (periodicAngularBin n j) (2*Real.pi) := by
  have hp := angularBinSelection_periodic (fun k => (k % (n : ℤ)).toNat = j) (n : ℤ)
    (fun k => by simp)
  intro θ
  unfold periodicAngularBin
  convert hp ((n : ℝ)/(2*Real.pi)*θ) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  field_simp

theorem periodicAngularBin_contDiff (n j : ℕ) : ContDiff ℝ ∞ (periodicAngularBin n j) :=
  (angularBinSelection_contDiff _).comp (contDiff_const.mul contDiff_id)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SelectedAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open scoped ContDiff Topology

theorem periodicAngularBin_sum (n : ℕ) (S : Finset ℕ) :
    (fun θ => ∑ j ∈ S, periodicAngularBin n j θ) =
      fun θ => angularBinSelection (fun k => (k % (n : ℤ)).toNat ∈ S)
        ((n : ℝ)/(2*Real.pi)*θ) := by
  funext θ
  have hsum (q : ℕ) (w : ℝ) :
      (∑ j ∈ S, if q = j then w else 0) = if q ∈ S then w else 0 :=
    Finset.sum_ite_eq _ _ (fun _ => w)
  simp only [periodicAngularBin, angularBinSelection_two_terms, Finset.sum_add_distrib]
  let t := (n : ℝ)/(2*Real.pi)*θ
  convert congrArg₂ (fun a b : ℝ => a+b)
    (hsum (⌊t⌋ % (n : ℤ)).toNat (angularBinKernel (t-(⌊t⌋ : ℤ))))
    (hsum ((⌊t⌋+1) % (n : ℤ)).toNat (angularBinKernel (t-(⌊t⌋+1 : ℤ)))) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> split_ifs <;> rfl
  congr 1 <;> split_ifs <;> rfl

theorem selectedAngularBins_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (S : Finset ℕ) θ,
      ‖iteratedDeriv j (fun φ => ∑ k ∈ S, periodicAngularBin n k φ) θ‖ ≤
        C * ((n : ℝ)/(2*Real.pi))^j := by
  obtain ⟨C,hC0,hC⟩ := angularBinSelection_derivative_bound j
  refine ⟨C,hC0,?_⟩
  intro n S θ
  rw [periodicAngularBin_sum, iteratedDeriv_comp_const_mul
    ((angularBinSelection_contDiff _).of_le
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)))]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)/(2*Real.pi))]
  simpa only [mul_comm, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left (hC _ _)
    (by positivity : 0 ≤ ((n : ℝ)/(2*Real.pi))^j)

theorem selectedAngularBins_scale_derivatives (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ, 0 < δ → δ ≤ 2*Real.pi → ∀ (S : Finset ℕ) θ,
      ‖iteratedDeriv j (fun φ => ∑ k ∈ S, periodicAngularBin (angularBinCount δ) k φ) θ‖ ≤
        C * δ⁻¹^j := by
  obtain ⟨C,hC0,hC⟩ := selectedAngularBins_derivative_bound j
  refine ⟨C*2^j, by positivity, ?_⟩
  intro δ hδ hcap S θ
  apply (hC _ S θ).trans
  calc
    _ ≤ C*(2/δ)^j := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (angularBinCount_bounds hδ hcap).2 j) hC0
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleAngularBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem circleAngularBin_comp (n j : ℕ) (θ : ℝ) :
    circleAngularBin n j (sourceUnitDirection θ) = periodicAngularBin n j θ :=
  periodic_sourceAngle (periodicAngularBin_periodic n j) θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_FrechetCompositionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem frechetCompositionCost_continuousAt {g : E → ℝ} {x : E}
    (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ContinuousAt (frechetCompositionCost g n) x := by
  apply tendsto_finsetSum
  intro c _
  apply tendsto_finsetProd
  intro j _
  exact (hg.continuousAt_iteratedFDeriv
    (by exact_mod_cast (le_top : (c.partSize j : ℕ∞) ≤ ⊤))).norm

theorem frechet_composition_scale {f : ℝ → ℂ} {g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ)
    (hb : ∀ k ≤ n, ‖iteratedDeriv k f (g x)‖ ≤ C*D^k) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ frechetCompositionCost g n x * (C*D^n) := by
  rw [iteratedFDeriv_comp hf hg
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  simp only [FormalMultilinearSeries.taylorComp, frechetCompositionCost, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  apply (c.norm_compAlongOrderedFinpartition_le _ _).trans
  change ‖iteratedFDeriv ℝ c.length f (g x)‖ *
    (∏ j, ‖iteratedFDeriv ℝ (c.partSize j) g x‖) ≤ _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  exact (hb c.length c.length_le).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD c.length_le) hC)

theorem compact_frechet_composition_scale {g : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hg : ∀ x ∈ K, ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ y, ‖iteratedDeriv k f y‖ ≤ C*D^k) →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ A*C*D^n := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (fun x hx => (frechetCompositionCost_continuousAt (hg x hx) n).continuousWithinAt)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro f hf C D hC hD hb x hx
  have hA : frechetCompositionCost g n x ≤ max 0 B :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_right _ _))
  calc
    _ ≤ frechetCompositionCost g n x * (C*D^n) :=
      frechet_composition_scale hf.contDiffAt (hg x hx) hC hD n (fun k hk => hb k hk _)
    _ ≤ max 0 B * (C*D^n) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphSignPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem graphSignPlus_contDiff : ContDiff ℝ ∞ graphSignPlus := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_fst.add contDiff_snd).norm_sq ℝ).sub contDiff_const |>.div_const 2)

theorem graphSignMinus_contDiff : ContDiff ℝ ∞ graphSignMinus :=
  contDiff_const.sub graphSignPlus_contDiff

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphAngularCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem sourceDirection_add_arctan (φ z : ℝ) :
    sourceDirection (φ+Real.arctan z) =
      (Real.sqrt (1+z^2))⁻¹ • (sourceDirection φ+z • quarterTurn (sourceDirection φ)) := by
  ext i
  fin_cases i <;>
    simp [sourceDirection, quarterTurn, Complex.orthonormalBasisOneI_repr_apply,
      Real.cos_add, Real.sin_add, Real.cos_arctan, Real.sin_arctan,
      -Complex.ofReal_sin, -Complex.ofReal_cos] <;> ring

theorem sourceDirection_sub_arctan (φ z : ℝ) :
    sourceDirection (φ-Real.arctan z) =
      (Real.sqrt (1+z^2))⁻¹ • (sourceDirection φ-z • quarterTurn (sourceDirection φ)) := by
  simpa only [Real.arctan_neg, neg_sq, neg_smul, sub_eq_add_neg] using
    sourceDirection_add_arctan φ (-z)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAlgebraicDirections
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem graphNormalizedAxis_contDiffAt (η : Plane) (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ graphNormalizedAxis η :=
  ((contDiffAt_id.norm ℝ hη).inv (norm_ne_zero_iff.mpr hη)).smul contDiffAt_id

theorem quarterTurn_contDiff : ContDiff ℝ ∞ quarterTurn := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun x : Plane => -x 1)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : Plane => x 0)
    fun_prop

theorem graphAlgebraicDirection_contDiffAt (plus : Bool) (p : Plane × ℝ) (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (graphAlgebraicDirection plus) p := by
  have ha : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => graphNormalizedAxis q.1) p :=
    (graphNormalizedAxis_contDiffAt p.1 hp).comp p contDiffAt_fst
  have hs : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => (Real.sqrt (1+q.2^2))⁻¹) p :=
    ((contDiffAt_const.add (contDiffAt_snd.pow 2)).sqrt (by positivity)).inv (by positivity)
  have hz : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => if plus then q.2 else -q.2) p := by
    cases plus <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  exact hs.smul (ha.add (hz.smul (quarterTurn_contDiff.contDiffAt.comp p ha)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_GraphAngleCharts
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric Filter
open scoped ContDiff Topology

theorem graphComplexCoordinate_contDiff : ContDiff ℝ ∞ graphComplexCoordinate :=
  Complex.orthonormalBasisOneI.repr.symm.contDiff

theorem graphComplexCoordinate_norm (η : Plane) : ‖graphComplexCoordinate η‖ = ‖η‖ :=
  Complex.orthonormalBasisOneI.repr.symm.norm_map η

theorem graphPlaneAngle_eq_arg (η : Plane) :
    graphPlaneAngle η = Complex.arg (graphComplexCoordinate η) := by
  change Complex.arg (Complex.equivRealProd.symm (graphPlaneEquiv.symm η)) = _
  congr 1
  apply Complex.orthonormalBasisOneI.repr.injective
  ext i
  fin_cases i <;> simp [graphPlaneEquiv, graphComplexCoordinate,
    Complex.orthonormalBasisOneI_repr_apply]

theorem periodic_eq_of_angle_eq {f : ℝ → ℂ} (hp : Function.Periodic f (2*Real.pi))
    {a b : ℝ} (he : (a : Real.Angle) = (b : Real.Angle)) : f a = f b := by
  exact congrArg hp.lift he

theorem periodic_arg_neg {f : ℝ → ℂ} (hp : Function.Periodic f (2*Real.pi))
    {w : ℂ} (hw : w ≠ 0) (c : ℝ) :
    f (Complex.arg (-w)+Real.pi+c) = f (Complex.arg w+c) := by
  apply periodic_eq_of_angle_eq hp
  simp only [Real.Angle.coe_add, Complex.arg_neg_coe_angle hw]
  congr 1
  rw [add_assoc, ← Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi, add_zero]

theorem complex_arg_contDiffAt {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg w := by
  have hl : ContDiffAt ℝ ∞ Complex.log w :=
    (show ContDiffAt ℂ ∞ Complex.log w from Complex.contDiffAt_log hw).restrict_scalars ℝ
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using Complex.imCLM.contDiff.contDiffAt.comp w hl

theorem graphAngularPullback_chart {f : ℝ → ℂ} (hp : Function.Periodic f (2*Real.pi))
    (positive plus : Bool) (c : ℝ) {p : Plane × ℝ} (hη : p.1 ≠ 0) :
    graphAngularPullback f plus c p =
      f (graphAngleCoordinate positive plus p + (if positive then 0 else Real.pi)+c) := by
  have hw : graphComplexCoordinate p.1 ≠ 0 := by
    intro he
    have := graphComplexCoordinate_norm p.1
    rw [he, norm_zero] at this
    exact hη (norm_eq_zero.mp this.symm)
  cases positive
  · simp only [graphAngularPullback, graphAngleCoordinate, Bool.false_eq_true, ↓reduceIte,
      graphPlaneAngle_eq_arg]
    convert (periodic_arg_neg hp hw ((if plus then Real.arctan p.2 else -Real.arctan p.2)+c)).symm using 1 <;>
      congr 1 <;> ring
  · simp [graphAngularPullback, graphAngleCoordinate, graphPlaneAngle_eq_arg]

theorem graphAngleCoordinate_contDiffAt (positive plus : Bool) {p : Plane × ℝ}
    (hp : (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1)
      ∈ Complex.slitPlane) : ContDiffAt ℝ ∞ (graphAngleCoordinate positive plus) p := by
  have hw : ContDiff ℝ ∞ (fun q : Plane × ℝ =>
      if positive then graphComplexCoordinate q.1 else -graphComplexCoordinate q.1) := by
    cases positive
    · exact (graphComplexCoordinate_contDiff.comp contDiff_fst).neg
    · exact graphComplexCoordinate_contDiff.comp contDiff_fst
  have hz : ContDiff ℝ ∞ (fun q : Plane × ℝ =>
      if plus then Real.arctan q.2 else -Real.arctan q.2) := by
    cases plus
    · exact (Real.contDiff_arctan.comp contDiff_snd).neg
    · exact Real.contDiff_arctan.comp contDiff_snd
  exact ((complex_arg_contDiffAt hp).comp p hw.contDiffAt).add hz.contDiffAt

theorem graphAngleCompact_isCompact (positive : Bool) : IsCompact (graphAngleCompact positive) := by
  have hc : Continuous (fun p : Plane × ℝ =>
      (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1).re) := by
    cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop [graphComplexCoordinate]
  exact ((isCompact_closedBall (0:Plane × ℝ) 8).inter_right
    (isClosed_le continuous_const continuous_fst.norm)).inter_right
      (isClosed_le continuous_const hc)

theorem graphAngleCompact_slit (positive : Bool) {p : Plane × ℝ}
    (hp : p ∈ graphAngleCompact positive) :
    (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1)
      ∈ Complex.slitPlane := by
  let w := if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1
  have hn : ‖w‖ = ‖p.1‖ := by
    cases positive <;> simp [w, graphComplexCoordinate_norm]
  have hlo : (1:ℝ)/8 ≤ ‖p.1‖ := hp.1.2
  have hw : w ≠ 0 := norm_pos_iff.mp (by rw [hn]; linarith)
  have hr : 0 ≤ w.re := hp.2
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hi : w.im = 0
  · left
    apply lt_of_le_of_ne hr
    intro he
    apply hw
    apply Complex.ext <;> simp [he.symm, hi]
  · exact Or.inr hi

theorem graphAngleCompact_cover {η : Plane} {z : ℝ}
    (hhi : ‖η‖ ≤ 8) (hz : |z| ≤ 4) (hlo : 1/8 ≤ ‖η‖) :
    ∃ positive : Bool, (η,z) ∈ graphAngleCompact positive := by
  have hmem : (η,z) ∈ closedBall (0:Plane × ℝ) 8 ∩ {p | 1/8 ≤ ‖p.1‖} := by
    refine ⟨?_,hlo⟩
    simp only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨hhi,hz.trans (by norm_num)⟩
  by_cases hr : 0 ≤ (graphComplexCoordinate η).re
  · exact ⟨true,hmem,hr⟩
  · exact ⟨false,hmem,by simpa using (neg_nonneg.mpr (le_of_not_ge hr))⟩

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate ContDiff

theorem sourceAngle_comp_on_period {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    sourceAngle (sourceUnitDirection θ) = θ := by
  rw [sourceAngle_sourceUnitDirection]
  exact_mod_cast Complex.arg_cos_add_sin_mul_I hθ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothRotatedCone
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology

theorem periodic_contDiff_of_principal {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi))
    (hf : ∀ θ ∈ Ioc (-Real.pi) Real.pi, ContDiffAt ℝ ∞ f θ) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hr : sourceAngle (sourceUnitDirection θ) ∈ Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hh := hf _ hr
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [sourceAngle_sourceUnitDirection, he] at hh
  let c : ℝ := 2*Real.pi*(⌊(Real.pi-θ)/(2*Real.pi)⌋ : ℤ)
  have ht : ContDiffAt ℝ ∞ (fun t : ℝ => t+c) θ := contDiffAt_id.add contDiffAt_const
  have hc : ContDiffAt ℝ ∞ f (θ+c) := by simpa only [c, add_comm] using hh
  have hcomp := hc.comp θ ht
  have heq : (fun t => f (t+c)) = f := by
    funext t
    simpa only [c, mul_comm] using hp.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋ t
  simpa only [Function.comp_def, heq] using hcomp

theorem sourceConeCircle_angular_contDiff :
    ContDiff ℝ ∞ (fun θ => sourceConeCircle 0 (sourceUnitDirection θ)) := by
  let f : ℝ → ℂ := fun θ => sourceConeCircle 0 (sourceUnitDirection θ)
  have hp : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg (sourceConeCircle 0) (sourceUnitDirection_periodic θ)
  have hlocal {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) : f θ = graphConeCutoff θ := by
    simp only [f, sourceConeCircle, neg_zero, sourceCircleRotate_zero, sourceAngle_comp_on_period hθ]
  have hzero (θ : ℝ) (hc : Real.cos θ < 0) : f θ = 0 := by
    by_contra hn
    have hs : sourceAngle (sourceUnitDirection θ) ∈ Icc (-1/5 : ℝ) (1/5) := by
      apply graphConeCutoff_support
      apply subset_closure
      simpa only [Function.mem_support, f, sourceConeCircle, neg_zero, sourceCircleRotate_zero] using hn
    have hcos : 0 ≤ Real.cos (sourceAngle (sourceUnitDirection θ)) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by have := Real.one_le_pi_div_two; linarith [hs.1])
        (by have := Real.one_le_pi_div_two; linarith [hs.2])
    have he := periodic_sourceAngle (show Function.Periodic Real.cos (2*Real.pi) from Real.cos_periodic) θ
    rw [he] at hcos
    linarith
  apply periodic_contDiff_of_principal hp
  intro θ hθ
  by_cases hlt : θ < Real.pi
  · apply graphConeCutoff_contDiff.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ.1, hlt⟩] with t ht
    exact hlocal ⟨ht.1, ht.2.le⟩
  · have hθπ : θ = Real.pi := le_antisymm hθ.2 (le_of_not_gt hlt)
    rw [hθπ]
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    have hn : {t : ℝ | Real.cos t < 0} ∈ 𝓝 Real.pi :=
      (isOpen_lt Real.continuous_cos continuous_const).mem_nhds (by simp)
    filter_upwards [hn] with t ht
    exact hzero t ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_FrechetProductScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem frechet_mul_scale_on {U : Set E} (hU : IsOpen U) {f g : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) {x : E} (hx : x ∈ U)
    {C₁ C₂ D₁ D₂ : ℝ} (hC₁ : 0 ≤ C₁) (_ : 0 ≤ C₂)
    (hD₁ : 0 ≤ D₁) (_ : 0 ≤ D₂) (n : ℕ)
    (hb₁ : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ C₁*D₁^j)
    (hb₂ : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ C₂*D₂^j) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ C₁*C₂*(D₁+D₂)^n := by
  have he := norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hx
    (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at he
  apply he.trans
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  calc
    _ ≤ (n.choose j:ℝ) * (C₁*D₁^j) * (C₂*D₂^(n-j)) := by
      gcongr
      · exact hb₁ j hjn
      · exact hb₂ (n-j) (Nat.sub_le _ _)
    _ = _ := by ring

theorem frechet_conj_norm {f : E → ℂ} {x : E} (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => star (f y)) x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  exact Complex.conjLIE.norm_iteratedFDeriv_comp_left f x n

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphMixedComposition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology

theorem graphAngularPullback_eventually_chart {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi)) (positive plus : Bool) (c : ℝ)
    {p : Plane × ℝ} (hη : p.1 ≠ 0) :
    graphAngularPullback f plus c =ᶠ[𝓝 p]
      fun q => f (graphAngleCoordinate positive plus q + (if positive then 0 else Real.pi)+c) := by
  have he : ∀ᶠ q : Plane × ℝ in 𝓝 p, q.1 ≠ 0 :=
    continuousAt_fst.eventually_ne hη
  filter_upwards [he] with q hq
  exact graphAngularPullback_chart hp positive plus c hq

theorem graphAngularPullback_contDiffAt {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f (2*Real.pi))
    (plus : Bool) (c : ℝ) {p : Plane × ℝ} (hη : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (graphAngularPullback f plus c) p := by
  have hw : graphComplexCoordinate p.1 ≠ 0 := by
    intro he
    apply hη
    apply norm_eq_zero.mp
    rw [← graphComplexCoordinate_norm, he, norm_zero]
  have hs : ∃ positive : Bool,
      (if positive then graphComplexCoordinate p.1 else -graphComplexCoordinate p.1)
        ∈ Complex.slitPlane := by
    by_cases hi : (graphComplexCoordinate p.1).im = 0
    · have hr : (graphComplexCoordinate p.1).re ≠ 0 := by
        intro hr
        exact hw (Complex.ext (by simpa using hr) (by simpa using hi))
      rcases lt_or_gt_of_ne hr with hr | hr
      · exact ⟨false, Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using neg_pos.mpr hr))⟩
      · exact ⟨true, Complex.mem_slitPlane_iff.mpr (Or.inl hr)⟩
    · exact ⟨true, Complex.mem_slitPlane_iff.mpr (Or.inr hi)⟩
  obtain ⟨positive,hs⟩ := hs
  have hg : ContDiffAt ℝ ∞ (fun q => graphAngleCoordinate positive plus q +
      (if positive then 0 else Real.pi)+c) p :=
    ((graphAngleCoordinate_contDiffAt positive plus hs).add contDiffAt_const).add contDiffAt_const
  exact (hf.contDiffAt.comp p hg).congr_of_eventuallyEq
    (graphAngularPullback_eventually_chart hp positive plus c hη)

theorem graph_mixed_composition_scale (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f →
      Function.Periodic f (2*Real.pi) → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ θ, ‖iteratedDeriv k f θ‖ ≤ C*D^k) →
      ∀ (plus : Bool) (c : ℝ) (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
      ‖iteratedFDeriv ℝ n (graphAngularPullback f plus c) (η,z)‖ ≤ A*C*D^n := by
  choose A hA hb using fun positive plus => compact_frechet_composition_scale
    (graphAngleCompact_isCompact positive)
    (fun p hp => graphAngleCoordinate_contDiffAt positive plus (graphAngleCompact_slit positive hp)) n
  let B := max (max (A true true) (A true false)) (max (A false true) (A false false))
  have hAB (positive plus : Bool) : A positive plus ≤ B := by
    cases positive <;> cases plus <;> dsimp [B] <;> order
  refine ⟨B, (hA true true).trans (hAB true true), ?_⟩
  intro f hf hp C D hC hD hbound plus c η z hhi hz hlo
  obtain ⟨positive,hmem⟩ := graphAngleCompact_cover hhi hz hlo
  let shift : ℝ := (if positive then 0 else Real.pi)+c
  let fshift : ℝ → ℂ := fun t => f (t+shift)
  have hfshift : ContDiff ℝ ∞ fshift := hf.comp (contDiff_id.add contDiff_const)
  have hshift : ∀ k ≤ n, ∀ θ, ‖iteratedDeriv k fshift θ‖ ≤ C*D^k := by
    intro k hk θ
    dsimp [fshift]
    rw [iteratedDeriv_comp_add_const]
    exact hbound k hk _
  have he : graphAngularPullback f plus c =ᶠ[𝓝 (η,z)]
      fshift ∘ graphAngleCoordinate positive plus := by
    have hη : η ≠ 0 := norm_pos_iff.mp (by linarith)
    simpa only [fshift,shift,Function.comp_def,add_assoc] using
      graphAngularPullback_eventually_chart hp positive plus c (p := (η,z)) hη
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
  exact (hb positive plus fshift hfshift C D hC hD hshift (η,z) hmem).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hAB positive plus) hC)
      (pow_nonneg (zero_le_one.trans hD) _))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualMixedDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem complex_periodic_iteratedDeriv {f : ℝ → ℂ} {p : ℝ}
    (hp : Function.Periodic f p) (j : ℕ) : Function.Periodic (iteratedDeriv j f) p := by
  have he : (fun x => f (x+p)) = f := funext hp
  have hh := iteratedDeriv_comp_add_const j f p
  rw [he] at hh
  intro x
  exact (congrFun hh x).symm

theorem uniform_actual_graph_symbol_mixed {sig : ℝ} (hsig : 0 < sig) (K m n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (mass : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane), ‖h x‖ ≤ 1 →
    ∀ (plus : Bool) (c : ℝ) (η : Plane) (z : ℝ),
    ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
    ‖iteratedFDeriv ℝ n (fun p : Plane × ℝ => iteratedDeriv m
      (fun t => inheritedCircleSymbol S b k Q ρ mass N lam sig J i h x
        (sourceUnitDirection (graphPlaneAngle p.1 +
          (if plus then Real.arctan p.2 else -Real.arctan p.2)+t))) c) (η,z)‖ ≤
      A * sourceSymbolScale N sig L^(m+n) := by
  choose N₀ h₀ using fun j => uniform_actual_symbol_derivatives hsig K j
  let C : ℝ := ∑ j ∈ Finset.range (m+n+1), symbolDerivativeConstant (K+j)^(K+j)
  have hCj (j : ℕ) : 0 ≤ symbolDerivativeConstant (K+j)^(K+j) :=
    pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hCj j)
  obtain ⟨A,hA,hbound⟩ := graph_mixed_composition_scale n
  refine ⟨A*C,mul_nonneg hA hC, (Finset.range (m+n+1)).sup N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ mass lam J i h x hx plus c η z hhi hz hlo
  let f : ℝ → ℂ := fun θ => inheritedCircleSymbol S b k Q ρ mass N lam sig J i h x
    (sourceUnitDirection θ)
  have hf : ContDiff ℝ ∞ f := inheritedCircleSymbol_contDiff S b k Q hQ ρ mass N lam sig J i h x
  have hp : Function.Periodic f (2*Real.pi) := by
    intro θ
    dsimp [f]
    rw [sourceUnitDirection_periodic]
  have hsmooth : ∀ q : ℕ, ContDiff ℝ ∞ (iteratedDeriv q f) := by
    intro q
    induction q with
    | zero => simpa using hf
    | succ q ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2
  have hfder := hsmooth m
  have hDpos := sourceSymbolScale_pos N sig L
  have hb : ∀ j ≤ n, ∀ θ, ‖iteratedDeriv j (iteratedDeriv m f) θ‖ ≤
      (C*sourceSymbolScale N sig L^m)*sourceSymbolScale N sig L^j := by
    intro j hj θ
    have hiter : iteratedDeriv j (iteratedDeriv m f) = iteratedDeriv (j+m) f := by
      simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
    rw [hiter]
    have hjmem : j+m ∈ Finset.range (m+n+1) := Finset.mem_range.mpr (by omega)
    have hNj : N₀ (j+m) ≤ N := (Finset.le_sup hjmem).trans hN
    have he := h₀ (j+m) N hNj S b k hcard hK L hL Q hQ ρ mass lam J i h x hx θ
    calc
      _ ≤ symbolDerivativeConstant (K+(j+m))^(K+(j+m))*sourceSymbolScale N sig L^(j+m) := he
      _ ≤ C*sourceSymbolScale N sig L^(j+m) := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun l _ => hCj l) hjmem) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have he := hbound (iteratedDeriv m f) hfder (complex_periodic_iteratedDeriv hp m)
    (C*sourceSymbolScale N sig L^m) (sourceSymbolScale N sig L) (by positivity)
    (sourceSymbolScale_one_le N hsig.le L) hb plus c η z hhi hz hlo
  change ‖iteratedFDeriv ℝ n (fun p : Plane × ℝ => iteratedDeriv m
    (fun t => f (graphPlaneAngle p.1 +
      (if plus then Real.arctan p.2 else -Real.arctan p.2)+t)) c) (η,z)‖ ≤ _
  simp only [iteratedDeriv_comp_const_add]
  convert he using 1
  · rfl
  · rw [pow_add]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GraphFourSymbolDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem graphSmoothDomain_isOpen : IsOpen graphSmoothDomain :=
  isOpen_ne_fun continuous_fst continuous_const

theorem graph_four_symbol_product_scale (F : Fin 4 → (Plane × ℝ) → ℂ)
    (hF : ∀ a, ContDiffOn ℝ ∞ (F a) graphSmoothDomain)
    {p : Plane × ℝ} (hp : p ∈ graphSmoothDomain) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (n : ℕ)
    (hb : ∀ a j, j ≤ n → ‖iteratedFDeriv ℝ j (F a) p‖ ≤ C*D^j) :
    ‖iteratedFDeriv ℝ n (graphFourSymbolProduct F) p‖ ≤ C^4*(4*D)^n := by
  have hconj (a) : ContDiffOn ℝ ∞ (fun q => conj (F a q)) graphSmoothDomain :=
    Complex.conjCLE.contDiff.comp_contDiffOn (hF a)
  have hpair (a b : Fin 4) (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (fun q => F a q * conj (F b q)) p‖ ≤ C*C*(D+D)^j := by
    apply frechet_mul_scale_on graphSmoothDomain_isOpen (hF a) (hconj b) hp hC hC hD hD j
    · intro k hk
      exact hb a k (hk.trans hj)
    · intro k hk
      change ‖iteratedFDeriv ℝ k (fun q => star (F b q)) p‖ ≤ _
      rw [frechet_conj_norm]
      exact hb b k (hk.trans hj)
  have he := frechet_mul_scale_on graphSmoothDomain_isOpen
    ((hF 0).mul (hconj 1)) ((hF 2).mul (hconj 3)) hp
    (mul_nonneg hC hC) (mul_nonneg hC hC) (add_nonneg hD hD) (add_nonneg hD hD) n
    (hpair 0 1) (hpair 2 3)
  convert he using 1 <;> first | rfl | ring

theorem uniform_actual_graph_four_symbols {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ (plus : Fin 4 → Bool) (c : Fin 4 → ℝ),
    ∀ (η : Plane) (z : ℝ), ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
    let F := fun a => graphAngularPullback
      (fun θ => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
        N lam sig J i (h a) (x a) (sourceUnitDirection θ)) (plus a) (c a)
    ‖iteratedFDeriv ℝ n (graphFourSymbolProduct F) (η,z)‖ ≤ A*sourceSymbolScale N sig L^n := by
  choose A hA N₀ hb using fun j => uniform_actual_graph_symbol_mixed hsig K 0 j
  let C : ℝ := ∑ j ∈ Finset.range (n+1), A j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hA j)
  refine ⟨C^4*4^n,by positivity,(Finset.range (n+1)).sup N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx plus c η z hhi hz hlo
  dsimp only
  let F := fun a => graphAngularPullback
    (fun θ => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a) (x a) (sourceUnitDirection θ)) (plus a) (c a)
  have hF : ∀ a, ContDiffOn ℝ ∞ (F a) graphSmoothDomain := by
    intro a p hp
    apply (graphAngularPullback_contDiffAt
      (inheritedCircleSymbol_contDiff (S a) (d a) (k a) (Q a) (hQ a) (ρ a) (mass a)
        N lam sig J i (h a) (x a)) _ (plus a) (c a) hp).contDiffWithinAt
    intro θ
    exact congrArg (inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a) (x a)) (sourceUnitDirection_periodic θ)
  have hder : ∀ a j, j ≤ n → ‖iteratedFDeriv ℝ j (F a) (η,z)‖ ≤ C*sourceSymbolScale N sig L^j := by
    intro a j hj
    have hjmem : j ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have he := hb j N ((Finset.le_sup hjmem).trans hN) (S a) (d a) (k a) (hcard a)
      (hK a) L (hL a) (Q a) (hQ a) (ρ a) (mass a) lam J i (h a) (x a) (hx a)
      (plus a) (c a) η z hhi hz hlo
    simp only [iteratedDeriv_zero, Nat.zero_add] at he
    apply he.trans
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun l _ => hA l) hjmem)
      (pow_nonneg (sourceSymbolScale_pos _ _ _).le _)
  have hp : (η,z) ∈ graphSmoothDomain := norm_pos_iff.mp (by linarith)
  have he := graph_four_symbol_product_scale F hF hp hC (sourceSymbolScale_pos N sig L).le n hder
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | (rw [mul_pow]; ring)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem dyadic_power_real (N : ℕ) (s : ℝ) :
    ((2 : ℝ)^N)^s = (2 : ℝ)^((N : ℝ)*s) := by
  rw [← Real.rpow_natCast (2 : ℝ) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphBinDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

theorem graph_selected_bins_mixed (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 2*Real.pi →
      ∀ (S : Finset ℕ) (plus : Bool) (c : ℝ) (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
      ‖iteratedFDeriv ℝ n (graphAngularPullback
        (fun θ => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ : ℝ):ℂ)) plus c) (η,z)‖ ≤
        A * (max 1 δ⁻¹)^n := by
  choose C hC hbound using fun j => selectedAngularBins_scale_derivatives j
  let B : ℝ := ∑ j ∈ Finset.range (n+1), C j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hC j)
  obtain ⟨A,hA,hcomp⟩ := graph_mixed_composition_scale n
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro δ hδ hcap S plus c η z hhi hz hlo
  have hf : ContDiff ℝ ∞ (fun θ => ∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ) := by
    apply ContDiff.sum
    intro k _
    exact periodicAngularBin_contDiff _ _
  apply hcomp _ (Complex.ofRealCLM.contDiff.comp hf) _ B (max 1 δ⁻¹) hB (le_max_left _ _) _
    plus c η z hhi hz hlo
  · intro θ
    change ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k (θ+2*Real.pi) : ℝ):ℂ) = _
    apply congrArg Complex.ofReal
    apply Finset.sum_congr rfl
    intro k _
    exact periodicAngularBin_periodic _ _ θ
  · intro j hj θ
    change ‖iteratedDeriv j (fun t => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k t : ℝ):ℂ)) θ‖ ≤ _
    rw [iteratedDeriv_ofReal hf, Complex.norm_real]
    apply (hbound j δ hδ hcap S θ).trans
    apply mul_le_mul
    · exact Finset.single_le_sum (fun l _ => hC l)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    · exact pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
    · positivity
    · exact hB

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFixedCutoffs
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff ComplexConjugate

theorem graph_plane_axis_all (η : Plane) :
    ‖η‖ • sourceDirection (graphPlaneAngle η) = η := by
  rw [graphPlaneAngle_eq_arg]
  have he := congrArg Complex.orthonormalBasisOneI.repr
    (Complex.norm_mul_cos_add_sin_mul_I (graphComplexCoordinate η))
  simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.real_smul, LinearIsometryEquiv.map_smul,
    graphComplexCoordinate_norm, graphComplexCoordinate,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map, sourceDirection] using he

theorem graphNormalizedAxis_eq_all {η : Plane} (hη : η ≠ 0) :
    graphNormalizedAxis η = sourceDirection (graphPlaneAngle η) := by
  calc
    graphNormalizedAxis η = ‖η‖⁻¹ • (‖η‖ • sourceDirection (graphPlaneAngle η)) :=
      congrArg (fun v : Plane => ‖η‖⁻¹ • v) (graph_plane_axis_all η).symm
    _ = _ := by rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hη), one_smul]

theorem graphAlgebraicDirection_eq_all (plus : Bool) {η : Plane} (hη : η ≠ 0) (z : ℝ) :
    graphAlgebraicDirection plus (η,z) =
      sourceDirection (graphPlaneAngle η+(if plus then Real.arctan z else -Real.arctan z)) := by
  cases plus
  · simp only [graphAlgebraicDirection, Bool.false_eq_true, ↓reduceIte,
      graphNormalizedAxis_eq_all hη, neg_smul, ← sub_eq_add_neg]
    exact (sourceDirection_sub_arctan _ _).symm
  · simp only [graphAlgebraicDirection, ↓reduceIte, graphNormalizedAxis_eq_all hη]
    exact (sourceDirection_add_arctan _ _).symm

theorem graphFixedSign_eq (plus : Bool) {p : Plane × ℝ} (hp : p.1 ≠ 0) :
    graphFixedSign plus p =
      ((if plus then circleGraphSignPlus else circleGraphSignMinus)
        (sourceUnitDirection (graphPlaneAngle p.1+Real.arctan p.2),
          sourceUnitDirection (graphPlaneAngle p.1-Real.arctan p.2+(if plus then 0 else Real.pi))) : ℝ) := by
  cases plus <;> simp only [graphFixedSign, Bool.false_eq_true, ↓reduceIte,
    circleGraphSignPlus, circleGraphSignMinus, sourceUnitDirection, add_zero,
    graphAlgebraicDirection_eq_all true hp, graphAlgebraicDirection_eq_all false hp,
    Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg, sourceDirection_add_pi]

theorem graphFixedSign_contDiffAt (plus : Bool) {p : Plane × ℝ} (hp : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (graphFixedSign plus) p := by
  have ha := graphAlgebraicDirection_contDiffAt true p hp
  have hb := graphAlgebraicDirection_contDiffAt false p hp
  cases plus
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (graphSignMinus_contDiff.contDiffAt.comp p (ha.prodMk hb.neg))
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (graphSignPlus_contDiff.contDiffAt.comp p (ha.prodMk hb))

theorem graphShellJacobian_contDiffAt {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    {p : Plane × ℝ} (hp : p.1 ≠ 0) : ContDiffAt ℝ ∞ (graphShellJacobian Ψ) p := by
  have hr : ContDiffAt ℝ ∞ (fun q : Plane × ℝ => ‖q.1‖*Real.sqrt (1+q.2^2)) p :=
    (contDiffAt_fst.norm ℝ hp).mul
      ((contDiffAt_const.add (contDiffAt_snd.pow 2)).sqrt (by positivity))
  have hn : ‖p.1‖*Real.sqrt (1+p.2^2) ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hp) (by positivity)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
    ((hr.inv hn).mul (hΨ.contDiffAt.comp p (hr.div_const 2)))

theorem graph_compact_derivative_bound {f : (Plane × ℝ) → ℂ}
    (hf : ∀ p, p.1 ≠ 0 → ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Plane) (z : ℝ),
      ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ → ‖iteratedFDeriv ℝ n f (η,z)‖ ≤ C := by
  let K : Set (Plane × ℝ) := closedBall 0 8 ∩ {p | 1/8 ≤ ‖p.1‖}
  have hK : IsCompact K := (isCompact_closedBall (0:Plane × ℝ) 8).inter_right
    (isClosed_le continuous_const continuous_fst.norm)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (f := iteratedFDeriv ℝ n f) (fun p hp =>
      ((hf p (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/8) hp.2))).continuousAt_iteratedFDeriv
        (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).continuousWithinAt)
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro η z hhi hz hlo
  apply (hC (η,z) ?_).trans (le_max_right _ _)
  refine ⟨?_,hlo⟩
  simp only [mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff,Real.norm_eq_abs]
  exact ⟨hhi,hz.trans (by norm_num)⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphDerivativeBounds
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology ComplexConjugate

theorem GraphDerivativeBound.mul {n : ℕ} {f g : (Plane × ℝ) → ℂ} {C₁ C₂ D₁ D₂ : ℝ}
    (hf : GraphDerivativeBound n f C₁ D₁) (hg : GraphDerivativeBound n g C₂ D₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) :
    GraphDerivativeBound n (fun p => f p*g p) (C₁*C₂) (D₁+D₂) := by
  refine ⟨hf.smooth.mul hg.smooth,?_⟩
  intro j hj η z hhi hz hlo
  exact frechet_mul_scale_on graphSmoothDomain_isOpen hf.smooth hg.smooth
    (norm_pos_iff.mp (by linarith)) hC₁ hC₂ hD₁ hD₂ j
    (fun k hk => hf.bound k (hk.trans hj) η z hhi hz hlo)
    (fun k hk => hg.bound k (hk.trans hj) η z hhi hz hlo)

theorem GraphDerivativeBound.conj {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) : GraphDerivativeBound n (fun p => conj (f p)) C D := by
  refine ⟨Complex.conjCLE.contDiff.comp_contDiffOn hf.smooth,?_⟩
  intro j hj η z hhi hz hlo
  change ‖iteratedFDeriv ℝ j (fun p => star (f p)) (η,z)‖ ≤ _
  rw [frechet_conj_norm]
  exact hf.bound j hj η z hhi hz hlo

theorem GraphDerivativeBound.mono {n : ℕ} {f : (Plane × ℝ) → ℂ} {C C' D D' : ℝ}
    (hf : GraphDerivativeBound n f C D) (hC : C ≤ C') (hC' : 0 ≤ C')
    (hD : D ≤ D') (hD0 : 0 ≤ D) : GraphDerivativeBound n f C' D' := by
  refine ⟨hf.smooth,?_⟩
  intro j hj η z hhi hz hlo
  exact (hf.bound j hj η z hhi hz hlo).trans
    (mul_le_mul hC (pow_le_pow_left₀ hD0 hD _) (pow_nonneg hD0 _) hC')

theorem GraphDerivativeBound.congr {n : ℕ} {f g : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) (he : EqOn g f graphSmoothDomain) :
    GraphDerivativeBound n g C D := by
  have hevent {p : Plane × ℝ} (hp : p ∈ graphSmoothDomain) : g =ᶠ[𝓝 p] f :=
    Filter.eventuallyEq_of_mem (graphSmoothDomain_isOpen.mem_nhds hp) he
  refine ⟨?_,?_⟩
  · intro p hp
    exact ((hf.smooth p hp).contDiffAt (graphSmoothDomain_isOpen.mem_nhds hp)).congr_of_eventuallyEq
      (hevent hp) |>.contDiffWithinAt
  · intro j hj η z hhi hz hlo
    have hp : (η,z) ∈ graphSmoothDomain := norm_pos_iff.mp (by linarith)
    rw [((hevent hp).iteratedFDeriv ℝ j).eq_of_nhds]
    exact hf.bound j hj η z hhi hz hlo

theorem graph_fixed_derivative_budget {f : (Plane × ℝ) → ℂ}
    (hf : ∀ p, p.1 ≠ 0 → ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ GraphDerivativeBound n f C 1 := by
  choose C hC hb using fun j => graph_compact_derivative_bound hf j
  let A := ∑ j ∈ Finset.range (n+1), C j
  refine ⟨A,Finset.sum_nonneg (fun j _ => hC j),fun p hp => (hf p hp).contDiffWithinAt,?_⟩
  intro j hj η z hhi hz hlo
  rw [one_pow,mul_one]
  exact (hb j η z hhi hz hlo).trans
    (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem graph_periodic_derivative_budget {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (2*Real.pi)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (plus : Bool) (c : ℝ),
      GraphDerivativeBound n (graphAngularPullback f plus c) C 1 := by
  have hj (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ θ, ‖iteratedDeriv j f θ‖ ≤ B := by
    obtain ⟨B,hB⟩ := ((complex_periodic_iteratedDeriv hp j).isBounded_of_continuous
      (by positivity : 2*Real.pi ≠ 0) (hf.continuous_iteratedDeriv j
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)))).exists_norm_le
    exact ⟨max 0 B,le_max_left _ _,fun θ => (hB _ ⟨θ,rfl⟩).trans (le_max_right _ _)⟩
  choose B hB hb using hj
  let C := ∑ j ∈ Finset.range (n+1), B j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hB j)
  choose A hA ha using fun j => graph_mixed_composition_scale j
  let M := ∑ j ∈ Finset.range (n+1), A j
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ => hA j)
  refine ⟨M*C,mul_nonneg hM hC,?_⟩
  intro plus c
  refine ⟨fun p hp' => (graphAngularPullback_contDiffAt hf hp plus c hp').contDiffWithinAt,?_⟩
  intro j hj η z hhi hz hlo
  have he := ha j f hf hp C 1 hC le_rfl (fun k hk θ => by
    rw [one_pow,mul_one]
    exact (hb k θ).trans (Finset.single_le_sum (fun l _ => hB l)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hk.trans hj))))) plus c η z hhi hz hlo
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun l _ => hA l) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) hC

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphWeightDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff ComplexConjugate

theorem graph_bin_derivative_budget (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 2*Real.pi →
      ∀ (S : Finset ℕ) (plus : Bool) (c : ℝ),
      GraphDerivativeBound n (graphBinPullback δ S plus c) C (max 1 δ⁻¹) := by
  choose A hA ha using fun j => graph_selected_bins_mixed j
  let C := ∑ j ∈ Finset.range (n+1), A j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hA j)
  refine ⟨C,hC,?_⟩
  intro δ hδ hcap S plus c
  have hf : ContDiff ℝ ∞ (fun θ => ∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ) :=
    ContDiff.sum (fun k _ => periodicAngularBin_contDiff _ _)
  have hp : Function.Periodic (fun θ => ((∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ : ℝ):ℂ))
      (2*Real.pi) := by
    intro θ
    apply congrArg Complex.ofReal
    exact Finset.sum_congr rfl (fun k _ => periodicAngularBin_periodic _ _ θ)
  refine ⟨fun p hp' => (graphAngularPullback_contDiffAt
    (Complex.ofRealCLM.contDiff.comp hf) hp plus c hp').contDiffWithinAt,?_⟩
  intro j hj η z hhi hz hlo
  exact (ha j δ hδ hcap S plus c η z hhi hz hlo).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun l _ => hA l) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
      (by positivity))

theorem graph_cone_derivative_budget (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (plus : Bool) (c : ℝ),
      GraphDerivativeBound n (graphConePullback plus c) C 1 := by
  apply graph_periodic_derivative_budget sourceConeCircle_angular_contDiff
  intro θ
  exact congrArg (sourceConeCircle 0) (sourceUnitDirection_periodic θ)

theorem graphWeightPullback_distance (axis δ : ℝ) (j k : ℕ) (p : Plane × ℝ) :
    graphWeightPullback true true axis δ j k p =
      (graphConePullback true (-axis) p * graphBinPullback δ {j} true (-axis) p) *
        conj (graphConePullback false (-axis) p * graphBinPullback δ {k} false (-axis) p) := by
  simp only [graphWeightPullback, graphSourceWeight, graphSourceChartAxis, ↓reduceIte, add_zero,
    graphRotatedDistanceWeight_eq, sourceConeCircle, rotatedBinSelection,
    sourceCircleRotate_comp, graphConePullback, graphBinPullback, graphAngularPullback,
    neg_zero, Finset.sum_singleton, circleAngularBin_comp,
    Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg]

theorem graphWeightPullback_product (plus : Bool) (axis δ : ℝ) (j k : ℕ)
    {p : Plane × ℝ} (hp : p.1 ≠ 0) :
    graphWeightPullback false plus axis δ j k p =
      (graphBinPullback δ {j} true 0 p *
        graphBinPullback δ {k} false (if plus then 0 else Real.pi) p) * graphFixedSign plus p := by
  rw [graphFixedSign_eq plus hp]
  cases plus <;> simp only [graphWeightPullback, graphSourceWeight, graphSourceChartAxis,
    graphProductWeight, graphBinWeight, graphBinPullback, graphAngularPullback,
    Bool.false_eq_true, ↓reduceIte, Finset.sum_singleton, add_zero,
    ← sub_eq_add_neg, circleAngularBin_comp, Complex.ofReal_mul]

theorem graph_source_weight_derivative_budget (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 2*Real.pi →
      ∀ (distance plus : Bool) (axis : ℝ) (j k : ℕ),
      GraphDerivativeBound n (graphWeightPullback distance plus axis δ j k) C (4*max 1 δ⁻¹) := by
  obtain ⟨B,hB,hbin⟩ := graph_bin_derivative_budget n
  obtain ⟨A,hA,hcone⟩ := graph_cone_derivative_budget n
  choose S hS hs using fun plus => graph_fixed_derivative_budget
    (fun _ hp => graphFixedSign_contDiffAt plus hp) n
  let T := max (S true) (S false)
  have hT : 0 ≤ T := (hS true).trans (le_max_left _ _)
  have hsign (plus : Bool) : GraphDerivativeBound n (graphFixedSign plus) T 1 :=
    (hs plus).mono (by cases plus <;> simp [T]) hT le_rfl zero_le_one
  let C := max ((A*B)*(A*B)) ((B*B)*T)
  have hC : 0 ≤ C := (mul_nonneg (mul_nonneg hA hB) (mul_nonneg hA hB)).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro δ hδ hcap distance plus axis j k
  let D := max 1 δ⁻¹
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  cases distance
  · have hb := ((hbin δ hδ hcap {j} true 0).mul
      (hbin δ hδ hcap {k} false (if plus then 0 else Real.pi)) hB hB hD0 hD0).mul
        (hsign plus) (mul_nonneg hB hB) hT (add_nonneg hD0 hD0) zero_le_one
    have hb' := hb.mono (le_max_right _ _) hC (show D+D+1 ≤ 4*D by linarith) (by positivity)
    exact hb'.congr (fun p hp => graphWeightPullback_product plus axis δ j k hp)
  · have hb₁ := (hcone true (-axis)).mul (hbin δ hδ hcap {j} true (-axis)) hA hB zero_le_one hD0
    have hb₂ := (hcone false (-axis)).mul (hbin δ hδ hcap {k} false (-axis)) hA hB zero_le_one hD0
    have hb := hb₁.mul hb₂.conj (mul_nonneg hA hB) (mul_nonneg hA hB)
      (by positivity) (by positivity)
    have hb' := hb.mono (le_max_left _ _) hC (show (1+D)+(1+D) ≤ 4*D by linarith) (by positivity)
    apply hb'.congr
    intro p _
    have he : graphWeightPullback true plus axis δ j k p = graphWeightPullback true true axis δ j k p := rfl
    rw [he, graphWeightPullback_distance]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem graphAmplitudePullback_factorization (b : Fin 4 → Plane → UnitCircle → ℂ)
    (x : Fin 4 → Plane) (distance plus : Bool) (axis δ : ℝ) (j k : ℕ)
    (Ψ : ℝ → ℝ) (p : Plane × ℝ) :
    graphAmplitudePullback b x distance plus axis δ j k Ψ p =
      (graphShellJacobian Ψ p * graphWeightPullback distance plus axis δ j k p) *
        graphFourSymbolProduct (fun a => graphAngularPullback
          (fun θ => b a (x a) (sourceUnitDirection θ))
          (decide (a.val < 2)) (if a.val < 2 then 0 else graphSourceChartAxis distance plus)) p := by
  norm_num [graphAmplitudePullback, graphFourAmplitude, graphWeightPullback,
    graphFourSymbolProduct, graphAngularPullback, ← sub_eq_add_neg]
  ring

theorem uniform_actual_four_symbol_budget {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ (plus : Fin 4 → Bool) (c : Fin 4 → ℝ),
    let F := fun a => graphAngularPullback
      (fun θ => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
        N lam sig J i (h a) (x a) (sourceUnitDirection θ)) (plus a) (c a)
    GraphDerivativeBound n (graphFourSymbolProduct F) A (sourceSymbolScale N sig L) := by
  choose A hA N₀ hb using fun j => uniform_actual_graph_four_symbols hsig K j
  let C := ∑ j ∈ Finset.range (n+1), A j
  refine ⟨C,Finset.sum_nonneg (fun j _ => hA j),(Finset.range (n+1)).sup N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx plus c
  dsimp only
  let F := fun a => graphAngularPullback
    (fun θ => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a) (x a) (sourceUnitDirection θ)) (plus a) (c a)
  have hF : ∀ a, ContDiffOn ℝ ∞ (F a) graphSmoothDomain := by
    intro a p hp
    apply (graphAngularPullback_contDiffAt
      (inheritedCircleSymbol_contDiff (S a) (d a) (k a) (Q a) (hQ a) (ρ a) (mass a)
        N lam sig J i (h a) (x a)) _ (plus a) (c a) hp).contDiffWithinAt
    intro θ
    exact congrArg (inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a) (x a)) (sourceUnitDirection_periodic θ)
  refine ⟨?_,?_⟩
  · exact ((hF 0).mul (Complex.conjCLE.contDiff.comp_contDiffOn (hF 1))).mul
      ((hF 2).mul (Complex.conjCLE.contDiff.comp_contDiffOn (hF 3)))
  · intro j hj η z hhi hz hlo
    have hjmem : j ∈ Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    apply (hb j N ((Finset.le_sup hjmem).trans hN) S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
      plus c η z hhi hz hlo).trans
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun l _ => hA l) hjmem)
      (pow_nonneg (sourceSymbolScale_pos _ _ _).le _)

theorem uniform_actual_graph_amplitude {sig : ℝ} (hsig : 0 < sig) (K n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ δ : ℝ, 0 < δ → δ ≤ 2*Real.pi →
    ∀ (distance plus : Bool) (axis : ℝ) (j₁ j₂ : ℕ),
    let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a)
    GraphDerivativeBound n (graphAmplitudePullback b x distance plus axis δ j₁ j₂ Ψ)
      A (1+4*max 1 δ⁻¹+sourceSymbolScale N sig L) := by
  obtain ⟨B,hB,N₀,hb⟩ := uniform_actual_four_symbol_budget hsig K n
  obtain ⟨W,hW,hw⟩ := graph_source_weight_derivative_budget n
  obtain ⟨Jc,hJc,hjc⟩ := graph_fixed_derivative_budget
    (fun _ hp => graphShellJacobian_contDiffAt hΨ hp) n
  refine ⟨(Jc*W)*B,mul_nonneg (mul_nonneg hJc hW) hB,N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx δ hδ hcap distance plus axis j₁ j₂
  dsimp only
  have hfour := hb N hN S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
    (fun a => decide (a.val < 2)) (fun a => if a.val < 2 then 0 else graphSourceChartAxis distance plus)
  have hD := sourceSymbolScale_pos N sig L
  have hweight := hjc.mul (hw δ hδ hcap distance plus axis j₁ j₂) hJc hW zero_le_one (by positivity)
  have hall := hweight.mul hfour (mul_nonneg hJc hW) hB (by positivity) hD.le
  exact hall.congr (fun p _ => graphAmplitudePullback_factorization _ x distance plus axis δ j₁ j₂ Ψ p)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphAmplitudeScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem graphNonedgeDerivativeScale_one_le (N : ℕ) {sig u : ℝ}
    (hsig : 0 ≤ sig) (hu : 0 ≤ u) : 1 ≤ graphNonedgeDerivativeScale N sig u := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Real.one_le_rpow (by norm_num) hu
  · exact Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)

theorem source_symbol_le_nonedge_scale (N L : ℕ) {sig u : ℝ}
    (hsig : 0 ≤ sig) (hu : 0 ≤ u) (hL : (L:ℝ) ≤ u+2*sig*(N:ℝ)) :
    sourceSymbolScale N sig L ≤ graphNonedgeDerivativeScale N sig u := by
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  unfold sourceSymbolScale graphNonedgeDerivativeScale
  rw [mul_max_of_nonneg _ _ (by positivity)]
  apply max_le
  · simp only [mul_one,dyadic_power_real,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [hu, mul_nonneg hsig hN]
  · rw [← Real.rpow_natCast (2:ℝ) L]
    simp only [dyadic_power_real,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg hsig hN]

theorem graph_bin_le_nonedge_scale (N : ℕ) {sig t u c₀ : ℝ}
    (hsig : 0 ≤ sig) (hu : 0 ≤ u) (_hc : 0 < c₀)
    (ht : t ≤ u+2*sig*(N:ℝ)) :
    max 1 (graphAngularScale N sig t c₀)⁻¹ ≤
      max 1 c₀⁻¹ * graphNonedgeDerivativeScale N sig u := by
  have hE := graphNonedgeDerivativeScale_one_le N hsig hu
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hunc : (graphUncappedAngularScale N sig t)⁻¹ ≤ graphNonedgeDerivativeScale N sig u := by
    simp only [graphUncappedAngularScale,graphNonedgeDerivativeScale,dyadic_power_real,
      ← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_neg_one,
      ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg hsig hN]
  have hM : 1 ≤ max 1 c₀⁻¹ := le_max_left _ _
  have hEM : graphNonedgeDerivativeScale N sig u ≤ max 1 c₀⁻¹ * graphNonedgeDerivativeScale N sig u :=
    le_mul_of_one_le_left (zero_le_one.trans hE) hM
  apply max_le (hE.trans hEM)
  unfold graphAngularScale
  by_cases hcap : c₀ ≤ graphUncappedAngularScale N sig t
  · rw [min_eq_left hcap]
    exact (le_max_right 1 c₀⁻¹).trans (le_mul_of_one_le_right (zero_le_one.trans hM) hE)
  · rw [min_eq_right (le_of_not_ge hcap)]
    exact hunc.trans hEM

theorem graph_total_amplitude_scale (N L : ℕ) {sig t u c₀ : ℝ}
    (hsig : 0 ≤ sig) (hu : 0 ≤ u) (hc : 0 < c₀)
    (ht : t ≤ u+2*sig*(N:ℝ)) (hL : (L:ℝ) ≤ u+2*sig*(N:ℝ)) :
    1+4*max 1 (graphAngularScale N sig t c₀)⁻¹+sourceSymbolScale N sig L ≤
      (2+4*max 1 c₀⁻¹)*graphNonedgeDerivativeScale N sig u := by
  have hE := graphNonedgeDerivativeScale_one_le N hsig hu
  have hB := graph_bin_le_nonedge_scale N hsig hu hc ht
  have hD := source_symbol_le_nonedge_scale N L hsig hu hL
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeAmplitude
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem GraphDerivativeBound.rescale {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D q E : ℝ}
    (hf : GraphDerivativeBound n f C D) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hq : 1 ≤ q) (hE : 0 ≤ E) (hle : D ≤ q*E) :
    GraphDerivativeBound n f (C*q^n) E := by
  refine ⟨hf.smooth,?_⟩
  intro j hj η z hhi hz hlo
  calc
    _ ≤ C*D^j := hf.bound j hj η z hhi hz hlo
    _ ≤ C*(q*E)^j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hle _) hC
    _ = (C*q^j)*E^j := by rw [mul_pow]; ring
    _ ≤ (C*q^n)*E^j := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hj) hC) (pow_nonneg hE _)

theorem uniform_actual_graph_amplitude_E_oai {sig : ℝ} (hsig : 0 < sig) (K n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ a, DecidableEq (ι a)],
    ∀ (S : ∀ a, Finset (ι a)) (d : ∀ a, ι a → PolicyDescriptor) (k : ∀ a, ι a → ℕ),
    (∀ a, (S a).card ≤ (N+1)^3+1) → (∀ a, (∑ t ∈ S a, k a t) ≤ K) →
    ∀ L : ℕ, (∀ a t, t ∈ S a → descriptorLength (d a t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ a, 0 < (Q a).side) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ) (x : Fin 4 → Plane),
    (∀ a, ‖h a (x a)‖ ≤ 1) → ∀ t u : ℝ, 0 ≤ u →
    t ≤ u+2*sig*(N:ℝ) → (L:ℝ) ≤ u+2*sig*(N:ℝ) →
    ∀ (distance plus : Bool) (axis : ℝ) (j₁ j₂ : ℕ),
    let b := fun a => inheritedCircleSymbol (S a) (d a) (k a) (Q a) (ρ a) (mass a)
      N lam sig J i (h a)
    GraphDerivativeBound n (graphAmplitudePullback b x distance plus axis (graphAngularScale N sig t c₀) j₁ j₂ Ψ)
      A (graphNonedgeDerivativeScale N sig u) := by
  obtain ⟨A,hA,N₀,hb⟩ := uniform_actual_graph_amplitude hsig K n hΨ
  let q := 2+4*max 1 c₀⁻¹
  have hq : 1 ≤ q := by dsimp [q]; linarith [le_max_left (1:ℝ) c₀⁻¹]
  refine ⟨A*q^n,mul_nonneg hA (pow_nonneg (zero_le_one.trans hq) _),N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass lam J i h x hx t u hu ht hLu distance plus axis j₁ j₂
  have he := hb N hN S d k hcard hK L hL Q hQ ρ mass lam J i h x hx
    (graphAngularScale N sig t c₀) (graphAngularScale_pos N sig t hc)
    ((min_le_left _ _).trans hcap) distance plus axis j₁ j₂
  exact he.rescale hA (by have := sourceSymbolScale_pos N sig L; positivity) hq
    (zero_le_one.trans (graphNonedgeDerivativeScale_one_le N hsig.le hu))
    (graph_total_amplitude_scale N L hsig.le hu hc ht hLu)

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_graph_amplitude_E_oai := @OAI.PlanarFalconer.uniform_actual_graph_amplitude_E_oai
