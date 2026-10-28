-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:35:08.050538+00:00
-- url     : https://prove2.me/submissions/d2f9a164-9286-4b27-b819-863290b55148

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

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

 theorem compact_smooth_to_schwartz {f : ℝ → ℂ} {a b : ℝ}
    (hs : tsupport f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = f := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  exact ⟨hc.toSchwartzMap hf,rfl⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SmoothCompositionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem compositionDerivativeCost_nonneg (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ compositionDerivativeCost g n x := by
  unfold compositionDerivativeCost
  positivity

 theorem compositionDerivativeCost_continuous {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (n : ℕ) : Continuous (compositionDerivativeCost g n) := by
  apply continuous_finsetSum
  intro c _
  apply continuous_finsetProd
  intro j _
  exact (hg.continuous_iteratedDeriv _ (by exact_mod_cast (le_top : (c.partSize j:ℕ∞) ≤ ⊤))).norm

 theorem composition_derivative_scale {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ) (x : ℝ)
    (hb : ∀ k ≤ n, ‖iteratedDeriv k f (g x)‖ ≤ C*D^k) :
    ‖iteratedDeriv n (f ∘ g) x‖ ≤ compositionDerivativeCost g n x * (C*D^n) := by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt hg.contDiffAt
    (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))]
  rw [compositionDerivativeCost,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  rw [norm_smul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  exact (hb c.length c.length_le).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD c.length_le) hC)

 theorem weightedCompositionCost_continuous {w : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    Continuous (weightedCompositionCost w g n) := by
  apply continuous_finsetSum
  intro k _
  exact (continuous_const.mul (hw.continuous_iteratedDeriv k
    (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).norm).mul
      (compositionDerivativeCost_continuous hg (n-k))

 theorem weighted_composition_derivative_scale {w f : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ) (x : ℝ)
    (hb : ∀ k ≤ n, ‖iteratedDeriv k f (g x)‖ ≤ C*D^k) :
    ‖iteratedDeriv n (fun x => w x * f (g x)) x‖ ≤
      weightedCompositionCost w g n x * (C*D^n) := by
  have hwn : ContDiffAt ℝ n w x := (hw.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  have hfn : ContDiffAt ℝ n (f ∘ g) x :=
    ((hf.comp hg).of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  change ‖iteratedDeriv n (fun y => w y * (f ∘ g) y) x‖ ≤ _
  rw [iteratedDeriv_fun_mul hwn hfn,weightedCompositionCost,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  simp only [norm_mul,Complex.norm_natCast]
  have hc := composition_derivative_scale hf hg hC hD (n-k) x
    (fun l hl => hb l (hl.trans (Nat.sub_le _ _)))
  have hp : C*D^(n-k) ≤ C*D^n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.sub_le _ _)) hC
  calc
    _ ≤ (n.choose k:ℝ) * ‖iteratedDeriv k w x‖ *
        (compositionDerivativeCost g (n-k) x * (C*D^n)) := by
      gcongr
      exact hc.trans (mul_le_mul_of_nonneg_left hp (compositionDerivativeCost_nonneg _ _ _))
    _ = _ := by ring

 theorem compact_weighted_composition_scale {w : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ y, ‖iteratedDeriv k f y‖ ≤ C*D^k) →
      ∀ x ∈ K, ‖iteratedDeriv n (fun y => w y * f (g y)) x‖ ≤ A*C*D^n := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (weightedCompositionCost_continuous hw hg n).continuousOn
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro f hf C D hC hD hb x hx
  have hA : weightedCompositionCost w g n x ≤ max 0 B :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_right _ _))
  calc
    _ ≤ weightedCompositionCost w g n x * (C*D^n) :=
      weighted_composition_derivative_scale hw hf hg hC hD n x (fun k hk => hb k hk _)
    _ ≤ max 0 B * (C*D^n) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularIntegrationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem cosineOscillator_hasDerivAt (Λ x : ℝ) :
    HasDerivAt (cosineOscillator Λ)
      (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x) x := by
  have h := (((Real.hasDerivAt_cos x).ofReal_comp).const_mul (Complex.I*(Λ:ℂ))).cexp
  have he : Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos x:ℂ)) *
      (Complex.I*(Λ:ℂ)*(-Real.sin x:ℝ)) =
        -Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x := by
    simp only [cosineOscillator,Complex.ofReal_neg]
    ring
  rw [he] at h
  exact h

 theorem cosineOscillator_continuous (Λ : ℝ) : Continuous (cosineOscillator Λ) :=
  continuous_iff_continuousAt.mpr (fun x => (cosineOscillator_hasDerivAt Λ x).continuousAt)

 theorem cosineOscillator_norm (Λ x : ℝ) : ‖cosineOscillator Λ x‖ = 1 := by
  simp [cosineOscillator,Complex.norm_exp]

 theorem angular_integration_by_parts {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hqs : ∀ x ∈ tsupport f, (Real.sin x:ℂ)*q x = 1) (Λ : ℝ) :
    (∫ x : ℝ, cosineOscillator Λ x * angularTransport q f x) =
      (Complex.I*(Λ:ℂ)) * ∫ x : ℝ, cosineOscillator Λ x * f x := by
  let v : ℝ → ℂ := fun x => q x * f x
  have hv : ContDiff ℝ ∞ v := hq.mul hf
  have hvc : HasCompactSupport v := hc.mul_left
  have hE := cosineOscillator_continuous Λ
  have hv' : Continuous (angularTransport q f) := hv.continuous_deriv (by simp)
  have hi₁ : Integrable (fun x => cosineOscillator Λ x * angularTransport q f x) :=
    (hE.mul hv').integrable_of_hasCompactSupport hvc.deriv.mul_left
  have hE' : Continuous (fun x => -Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sin)).mul hE
  have hi₂ : Integrable (fun x => (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x)*v x) :=
    (hE'.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hi₃ : Integrable (fun x => cosineOscillator Λ x * v x) :=
    (hE.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := cosineOscillator Λ) (v := v) (v' := angularTransport q f)
    (fun x _ => cosineOscillator_hasDerivAt Λ x)
    (fun x _ => (hv.differentiable (by simp)).differentiableAt.hasDerivAt) hi₁ hi₂ hi₃
  change (∫ x : ℝ, cosineOscillator Λ x * angularTransport q f x) = _ at hh
  rw [hh]
  have he : (fun x => (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x)*v x) =
      fun x => -(Complex.I*(Λ:ℂ)) * (cosineOscillator Λ x * f x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · dsimp [v]
      calc
        _ = -(Complex.I*(Λ:ℂ)) * cosineOscillator Λ x * ((Real.sin x:ℂ)*q x) * f x := by ring
        _ = _ := by rw [hqs x hx]; ring
    · simp [v,image_eq_zero_of_notMem_tsupport hx]
  rw [he,integral_const_mul]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransportBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem angularTransportIterate_contDiff {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (angularTransportIterate q n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (contDiff_infty_iff_deriv.mp (hq.mul ih)).2

 theorem angularTransportIterate_support (q f : ℝ → ℂ) (n : ℕ) :
    tsupport (angularTransportIterate q n f) ⊆ tsupport f := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans ih)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothInverseSine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem smoothInverseSine_contDiff (η : ℝ) (hη : 0 < η) :
    ContDiff ℝ ∞ (smoothInverseSine η hη) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : Real.sin x = 0
  · have hb : (sineZeroCutoff η hη : ℝ → ℝ) =ᶠ[𝓝 (Real.sin x)] (fun _ => 1) := by
      rw [hx]
      exact (sineZeroCutoff η hη).eventuallyEq_one
    have he : smoothInverseSine η hη =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hb.comp_tendsto Real.continuous_sin.continuousAt] with y hy
      simp only [Function.comp_apply] at hy
      simp [smoothInverseSine,hy]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hb : ContDiffAt ℝ ∞ (fun y => sineZeroCutoff η hη (Real.sin y)) x :=
      (sineZeroCutoff η hη).contDiffAt.comp x Real.contDiff_sin.contDiffAt
    exact (contDiffAt_const.sub hb).mul (Real.contDiff_sin.contDiffAt.inv hx)

 theorem smoothInverseSine_eq {η : ℝ} (hη : 0 < η) {θ : ℝ}
    (hθ : η ≤ |Real.sin θ|) : (Real.sin θ)*smoothInverseSine η hη θ = 1 := by
  have hb : sineZeroCutoff η hη (Real.sin θ) = 0 :=
    (sineZeroCutoff η hη).zero_of_le_dist (by simpa [sineZeroCutoff,Real.dist_eq] using hθ)
  have hs : Real.sin θ ≠ 0 := by intro he; simp [he] at hθ; linarith
  simp [smoothInverseSine,hb,hs]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNonstationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem angularTransportIterate_integral {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hqs : ∀ x ∈ tsupport f, (Real.sin x:ℂ)*q x = 1) (Λ : ℝ) (n : ℕ) :
    (∫ x : ℝ, cosineOscillator Λ x * angularTransportIterate q n f x) =
      (Complex.I*(Λ:ℂ))^n * ∫ x : ℝ, cosineOscillator Λ x * f x := by
  induction n with
  | zero => simp [angularTransportIterate]
  | succ n ih =>
    have hi := angularTransportIterate_contDiff hq hf n
    have hc' : HasCompactSupport (angularTransportIterate q n f) :=
      hc.mono' (fun x hx => angularTransportIterate_support q f n (subset_closure hx))
    have hh := angular_integration_by_parts hq hi hc'
      (fun x hx => hqs x (angularTransportIterate_support q f n hx)) Λ
    change (∫ x : ℝ, cosineOscillator Λ x * angularTransport q (angularTransportIterate q n f) x) = _
    rw [hh,ih,pow_succ]
    ring

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_ReciprocalSineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

theorem reciprocal_sine_germ_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℝ → ℝ), ContDiff ℝ ∞ q →
      ∀ η, 0 < η → η ≤ 1 → ∀ x, η ≤ |Real.sin x| →
      (fun y => q y * Real.sin y) =ᶠ[𝓝 x] (fun _ => 1) →
      |iteratedDeriv n q x| ≤ C * η⁻¹^(n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro q hq η hη hη1 x hx he
      have heq := he.eq_of_nhds
      have hs : Real.sin x ≠ 0 := by intro hz; simp [hz] at hx; linarith
      have hqv : q x = (Real.sin x)⁻¹ := by
        calc
          q x = q x * Real.sin x * (Real.sin x)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
          _ = (Real.sin x)⁻¹ := by rw [heq, one_mul]
      simp only [iteratedDeriv_zero, hqv, abs_inv, Nat.zero_add, pow_one, one_mul]
      exact inv_le_inv₀ (lt_of_lt_of_le hη hx) hη |>.mpr hx
    | succ n =>
      classical
      let B : ℕ → ℝ := fun k => if hk : k < n+1 then (ih k hk).choose else 0
      have hB0 (k : ℕ) : 0 ≤ B k := by
        dsimp [B]
        split_ifs with hk
        · exact (ih k hk).choose_spec.1
        · exact le_rfl
      let C := ∑ k ∈ Finset.range (n+1), ((n+1).choose k : ℝ) * B k
      have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hB0 k))
      refine ⟨C, hC, ?_⟩
      intro q hq η hη hη1 x hx he
      have hηinv : 1 ≤ η⁻¹ := (one_le_inv₀ hη).mpr hη1
      have hqfin : ContDiffAt ℝ (n+1 : ℕ) q x :=
        (hq.of_le (WithTop.coe_le_coe.mpr (show ((n+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      have hsfin : ContDiffAt ℝ (n+1 : ℕ) Real.sin x := Real.contDiff_sin.contDiffAt
      have hid := he.iteratedDeriv_eq (n+1)
      rw [iteratedDeriv_fun_mul hqfin hsfin, Finset.sum_range_succ] at hid
      simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        iteratedDeriv_zero, iteratedDeriv_const, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, ↓reduceIte] at hid
      have hlast : iteratedDeriv (n+1) q x * Real.sin x =
          -(∑ k ∈ Finset.range (n+1),
            ((n+1).choose k : ℝ) * iteratedDeriv k q x * iteratedDeriv (n+1-k) Real.sin x) := by
        linarith
      have hsum : |iteratedDeriv (n+1) q x| * |Real.sin x| ≤ C * η⁻¹^(n+1) := by
        rw [← abs_mul, hlast, abs_neg]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        change _ ≤ (∑ k ∈ Finset.range (n+1), _) * _
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n+1 := Finset.mem_range.mp hk
        have hb := (ih k hk').choose_spec.2 q hq η hη hη1 x hx he
        change |iteratedDeriv k q x| ≤ (ih k hk').choose * η⁻¹^(k+1) at hb
        have hbk : |iteratedDeriv k q x| ≤ B k * η⁻¹^(n+1) := by
          have heB : B k = (ih k hk').choose := dite_eq_left hk'
          rw [heB]
          exact hb.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hηinv (by omega)) (ih k hk').choose_spec.1)
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ ((n+1).choose k : ℝ) * (B k * η⁻¹^(n+1)) * 1 := by
            exact mul_le_mul (mul_le_mul_of_nonneg_left hbk (Nat.cast_nonneg _))
              (Real.abs_iteratedDeriv_sin_le_one _ _) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (hB0 k) (pow_nonneg (le_of_lt (inv_pos.mpr hη)) _)))
          _ = _ := by ring
      have hsmall : |iteratedDeriv (n+1) q x| * η ≤ C * η⁻¹^(n+1) :=
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans hsum
      have hh := (le_div_iff₀ hη).mpr hsmall
      simpa only [div_eq_mul_inv, pow_succ, mul_assoc] using hh

theorem smoothInverseSine_half_germ {η : ℝ} (hη : 0 < η) {x : ℝ}
    (hx : η ≤ |Real.sin x|) :
    (fun y => smoothInverseSine (η/2) (half_pos hη) y * Real.sin y)
      =ᶠ[𝓝 x] (fun _ => 1) := by
  have hh : η/2 < |Real.sin x| := (half_lt_self hη).trans_le hx
  have he : ∀ᶠ y in 𝓝 x, η/2 < |Real.sin y| :=
    (Real.continuous_sin.abs.continuousAt.eventually (lt_mem_nhds hh))
  filter_upwards [he] with y hy
  simpa only [mul_comm] using smoothInverseSine_eq (half_pos hη) hy.le

theorem smoothInverseSine_half_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η (hη : 0 < η), η ≤ 1 → ∀ x, η ≤ |Real.sin x| →
      ‖iteratedDeriv n (fun y => (smoothInverseSine (η/2) (half_pos hη) y : ℂ)) x‖ ≤
        C * η⁻¹^(n+1) := by
  obtain ⟨C,hC,hb⟩ := reciprocal_sine_germ_derivatives n
  refine ⟨C,hC,?_⟩
  intro η hη hη1 x hx
  rw [iteratedDeriv_ofReal (smoothInverseSine_contDiff _ _), Complex.norm_real, Real.norm_eq_abs]
  exact hb _ (smoothInverseSine_contDiff _ _) η hη hη1 x hx (smoothInverseSine_half_germ hη hx)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_CompactMultiplierScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem compact_multiplier_uniform_derivatives {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {K : Set ℝ} (hK : IsCompact K) (hs : tsupport w ⊆ K) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
      ∀ {C D : ℝ}, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
      ∀ k ≤ n, ∀ x, ‖iteratedDeriv k (fun y => w y*f y) x‖ ≤ (A*C)*D^k := by
  choose A hA hbound using fun k => compact_weighted_composition_scale hw
    (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)) hK k
  let B : ℝ := ∑ k ∈ Finset.range (n+1), A k
  refine ⟨B,Finset.sum_nonneg (fun k _ => hA k),?_⟩
  intro f hf C D hC hD hb k hk x
  have hkB : A k ≤ B := Finset.single_le_sum (fun l _ => hA l)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  by_cases hx : x ∈ K
  · have hh := hbound k f hf C D hC hD (fun l hl => hb l (hl.trans hk)) x hx
    change ‖iteratedDeriv k (fun y => w y*f y) x‖ ≤ A k*C*D^k at hh
    apply hh.trans
    gcongr
  · have he : iteratedDeriv k (fun y => w y*f y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hx (hs (tsupport_mul_subset_left
        (complex_iteratedDeriv_tsupport _ k hh))))
    rw [he,norm_zero]
    have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => hA k)
    positivity

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ScaledAngularTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem scaledAngularTransportCost_nonneg {Q : ℕ → ℝ} (hQ : ∀ k, 0 ≤ Q k)
    (n m : ℕ) : 0 ≤ scaledAngularTransportCost Q n m := by
  induction n generalizing m with
  | zero => exact zero_le_one
  | succ n ih =>
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hQ k)) (ih _))

theorem angularTransportIterate_scaled_bound {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    {Q : ℕ → ℝ} (hQ : ∀ k, 0 ≤ Q k) {C U D : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hD : 0 ≤ D) (n m : ℕ) (x : ℝ)
    (hbq : ∀ k ≤ n+m, ‖iteratedDeriv k q x‖ ≤ Q k * U * D^k)
    (hbf : ∀ k ≤ n+m, ‖iteratedDeriv k f x‖ ≤ C * D^k) :
    ‖iteratedDeriv m (angularTransportIterate q n f) x‖ ≤
      scaledAngularTransportCost Q n m * C * U^n * D^(n+m) := by
  induction n generalizing m with
  | zero => simpa [angularTransportIterate, scaledAngularTransportCost] using hbf m (by omega)
  | succ n ih =>
    have hqn : ContDiffAt ℝ (m+1 : ℕ) q x :=
      (hq.of_le (WithTop.coe_le_coe.mpr (show ((m+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    have hfn : ContDiffAt ℝ (m+1 : ℕ) (angularTransportIterate q n f) x :=
      ((angularTransportIterate_contDiff hq hf n).of_le
        (WithTop.coe_le_coe.mpr (show ((m+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    change ‖iteratedDeriv m (deriv (fun y => q y * angularTransportIterate q n f y)) x‖ ≤ _
    rw [← iteratedDeriv_succ', iteratedDeriv_fun_mul hqn hfn]
    change ‖_‖ ≤ (∑ k ∈ Finset.range (m+2), _) * C * U^(n+1) * D^(n+1+m)
    simp only [Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ m+1 := by simp only [Finset.mem_range] at hk; omega
    have hl : n+(m+1-k) ≤ n+1+m := by omega
    have hb := ih (m+1-k) (fun j hj => hbq j (hj.trans hl))
      (fun j hj => hbf j (hj.trans hl))
    simp only [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ((m+1).choose k : ℝ) * (Q k * U * D^k) *
          (scaledAngularTransportCost Q n (m+1-k) * C * U^n * D^(n+(m+1-k))) := by
        apply mul_le_mul_of_nonneg
        · exact mul_le_mul_of_nonneg_left (hbq k (by omega)) (Nat.cast_nonneg _)
        · exact hb
        · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
        · exact mul_nonneg
            (mul_nonneg (mul_nonneg (scaledAngularTransportCost_nonneg hQ _ _) hC)
              (pow_nonneg hU _)) (pow_nonneg hD _)
      _ = _ := by
        have he : k+(n+(m+1-k)) = n+1+m := by omega
        rw [pow_succ]
        calc
          _ = ((m+1).choose k : ℝ) * Q k * scaledAngularTransportCost Q n (m+1-k) *
              C * (U^n * U) * (D^k * D^(n+(m+1-k))) := by ring
          _ = _ := by rw [← pow_add, he]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ScaleUniformNonstationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

theorem angular_nonstationary_scale_uniform {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ η, 0 < η → η ≤ 1 →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → tsupport f ⊆ Icc a b →
    (∀ x ∈ tsupport f, η ≤ |Real.sin x|) →
    ∀ {C D Λ : ℝ}, 0 ≤ C → η⁻¹ ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ ≤ A*C*(D/(Λ*η))^n := by
  choose Q hQ hbQ using smoothInverseSine_half_derivatives
  let B := scaledAngularTransportCost Q n 0
  have hB : 0 ≤ B := scaledAngularTransportCost_nonneg hQ n 0
  refine ⟨B*(b-a), mul_nonneg hB (sub_nonneg.mpr hab), ?_⟩
  intro η hη hη1 f hf hs haway C D Λ hC hD hΛ hb
  let q : ℝ → ℂ := fun x => (smoothInverseSine (η/2) (half_pos hη) x : ℂ)
  have hq : ContDiff ℝ ∞ q :=
    Complex.ofRealCLM.contDiff.comp (smoothInverseSine_contDiff _ _)
  have hD0 : 0 ≤ D := (le_of_lt (inv_pos.mpr hη)).trans hD
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have hqs : ∀ x ∈ tsupport f, (Real.sin x : ℂ)*q x = 1 := by
    intro x hx
    have hh := (smoothInverseSine_half_germ hη (haway x hx)).eq_of_nhds
    dsimp [q]
    exact_mod_cast (show Real.sin x * smoothInverseSine (η/2) (half_pos hη) x = 1 by
      simpa only [mul_comm] using hh)
  have hit := angularTransportIterate_contDiff hq hf n
  have hist : tsupport (angularTransportIterate q n f) ⊆ Icc a b :=
    (angularTransportIterate_support q f n).trans hs
  have hib : ∀ x, ‖angularTransportIterate q n f x‖ ≤ B*C*η⁻¹^n*D^n := by
    intro x
    by_cases hx : x ∈ tsupport f
    · have hbq : ∀ k ≤ n+0, ‖iteratedDeriv k q x‖ ≤ Q k * η⁻¹ * D^k := by
        intro k hk
        calc
          _ ≤ Q k * η⁻¹^(k+1) := hbQ k η hη hη1 x (haway x hx)
          _ = Q k * η⁻¹ * η⁻¹^k := by rw [pow_succ]; ring
          _ ≤ Q k * η⁻¹ * D^k := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hη)) hD k)
            (mul_nonneg (hQ k) (le_of_lt (inv_pos.mpr hη)))
      simpa only [iteratedDeriv_zero, Nat.add_zero] using
        angularTransportIterate_scaled_bound hq hf hQ hC (le_of_lt (inv_pos.mpr hη))
          hD0 n 0 x hbq (fun k hk => hb k (by simpa using hk) x hx)
    · rw [image_eq_zero_of_notMem_tsupport
        (fun hh => hx (angularTransportIterate_support q f n hh)), norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hB hC) (pow_nonneg (le_of_lt (inv_pos.mpr hη)) _))
        (pow_nonneg hD0 _)
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hist hit
  have hsφ : tsupport (φ : ℝ → ℂ) ⊆ Icc a b := by simpa [hφ] using hist
  have hbφ : ∀ x, ‖iteratedDeriv 0 (φ : ℝ → ℂ) x‖ ≤ B*C*η⁻¹^n*D^n := by
    simpa [hφ] using hib
  have hL := compact_derivative_integral_bound φ hab hsφ 0 hbφ
  simp only [iteratedDeriv_zero] at hL
  have hφ' : ∀ x, φ x = angularTransportIterate q n f x := congrFun hφ
  simp only [hφ'] at hL
  have hi : ‖∫ x : ℝ, cosineOscillator Λ x * angularTransportIterate q n f x‖ ≤
      (B*C*η⁻¹^n*D^n)*(b-a) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul, cosineOscillator_norm, one_mul] using hL
  rw [angularTransportIterate_integral hq hf hc hqs Λ n, norm_mul, norm_pow, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΛ] at hi
  have hh := (le_div_iff₀ (pow_pos hΛ n)).mpr (show
    ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ * Λ^n ≤ (B*C*η⁻¹^n*D^n)*(b-a) by
      simpa only [mul_comm (Λ^n)] using hi)
  apply hh.trans_eq
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow]
  ring

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

theorem selectedBinAmplitude_contDiff (δ : ℝ) (S : Finset ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (selectedBinAmplitude δ S f) :=
  (Complex.ofRealCLM.contDiff.comp
    (ContDiff.sum (fun k _ => periodicAngularBin_contDiff _ k))).mul hf

theorem selectedBinAmplitude_derivatives (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ, 0 < δ → δ ≤ 2*Real.pi → ∀ S : Finset ℕ,
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {C D : ℝ}, 0 ≤ C → 0 ≤ D →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ∀ j ≤ n, ∀ x, ‖iteratedDeriv j (selectedBinAmplitude δ S f) x‖ ≤
      A*C*(max D δ⁻¹)^j := by
  choose Q hQ hbQ using selectedAngularBins_scale_derivatives
  let B := ∑ j ∈ Finset.range (n+1), Q j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hQ j)
  refine ⟨B*2^n, by positivity, ?_⟩
  intro δ hδ hcap S f hf C D hC hD hb j hj x
  let g : ℝ → ℝ := fun θ => ∑ k ∈ S, periodicAngularBin (angularBinCount δ) k θ
  have hg : ContDiff ℝ ∞ g := ContDiff.sum (fun k _ => periodicAngularBin_contDiff _ k)
  have hbg : ∀ k ≤ j, ‖iteratedDeriv k (fun y => (g y : ℂ)) x‖ ≤ B*δ⁻¹^k := by
    intro k hk
    rw [iteratedDeriv_ofReal hg, Complex.norm_real]
    have hQB : Q k ≤ B := Finset.single_le_sum (fun l _ => hQ l)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hk.trans hj)))
    exact (hbQ k δ hδ hcap S x).trans
      (mul_le_mul_of_nonneg_right hQB (by positivity))
  have hm := complex_mul_derivative_scale (Complex.ofRealCLM.contDiff.comp hg) hf
    hB hC (inv_nonneg.mpr hδ.le) hD j x hbg (fun k hk => hb k (hk.trans hj) x)
  apply hm.trans
  have hscale : δ⁻¹+D ≤ 2*max D δ⁻¹ := by
    have h1 := le_max_left D δ⁻¹
    have h2 := le_max_right D δ⁻¹
    linarith
  calc
    _ ≤ B*C*(2*max D δ⁻¹)^j := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hscale j) (mul_nonneg hB hC)
    _ = (B*2^j)*C*(max D δ⁻¹)^j := by rw [mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (hD.trans (le_max_left _ _)) _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) hB) hC

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphDirectionStability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

 theorem excluded_direction_separation {actual center dir : UnitCircle} {δ ε K : ℝ}
    (hmove : dist actual center ≤ ε) (hexcluded : K*δ ≤ dist center dir) :
    K*δ-ε ≤ dist actual dir := by
  have htri := dist_triangle center actual dir
  rw [dist_comm center actual] at htri
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Metric
open scoped ContDiff Topology

theorem inactiveAngularLabels_separation (n : ℕ) (e : UnitCircle) (radius : ℝ)
    {j : ℕ} (hj : j ∈ inactiveAngularLabels n e radius)
    {dir : UnitCircle} (hd : dir ∈ tsupport (circleAngularBin n j)) :
    radius ≤ dist e dir := by
  classical
  exact le_of_not_gt (fun hh => (Finset.mem_filter.mp hj).2 ⟨dir,hd,hh⟩)

theorem inactive_angular_sum_support (n : ℕ) (e : UnitCircle) (radius : ℝ) :
    tsupport (fun θ => ∑ j ∈ inactiveAngularLabels n e radius, periodicAngularBin n j θ) ⊆
      {θ | radius ≤ dist e (sourceUnitDirection θ)} := by
  apply closure_minimal
  · intro θ hθ
    by_contra hh
    apply hθ
    apply Finset.sum_eq_zero
    intro j hj
    by_contra hj0
    have hmem : sourceUnitDirection θ ∈ tsupport (circleAngularBin n j) := by
      apply subset_closure
      simpa only [Function.mem_support, circleAngularBin_comp] using hj0
    exact hh (inactiveAngularLabels_separation n e radius hj hmem)
  · exact isClosed_le continuous_const (continuous_const.dist continuous_sourceUnitDirection)

theorem sine_separation_of_forward_chord {θ φ δ : ℝ} (hδ : 0 ≤ δ)
    (hcos : 0 ≤ Real.cos (θ-φ))
    (hd : 2*δ ≤ dist (sourceUnitDirection θ) (sourceUnitDirection φ)) :
    δ ≤ |Real.sin (θ-φ)| := by
  have he := sourceUnitDirection_dist_sq θ φ
  have htrig := Real.sin_sq_add_cos_sq (θ-φ)
  have hc := Real.cos_le_one (θ-φ)
  have hsq := sq_le_sq₀ (by positivity : 0 ≤ 2*δ) dist_nonneg |>.mpr hd
  have hprod : 0 ≤ Real.cos (θ-φ)*(1-Real.cos (θ-φ)) := mul_nonneg hcos (sub_nonneg.mpr hc)
  have habs := sq_abs (Real.sin (θ-φ))
  nlinarith [abs_nonneg (Real.sin (θ-φ))]

theorem inactive_bin_sine_separation {δ φ : ℝ} (hδ : 0 < δ) (e : UnitCircle)
    (hmove : dist (sourceUnitDirection φ) e ≤ δ) {w f : ℝ → ℂ}
    (hcone : ∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ))
    {θ : ℝ}
    (hθ : θ ∈ tsupport (fun y => w y * selectedBinAmplitude δ
      (inactiveAngularLabels (angularBinCount δ) e (3*δ)) f y)) :
    δ ≤ |Real.sin (θ-φ)| := by
  have hw : θ ∈ tsupport w := tsupport_mul_subset_left hθ
  have hs : θ ∈ tsupport (fun y => ∑ j ∈ inactiveAngularLabels (angularBinCount δ) e (3*δ),
      periodicAngularBin (angularBinCount δ) j y) := by
    have hb := tsupport_mul_subset_left (tsupport_mul_subset_right hθ)
    apply closure_minimal (s := Function.support (fun y =>
      ((∑ j ∈ inactiveAngularLabels (angularBinCount δ) e (3*δ),
        periodicAngularBin (angularBinCount δ) j y : ℝ) : ℂ)))
      (fun y hy => subset_closure (by simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hy))
      isClosed_closure hb
  have hsep := inactive_angular_sum_support (angularBinCount δ) e (3*δ) hs
  have hchord := excluded_direction_separation (δ := δ) (ε := δ) (K := 3) hmove hsep
  apply sine_separation_of_forward_chord hδ.le (hcone θ hw)
  rw [dist_comm] at hchord
  linarith

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

theorem graphAngularScale_cap_inactive {sig κ c₀ : ℝ}
    (hgap : 10*sig < κ) (hc : 0 < c₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t : ℝ, κ*(N : ℝ) ≤ t →
      graphAngularScale N sig t c₀ = graphUncappedAngularScale N sig t := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (sub_pos.mpr hgap) c₀⁻¹
  refine ⟨N₀,?_⟩
  intro N hN t ht
  apply min_eq_right
  have hb : graphUncappedAngularScale N sig t ≤ ((2 : ℝ)^N)^(sig*10-κ) := by
    simp only [graphUncappedAngularScale, dyadic_power_real, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hp : 0 < ((2 : ℝ)^N)^(κ-10*sig) := by positivity
  have hi := inv_anti₀ (inv_pos.mpr hc) (hN₀ N hN)
  simp only [inv_inv] at hi
  apply hb.trans
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  rw [show sig*10-κ = -(κ-10*sig) by ring, Real.rpow_neg (by positivity)]

theorem inactive_bin_scale_slack (N L : ℕ) {sig t u c Λ : ℝ}
    (hsig : 0 ≤ sig) (hc : 0 < c)
    (ht : t ≤ u+2*sig*(N : ℝ)) (hu : 10*sig*(N : ℝ) ≤ u)
    (hL : (L : ℝ) ≤ u+2*sig*(N : ℝ))
    (hΛ : c*(2 : ℝ)^(t+u) ≤ Λ) :
    c*((2 : ℝ)^N)^(18*sig) ≤ Λ*(graphUncappedAngularScale N sig t)^2 ∧
    sourceSymbolScale N sig L / (Λ*graphUncappedAngularScale N sig t) ≤
      c⁻¹*((2 : ℝ)^N)^(-19*sig) := by
  have hδ := graphUncappedAngularScale_pos N sig t
  have hΛp : 0 < Λ := (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)).trans_le hΛ
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hδeq : (2 : ℝ)^(t+u)*graphUncappedAngularScale N sig t =
      (2 : ℝ)^u * ((2 : ℝ)^N)^(10*sig) := by
    unfold graphUncappedAngularScale
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 2
    ring
  constructor
  · have hb : ((2 : ℝ)^N)^(18*sig) ≤
        (2 : ℝ)^(t+u)*(graphUncappedAngularScale N sig t)^2 := by
      simp only [graphUncappedAngularScale, dyadic_power_real,
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      norm_num at *
      nlinarith
    exact (mul_le_mul_of_nonneg_left hb hc.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hΛ (sq_nonneg (graphUncappedAngularScale N sig t)))
  · have hD : sourceSymbolScale N sig L ≤ (2 : ℝ)^u * ((2 : ℝ)^N)^(-9*sig) := by
      unfold sourceSymbolScale
      rw [mul_max_of_nonneg _ _ (by positivity)]
      apply max_le
      · simp only [mul_one, dyadic_power_real, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith
      · rw [← Real.rpow_natCast (2 : ℝ) L]
        simp only [dyadic_power_real, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_nonneg hsig hN]
    apply (div_le_iff₀ (mul_pos hΛp hδ)).mpr
    have he : (2 : ℝ)^u * ((2 : ℝ)^N)^(-9*sig) =
        (c⁻¹*((2 : ℝ)^N)^(-19*sig)) * (c*(2 : ℝ)^(t+u)*graphUncappedAngularScale N sig t) := by
      rw [mul_assoc c, hδeq]
      calc
        _ = (2 : ℝ)^u * (((2 : ℝ)^N)^(-19*sig) * ((2 : ℝ)^N)^(10*sig)) := by
          rw [← Real.rpow_add (by positivity)]
          congr 2
          ring
        _ = _ := by field_simp
    exact (hD.trans_eq he).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hΛ hδ.le) (by positivity))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedScaleNonstationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem rotated_cosine_integral (f : ℝ → ℂ) (Λ φ : ℝ) :
    (∫ x : ℝ, cosineOscillator Λ (x-φ)*f x) =
      ∫ x : ℝ, cosineOscillator Λ x * f (x+φ) := by
  have h := integral_add_right_eq_self (μ := volume) (fun x : ℝ => cosineOscillator Λ (x-φ)*f x) φ
  simpa only [add_sub_cancel_right] using h.symm

theorem angular_nonstationary_rotated_scale {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ η, 0 < η → η ≤ 1 → ∀ φ : ℝ, |φ| ≤ Real.pi →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → tsupport f ⊆ Icc a b →
    (∀ x ∈ tsupport f, η ≤ |Real.sin (x-φ)|) →
    ∀ {C D Λ : ℝ}, 0 ≤ C → η⁻¹ ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ (x-φ)*f x‖ ≤ A*C*(D/(Λ*η))^n := by
  obtain ⟨A,hA,hbound⟩ := angular_nonstationary_scale_uniform
    (a := a-Real.pi) (b := b+Real.pi) (by have := Real.pi_pos; linarith) n
  refine ⟨A,hA,?_⟩
  intro η hη hη1 φ hφ f hf hs haway C D Λ hC hD hΛ hb
  let g : ℝ → ℂ := fun x => f (x+φ)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have hgs : tsupport g ⊆ (fun x : ℝ => x+φ) ⁻¹' tsupport f :=
    tsupport_comp_subset_preimage f (continuous_id.add continuous_const)
  have hs' : tsupport g ⊆ Icc (a-Real.pi) (b+Real.pi) := by
    intro x hx
    have ht := hs (hgs hx)
    have hp := abs_le.mp hφ
    constructor <;> dsimp at ht <;> linarith [ht.1,ht.2,hp.1,hp.2]
  have ha' : ∀ x ∈ tsupport g, η ≤ |Real.sin x| := by
    intro x hx
    simpa only [add_sub_cancel_right] using haway (x+φ) (hgs hx)
  rw [rotated_cosine_integral]
  exact hbound η hη hη1 hg hs' ha' hC hD hΛ (fun k hk x _ => by
    dsimp [g]
    rw [iteratedDeriv_comp_add_const]
    exact hb k hk (x+φ))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_InactiveBinIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem inactive_bin_integral_bound {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
    (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ, 0 < δ → δ ≤ 1 → ∀ (e : UnitCircle) (φ : ℝ),
    |φ| ≤ Real.pi → dist (sourceUnitDirection φ) e ≤ δ →
    (∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ)) →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {C D Λ : ℝ}, 0 ≤ C → 0 ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ (x-φ) *
      (w x * selectedBinAmplitude δ (inactiveAngularLabels (angularBinCount δ) e (3*δ)) f x)‖ ≤
      A*C*(max D δ⁻¹/(Λ*δ))^n := by
  obtain ⟨B,hB,hbin⟩ := selectedBinAmplitude_derivatives n
  obtain ⟨W,hW,hweight⟩ := compact_multiplier_uniform_derivatives hw isCompact_Icc hsw n
  obtain ⟨A,hA,hnon⟩ := angular_nonstationary_rotated_scale hab n
  refine ⟨A*(W*B), by positivity, ?_⟩
  intro δ hδ hcap e φ hφ hmove hcone f hf C D Λ hC hD hΛ hb
  let S := inactiveAngularLabels (angularBinCount δ) e (3*δ)
  have hg := selectedBinAmplitude_contDiff δ S hf
  have hδπ : δ ≤ 2*Real.pi := hcap.trans (by have := Real.one_le_pi_div_two; linarith)
  have hbin' := hbin δ hδ hδπ S hf hC hD hb
  have hd : 1 ≤ max D δ⁻¹ := ((one_le_inv₀ hδ).mpr hcap).trans (le_max_right _ _)
  have hh := hweight hg (mul_nonneg hB hC) hd hbin'
  have hs : tsupport (fun y => w y * selectedBinAmplitude δ S f y) ⊆ Icc a b :=
    tsupport_mul_subset_left.trans hsw
  have hi := hnon δ hδ hcap φ hφ (hw.mul hg) hs
    (fun θ hθ => inactive_bin_sine_separation hδ e hmove hcone hθ)
    (mul_nonneg hW (mul_nonneg hB hC)) (le_max_right _ _) hΛ hh
  apply hi.trans_eq
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_InactiveBinDecay
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem inactive_bin_ratio_bound (N L : ℕ) {sig t u c Λ : ℝ}
    (hsig : 0 ≤ sig) (hc : 0 < c)
    (ht : t ≤ u+2*sig*(N : ℝ)) (hu : 10*sig*(N : ℝ) ≤ u)
    (hL : (L : ℝ) ≤ u+2*sig*(N : ℝ))
    (hΛ : c*(2 : ℝ)^(t+u) ≤ Λ) :
    max (sourceSymbolScale N sig L) (graphUncappedAngularScale N sig t)⁻¹ /
      (Λ*graphUncappedAngularScale N sig t) ≤ c⁻¹*((2 : ℝ)^N)^(-18*sig) := by
  obtain ⟨h1,h2⟩ := inactive_bin_scale_slack N L hsig hc ht hu hL hΛ
  have hδ := graphUncappedAngularScale_pos N sig t
  have hΛp : 0 < Λ := (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)).trans_le hΛ
  rw [← max_div_div_right (mul_nonneg hΛp.le hδ.le)]
  apply max_le
  · exact h2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith))
      (inv_nonneg.mpr hc.le))
  · have hi := inv_anti₀ (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)) h1
    have he : (c*((2 : ℝ)^N)^(18*sig))⁻¹ = c⁻¹*((2 : ℝ)^N)^(-18*sig) := by
      rw [mul_inv_rev, show -18*sig = -(18*sig) by ring, Real.rpow_neg (by positivity)]
      ring
    rw [he] at hi
    simpa only [div_eq_mul_inv, mul_inv_rev, pow_two, mul_assoc] using hi

theorem inactive_bin_integral_power {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
    {sig κ c T outer : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c) :
    ∃ n : ℕ, ∀ C : ℝ, 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (t u Λ : ℝ),
    κ*(N : ℝ) ≤ t → t ≤ u+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ u →
    (L : ℝ) ≤ u+2*sig*(N : ℝ) → c*(2 : ℝ)^(t+u) ≤ Λ →
    ∀ (e : UnitCircle) (φ : ℝ), |φ| ≤ Real.pi →
    dist (sourceUnitDirection φ) e ≤ graphUncappedAngularScale N sig t →
    (∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ)) →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*(sourceSymbolScale N sig L)^k) →
    ((2 : ℝ)^N)^outer * ‖∫ x : ℝ, cosineOscillator Λ (x-φ) *
      (w x * selectedBinAmplitude (graphUncappedAngularScale N sig t)
        (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t)) e
          (3*graphUncappedAngularScale N sig t)) f x)‖ ≤ ((2 : ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := exists_nat_gt ((T+outer+1)/(18*sig))
  have hexp : outer+1+(-18*sig)*(n : ℝ) ≤ -T := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 18*sig)).mp hn
    nlinarith
  obtain ⟨A,hA,hbound⟩ := inactive_bin_integral_bound hw hab hsw n
  obtain ⟨Ncap,hcap⟩ := graphAngularScale_cap_inactive hgap (by norm_num : (0 : ℝ) < 1)
  refine ⟨n,?_⟩
  intro C hC
  obtain ⟨Nc,hconst⟩ := fixed_constant_absorbed (by norm_num : (0 : ℝ) < 1) (A*C*c⁻¹^n)
  refine ⟨max Ncap Nc,?_⟩
  intro N hN L t u Λ hlow ht hu hL hΛ e φ hφ hmove hcone f hf hb
  have hδ := graphUncappedAngularScale_pos N sig t
  have hδ1 : graphUncappedAngularScale N sig t ≤ 1 := by
    have he := hcap N ((le_max_left _ _).trans hN) t hlow
    have hm := min_le_left 1 (graphUncappedAngularScale N sig t)
    change min 1 (graphUncappedAngularScale N sig t) = graphUncappedAngularScale N sig t at he
    rwa [he] at hm
  have hΛp : 0 < Λ := (mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _)).trans_le hΛ
  have hi := hbound _ hδ hδ1 e φ hφ hmove hcone hf hC (sourceSymbolScale_pos N sig L).le hΛp hb
  have hr := inactive_bin_ratio_bound N L hsig.le hc ht hu hL hΛ
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
    max (sourceSymbolScale N sig L) (graphUncappedAngularScale N sig t)⁻¹ /
      (Λ*graphUncappedAngularScale N sig t)) hr n
  have hR : 1 ≤ (2 : ℝ)^N := one_le_pow₀ (by norm_num)
  have hRp : 0 < (2 : ℝ)^N := by positivity
  have hA' : A*C*c⁻¹^n ≤ (2 : ℝ)^N := by
    simpa only [Real.rpow_one] using hconst N ((le_max_right _ _).trans hN)
  calc
    _ ≤ ((2 : ℝ)^N)^outer * (A*C*(c⁻¹*((2 : ℝ)^N)^(-18*sig))^n) := by
      exact mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hA hC))) (by positivity)
    _ = (A*C*c⁻¹^n) * ((2 : ℝ)^N)^(outer+(-18*sig)*(n : ℝ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hRp.le, Real.rpow_add hRp]
      ring
    _ ≤ (2 : ℝ)^N * ((2 : ℝ)^N)^(outer+(-18*sig)*(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hA' (by positivity)
    _ = ((2 : ℝ)^N)^(outer+1+(-18*sig)*(n : ℝ)) := by
      conv_lhs => arg 1; rw [← Real.rpow_one ((2 : ℝ)^N)]
      rw [← Real.rpow_add hRp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR hexp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RotatedActualInactive
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_rotated_actual_inactive_bins_oai {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
    {sig κ c T outer : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c)
    (K₁ K₂ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (t u Λ : ℝ),
    κ*(N : ℝ) ≤ t → t ≤ u+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ u →
    (L : ℝ) ≤ u+2*sig*(N : ℝ) → c*(2 : ℝ)^(t+u) ≤ Λ →
    ∀ (e : UnitCircle) (φ axis : ℝ), |φ| ≤ Real.pi →
    dist (sourceUnitDirection φ) e ≤ graphUncappedAngularScale N sig t →
    (∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ)) →
    ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
    ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
      (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
    S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
    S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
    (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
    ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
    ∀ (ρ₁ ρ₂ : Measure Plane) (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ)
      (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ) (x y : Plane), ‖h₁ x‖ ≤ 1 → ‖h₂ y‖ ≤ 1 →
    let f := fun θ =>
      inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁ x (sourceUnitDirection (θ+axis)) *
      conj (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂ y (sourceUnitDirection (θ+axis)))
    ((2 : ℝ)^N)^outer * ‖∫ θ : ℝ, cosineOscillator Λ (θ-φ) *
      (w θ * selectedBinAmplitude (graphUncappedAngularScale N sig t)
        (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t)) e
          (3*graphUncappedAngularScale N sig t)) f θ)‖ ≤ ((2 : ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := inactive_bin_integral_power (T := T) (outer := outer) hw hab hsw hsig hgap hc
  obtain ⟨C₁,hC₁,N₁,h₁⟩ := uniform_actual_symbol_derivatives_upto hsig K₁ n
  obtain ⟨C₂,hC₂,N₂,h₂⟩ := uniform_actual_symbol_derivatives_upto hsig K₂ n
  obtain ⟨N₃,h₃⟩ := hn (C₁*C₂*2^n)
    (mul_nonneg (mul_nonneg hC₁ hC₂) (pow_nonneg zero_le_two n))
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN L t u Λ hlow ht hu hL hΛ e φ axis hφ hmove hcone ι₁ ι₂ inst₁ inst₂
    S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
    ρ₁ ρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ x y hx hy
  let f₁ := fun θ => inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ x (sourceUnitDirection (θ+axis))
  let f₂ := fun θ => inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ y (sourceUnitDirection (θ+axis))
  have hf₁ : ContDiff ℝ ∞ f₁ :=
    (inheritedCircleSymbol_contDiff S₁ b₁ k₁ Q₁ hQ₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ x).comp
      (contDiff_id.add contDiff_const)
  have hf₂ : ContDiff ℝ ∞ f₂ :=
    (inheritedCircleSymbol_contDiff S₂ b₂ k₂ Q₂ hQ₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ y).comp
      (contDiff_id.add contDiff_const)
  have hb₁ := h₁ N ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
    S₁ b₁ k₁ hc₁ hk₁ L hl₁ Q₁ hQ₁ ρ₁ m₁ lam₁ J₁ i₁ hsp₁ x hx
  have hb₂ := h₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
    S₂ b₂ k₂ hc₂ hk₂ L hl₂ Q₂ hQ₂ ρ₂ m₂ lam₂ J₂ i₂ hsp₂ y hy
  have hs₁ (k : ℕ) (hk : k ≤ n) (θ : ℝ) :
      ‖iteratedDeriv k f₁ θ‖ ≤ C₁*(sourceSymbolScale N sig L)^k := by
    dsimp only [f₁]
    rw [iteratedDeriv_comp_add_const k
      (fun θ => inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ x (sourceUnitDirection θ))]
    exact hb₁ k hk (θ+axis)
  have hs₂ (k : ℕ) (hk : k ≤ n) (θ : ℝ) :
      ‖iteratedDeriv k f₂ θ‖ ≤ C₂*(sourceSymbolScale N sig L)^k := by
    dsimp only [f₂]
    rw [iteratedDeriv_comp_add_const k
      (fun θ => inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ y (sourceUnitDirection θ))]
    exact hb₂ k hk (θ+axis)
  apply h₃ N ((le_max_right _ _).trans hN) L t u Λ hlow ht hu hL hΛ e φ hφ hmove hcone
    (hf₁.mul (Complex.conjCLE.contDiff.comp hf₂))
  intro j hj θ
  have hbconj : ∀ k ≤ j, ‖iteratedDeriv k (fun z => conj (f₂ z)) θ‖ ≤ C₂*(sourceSymbolScale N sig L)^k := by
    intro k hk
    rw [complex_iteratedDeriv_conj hf₂, Complex.norm_conj]
    exact hs₂ k (hk.trans hj) θ
  have hh := complex_mul_derivative_scale hf₁ (Complex.conjCLE.contDiff.comp hf₂)
    hC₁ hC₂ (sourceSymbolScale_pos N sig L).le (sourceSymbolScale_pos N sig L).le j θ
    (fun k hk => hs₁ k (hk.trans hj) θ) hbconj
  apply hh.trans
  calc
    _ = (C₁*C₂*2^j)*(sourceSymbolScale N sig L)^j := by rw [← two_mul, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two hj) (mul_nonneg hC₁ hC₂)) (pow_nonneg (sourceSymbolScale_pos N sig L).le j)

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins_oai := @OAI.PlanarFalconer.uniform_rotated_actual_inactive_bins_oai
