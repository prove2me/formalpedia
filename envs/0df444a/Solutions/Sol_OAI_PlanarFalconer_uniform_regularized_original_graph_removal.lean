-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_regularized_original_graph_removal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:34:00.778461+00:00
-- url     : https://prove2.me/submissions/77d203eb-0dd3-4c26-bf8a-e0ceb5d5f8b6

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_sourceGraphFourTransform_pointIntegral
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_graph_nonedge_power

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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem dyadicPaths_card_le (N : ℕ) : (dyadicPaths N).card ≤ 4 ^ N := by
  classical
  induction N with
  | zero => simp [dyadicPaths]
  | succ N ih =>
    calc
      (dyadicPaths (N+1)).card ≤ ∑ a ∈ (Finset.univ : Finset (Bool × Bool)),
          ((dyadicPaths N).image (List.cons a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ (Finset.univ : Finset (Bool × Bool)), 4 ^ N := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.card_image_le.trans ih
      _ = 4 ^ (N+1) := by simp [pow_succ, Nat.mul_comm]

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

 theorem inheritedCircleSymbol_contDiff {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection θ)) := by
  simp only [inheritedCircleSymbol_comp]
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (inheritedMaskProduct_contDiff S b k Q hQ ρ m N lam sig J i (fun _ => x)))

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeIndexCount
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem graphBinCountConstant_nonneg (c₀ : ℝ) : 0 ≤ graphBinCountConstant c₀ := by
  dsimp [graphBinCountConstant]
  positivity

theorem graph_source_bin_count_le (N : ℕ) {sig t c₀ : ℝ} (hsig : 0 ≤ sig)
    (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) (ht : t ≤ (N:ℝ)) :
    (angularBinCount (graphAngularScale N sig t c₀) : ℝ) ≤ graphBinCountConstant c₀*(2:ℝ)^N := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hM : 1 ≤ max 1 c₀⁻¹ := le_max_left _ _
  have hunc : (graphUncappedAngularScale N sig t)⁻¹ ≤ (2:ℝ)^N := by
    rw [graphUncappedAngularScale,dyadic_power_real,← Real.rpow_add (by norm_num : (0:ℝ)<2),
      ← Real.rpow_neg_one,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    rw [← Real.rpow_natCast (2:ℝ) N]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg hsig (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hi : (graphAngularScale N sig t c₀)⁻¹ ≤ max 1 c₀⁻¹*(2:ℝ)^N := by
    unfold graphAngularScale
    by_cases hh : c₀ ≤ graphUncappedAngularScale N sig t
    · rw [min_eq_left hh]
      exact (le_max_right _ _).trans (le_mul_of_one_le_right (zero_le_one.trans hM) hR)
    · rw [min_eq_right (le_of_not_ge hh)]
      exact hunc.trans (le_mul_of_one_le_left (zero_le_one.trans hR) hM)
  have hb := (angularBinCount_bounds (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap)).2
  have he := (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mp hb
  calc
    _ ≤ (2 / graphAngularScale N sig t c₀) * (2*Real.pi) := he
    _ = 4*Real.pi*(graphAngularScale N sig t c₀)⁻¹ := by ring
    _ ≤ 4*Real.pi*(max 1 c₀⁻¹*(2:ℝ)^N) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by dsimp [graphBinCountConstant]; ring

theorem graph_cell_quad_count_le (N p : ℕ) (hp : p ≤ N) :
    ((graphCellQuadIndices p).card : ℝ) ≤ ((2:ℝ)^N)^8 := by
  have hc : ((dyadicPaths p).card : ℝ) ≤ (4:ℝ)^N := by
    exact_mod_cast (dyadicPaths_card_le p).trans (pow_le_pow_right₀ (by norm_num) hp)
  have he : (4:ℝ)^N = ((2:ℝ)^N)^2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul,Nat.mul_comm 2 N]
  rw [he] at hc
  simp only [graphCellQuadIndices,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ (((2:ℝ)^N)^2*((2:ℝ)^N)^2)*(((2:ℝ)^N)^2*((2:ℝ)^N)^2) := by
      gcongr
    _ = _ := by ring

theorem graph_nonedge_index_count_le (N p n : ℕ) (hp : p ≤ N) {C : ℝ}
    (hC : 0 ≤ C) (hn : (n:ℝ) ≤ C*(2:ℝ)^N) :
    ((graphNonedgeIndices p n).card : ℝ) ≤ 2*C^2*((2:ℝ)^N)^10 := by
  have hq := graph_cell_quad_count_le N p hp
  simp only [graphNonedgeIndices,Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_bool,
    Finset.card_range,Nat.cast_mul,Nat.cast_ofNat]
  calc
    _ ≤ ((2:ℝ)^N)^8*((C*(2:ℝ)^N)*(C*(2:ℝ)^N)*2) := by
      gcongr
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualQuadCells
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphQuadPath_length {p : ℕ} {q : GraphCellQuadIndex} (hq : q ∈ graphCellQuadIndices p) (l : Fin 4) :
    (graphQuadPath q l).length = p := by
  simp only [graphCellQuadIndices,Finset.product_eq_sprod,Finset.mem_product,mem_dyadicPaths] at hq
  fin_cases l
  · exact hq.1.1
  · exact hq.1.2
  · exact hq.2.1
  · exact hq.2.2

theorem graphQuadCells_pos (Q : Fin 4 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (q : GraphCellQuadIndex) (l : Fin 4) : 0 < (graphQuadCells Q q l).side := by
  rw [graphQuadCells,DyadicSquare.descendant_side]
  exact div_pos (hQ l) (by positivity)

theorem graphQuadCells_side_le (Q : Fin 4 → DyadicSquare) (hQ : ∀ l, (Q l).side ≤ 1)
    {p : ℕ} {q : GraphCellQuadIndex} (hq : q ∈ graphCellQuadIndices p) (l : Fin 4) :
    (graphQuadCells Q q l).side ≤ (2:ℝ)^(-(p:ℝ)) := by
  rw [graphQuadCells,DyadicSquare.descendant_side,graphQuadPath_length hq l,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  simpa only [one_div] using div_le_div_of_nonneg_right (hQ l) (by positivity : (0:ℝ) ≤ 2^p)

theorem graphQuadCells_profile_mass_le
    (Q : Fin 4 → DyadicSquare) (ρ : Fin 4 → Measure Plane) (N B : ℕ)
    (δ lam : ℝ) (mass : Fin 4 → ℝ → ℝ)
    (hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l))
    {p : ℕ} (hp : p ≤ N) {q : GraphCellQuadIndex} (hq : q ∈ graphCellQuadIndices p) (l : Fin 4) :
    (ρ l (graphQuadCells Q q l).carrier).toReal / ((2:ℝ)^N)^(-mass l p) ≤ ((2:ℝ)^N)^(3*lam) :=
  (hd l).normalized_cell_mass_le hp (graphQuadPath_length hq l)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphNonedgeFiniteSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem graph_nonedge_sum_power (N p n : ℕ) (hp : p ≤ N) {C T outer : ℝ}
    (hC : 0 ≤ C) (hn : (n:ℝ) ≤ C*(2:ℝ)^N) (hconst : 2*C^2 ≤ (2:ℝ)^N)
    (I : Finset GraphNonedgeIndex) (hI : I ⊆ graphNonedgeIndices p n)
    (F : GraphNonedgeIndex → ℂ) (c : GraphNonedgeIndex → ℝ)
    (hc : ∀ i ∈ I, |c i| ≤ 1) (houter : |outer| ≤ ((2:ℝ)^N)^2)
    (hb : ∀ i ∈ I, ‖F i‖ ≤ ((2:ℝ)^N)^(-(T+13))) :
    ‖outer • (∑ i ∈ I, c i • F i)‖ ≤ ((2:ℝ)^N)^(-T) := by
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hsub : (I.card : ℝ) ≤ ((graphNonedgeIndices p n).card : ℝ) := by exact_mod_cast Finset.card_le_card hI
  have hcard : (I.card : ℝ) ≤ 2*C^2*R^10 :=
    hsub.trans (graph_nonedge_index_count_le N p n hp hC hn)
  have hsum : ‖∑ i ∈ I, c i • F i‖ ≤ (I.card:ℝ)*R^(-(T+13)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ I, R^(-(T+13)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul,Real.norm_eq_abs]
        exact (mul_le_mul (hc i hi) (hb i hi) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by simp
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ R^2*((2*C^2*R^10)*R^(-(T+13))) :=
      mul_le_mul houter (hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity)))
        (norm_nonneg _) (by positivity)
    _ = (2*C^2)*R^(-T-1) := by
      have he : R^12*R^(-(T+13)) = R^(-T-1) := by
        rw [← Real.rpow_natCast R 12,← Real.rpow_add hR]
        congr 1
        norm_num
        ring
      calc
        _ = (2*C^2)*(R^12*R^(-(T+13))) := by ring
        _ = _ := by rw [he]
    _ ≤ R*R^(-T-1) := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = R^(-T) := by
      nth_rw 1 [← Real.rpow_one R]
      rw [← Real.rpow_add hR]
      congr 1
      ring

theorem uniform_graph_nonedge_sum_power {sig c₀ : ℝ} (hsig : 0 ≤ sig)
    (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : ℕ), p ≤ N → ∀ t : ℝ, t ≤ (N:ℝ) →
    ∀ (T outer : ℝ) (I : Finset GraphNonedgeIndex),
    I ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig t c₀)) →
    ∀ (F : GraphNonedgeIndex → ℂ) (c : GraphNonedgeIndex → ℝ),
    (∀ i ∈ I, |c i| ≤ 1) → |outer| ≤ ((2:ℝ)^N)^2 →
    (∀ i ∈ I, ‖F i‖ ≤ ((2:ℝ)^N)^(-(T+13))) →
    ‖outer • (∑ i ∈ I, c i • F i)‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (2*(graphBinCountConstant c₀)^2)
  refine ⟨N₀,?_⟩
  intro N hN p hp t ht T outer I hI F c hcoeff houter hb
  exact graph_nonedge_sum_power N p _ hp (graphBinCountConstant_nonneg c₀)
    (graph_source_bin_count_le N hsig hc hcap ht) (by simpa using hN₀ N hN) I hI F c hcoeff houter hb

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

theorem normalized_four_integral_norm_le (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (hX : ∀ i, MeasurableSet (X i))
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 < M i) (F : (Fin 4 → Plane) → ℂ) {ε : ℝ}
    (hb : ∀ x, (∀ i, x i ∈ X i) → ‖F x‖ ≤ ε) :
    ‖((M 0*M 1)*(M 2*M 3))⁻¹ • (∫ x, F x ∂Measure.pi (fun i => (ρ i).restrict (X i)))‖ ≤
      ε * ∏ i : Fin 4, (ρ i (X i)).toReal / M i := by
  let μ := Measure.pi (fun i => (ρ i).restrict (X i))
  have he : ∀ᵐ x ∂μ, ‖F x‖ ≤ ε := (graph_four_spatial_ae_carrier ρ X hX).mono (fun x hx => hb x hx)
  have hi := norm_integral_le_of_norm_le_const he
  have hm : μ.real univ = ∏ i : Fin 4, (ρ i (X i)).toReal := by
    simp only [μ,Measure.real,Measure.pi_univ,Measure.restrict_apply_univ,ENNReal.toReal_prod]
  rw [hm] at hi
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos (mul_pos (hM 0) (hM 1)) (mul_pos (hM 2) (hM 3))))]
  apply (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (mul_nonneg (mul_pos (hM 0) (hM 1)).le (mul_pos (hM 2) (hM 3)).le))).trans_eq
  simp only [Fin.prod_univ_four,div_eq_mul_inv,mul_inv_rev]
  ring

theorem normalized_four_integral_power_le (ρ : Fin 4 → Measure Plane) [∀ i, IsFiniteMeasure (ρ i)]
    (X : Fin 4 → Set Plane) (hX : ∀ i, MeasurableSet (X i))
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 < M i) (F : (Fin 4 → Plane) → ℂ)
    {R lam U : ℝ} (hR : 0 < R)
    (hb : ∀ x, (∀ i, x i ∈ X i) → ‖F x‖ ≤ R^(-U))
    (hm : ∀ i, (ρ i (X i)).toReal / M i ≤ R^(3*lam)) :
    ‖((M 0*M 1)*(M 2*M 3))⁻¹ • (∫ x, F x ∂Measure.pi (fun i => (ρ i).restrict (X i)))‖ ≤
      R^(-U+12*lam) := by
  apply (normalized_four_integral_norm_le ρ X hX M hM F hb).trans
  have hprod : (∏ i : Fin 4, (ρ i (X i)).toReal / M i) ≤ ∏ _i : Fin 4, R^(3*lam) :=
    Finset.prod_le_prod (fun i _ => div_nonneg ENNReal.toReal_nonneg (hM i).le) (fun i _ => hm i)
  calc
    _ ≤ R^(-U)*(∏ _i : Fin 4, R^(3*lam)) := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = R^(-U+12*lam) := by
      simp only [Fin.prod_univ_four,← Real.rpow_add hR]
      congr 1
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphFourTransformPointIntegral
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem actual_inherited_fourTransform_pointIntegral
    {ι : Fin 4 → Type*} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (Q : Fin 4 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (mass : Fin 4 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Fin 4 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhbound : ∀ l x, ‖h l x‖ ≤ 1)
    (K : ℕ) (hK : ∀ l, ∑ t ∈ S l, k l t ≤ K)
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (distance plus : Bool) (axis δ v : ℝ) (j₁ j₂ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ) (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) •
      sourceGraphFourTransform ρ X M b (graphSourceWeight distance plus axis (angularBinCount δ) j₁ j₂) r u w
        ∂sourceArcLength ∂sourceArcLength) =
    ((M 0*M 1)*(M 2*M 3))⁻¹ •
      (∫ x, graphPointIntegral (graphAmplitudePullback b x distance plus axis δ j₁ j₂ Ψ)
        v (graphSourceSign distance plus) (x 0-x 1) (x 2-x 3)
        ∂Measure.pi (fun l => (ρ l).restrict (X l))) := by
  dsimp only
  let B : Fin 4 → ℝ := fun _ => symbolDerivativeConstant K^K
  apply sourceGraphFourTransform_pointIntegral ρ X M _ _ _ B _ _ distance plus axis δ v j₁ j₂ hΨ hsupp
  · intro l
    exact measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
      N lam sig J i (h l) (hh l)
  · intro l x
    exact inheritedCircleSymbol_continuous (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l)
      N lam sig J i (h l) x
  · intro l
    exact pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  · intro l x ω
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l)
      N lam sig J i (h l) K (hK l) x (hhbound l x) ω

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphOriginalNonedgePower
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_original_nonedge_power {sig : ℝ} (hsig : 0 < sig) (K : ℕ) (lam T : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    ∀ (mass : Fin 4 → ℝ → ℝ) (J i : ℕ) (h : Fin 4 → Plane → ℂ),
    (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ a p v : ℝ, 0 ≤ v-p → p-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) →
    ∀ (distance plus : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ P : Fin 4 → DyadicSquare, (∀ l, 0 < (P l).side) →
    (∀ l, (P l).side ≤ (2:ℝ)^(-p)) →
    (∀ l, (P l).carrier ⊆ (graphSlotParent distance X Y l).carrier) →
    ∀ M : Fin 4 → ℝ, (∀ l, 0 < M l) →
    (∀ l, (ρ l (P l).carrier).toReal / M l ≤ ((2:ℝ)^N)^(3*lam)) →
    ∀ (axis : ℝ) (j₁ j₂ : ℕ) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative distance plus axis (graphAngularScale N sig (p-a) c₀) j₁ j₂ q →
    GraphNonedge N sig p (graphSourceSign distance plus) (graphRepresentativeZ distance plus q)
      (graphRepresentativeAxis distance plus q) ((P 0).center-(P 1).center) ((P 2).center-(P 3).center) →
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l)
      N lam sig J i (h l)
    ‖graphOriginalTerm ρ (fun l => (P l).carrier) M b distance plus axis
      (graphAngularScale N sig (p-a) c₀) v j₁ j₂ Ψ‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₀,hbound⟩ := uniform_actual_graph_nonedge_power hsig K (T+12*lam) hΨ hsupp hc hcap
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ instρ mass J i h hh hhbound a p v hu ht hLu
    distance plus X Y hX hY hXa hYa hsep P hP hPp hparent M hM hmass axis j₁ j₂ q hq hfail
  let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  change ‖graphOriginalTerm ρ (fun l => (P l).carrier) M b distance plus axis
    (graphAngularScale N sig (p-a) c₀) v j₁ j₂ Ψ‖ ≤ _
  rw [graphOriginalTerm,actual_inherited_fourTransform_pointIntegral S d k Q hQ ρ mass N lam sig J i
    h hh hhbound K hK (fun l => (P l).carrier) M distance plus axis
    (graphAngularScale N sig (p-a) c₀) v j₁ j₂ hΨ.continuous hsupp]
  have hp : ∀ x : Fin 4 → Plane, (∀ l, x l ∈ (P l).carrier) →
      ‖graphPointIntegral (graphAmplitudePullback b x distance plus axis
        (graphAngularScale N sig (p-a) c₀) j₁ j₂ Ψ) v (graphSourceSign distance plus)
        (x 0-x 1) (x 2-x 3)‖ ≤ ((2:ℝ)^N)^(-(T+12*lam)) := by
    intro x hx
    exact hbound N hN S d k hcard hK L hL Q hQ ρ mass lam J i h x (fun l => hhbound l (x l))
      a p v hu ht hLu distance plus X Y hX hY hXa hYa hsep P hP hPp hparent hx axis j₁ j₂ q hq hfail
  have he := normalized_four_integral_power_le ρ (fun l => (P l).carrier)
    (fun l => (P l).measurable) M hM _ (by positivity : (0:ℝ) < (2:ℝ)^N) hp hmass
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphProfileCoefficient
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem graphProfileCoefficient_bounds
    (Q : Fin 4 → DyadicSquare) (ρ : Fin 4 → Measure Plane) (N B : ℕ)
    (δ lam : ℝ) (mass : Fin 4 → ℝ → ℝ)
    (hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l))
    {a p : ℝ} (ha : 0 ≤ a) (hap : a ≤ p) (hp : p ≤ N) :
    0 ≤ graphProfileCoefficient N mass a p ∧ graphProfileCoefficient N mass a p ≤ 1 := by
  have hn (l : Fin 4) : 0 ≤ ((2:ℝ)^N)^(-mass l p) / ((2:ℝ)^N)^(-mass l a) := by positivity
  constructor
  · exact Finset.prod_nonneg (fun l _ => hn l)
  · apply Finset.prod_le_one (fun l _ => hn l)
    intro l _
    apply (div_le_one (by positivity : 0 < ((2:ℝ)^N)^(-mass l a))).mpr
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    have hs := (hd l).slope a p ha hap hp
    linarith [hs.1]

theorem graph_original_outer_le (N : ℕ) {a v : ℝ} (hv : v-a ≤ (N:ℝ)) :
    |(2:ℝ)^(2*(v-a))| ≤ ((2:ℝ)^N)^2 := by
  rw [abs_of_pos (by positivity : 0 < (2:ℝ)^(2*(v-a))),← pow_mul,
    ← Real.rpow_natCast (2:ℝ) (N*2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphActualNonedgeSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem graphOriginalTerm_zero_of_empty_weight_support
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (distance plus : Bool) (axis δ v : ℝ)
    (j k : ℕ) (Ψ : ℝ → ℝ)
    (hS : ¬(tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty) :
    graphOriginalTerm ρ X M b distance plus axis δ v j k Ψ = 0 := by
  have hw (u w : UnitCircle) : graphSourceWeight distance plus axis (angularBinCount δ) j k (u,w) = 0 := by
    by_contra hn
    exact hS ⟨(u,w),subset_closure hn⟩
  simp [graphOriginalTerm,sourceGraphFourTransform,hw]

theorem uniform_regularized_original_nonedge_sum {sig : ℝ} (hsig : 0 < sig)
    (K : ℕ) (lam T : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 4 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a : ℝ) (p : ℕ) (v : ℝ), 0 ≤ a → a ≤ p → p ≤ N →
    0 ≤ v-p → (p:ℝ)-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) → v-a ≤ N →
    ∀ (distance : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ (axis : ℝ) (q : (ℕ × ℕ) × Bool → UnitCircle × UnitCircle) (I : Finset GraphNonedgeIndex),
    I ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) →
    (∀ e ∈ I, ∀ l, (graphQuadCells Q e.1 l).carrier ⊆ (graphSlotParent distance X Y l).carrier) →
    (∀ e ∈ I,
      (GraphSourceRepresentative distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀)
          e.2.1.1 e.2.1.2 (q e.2) ∧
        GraphNonedge N sig p (graphSourceSign distance e.2.2) (graphRepresentativeZ distance e.2.2 (q e.2))
          (graphRepresentativeAxis distance e.2.2 (q e.2))
          ((graphQuadCells Q e.1 0).center-(graphQuadCells Q e.1 1).center)
          ((graphQuadCells Q e.1 2).center-(graphQuadCells Q e.1 3).center)) ∨
      ¬(tsupport (graphSourceWeight distance e.2.2 axis
        (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) e.2.1.1 e.2.1.2)).Nonempty) →
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l p)
    ‖((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p •
      (∑ e ∈ I, graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b distance e.2.2 axis
        (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ))‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨N₁,hterm⟩ := uniform_actual_original_nonedge_power hsig K lam (T+13) hΨ hsupp hc hcap
  obtain ⟨N₂,hsum⟩ := uniform_graph_nonedge_sum_power hsig.le hc hcap
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ hQside ρ mass B δ hd J i h hh hhbound
    a p v ha hap hp hu ht hLu hv distance X Y hX hY hXa hYa hsep axis q I hI hparent hlabel
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let M := fun l => ((2:ℝ)^N)^(-mass l p)
  let F := fun e : GraphNonedgeIndex => graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier)
    M b distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ
  have hcoeff := graphProfileCoefficient_bounds Q ρ N B δ lam mass hd ha hap (Nat.cast_le.mpr hp)
  have hpoint : ∀ e ∈ I, ‖F e‖ ≤ ((2:ℝ)^N)^(-(T+13)) := by
    intro e he
    have hquad : e.1 ∈ graphCellQuadIndices p := by
      have hh := hI he
      simp only [graphNonedgeIndices,Finset.product_eq_sprod,Finset.mem_product] at hh
      exact hh.1
    rcases hlabel e he with ⟨hq,hfail⟩ | hempty
    · exact hterm N ((le_max_left _ _).trans hN) S d k hcard hK L hL Q hQ ρ mass J i h hh hhbound
        a p v hu ht hLu distance e.2.2 X Y hX hY hXa hYa hsep (graphQuadCells Q e.1)
        (graphQuadCells_pos Q hQ e.1) (graphQuadCells_side_le Q hQside hquad) (hparent e he) M
        (fun _ => by dsimp [M]; positivity) (graphQuadCells_profile_mass_le Q ρ N B δ lam mass hd hp hquad)
        axis e.2.1.1 e.2.1.2 (q e.2) hq hfail
    · have hz := graphOriginalTerm_zero_of_empty_weight_support ρ (fun l => (graphQuadCells Q e.1 l).carrier)
        M b distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ hempty
      change ‖F e‖ ≤ _
      rw [show F e = 0 from hz,norm_zero]
      positivity
  have he := hsum N ((le_max_right _ _).trans hN) p hp ((p:ℝ)-a)
    (by have hp' : (p:ℝ) ≤ N := Nat.cast_le.mpr hp; linarith) T ((2:ℝ)^(2*(v-a))) I hI F
    (fun _ => graphProfileCoefficient N mass a p)
    (fun _ _ => by rw [abs_of_nonneg hcoeff.1]; exact hcoeff.2) (graph_original_outer_le N hv) hpoint
  simpa only [← Finset.smul_sum] using he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphRetainedEdges
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem graphChosenRepresentative_spec {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (distance plus : Bool) (axis : ℝ) (j k : ℕ) :
    GraphSourceRepresentative distance plus axis δ j k (graphChosenRepresentative hδ hcap distance plus axis j k) ∨
      ¬(tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty := by
  classical
  by_cases hs : (tsupport (graphSourceWeight distance plus axis (angularBinCount δ) j k)).Nonempty
  · left
    simpa only [graphChosenRepresentative,dite_eq_left hs] using
      Classical.choose_spec (graphSourceRepresentative_exists hδ hcap distance plus axis j k hs)
  · exact Or.inr hs

theorem graph_nonedge_of_not_retained (N : ℕ) (sig p : ℝ) (distance plus : Bool)
    (P : Fin 4 → DyadicSquare) (q : UnitCircle × UnitCircle)
    (hf : ¬GraphRetainedEdge N sig p distance plus P q) :
    GraphNonedge N sig p (graphSourceSign distance plus) (graphRepresentativeZ distance plus q)
      (graphRepresentativeAxis distance plus q) ((P 0).center-(P 1).center) ((P 2).center-(P 3).center) := by
  classical
  unfold GraphRetainedEdge at hf
  rcases not_and_or.mp hf with hvec | hscalar
  · exact Or.inl (not_le.mp hvec)
  · have hs := not_forall.mp hscalar
    obtain ⟨_,hs⟩ := hs
    exact Or.inr (not_le.mp hs)

theorem graph_sum_minus_retained (I : Finset GraphNonedgeIndex) (keep : GraphNonedgeIndex → Prop)
    [DecidablePred keep] (F : GraphNonedgeIndex → ℂ) (outer coeff : ℝ) :
    outer • (coeff • (∑ e ∈ I, F e)) - outer • (coeff • (∑ e ∈ I.filter keep, F e)) =
      outer • (coeff • (∑ e ∈ I.filter (fun e => ¬keep e), F e)) := by
  have he := Finset.sum_filter_add_sum_filter_not I keep F
  rw [← he,smul_add,smul_add,add_sub_cancel_left]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphOriginalGraphRemoval
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_regularized_original_graph_removal_oai {sig : ℝ} (hsig : 0 < sig)
    (K : ℕ) (lam T : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {c₀ : ℝ} (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 4 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 4 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 4 → Measure Plane) (mass : Fin 4 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 4 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a : ℝ) (p : ℕ) (v : ℝ), 0 ≤ a → a ≤ p → p ≤ N →
    0 ≤ v-p → (p:ℝ)-a ≤ v-p+2*sig*(N:ℝ) → (L:ℝ) ≤ v-p+2*sig*(N:ℝ) → v-a ≤ N →
    ∀ (distance : Bool) (X Y : DyadicSquare), 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    (distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a)) →
    ∀ (axis : ℝ) (I : Finset GraphNonedgeIndex),
    I ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) →
    (∀ e ∈ I, ∀ l, (graphQuadCells Q e.1 l).carrier ⊆ (graphSlotParent distance X Y l).carrier) →
    let q := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig ((p:ℝ)-a) hc) ((min_le_left _ _).trans hcap) distance e.2 axis e.1.1 e.1.2
    let b := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l p)
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ρ (fun l => (graphQuadCells Q e.1 l).carrier) M b
      distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀) v e.2.1.1 e.2.1.2 Ψ
    ‖((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p • (∑ e ∈ I, F e)) -
      ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N mass a p •
        (∑ e ∈ graphRetainedIndices I N sig p distance Q q, F e))‖ ≤ ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₀,hbound⟩ := uniform_regularized_original_nonedge_sum hsig K lam T hΨ hsupp hc hcap
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ hQside ρ mass B δ hd J i h hh hhbound
    a p v ha hap hp hu ht hLu hv distance X Y hX hY hXa hYa hsep axis I hI hparent
  let q := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig ((p:ℝ)-a) hc) ((min_le_left _ _).trans hcap) distance e.2 axis e.1.1 e.1.2
  let keep := fun e : GraphNonedgeIndex => GraphRetainedEdge N sig p distance e.2.2 (graphQuadCells Q e.1) (q e.2)
  let bad := I.filter (fun e => ¬keep e)
  have hbad : bad ⊆ graphNonedgeIndices p (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) :=
    (Finset.filter_subset _ _).trans hI
  have hparents : ∀ e ∈ bad, ∀ l, (graphQuadCells Q e.1 l).carrier ⊆ (graphSlotParent distance X Y l).carrier :=
    fun e he => hparent e (Finset.mem_of_mem_filter e he)
  have hlabels : ∀ e ∈ bad,
      (GraphSourceRepresentative distance e.2.2 axis (graphAngularScale N sig ((p:ℝ)-a) c₀)
          e.2.1.1 e.2.1.2 (q e.2) ∧
        GraphNonedge N sig p (graphSourceSign distance e.2.2) (graphRepresentativeZ distance e.2.2 (q e.2))
          (graphRepresentativeAxis distance e.2.2 (q e.2))
          ((graphQuadCells Q e.1 0).center-(graphQuadCells Q e.1 1).center)
          ((graphQuadCells Q e.1 2).center-(graphQuadCells Q e.1 3).center)) ∨
      ¬(tsupport (graphSourceWeight distance e.2.2 axis
        (angularBinCount (graphAngularScale N sig ((p:ℝ)-a) c₀)) e.2.1.1 e.2.1.2)).Nonempty := by
    intro e he
    rcases graphChosenRepresentative_spec (graphAngularScale_pos N sig ((p:ℝ)-a) hc)
      ((min_le_left _ _).trans hcap) distance e.2.2 axis e.2.1.1 e.2.1.2 with hrep | hempty
    · exact Or.inl ⟨hrep,graph_nonedge_of_not_retained N sig p distance e.2.2 (graphQuadCells Q e.1)
        (q e.2) (Finset.mem_filter.mp he).2⟩
    · exact Or.inr hempty
  have he := hbound N hN S d k hcard hK L hL Q hQ hQside ρ mass B δ hd J i h hh hhbound
    a p v ha hap hp hu ht hLu hv distance X Y hX hY hXa hYa hsep axis q bad hbad hparents hlabels
  dsimp only
  rw [graphRetainedIndices,graph_sum_minus_retained]
  exact he

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_regularized_original_graph_removal_oai := @OAI.PlanarFalconer.uniform_regularized_original_graph_removal_oai
