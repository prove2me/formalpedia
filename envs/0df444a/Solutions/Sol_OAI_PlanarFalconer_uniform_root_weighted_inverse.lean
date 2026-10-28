-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_root_weighted_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:34:03.56836+00:00
-- url     : https://prove2.me/submissions/3579f041-6c7d-4967-8f27-7e54bf76dbf3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_rotated_inverse_circle_power

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryPowerRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem sourceSymbolScale_upper (N : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) {L : ℕ} (hL : L ≤ N) :
    sourceSymbolScale N sig L ≤ ((2:ℝ)^N)^(1+sig) := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hRpos : 0 < (2:ℝ)^N := by positivity
  have hm : max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*sig)) ≤ (2:ℝ)^N := by
    apply max_le hR
    calc
      _ ≤ (2:ℝ)^N * 1 :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hL)
          (Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)) (by positivity) (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ ((2:ℝ)^N)^sig * (2:ℝ)^N := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by
      conv_lhs => arg 2; rw [← Real.rpow_one ((2:ℝ)^N)]
      rw [← Real.rpow_add hRpos]
      congr 1
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

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularFarStationaryScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem sourceSymbolScale_dyadic (N : ℕ) (sig : ℝ) (L : ℕ) :
    sourceSymbolScale N sig L =
      max ((2:ℝ)^((N:ℝ)*sig)) ((2:ℝ)^((L:ℝ)-49*(N:ℝ)*sig)) := by
  unfold sourceSymbolScale
  rw [mul_max_of_nonneg _ _ (by positivity),mul_one]
  congr 1
  · exact (Real.rpow_natCast_mul (by norm_num) N sig).symm
  · rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_natCast]
    rw [← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring

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

theorem inverseStationaryOperator_contDiff (n : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (inverseStationaryOperator n f) :=
  (inverseStationaryExpr n).apply_contDiff hf

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseStationaryCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

theorem AngularDifferentialExpr.apply_shift (p : AngularDifferentialExpr)
    (f : ℝ → ℂ) (a : ℝ) :
    p.apply (fun x => f (x+a)) = fun x => p.apply f (x+a) := by
  induction p generalizing f with
  | term c k => simp [apply, iteratedDeriv_comp_add_const]
  | add p q hp hq => simp [apply, hp, hq]
  | comp p q hp hq => simp only [apply, hq, hp]

theorem AngularDifferentialExpr.apply_periodic (p : AngularDifferentialExpr)
    {f : ℝ → ℂ} {a : ℝ} (hf : Function.Periodic f a) :
    Function.Periodic (p.apply f) a := by
  have he : (fun x => f (x+a)) = f := funext hf
  have h := p.apply_shift f a
  rw [he] at h
  intro x
  exact (congrFun h x).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryArcLength
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

 theorem sourceArcLength_integral_period {F : UnitCircle → ℂ}
    (hF : AEStronglyMeasurable F sourceArcLength) :
    (∫ ω, F ω ∂sourceArcLength) = ∫ θ in (-Real.pi)..Real.pi, F (sourceUnitDirection θ) := by
  have he : (∫ ω, F ω ∂sourceArcLength) = ∫ θ in (0:ℝ)..2*Real.pi, F (sourceUnitDirection θ) := by
    rw [sourceArcLength,integral_map continuous_sourceUnitDirection.measurable.aemeasurable hF]
    exact (intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)).symm
  rw [he]
  have hp : Function.Periodic (fun θ => F (sourceUnitDirection θ)) (2*Real.pi) :=
    fun θ => congrArg F (sourceUnitDirection_periodic θ)
  have hh := hp.intervalIntegral_add_eq 0 (-Real.pi)
  have he' : -Real.pi+2*Real.pi = Real.pi := by ring
  simpa only [zero_add,he'] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InverseCircleArcLength
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

theorem periodic_sourceAngle_complex {f : ℝ → ℂ}
    (hf : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    f (sourceAngle (sourceUnitDirection θ)) = f θ := by
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := hf.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm, add_comm] using hp θ

theorem inverseCircleOperator_comp (j : ℕ) (b : UnitCircle → ℂ) (θ : ℝ) :
    inverseCircleOperator j b (sourceUnitDirection θ) =
      inverseStationaryOperator j (fun φ => b (sourceUnitDirection φ)) θ := by
  have hp : Function.Periodic (fun φ => b (sourceUnitDirection φ)) (2*Real.pi) :=
    fun φ => congrArg b (sourceUnitDirection_periodic φ)
  exact periodic_sourceAngle_complex ((inverseStationaryExpr j).apply_periodic hp) θ

theorem circle_measurable_of_angular {b : UnitCircle → ℂ}
    (hb : Continuous (fun θ => b (sourceUnitDirection θ))) : Measurable b := by
  have he : b = (fun θ => b (sourceUnitDirection θ)) ∘ sourceAngle := by
    funext dir
    simp [sourceUnitDirection_sourceAngle]
  rw [he]
  exact hb.measurable.comp measurable_sourceAngle

theorem inverseCircleOperator_measurable (j : ℕ) {b : UnitCircle → ℂ}
    (hb : ContDiff ℝ ∞ (fun θ => b (sourceUnitDirection θ))) :
    Measurable (inverseCircleOperator j b) :=
  (inverseStationaryOperator_contDiff j hb).continuous.measurable.comp measurable_sourceAngle

theorem sourceInverseCircleIntegral_eq (n : ℕ) (r θ₀ : ℝ) {Δ : Plane}
    (hΔ : Δ = ‖Δ‖ • sourceDirection θ₀) {ψ b : UnitCircle → ℂ}
    (hψ : Continuous (fun θ => ψ (sourceUnitDirection θ)))
    (hb : ContDiff ℝ ∞ (fun θ => b (sourceUnitDirection θ))) :
    sourceInverseCircleIntegral n r Δ ψ b =
      rotatedInverseCircleIntegral n (r*‖Δ‖) θ₀
        (fun θ => ψ (sourceUnitDirection θ)) (fun θ => b (sourceUnitDirection θ)) := by
  unfold sourceInverseCircleIntegral rotatedInverseCircleIntegral
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hmeas : Measurable (fun dir : UnitCircle =>
      Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (dir:Plane) Δ:ℂ)) *
        (ψ dir * inverseCircleOperator j b dir)) := by
    apply Measurable.mul
    · fun_prop
    · exact (circle_measurable_of_angular hψ).mul (inverseCircleOperator_measurable j hb)
  rw [sourceArcLength_integral_period hmeas.aestronglyMeasurable]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [inverseCircleOperator_comp]
  congr 1
  have he : inner ℝ (sourceDirection θ) Δ = ‖Δ‖*Real.cos (θ-θ₀) := by
    calc
      _ = inner ℝ (sourceDirection θ) (‖Δ‖ • sourceDirection θ₀) :=
        congrArg (inner ℝ (sourceDirection θ)) hΔ
      _ = _ := by rw [inner_smul_right, inner_sourceDirection]
  change Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (sourceDirection θ) Δ:ℂ)) = _
  rw [he]
  simp only [cosineOscillator, Complex.ofReal_mul]
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RootStationaryScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem root_symbol_scale_square {sig : ℝ} (hsig : 0 ≤ sig) (hsmall : sig ≤ 1/4)
    (N L : ℕ) (hL : 2*L ≤ N) :
    sourceSymbolScale N sig L^2 ≤ ((2:ℝ)^N)^(1-2*sig) := by
  have hL' : 2*(L:ℝ) ≤ (N:ℝ) := by exact_mod_cast hL
  have hn := Nat.cast_nonneg (α := ℝ) N
  have hns := mul_nonneg hn hsig
  have hbase : sourceSymbolScale N sig L ≤ (2:ℝ)^((N:ℝ)*(1/2-sig)) := by
    rw [sourceSymbolScale_dyadic]
    apply max_le <;> apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    · nlinarith [mul_nonneg hn (sub_nonneg.mpr hsmall)]
    · nlinarith
  apply (pow_le_pow_left₀ (sourceSymbolScale_pos N sig L).le hbase 2).trans_eq
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem root_frequency_lower {sig δ : ℝ} (hsig : 0 < sig) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ r d : ℝ,
    (2:ℝ)^((N:ℝ)-1) ≤ r → δ ≤ d →
    ((2:ℝ)^N)^(1-sig) ≤ r*d := by
  obtain ⟨N₀,h₀⟩ := fixed_constant_absorbed hsig (2/δ)
  refine ⟨N₀,?_⟩
  intro N hN r d hr hd
  have hconst := (div_le_iff₀ hδ).mp (h₀ N hN)
  have hprod : (2:ℝ)^N/2*δ ≤ r*d := by
    have hr' : (2:ℝ)^N/2 ≤ r := by
      simpa [Real.rpow_sub (by norm_num : (0:ℝ) < 2)] using hr
    exact mul_le_mul hr' hd hδ.le ((by positivity : 0 < (2:ℝ)^N/2).trans_le hr').le
  apply le_trans _ hprod
  have hp : 0 < ((2:ℝ)^N)^sig := by positivity
  rw [Real.rpow_sub (by positivity : (0:ℝ) < (2:ℝ)^N),Real.rpow_one]
  apply (div_le_iff₀ hp).mpr
  have hh := mul_le_mul_of_nonneg_left hconst (by positivity : 0 ≤ (2:ℝ)^N/2)
  nlinarith

theorem root_stationary_slack {sig δ : ℝ} (hsig : 0 < sig) (hsmall : sig ≤ 1/4)
    (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 2*L ≤ N → ∀ r d : ℝ,
    (2:ℝ)^((N:ℝ)-1) ≤ r → δ ≤ d →
    ((2:ℝ)^N)^sig ≤ r*d ∧
    sourceSymbolScale N sig L^2/(r*d) ≤ ((2:ℝ)^N)^(-sig) := by
  obtain ⟨N₀,h₀⟩ := root_frequency_lower hsig hδ
  refine ⟨N₀,?_⟩
  intro N hN L hL r d hr hd
  have hΛ := h₀ N hN r d hr hd
  have hΛpos : 0 < r*d := (by positivity : 0 < ((2:ℝ)^N)^(1-sig)).trans_le hΛ
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  refine ⟨(Real.rpow_le_rpow_of_exponent_le hR (by linarith : sig ≤ 1-sig)).trans hΛ,?_⟩
  apply (div_le_iff₀ hΛpos).mpr
  calc
    _ ≤ ((2:ℝ)^N)^(1-2*sig) := root_symbol_scale_square hsig.le hsmall N L hL
    _ = ((2:ℝ)^N)^(-sig)*((2:ℝ)^N)^(1-sig) := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hΛ (by positivity)

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

 theorem endpoint_direction_dist_le {x y c d : Plane} (hxy : y ≠ x) (hcd : d ≠ c) :
    dist (sourceRadialUnit x y) (sourceRadialUnit c d) ≤
      2*(dist x c + dist y d)/dist x y := by
  change dist (sourceRadialVector x y) (sourceRadialVector c d) ≤ _
  simp only [sourceRadialVector, ite_eq_right hxy, ite_eq_right hcd]
  have hn := normalized_vector_dist_le (y-x) (d-c) (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hcd)
  have hd : dist (y-x) (d-c) ≤ dist x c + dist y d := by
    rw [dist_eq_norm, show (y-x)-(d-c) = (y-d)-(x-c) by abel]
    exact (norm_sub_le _ _).trans_eq (by rw [dist_eq_norm,dist_eq_norm]; ring)
  have he : ‖y-x‖ = dist x y := by rw [dist_eq_norm, norm_sub_rev]
  rw [he] at hn ⊢
  exact hn.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
    (dist_nonneg))

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

theorem graphConeCutoff_one {θ : ℝ} (hθ : |θ| ≤ 1/10) : graphConeCutoff θ = 1 := by
  have hb : graphConeBump θ = 1 := graphConeBump.one_of_mem_closedBall
    (by simpa [graphConeBump, Real.dist_eq] using hθ)
  simp only [graphConeCutoff, hb, Complex.ofReal_one]

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

theorem sourceConeCircle_rotated_contDiff (axis : ℝ) :
    ContDiff ℝ ∞ (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) := by
  have he : (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) =
      fun θ => sourceConeCircle 0 (sourceUnitDirection (θ-axis)) := by
    funext θ
    simp only [sourceConeCircle, sourceCircleRotate_comp, neg_zero,
      sub_eq_add_neg, add_zero]
  rw [he]
  exact sourceConeCircle_angular_contDiff.comp (contDiff_id.sub contDiff_const)

theorem sourceConeCircle_rotated_deriv (axis : ℝ) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun t => sourceConeCircle axis (sourceUnitDirection t)) θ =
      iteratedDeriv j (fun t => sourceConeCircle 0 (sourceUnitDirection t)) (θ-axis) := by
  have he : (fun t => sourceConeCircle axis (sourceUnitDirection t)) =
      fun t => sourceConeCircle 0 (sourceUnitDirection (t-axis)) := by
    funext t
    simp only [sourceConeCircle, sourceCircleRotate_comp, neg_zero,
      sub_eq_add_neg, add_zero]
  rw [he]
  exact congrFun (iteratedDeriv_comp_sub_const j
    (fun t => sourceConeCircle 0 (sourceUnitDirection t)) axis) θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_MinimalPairSymbol
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem inheritedCircleSymbol_zero_assignment (S : Finset PolicyDescriptor)
    (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ)
    (lam sig : ℝ) (J i : ℕ) (x : Plane) (dir : UnitCircle) :
    inheritedCircleSymbol S id (fun _ => 0) Q ρ m N lam sig J i (fun _ => 1) x dir =
      (descriptorListMask Q ρ m N lam sig J i S x dir : ℂ) := by
  simp [inheritedCircleSymbol,inheritedMaskProduct,normalizedMaskFactor,
    descriptorAngleMask,descriptorListMask,sourceUnitDirection_sourceAngle]

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

theorem symbol_zero (d : RootEndpointData) (N : ℕ) (sig : ℝ) (x : Plane) (dir : UnitCircle) :
    d.symbol N sig (fun _ => 0) (fun _ => 1) x dir = (d.mask N sig x dir : ℂ) :=
  inheritedCircleSymbol_zero_assignment _ _ _ _ _ _ _ _ _ _ _

end RootEndpointData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootPairDerivatives
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_root_pair_derivatives {sig : ℝ} (hsig : 0 < sig) (K n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ d e : RootEndpointData, 0 < d.Q.side → 0 < e.Q.side →
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    ∀ k l : PolicyDescriptor → ℕ, (∑ b ∈ d.S, k b) ≤ K → (∑ b ∈ e.S, l b) ≤ K →
    ∀ L : ℕ, (∀ b ∈ d.S, descriptorLength b ≤ L) →
    (∀ b ∈ e.S, descriptorLength b ≤ L) →
    ∀ (h g : Plane → ℂ) (x y : Plane), ‖h x‖ ≤ 1 → ‖g y‖ ≤ 1 →
    let f := fun θ => d.symbol N sig k h x (sourceUnitDirection θ) *
      conj (e.symbol N sig l g y (sourceUnitDirection θ))
    ContDiff ℝ ∞ f ∧ ∀ j ≤ n, ∀ θ, ‖iteratedDeriv j f θ‖ ≤ C*sourceSymbolScale N sig L^j := by
  obtain ⟨C,hC,N₀,h₀⟩ := uniform_actual_symbol_derivatives_upto hsig K n
  refine ⟨C*C*2^n,by positivity,N₀,?_⟩
  intro N hN d e hd he hc₁ hc₂ k l hk hl L hL₁ hL₂ h g x y hx hy
  have hf := inheritedCircleSymbol_contDiff d.S id k d.Q hd d.ρ d.mass N d.lam sig d.J d.i h x
  have hg := inheritedCircleSymbol_contDiff e.S id l e.Q he e.ρ e.mass N e.lam sig e.J e.i g y
  refine ⟨hf.mul (Complex.conjCLE.contDiff.comp hg),?_⟩
  exact complex_pair_derivatives_upto hf hg hC hC (sourceSymbolScale_pos N sig L).le n
    (h₀ N hN d.S id k hc₁ hk L hL₁ d.Q hd d.ρ d.mass d.lam d.J d.i h x hx)
    (h₀ N hN e.S id l hc₂ hl L hL₂ e.Q he e.ρ e.mass e.lam e.J e.i g y hy)

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

theorem rootPairSymbol_inherited (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (dir : UnitCircle) :
    rootPairSymbol d e N sig z dir =
      d.symbol N sig (fun _ => 0) (fun _ => 1) z.1 dir *
      conj (e.symbol N sig (fun _ => 0) (fun _ => 1) z.2 dir) := by
  rw [RootEndpointData.symbol_zero,RootEndpointData.symbol_zero,Complex.conj_ofReal]
  rfl

theorem rootPairSymbol_radial (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) :
    rootPairSymbol d e N sig z (sourceRadialUnit z.2 z.1) = (rootPairMask d e N sig z : ℂ) := by
  simp only [rootPairSymbol,rootPairMask,Complex.ofReal_mul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentConeGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem DyadicSquare.dist_center_le_three_quarters (Q : DyadicSquare)
    (hQ : 0 ≤ Q.side) {x : Plane} (hx : x ∈ Q.carrier) :
    dist x Q.center ≤ 3/4*Q.side := by
  have h0 : |x 0 - Q.center 0| ≤ Q.side/2 := by
    simp only [DyadicSquare.center, WithLp.ofLp_toLp, Matrix.cons_val_zero]
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2.1]
  have h1 : |x 1 - Q.center 1| ≤ Q.side/2 := by
    simp only [DyadicSquare.center, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply abs_le.mpr
    constructor <;> linarith [hx.2.2.1, hx.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq x Q.center
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr h0
  have hs1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [sq_nonneg Q.side, dist_nonneg (x := x) (y := Q.center)]

theorem strong_separation_direction_chord (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    dist (sourceRadialUnit y x) (sourceRadialUnit Q.center P.center) ≤ 1/32 := by
  have hs : 0 < s := hP.trans_le hp
  have hc : P.center ≠ Q.center := dist_pos.mp ((by positivity : 0 < 100*s).trans_le hl)
  have hx' := P.dist_center_le_three_quarters hP.le hx
  have hy' := Q.dist_center_le_three_quarters hQ.le hy
  have ht := dist_triangle P.center x Q.center
  have ht' := dist_triangle x y Q.center
  rw [dist_comm P.center x] at ht
  have hdist : 96*s ≤ dist x y := by linarith
  have hxy : x ≠ y := dist_pos.mp ((by positivity : 0 < 96*s).trans_le hdist)
  have he := endpoint_direction_dist_le (x := y) (y := x)
    (c := Q.center) (d := P.center) hxy hc
  rw [dist_comm y x] at he
  apply he.trans
  apply (div_le_iff₀ (dist_pos.mpr hxy)).mpr
  linarith

theorem small_chord_principal_angle {φ : ℝ} (hφ : |φ| ≤ Real.pi)
    (hd : dist (sourceUnitDirection φ) (sourceUnitDirection 0) ≤ 1/32) :
    |φ| ≤ 1/20 := by
  have he := sourceUnitDirection_dist_sq φ 0
  simp only [sub_zero] at he
  have hd2 := (sq_le_sq₀ dist_nonneg (by norm_num : (0:ℝ) ≤ 1/32)).mpr hd
  have hc := Real.cos_le_one_sub_mul_cos_sq hφ
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg Real.pi)
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hid : Real.pi^2 * (1-2/Real.pi^2*φ^2) = Real.pi^2-2*φ^2 := by
    field_simp
  rw [hid] at hm
  have hc0 : 0 ≤ 1-Real.cos φ := sub_nonneg.mpr (Real.cos_le_one φ)
  have hpi : Real.pi^2 ≤ (16/5:ℝ)^2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hb := mul_le_mul_of_nonneg_left (show 1-Real.cos φ ≤ (1:ℝ)/2048 by nlinarith) (sq_nonneg Real.pi)
  have ha := sq_abs φ
  nlinarith [abs_nonneg φ]

theorem strong_separation_parent_angle (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    ∃ φ : ℝ, |φ| ≤ 1/20 ∧
      sourceUnitDirection φ = sourceCircleRotate (-sourceParentAxis P Q) (sourceRadialUnit y x) ∧
      x-y = ‖x-y‖ • sourceDirection (φ+sourceParentAxis P Q) := by
  let axis := sourceParentAxis P Q
  let e := sourceRadialUnit Q.center P.center
  let dir := sourceCircleRotate (-axis) (sourceRadialUnit y x)
  let φ := sourceAngle dir
  have hφdir : sourceUnitDirection φ = dir := sourceUnitDirection_sourceAngle dir
  have hzero : sourceCircleRotate (-axis) e = sourceUnitDirection 0 := by
    change sourceUnitDirection (sourceAngle e + -sourceAngle e) = _
    rw [add_neg_cancel]
  have hchord := strong_separation_direction_chord P Q hP hQ hp hq hl hx hy
  have hd : dist (sourceUnitDirection φ) (sourceUnitDirection 0) ≤ 1/32 := by
    rw [hφdir, ← hzero, sourceCircleRotate_dist]
    exact hchord
  have hφpi : |φ| ≤ Real.pi := by
    exact abs_le.mpr ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  refine ⟨φ, small_chord_principal_angle hφpi hd, hφdir, ?_⟩
  have hrot := congrArg (sourceCircleRotate axis) hφdir
  simp only [dir, sourceCircleRotate_comp, sourceCircleRotate_add,
    neg_add_cancel, sourceCircleRotate_zero] at hrot
  have hv := congrArg (fun d : UnitCircle => (d : Plane)) hrot
  change sourceDirection (φ+axis) = sourceRadialVector y x at hv
  have hs : 0 < s := hP.trans_le hp
  have hx' := P.dist_le hP.le hx (P.center_mem hP)
  have hy' := Q.dist_le hQ.le hy (Q.center_mem hQ)
  have ht := dist_triangle P.center x Q.center
  have ht' := dist_triangle x y Q.center
  rw [dist_comm P.center x] at ht
  have hdist : 0 < dist x y := by linarith
  have hxy : x ≠ y := dist_pos.mp hdist
  rw [hv, sourceRadialVector, ite_eq_right hxy, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)), one_smul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentConeSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem sourceConeCircle_one_near_centered_angle (axis : ℝ) {φ θ : ℝ}
    (hφ : |φ| ≤ 1/20) (hθ : |θ-φ| ≤ 1/20) :
    sourceConeCircle axis (sourceUnitDirection (θ+axis)) = 1 := by
  have ht : |θ| ≤ 1/10 := by
    have hh := abs_add_le (θ-φ) φ
    rw [sub_add_cancel] at hh
    linarith
  have hperiod : θ ∈ Ioc (-Real.pi) Real.pi := by
    have hh := abs_le.mp ht
    exact ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  simp only [sourceConeCircle, sourceCircleRotate_comp, add_neg_cancel_right,
    sourceAngle_comp_on_period hperiod]
  exact graphConeCutoff_one ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_HighShellCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology

theorem sourceConeCircle_zero_of_cos_neg (axis θ : ℝ)
    (hc : Real.cos (θ-axis) < 0) : sourceConeCircle axis (sourceUnitDirection θ) = 0 := by
  by_contra hn
  have hs : sourceAngle (sourceUnitDirection (θ-axis)) ∈ Icc (-1/5:ℝ) (1/5) := by
    apply graphConeCutoff_support
    apply subset_closure
    simpa only [Function.mem_support,sourceConeCircle,sourceCircleRotate_comp,
      sub_eq_add_neg] using hn
  have hcos : 0 ≤ Real.cos (sourceAngle (sourceUnitDirection (θ-axis))) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith only [hs.1, Real.one_le_pi_div_two])
      (by linarith only [hs.2, Real.one_le_pi_div_two])
  rw [periodic_sourceAngle Real.cos_periodic] at hcos
  exact (not_lt_of_ge hcos) hc

theorem sourceConeCircle_inverse_germs (axis : ℝ) {φ : ℝ} (hφ : |φ| ≤ 1/20) :
    (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) =ᶠ[𝓝 (φ+axis)] (fun _ => 1) ∧
    (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) =ᶠ[𝓝 (φ+axis+Real.pi)] (fun _ => 0) := by
  constructor
  · filter_upwards [Metric.ball_mem_nhds (φ+axis) (by norm_num : (0:ℝ) < 1/20)] with θ hθ
    have hh : |(θ-axis)-φ| ≤ 1/20 := by
      rw [Metric.mem_ball,Real.dist_eq] at hθ
      convert hθ.le using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    simpa using sourceConeCircle_one_near_centered_angle axis hφ hh
  · have hc : Real.cos (φ+axis+Real.pi-axis) < 0 := by
      have hp : -(Real.pi/2) < φ ∧ φ < Real.pi/2 := by
        have hh := abs_le.mp hφ
        constructor
        · linarith only [hh.1, Real.pi_gt_three]
        · linarith only [hh.2, Real.pi_gt_three]
      rw [show φ+axis+Real.pi-axis = φ+Real.pi by ring,Real.cos_add_pi]
      exact neg_neg_of_pos (Real.cos_pos_of_mem_Ioo hp)
    have hne : {θ : ℝ | Real.cos (θ-axis) < 0} ∈ 𝓝 (φ+axis+Real.pi) :=
      (isOpen_lt (Real.continuous_cos.comp (continuous_id.sub continuous_const))
        continuous_const).mem_nhds hc
    filter_upwards [hne] with θ hθ
    exact sourceConeCircle_zero_of_cos_neg axis θ hθ

theorem sourceConeCircle_uniform_derivatives (n : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ axis : ℝ, ∀ j ≤ n, ∀ θ,
      ‖iteratedDeriv j (fun t => sourceConeCircle axis (sourceUnitDirection t)) θ‖ ≤ P := by
  let f := fun θ => sourceConeCircle 0 (sourceUnitDirection θ)
  have hf : ContDiff ℝ ∞ f := sourceConeCircle_angular_contDiff
  have hp : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg (sourceConeCircle 0) (sourceUnitDirection_periodic θ)
  have hj (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ θ, ‖iteratedDeriv j f θ‖ ≤ B := by
    have hpj : Function.Periodic (iteratedDeriv j f) (2*Real.pi) := by
      have he : (fun x => f (x+2*Real.pi)) = f := funext hp
      have hh := iteratedDeriv_comp_add_const j f (2*Real.pi)
      rw [he] at hh
      intro x
      exact (congrFun hh x).symm
    obtain ⟨B,hB⟩ := (hpj.isBounded_of_continuous
      (by positivity : 2*Real.pi ≠ 0) (hf.continuous_iteratedDeriv j
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)))).exists_norm_le
    exact ⟨max 0 B,le_max_left _ _,fun θ => (hB _ ⟨θ,rfl⟩).trans (le_max_right _ _)⟩
  choose B hB hb using hj
  refine ⟨∑ j ∈ Finset.range (n+1), B j,Finset.sum_nonneg (fun j _ => hB j),?_⟩
  intro axis j hj θ
  rw [sourceConeCircle_rotated_deriv]
  exact (hb j (θ-axis)).trans (Finset.single_le_sum (fun k _ => hB k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootHighShellInverse
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology ComplexConjugate

theorem uniform_root_high_shell_inverse {sig δ T : ℝ}
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
    ‖Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ))*(rootPairMask d e N sig (x,y):ℂ) -
      sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
        (rootPairSymbol d e N sig (x,y))‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := rotated_inverse_circle_power (T := T) (c := 1) (by norm_num) hsig
  obtain ⟨P,hP,hPb⟩ := sourceConeCircle_uniform_derivatives (4*(n+1)+2)
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_root_pair_derivatives hsig 0 (4*(n+1)+2)
  obtain ⟨N₂,h₂⟩ := hn P C hP hC
  obtain ⟨N₃,h₃⟩ := root_stationary_slack hsig hsmall hδ
  refine ⟨n,max (max N₁ N₂) N₃,?_⟩
  intro N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_right _ _).trans hN
  have hder := h₁ N hN₁ d e hd he hc₁ hc₂ (fun _ => 0) (fun _ => 0)
    (by simp) (by simp) (N/2) hL₁ hL₂ (fun _ => 1) (fun _ => 1) x y (by simp) (by simp)
  let f := fun θ => rootPairSymbol d e N sig (x,y) (sourceUnitDirection θ)
  have hf : ContDiff ℝ ∞ f := by
    simpa only [f,rootPairSymbol_inherited] using hder.1
  have hb : ∀ j ≤ 4*(n+1)+2, ∀ θ, ‖iteratedDeriv j f θ‖ ≤ C*sourceSymbolScale N sig (N/2)^j := by
    simpa only [f,rootPairSymbol_inherited] using hder.2
  let axis := sourceParentAxis U V
  obtain ⟨φ,hφ,hdir,hgeom⟩ := strong_separation_parent_angle U V hU hV hUs hVs hsep hx hy
  have hdir' : sourceUnitDirection (φ+axis) = sourceRadialUnit y x := by
    have hh := congrArg (sourceCircleRotate axis) hdir
    simpa only [axis,sourceCircleRotate_comp,sourceCircleRotate_add,neg_add_cancel,
      sourceCircleRotate_zero] using hh
  have hval : f (φ+axis) = (rootPairMask d e N sig (x,y):ℂ) := by
    change rootPairSymbol d e N sig (x,y) (sourceUnitDirection (φ+axis)) = _
    rw [hdir',rootPairSymbol_radial]
  have hslack := h₃ N hN₃ (N/2) (by omega) r (dist x y) hr hxy
  have hψ := sourceConeCircle_rotated_contDiff axis
  obtain ⟨hg₁,hg₂⟩ := sourceConeCircle_inverse_germs axis hφ
  have hpψ : Function.Periodic (fun θ => sourceConeCircle axis (sourceUnitDirection θ)) (2*Real.pi) :=
    fun θ => congrArg (sourceConeCircle axis) (sourceUnitDirection_periodic θ)
  have hpf : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg (rootPairSymbol d e N sig (x,y)) (sourceUnitDirection_periodic θ)
  have hh := h₂ N hN₂ hψ hf hpψ hpf (φ+axis) hg₁ hg₂
    (sourceSymbolScale_one_le N hsig.le (N/2))
    (by simpa only [one_mul] using hslack.1)
    (sourceSymbolScale_upper N hsig.le (Nat.div_le_self N 2))
    (by simpa only [neg_mul,one_mul] using hslack.2) (hPb axis) hb
  rw [hval] at hh
  rw [sourceInverseCircleIntegral_eq n r (φ+axis) hgeom hψ.continuous hf]
  simpa only [dist_eq_norm] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootWeightedInverse
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_root_weighted_inverse_oai {sig δ T : ℝ}
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
      (((dist x y)^(-(1/2:ℝ)):ℝ):ℂ) *
        sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
          (rootPairSymbol d e N sig (x,y))‖ ≤ ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,N₁,h₁⟩ := uniform_root_high_shell_inverse (T := T+1) hsig hsmall hδ
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (δ^(-(1/2:ℝ)))
  refine ⟨n,max N₁ N₂,?_⟩
  intro N hN d e hd he hc₁ hc₂ hL₁ hL₂ U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hb := h₁ N ((le_max_left _ _).trans hN) d e hd he hc₁ hc₂ hL₁ hL₂
    U V hU hV s hUs hVs hsep r hr x hx y hy hxy
  have hw0 : 0 ≤ (dist x y)^(-(1/2:ℝ)) := Real.rpow_nonneg dist_nonneg _
  have hw : (dist x y)^(-(1/2:ℝ)) ≤ ((2:ℝ)^N)^(1:ℝ) :=
    (Real.rpow_le_rpow_of_nonpos hδ hxy (by norm_num)).trans (h₂ N ((le_max_right _ _).trans hN))
  have hexp : ((2:ℝ)^N)^(1:ℝ)*((2:ℝ)^N)^(-(T+1)) = ((2:ℝ)^N)^(-T) := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
    congr 1
    ring
  have heq : (rootSpatialWeight d e N sig (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      (((dist x y)^(-(1/2:ℝ)):ℝ):ℂ) *
        sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
          (rootPairSymbol d e N sig (x,y)) =
      (((dist x y)^(-(1/2:ℝ)):ℝ):ℂ) *
        (Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ))*(rootPairMask d e N sig (x,y):ℂ) -
          sourceInverseCircleIntegral n r (x-y) (sourceConeCircle (sourceParentAxis U V))
            (rootPairSymbol d e N sig (x,y))) := by
    simp only [rootSpatialWeight,Complex.ofReal_mul]
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw0]
  exact (mul_le_mul hw hb (norm_nonneg _) (by positivity)).trans_eq hexp

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_root_weighted_inverse_oai := @OAI.PlanarFalconer.uniform_root_weighted_inverse_oai
