-- Prove2me | solution 1 for OAI.Falconer.endpoint_spherical_preparation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:14:42.549218+00:00
-- url     : https://prove2.me/submissions/e4e3ab6b-83c3-442b-b732-93adef7a51f8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_small_chart_weak_radial

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_smul (w v : E) (a : ℝ) :
    perpendicularPart w (a • v) = a • perpendicularPart w v := by
  simp only [perpendicularPart,inner_smul_right,smul_sub,smul_smul]

theorem norm_perpendicularPart_sq {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖^2 = ‖v‖^2-(inner ℝ w v)^2 := by
  have h := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right,real_inner_comm v w,norm_smul,hw,
    mul_one,Real.norm_eq_abs,sq_abs] at h
  dsimp only [perpendicularPart]
  rw [real_inner_comm v w]
  nlinarith

theorem unit_close_of_perpendicular {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hinner : 0 ≤ inner ℝ w u) :
    ‖w-u‖ ≤ 2*‖perpendicularPart w u‖ := by
  have hsq := norm_sub_sq_real w u
  have hp := norm_perpendicularPart_sq hw u
  have ha : inner ℝ w u ≤ 1 := by
    have h := (le_abs_self (inner ℝ w u)).trans (abs_real_inner_le_norm w u)
    simpa only [hw,hu,mul_one] using h
  rw [hw,hu] at hsq
  rw [hu] at hp
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 4*inner ℝ w u+2 by linarith)
  nlinarith [norm_nonneg (w-u),norm_nonneg (perpendicularPart w u)]

theorem perpendicular_direction_two_caps {w v : E} (hw : ‖w‖ = 1)
    (hv : v ≠ 0) {W : ℝ} (htube : ‖perpendicularPart w v‖ ≤ W) :
    ‖w-‖v‖⁻¹ • v‖ ≤ 2*W/‖v‖ ∨ ‖w-(-‖v‖⁻¹ • v)‖ ≤ 2*W/‖v‖ := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp),inv_mul_cancel₀ hvp.ne']
  have hpu : ‖perpendicularPart w u‖ ≤ W/‖v‖ := by
    dsimp [u]
    rw [perpendicularPart_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp)]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left htube (inv_nonneg.mpr hvp.le)
  have hscale : 2*‖perpendicularPart w u‖ ≤ 2*W/‖v‖ := by
    calc
      _ ≤ 2*(W/‖v‖) := mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ = _ := by ring
  rcases le_total 0 (inner ℝ w u) with hi | hi
  · exact Or.inl ((unit_close_of_perpendicular hw hu hi).trans hscale)
  · have hneg : perpendicularPart w (-u) = -perpendicularPart w u := by
      simp only [perpendicularPart,inner_neg_right,neg_smul]
      abel
    have hh := unit_close_of_perpendicular hw (by simpa only [norm_neg] using hu)
      (show 0 ≤ inner ℝ w (-u) by rw [inner_neg_right]; linarith)
    rw [hneg,norm_neg] at hh
    right
    simpa only [u,neg_smul] using hh.trans hscale

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem northLift_continuous (n : ℕ) : Continuous (@northLift n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · simpa only [Fin.cons_succ] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

theorem gnomonicChart_continuous (n : ℕ) : Continuous (@gnomonicChart n) := by
  apply Continuous.subtype_mk
  exact ((northLift_continuous n).norm.inv₀ (fun x =>
    norm_ne_zero_iff.mpr (northLift_ne_zero x))).smul (northLift_continuous n)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InversePowerSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic inverse-power sums at the critical ambient exponent -/

namespace Falconer

theorem inverse_power_dyadic {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (g k : ℕ)
    (hmin : 1/(2:ℝ)^(g+k) ≤ r) :
    (1/r)^s ≤ ((2:ℝ)^g)^s + ∑ j ∈ Finset.range k,
      if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
  induction k with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero] at *
    apply Real.rpow_le_rpow (by positivity) _ hs
    apply (div_le_iff₀ hr).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^g)).mp hmin
    nlinarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : 1/(2:ℝ)^(g+k) ≤ r
    · have hh := ih hc
      have hn : 0 ≤ (if r < 1/(2:ℝ)^(g+k) then ((2:ℝ)^(g+k+1))^s else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [ite_eq_left (lt_of_not_ge hc)]
      have hinv : 1/r ≤ (2:ℝ)^(g+k+1) := by
        apply (div_le_iff₀ hr).mpr
        have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(g+(k+1)))).mp hmin
        simpa only [Nat.add_assoc,mul_comm] using hh
      have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/r) hinv hs
      have hsum : 0 ≤ ∑ j ∈ Finset.range k,
          if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      have hz : 0 ≤ ((2:ℝ)^g)^s := by positivity
      linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RegularizedPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale inverse-distance potentials for the slicing kernels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_dyadic (μ : Measure X)
    (x : X) {s : ℝ} (hs : 0 ≤ s) (g k : ℕ) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
    ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g))+
      ∑ j ∈ Finset.range k, ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*
        μ (ball x (1/(2:ℝ)^(g+j))) := by
  let B := ball x (1/(2:ℝ)^g)
  let f : X → ℝ≥0∞ := fun y =>
    ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s)
  let F : X → ℝ≥0∞ := fun y =>
    B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k,
        (ball x (1/(2:ℝ)^(g+j))).indicator
          (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
  have hpoint : B.indicator f ≤ F := by
    intro y
    change B.indicator f y ≤ B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy,show B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y =
        ENNReal.ofReal (((2:ℝ)^g)^s) from indicator_of_mem hy _]
      have hi := inverse_power_dyadic (s := s)
        (by positivity : 0 < dist x y+1/(2:ℝ)^(g+k)) hs g k
        (by linarith [dist_nonneg (x := x) (y := y)])
      have hh := ENNReal.ofReal_le_ofReal hi
      rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)] at hh
      apply hh.trans
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      by_cases hdist : dist x y+1/(2:ℝ)^(g+k) < 1/(2:ℝ)^(g+j)
      · rw [ite_eq_left hdist]
        have hyj : y ∈ ball x (1/(2:ℝ)^(g+j)) := by
          rw [mem_ball,dist_comm]
          linarith [show (0:ℝ) < 1/(2:ℝ)^(g+k) by positivity]
        rw [indicator_of_mem hyj]
      · rw [ite_eq_right hdist,ENNReal.ofReal_zero]
        exact bot_le
    · rw [indicator_of_notMem hy]
      exact bot_le
  rw [← lintegral_indicator measurableSet_ball]
  apply (lintegral_mono hpoint).trans_eq
  change (∫⁻ y, B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y ∂μ) = _
  rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
    lintegral_indicator_const measurableSet_ball,
    lintegral_finsetSum _ (fun j _ => measurable_const.indicator measurableSet_ball)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_indicator_const measurableSet_ball _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric summation above the inverse-kernel exponent -/

namespace Falconer

theorem dyadic_potential_weight (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^(n+1))^s)*(1/(2:ℝ)^n)^q =
      (2:ℝ)^s*(((2:ℝ)^n)^(s-q)) := by
  rw [pow_succ,Real.mul_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2),
    one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_start (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^n)^s)*(1/(2:ℝ)^n)^q = (((2:ℝ)^n)^(s-q)) := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_series (g k : ℕ) {s q : ℝ} (hsq : s < q) :
    (∑ j ∈ Finset.range k, (((2:ℝ)^(g+j))^(s-q))) ≤
      (((2:ℝ)^g)^(s-q))/(1-(2:ℝ)^(s-q)) := by
  let a := (2:ℝ)^(s-q)
  have ha : 0 ≤ a := by positivity
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsq)
  have hsum : ∑ j ∈ Finset.range k, a^j ≤ (1-a)⁻¹ := by
    rw [← tsum_geometric_of_lt_one ha ha1]
    exact (summable_geometric_of_lt_one ha ha1).sum_le_tsum _ (fun _ _ => pow_nonneg ha _)
  have he (j : ℕ) : (((2:ℝ)^(g+j))^(s-q)) = (((2:ℝ)^g)^(s-q))*a^j := by
    rw [pow_add,Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    dsimp [a]
    rw [← Real.rpow_natCast_mul (by norm_num),← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by rw [div_eq_mul_inv])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialFrostman
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale ball bounds control the regularized slicing potential -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_frostman (μ : Measure X) (x : X)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hball : ∀ n : ℕ, n ≤ g+k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  apply (regularized_potential_dyadic μ x hs g k).trans
  have hstart : ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g)) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^g)^s)*ENNReal.ofReal (K*(1/(2:ℝ)^g)^q) :=
        mul_le_mul_right (hball g (by omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^g)^s)*(1/(2:ℝ)^g)^q) := by ring
          _ = _ := by rw [dyadic_potential_start]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*μ (ball x (1/(2:ℝ)^(g+j))) ≤
      ENNReal.ofReal (K*(2:ℝ)^s*(((2:ℝ)^(g+j))^(s-q))) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*ENNReal.ofReal (K*(1/(2:ℝ)^(g+j))^q) :=
        mul_le_mul_right (hball (g+j) (by have := Finset.mem_range.mp hj; omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^(g+j+1))^s)*(1/(2:ℝ)^(g+j))^q) := by ring
          _ = _ := by rw [dyadic_potential_weight]; ring
  calc
    _ ≤ ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q)))+
        ∑ j ∈ Finset.range k, ENNReal.ofReal (K*(2:ℝ)^s*(((2:ℝ)^(g+j))^(s-q))) :=
      add_le_add hstart (Finset.sum_le_sum hterm)
    _ = ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))+
        K*(2:ℝ)^s*(∑ j ∈ Finset.range k, (((2:ℝ)^(g+j))^(s-q)))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),Finset.mul_sum]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left (dyadic_potential_series g k hsq)
        (show 0 ≤ K*(2:ℝ)^s by positivity)
      calc
        _ ≤ K*(((2:ℝ)^g)^(s-q))+K*(2:ℝ)^s*
            ((((2:ℝ)^g)^(s-q))/(1-(2:ℝ)^(s-q))) := add_le_add le_rfl hh
        _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialPair
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Localized pair potentials at the original finite resolution -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem regularized_pair_potential (μ : Measure X) [SFinite μ]
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : X, ∀ n : ℕ, n ≤ N →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ z in {z : X × X | dist z.1 z.2 < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(dist z.1 z.2+1/(2:ℝ)^N))^s) ∂μ.prod μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  let D : Set (X × X) := {z | dist z.1 z.2 < 1/(2:ℝ)^g}
  let f : X × X → ℝ≥0∞ := fun z => ENNReal.ofReal ((1/(dist z.1 z.2+1/(2:ℝ)^N))^s)
  let B := ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q))))
  have hD : MeasurableSet D := measurableSet_lt (by fun_prop) measurable_const
  have hp (x : X) : (∫⁻ y in ball x (1/(2:ℝ)^g), f (x,y) ∂μ) ≤ B := by
    have hh := regularized_potential_frostman μ x hK hs hsq g (N-g) (by
      intro n hn
      exact hball x n (by omega))
    simpa only [Nat.add_sub_of_le hg,f,B] using hh
  rw [← lintegral_indicator hD,
    lintegral_prod _ (((by fun_prop : Measurable f).indicator hD).aemeasurable)]
  calc
    _ = ∫⁻ x, ∫⁻ y in ball x (1/(2:ℝ)^g), f (x,y) ∂μ ∂μ := by
      apply lintegral_congr
      intro x
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : dist x y < 1/(2:ℝ)^g
      · have hb : y ∈ ball x (1/(2:ℝ)^g) := by simpa only [mem_ball,dist_comm] using hy
        rw [indicator_of_mem (show (x,y) ∈ D from hy),indicator_of_mem hb]
      · have hb : y ∉ ball x (1/(2:ℝ)^g) := by simpa only [mem_ball,dist_comm] using hy
        rw [indicator_of_notMem (show (x,y) ∉ D from hy),indicator_of_notMem hb]
    _ ≤ ∫⁻ _ : X, B ∂μ := lintegral_mono hp
    _ = B*μ univ := lintegral_const _
    _ ≤ B*1 := mul_le_mul_right hmass B
    _ = _ := mul_one _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-vector Gaussian band estimates for the angular slicing construction -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianBandConstant_pos : 0 < gaussianBandConstant := by
  unfold gaussianBandConstant
  positivity

theorem standard_gaussian_density_bound :
    gaussianReal 0 1 ≤ ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) • (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards with x
  apply ENNReal.ofReal_le_ofReal
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  have he : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem standard_gaussian_band {r : ℝ} (_hr : 0 ≤ r) :
    gaussianReal 0 1 (Icc (-r) r) ≤ ENNReal.ofReal (gaussianBandConstant*r) := by
  calc
    _ ≤ (ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹) • (volume : Measure ℝ)) (Icc (-r) r) :=
      standard_gaussian_density_bound _
    _ = _ := by
      rw [Measure.smul_apply,smul_eq_mul,Real.volume_Icc,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold gaussianBandConstant
      ring

theorem gaussian_unit_inner_law {w : Space d} (hw : ‖w‖ = 1) :
    (stdGaussian (Space d)).map (innerSL ℝ w) = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,
    innerSL_apply_norm,hw]
  norm_num

theorem gaussian_unit_inner_band {w : Space d} (hw : ‖w‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space d) {x | |inner ℝ w x| ≤ r} ≤ ENNReal.ofReal (gaussianBandConstant*r) := by
  have he : {x : Space d | |inner ℝ w x| ≤ r} = (innerSL ℝ w) ⁻¹' Icc (-r) r := by
    ext x
    simp only [mem_ofPred_eq,mem_preimage,mem_Icc,innerSL_apply_apply,abs_le]
  rw [he,← Measure.map_apply (innerSL ℝ w).continuous.measurable measurableSet_Icc,
    gaussian_unit_inner_law hw]
  exact standard_gaussian_band hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianOrthogonal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal Gaussian coordinates for random-subspace band estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussian_orthogonal_inner_independent (u v : Space d) (huv : inner ℝ u v = 0) :
    IndepFun (fun x : Space d => inner ℝ u x) (fun x : Space d => inner ℝ v x)
      (stdGaussian (Space d)) := by
  have hpair : HasGaussianLaw (fun x : Space d => (inner ℝ u x,inner ℝ v x))
      (stdGaussian (Space d)) :=
    IsGaussian.hasGaussianLaw_id.map_fun ((innerSL ℝ u).prod (innerSL ℝ v))
  apply hpair.indepFun_of_covariance_eq_zero
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian,
    innerSL_apply_apply,huv]

theorem gaussian_orthogonal_pair_band {u v : Space d} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    stdGaussian (Space d) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ s} ≤
      ENNReal.ofReal (gaussianBandConstant^2*r*s) := by
  have hi := gaussian_orthogonal_inner_independent u v huv
  have he := hi.measure_inter_preimage_eq_mul (Icc (-r) r) (Icc (-s) s)
    measurableSet_Icc measurableSet_Icc
  have hsets (w : Space d) (t : ℝ) :
      (fun x : Space d => inner ℝ w x) ⁻¹' Icc (-t) t = {x | |inner ℝ w x| ≤ t} := by
    ext x
    simp only [mem_preimage,mem_Icc,mem_ofPred_eq,abs_le]
  rw [hsets,hsets] at he
  change stdGaussian (Space d) ({x | |inner ℝ u x| ≤ r} ∩ {x | |inner ℝ v x| ≤ s}) ≤ _
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (gaussianBandConstant*r)*ENNReal.ofReal (gaussianBandConstant*s) :=
      mul_le_mul' (gaussian_unit_inner_band hu hr) (gaussian_unit_inner_band hv hs)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg gaussianBandConstant_pos.le hr)]
      congr 1
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPairGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Resolving two Gaussian band constraints into orthogonal coordinates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem perpendicular_normalize_orthogonal {u v : Space d} (hu : ‖u‖ = 1) :
    inner ℝ u (normalize (perpendicularPart u v)) = 0 := by
  simp [NormedSpace.normalize,perpendicularPart,inner_sub_right,inner_smul_right,
    hu]

theorem two_band_perpendicular_coordinate {u v x : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {r : ℝ} (_hr : 0 ≤ r)
    (hux : |inner ℝ u x| ≤ r) (hvx : |inner ℝ v x| ≤ r)
    (hne : perpendicularPart u v ≠ 0) :
    |inner ℝ (normalize (perpendicularPart u v)) x| ≤ 2*r/‖perpendicularPart u v‖ := by
  have huv : |inner ℝ u v| ≤ 1 := by
    simpa only [hu,hv,mul_one] using abs_real_inner_le_norm u v
  have hinner : |inner ℝ (perpendicularPart u v) x| ≤ 2*r := by
    rw [perpendicularPart,inner_sub_left,real_inner_smul_left]
    calc
      _ ≤ |inner ℝ v x|+|inner ℝ u v*inner ℝ u x| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (inner ℝ v x) (inner ℝ u v*inner ℝ u x)
      _ ≤ r+1*r := add_le_add hvx (by rw [abs_mul]; exact mul_le_mul huv hux (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  rw [NormedSpace.normalize,real_inner_smul_left,abs_mul,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne))]
  simpa only [div_eq_mul_inv,mul_comm] using
    mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr (norm_nonneg (perpendicularPart u v)))

theorem gaussian_two_band_nondegenerate {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hne : perpendicularPart u v ≠ 0) :
    stdGaussian (Space d) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ≤
      ENNReal.ofReal (2*gaussianBandConstant^2*r^2/‖perpendicularPart u v‖) := by
  have hsub : {x : Space d | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ⊆
      {x : Space d | |inner ℝ u x| ≤ r ∧
        |inner ℝ (normalize (perpendicularPart u v)) x| ≤ 2*r/‖perpendicularPart u v‖} := by
    rintro x ⟨hx,hx'⟩
    exact ⟨hx,two_band_perpendicular_coordinate hu hv hr hx hx' hne⟩
  apply (measure_mono hsub).trans
  have h := gaussian_orthogonal_pair_band hu (norm_normalize hne)
    (perpendicular_normalize_orthogonal hu) hr (by positivity : 0 ≤ 2*r/‖perpendicularPart u v‖)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPairBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularized two-vector Gaussian band bounds -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianPairBandConstant_pos : 0 < gaussianPairBandConstant := by
  unfold gaussianPairBandConstant
  have := gaussianBandConstant_pos
  positivity

theorem gaussian_two_band {u v : Space d} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    stdGaussian (Space d) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ≤
      ENNReal.ofReal (gaussianPairBandConstant*r^2/(‖perpendicularPart u v‖+r)) := by
  let C := gaussianBandConstant
  let q := ‖perpendicularPart u v‖
  have hC : 0 < C := gaussianBandConstant_pos
  have hq₀ : 0 ≤ q := norm_nonneg _
  have hden : 0 < q+r := by positivity
  have hsub : {x : Space d | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ⊆
      {x : Space d | |inner ℝ u x| ≤ r} := fun _ hx => hx.1
  by_cases hqr : q ≤ r
  · apply ((measure_mono hsub).trans (gaussian_unit_inner_band hu hr.le)).trans
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hden).mpr
    calc
      C*r*(q+r) ≤ C*r*(2*r) := by gcongr; linarith
      _ = (2*C)*r^2 := by ring
      _ ≤ gaussianPairBandConstant*r^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        dsimp [gaussianPairBandConstant,C]
        nlinarith [sq_nonneg gaussianBandConstant]
  · have hqp : 0 < q := hr.trans (lt_of_not_ge hqr)
    have hne : perpendicularPart u v ≠ 0 := norm_pos_iff.mp hqp
    apply (gaussian_two_band_nondegenerate hu hv hr.le hne).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_iff₀ hqp hden).mpr
    calc
      (2*C^2*r^2)*(q+r) ≤ (2*C^2*r^2)*(2*q) := by gcongr; linarith
      _ = (4*C^2)*r^2*q := by ring
      _ ≤ gaussianPairBandConstant*r^2*q := by
        gcongr
        dsimp [gaussianPairBandConstant,C]
        linarith [gaussianBandConstant_pos]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Second moments of the actual Gaussian direction bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianDirectionBand_measurable (A : Fin h → Space d) (r : ℝ) :
    MeasurableSet (gaussianDirectionBand A r) := by
  simp only [gaussianDirectionBand,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized direction-slice masses and their second moment -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_squared_band_normalization {r C : ℝ} (hr : 0 < r) (_hC : 0 ≤ C) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^2*ENNReal.ofReal ((C*r^2)^h) =
      ENNReal.ofReal (C^h) := by
  rw [← ENNReal.ofReal_pow (by positivity),← ENNReal.ofReal_mul (by positivity),
    Real.rpow_neg hr.le,Real.rpow_natCast,mul_pow]
  congr 1
  have he : (r^2)^h = (r^h)^2 := by
    simp only [← pow_mul]
    congr 1
    omega
  rw [he]
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_FourierLebesgue
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate
open scoped ENNReal NNReal RealInnerProductSpace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem gaussian_lebesgue_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b * ‖ξ‖^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) hb 0 (0 : V)
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h.norm

theorem source_gaussian_fourier {b : ℝ} (hb : 0 < b) (x : V) :
    𝓕 (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) x =
      ((Real.pi / b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2 / b) * ‖x‖^2) : ℝ) := by
  have he : (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) =
      (fun ξ : V => Complex.exp (-(b : ℂ) * ‖ξ‖^2)) := by
    funext ξ
    push_cast
    rfl
  rw [he, fourier_gaussian_innerProductSpace (b := (b : ℂ)) hb,
    Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledConditional
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual affine rescaling of a conditional class probability -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_radius_bracket {m : ℕ} {r : ℝ}
    (hmin : 1/(2:ℝ)^m ≤ r) (hmax : r ≤ 1) :
    ∃ j ≤ m, r ≤ 1/(2:ℝ)^j ∧ 1/(2:ℝ)^j ≤ 2*r := by
  induction m with
  | zero =>
    refine ⟨0,le_rfl,?_,?_⟩
    · simpa using hmax
    · norm_num at hmin ⊢
      linarith
  | succ m ih =>
    by_cases hcoarse : 1/(2:ℝ)^m ≤ r
    · obtain ⟨j,hj,hr,hjr⟩ := ih hcoarse
      exact ⟨j,hj.trans (Nat.le_succ m),hr,hjr⟩
    · refine ⟨m,Nat.le_succ m,(lt_of_not_ge hcoarse).le,?_⟩
      have he : 1/(2:ℝ)^m = 2*(1/(2:ℝ)^(m+1)) := by rw [pow_succ]; field_simp
      rw [he]
      linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianConvolution
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian convolution of a finite measure Fourier transform -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace
variable {d : ℕ}

theorem sourceFourier_phase (μ : Measure (Space d)) (v : Space d) :
    PlanarFalconer.sourceFourier μ v = ∫ x, euclideanFourierPhase v x ∂μ := by
  simp only [PlanarFalconer.sourceFourier,charFun_apply,inner_smul_right,euclideanFourierPhase]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianProjection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact Gaussian law of an orthogonal projection -/

namespace Falconer
open MeasureTheory ProbabilityTheory
variable {d : ℕ}

theorem gaussian_orthogonal_projection (V : Submodule ℝ (Space d)) :
    (stdGaussian (Space d)).map V.orthogonalProjectionOnto = stdGaussian V := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply,integral_map V.orthogonalProjectionOnto.continuous.measurable.aemeasurable
    (by fun_prop)]
  simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← charFun_apply,charFun_stdGaussian,charFun_stdGaussian]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLebesgue
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Lebesgue density for the standard Gaussian used in the band estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

instance gaussianLebesgue_finite : IsFiniteMeasure (gaussianLebesgue d) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    (PlanarFalconer.gaussian_lebesgue_integrable (by norm_num : (0:ℝ) < 1/2))
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_ne_top

theorem gaussianLebesgue_sourceFourier (v : Space d) :
    PlanarFalconer.sourceFourier (gaussianLebesgue d) v =
      (((2*Real.pi)^((d:ℝ)/2)*Real.exp (-(2*Real.pi^2)*‖v‖^2):ℝ):ℂ) := by
  have he : PlanarFalconer.sourceFourier (gaussianLebesgue d) v =
      𝓕 (fun x : Space d => (Real.exp (-(1/2:ℝ)*‖x‖^2):ℂ)) v := by
    rw [sourceFourier_phase,gaussianLebesgue,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,Complex.real_smul]
    simp only [euclideanFourierPhase,smul_eq_mul]
    rw [mul_comm]
    congr 2
    ring_nf
  rw [he,PlanarFalconer.source_gaussian_fourier (by norm_num : (0:ℝ) < 1/2)]
  simp only [Space,finrank_euclideanSpace,Fintype.card_fin]
  congr 1
  congr 1 <;> ring_nf

instance normalizedGaussianLebesgue_finite : IsFiniteMeasure (normalizedGaussianLebesgue d) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (gaussianVolumeNormalization d)*gaussianLebesgue d univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem normalizedGaussianLebesgue_sourceFourier (v : Space d) :
    PlanarFalconer.sourceFourier (normalizedGaussianLebesgue d) v =
      (Real.exp (-(2*Real.pi^2)*‖v‖^2):ℂ) := by
  have hpos : 0 < (2*Real.pi)^((d:ℝ)/2) := by positivity
  rw [PlanarFalconer.sourceFourier,charFun_apply,normalizedGaussianLebesgue,integral_smul_measure]
  change (ENNReal.ofReal (gaussianVolumeNormalization d)).toReal •
    PlanarFalconer.sourceFourier (gaussianLebesgue d) v = _
  rw [ENNReal.toReal_ofReal (by unfold gaussianVolumeNormalization; positivity),
    gaussianLebesgue_sourceFourier,Complex.real_smul]
  unfold gaussianVolumeNormalization
  push_cast
  rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hpos.ne'),one_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianDensity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Gaussian density and its dimensional Lebesgue upper bound -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussian_frequency_scale (t : Space d) :
    2*Real.pi^2*‖((-(2*Real.pi))⁻¹) • t‖^2 = ‖t‖^2/2 := by
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  field_simp

theorem normalizedGaussianLebesgue_eq_standard :
    normalizedGaussianLebesgue d = stdGaussian (Space d) := by
  apply Measure.ext_of_charFun
  ext t
  let v : Space d := ((-(2*Real.pi))⁻¹) • t
  have he : (-(2*Real.pi)) • v = t := by
    dsimp [v]
    rw [smul_smul,mul_inv_cancel₀
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)),one_smul]
  have hh := normalizedGaussianLebesgue_sourceFourier v
  change charFun (normalizedGaussianLebesgue d) ((-(2*Real.pi)) • v) = _ at hh
  rw [he] at hh
  rw [hh,charFun_stdGaussian]
  dsimp [v]
  have hs := gaussian_frequency_scale t
  rw [show -(2*Real.pi^2)*‖((-(2*Real.pi))⁻¹) • t‖^2 = -‖t‖^2/2 by linarith]
  simp only [Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_pow,
    Complex.ofReal_ofNat]

theorem gaussianLebesgue_le_volume : gaussianLebesgue d ≤ (volume : Measure (Space d)) := by
  calc
    _ ≤ (volume : Measure (Space d)).withDensity (fun _ => (1:ℝ≥0∞)) := by
      apply withDensity_mono
      filter_upwards with x
      have he : Real.exp (-(1/2:ℝ)*‖x‖^2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
    _ = _ := by rw [withDensity_const,one_smul]

theorem standard_gaussian_le_volume : stdGaussian (Space d) ≤
    ENNReal.ofReal (gaussianVolumeNormalization d) • (volume : Measure (Space d)) := by
  rw [← normalizedGaussianLebesgue_eq_standard]
  unfold normalizedGaussianLebesgue
  gcongr
  exact gaussianLebesgue_le_volume

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBox
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian bounds for nonsingular systems of linear bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {j : ℕ}

theorem coordinateBox_measurable (r : ℝ) : MeasurableSet (coordinateBox j r) := by
  simp only [coordinateBox,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem coordinateBox_volume {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space j)) (coordinateBox j r) = ENNReal.ofReal ((2*r)^j) := by
  rw [← (PiLp.volume_preserving_toLp (Fin j)).measure_preimage
    (coordinateBox_measurable r).nullMeasurableSet]
  have he : (@WithLp.toLp 2 (Fin j → ℝ)) ⁻¹' coordinateBox j r =
      Set.pi univ (fun _ : Fin j => Icc (-r) r) := by
    ext x
    simp [coordinateBox,abs_le,Pi.le_def,forall_and]
  rw [he,volume_pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*r)]

theorem gaussian_linear_bands (L : Space j →L[ℝ] Space j)
    (hL : LinearMap.det (L : Space j →ₗ[ℝ] Space j) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space j) {x | ∀ i, |L x i| ≤ r} ≤
      ENNReal.ofReal (gaussianVolumeNormalization j*
        |(LinearMap.det (L : Space j →ₗ[ℝ] Space j))⁻¹| * (2*r)^j) := by
  have hc : 0 ≤ gaussianVolumeNormalization j := by unfold gaussianVolumeNormalization; positivity
  calc
    _ ≤ (ENNReal.ofReal (gaussianVolumeNormalization j) • (volume : Measure (Space j)))
        (L ⁻¹' coordinateBox j r) := standard_gaussian_le_volume _
    _ = _ := by
      rw [Measure.smul_apply,smul_eq_mul,Measure.addHaar_preimage_continuousLinearMap volume hL,
        coordinateBox_volume hr,← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by unfold gaussianVolumeNormalization; positivity)]
      congr 1
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PlanarSlopeBalls
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direction-ball control transfers to the slope coordinate -/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem normalize_dist_le_twice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x y : E} (hx : 1 ≤ ‖x‖) (hy : y ≠ 0) :
    dist (normalize x) (normalize y) ≤ 2*dist x y := by
  have he : ‖x‖ • (normalize x-normalize y) =
      x-y+(‖y‖-‖x‖) • normalize y := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (x-y) ((‖y‖-‖x‖) • normalize y)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hy,mul_one] at hb
  have hn := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  rw [dist_eq_norm,dist_eq_norm]
  nlinarith [norm_nonneg (normalize x-normalize y)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original direction labels in affine gnomonic coordinates -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem gnomonicCoordinates_measurable : Measurable (@gnomonicCoordinates n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  fun_prop

theorem northLift_gnomonicCoordinates (w : Sphere (n+1))
    (hw : 0 < (w:Space (n+1)) 0) :
    northLift (gnomonicCoordinates w) = ((w:Space (n+1)) 0)⁻¹ • (w:Space (n+1)) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [northLift_zero,PiLp.smul_apply,smul_eq_mul]
    exact (inv_mul_cancel₀ hw.ne').symm
  · simp only [northLift_succ,gnomonicCoordinates_apply,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv]
    exact mul_comm _ _

theorem gnomonicChart_gnomonicCoordinates (w : Sphere (n+1))
    (hw : 0 < (w:Space (n+1)) 0) :
    gnomonicChart (gnomonicCoordinates w) = w := by
  apply Subtype.ext
  change ‖northLift (gnomonicCoordinates w)‖⁻¹ • northLift (gnomonicCoordinates w) = _
  rw [northLift_gnomonicCoordinates w hw,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hw),sphere_norm,mul_one,inv_inv,smul_smul]
  rw [mul_inv_cancel₀ hw.ne',one_smul]

theorem northLift_distance (p q : Space n) : dist (northLift p) (northLift q) = dist p q := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [dist_eq_norm,dist_eq_norm,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  simp only [PiLp.sub_apply,northLift_zero,northLift_succ,sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add]

theorem gnomonicChart_distance_le (p q : Space n) :
    dist (gnomonicChart p) (gnomonicChart q) ≤ 2*dist p q := by
  have hp : 1 ≤ ‖northLift p‖ := by
    have he := northLift_norm_sq p
    nlinarith [norm_nonneg (northLift p),sq_nonneg ‖p‖]
  have hh := normalize_dist_le_twice hp (northLift_ne_zero q)
  simpa only [Subtype.dist_eq,NormedSpace.normalize,gnomonicChart,northLift_distance] using hh

end Falconer

/-! # Explicit inverse and cone coordinates for the gnomonic measure formula -/

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting an original direction law to its affine chart -/

namespace Falconer
open Set Metric MeasureTheory
variable {n : ℕ}

theorem gnomonicCoordinates_map_ball (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0) (p : Space n) (r : ℝ) :
    (Measure.map gnomonicCoordinates ν) (ball p r) ≤ ν (ball (gnomonicChart p) (2*r)) := by
  rw [Measure.map_apply gnomonicCoordinates_measurable measurableSet_ball]
  apply measure_mono_ae
  filter_upwards [hν] with w hw hmem
  change dist (gnomonicCoordinates w) p < r at hmem
  change dist w (gnomonicChart p) < 2*r
  rw [← gnomonicChart_gnomonicCoordinates w hw]
  exact (gnomonicChart_distance_le (gnomonicCoordinates w) p).trans_lt (by linarith)

theorem gnomonicCoordinates_map_recover (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0) :
    Measure.map gnomonicChart (Measure.map gnomonicCoordinates ν) = ν := by
  rw [Measure.map_map (gnomonicChart_continuous n).measurable gnomonicCoordinates_measurable]
  calc
    _ = Measure.map id ν := Measure.map_congr (by
      filter_upwards [hν] with w hw
      exact gnomonicChart_gnomonicCoordinates w hw)
    _ = ν := Measure.map_id

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicCap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small spherical cap has bounded original affine coordinates -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

theorem gnomonic_cap_first_coordinate (w : Sphere (n+1))
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ 1/2) :
    7/8 ≤ (w:Space (n+1)) 0 := by
  have hh := norm_sub_sq_real (w:Space (n+1)) (northLift (0 : Space n))
  rw [sphere_norm,northLift_zero_norm,inner_northLift_zero] at hh
  have hd : ‖(w:Space (n+1))-northLift (0 : Space n)‖ ≤ 1/2 := by
    simpa only [Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
  nlinarith [norm_nonneg ((w:Space (n+1))-northLift (0 : Space n))]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TripleGram
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram determinants for the endpoint's three original chart directions -/

namespace Falconer
variable {n : ℕ}

theorem tripleGram_polynomial {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : tripleGram a b c =
      gramPolynomial (inner ℝ a a) (inner ℝ b b) (inner ℝ c c)
        (inner ℝ a b) (inner ℝ a c) (inner ℝ b c) := by
  simp only [tripleGram,Matrix.det_fin_three,Matrix.gram_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  rw [real_inner_comm b a,real_inner_comm c a,real_inner_comm c b]
  unfold gramPolynomial
  ring

theorem tripleGram_nonnegative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : 0 ≤ tripleGram a b c :=
  (Matrix.posSemidef_gram ℝ ![a,b,c]).det_nonneg

theorem tripleGram_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) (r s t : ℝ) :
    tripleGram (r • a) (s • b) (t • c) = (r*s*t)^2*tripleGram a b c := by
  rw [tripleGram_polynomial,tripleGram_polynomial]
  simp only [inner_smul_left,inner_smul_right,conj_trivial]
  unfold gramPolynomial
  ring

theorem northLift_inner (x y : Space n) :
    inner ℝ (northLift x) (northLift y) = 1+inner ℝ x y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  simp only [northLift_zero,northLift_succ,RCLike.inner_apply,conj_trivial,map_one,one_mul]

theorem northLift_tripleGram_identity (p q r : Space n) :
    tripleGram (northLift p) (northLift q) (northLift r) =
      tripleGram p (q-p) (r-p) + ‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2 := by
  rw [tripleGram_polynomial,tripleGram_polynomial]
  simp only [northLift_inner,← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
    real_inner_comm]
  unfold gramPolynomial
  ring

theorem northLift_tripleGram_lower (p q r : Space n) :
    ‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2 ≤
      tripleGram (northLift p) (northLift q) (northLift r) := by
  rw [northLift_tripleGram_identity]
  linarith [tripleGram_nonnegative p (q-p) (r-p)]

theorem gnomonic_tripleGram (p q r : Space n) :
    tripleGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1))
      (gnomonicChart r : Space (n+1)) =
    (‖northLift p‖⁻¹*‖northLift q‖⁻¹*‖northLift r‖⁻¹)^2*
      tripleGram (northLift p) (northLift q) (northLift r) := by
  exact tripleGram_smul _ _ _ _ _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedTripleGram
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative triple transversality in the bounded unit-direction chart -/

namespace Falconer
variable {n : ℕ}

theorem northLift_norm_le_two {p : Space n} (hp : ‖p‖ ≤ 1) : ‖northLift p‖ ≤ 2 := by
  have he := northLift_norm_sq p
  nlinarith [norm_nonneg p,norm_nonneg (northLift p)]

theorem gnomonic_tripleGram_lower {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    (1/64:ℝ)*(‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2) ≤
      tripleGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1))
        (gnomonicChart r : Space (n+1)) := by
  have hinv (x : Space n) (hx : ‖x‖ ≤ 1) : (1/2:ℝ) ≤ ‖northLift x‖⁻¹ := by
    rw [← one_div (‖northLift x‖)]
    apply (div_le_div_iff₀ (by norm_num) (norm_pos_iff.mpr (northLift_ne_zero x))).mpr
    simpa only [one_mul] using northLift_norm_le_two hx
  have hp' := hinv p hp
  have hq' := hinv q hq
  have hr' := hinv r hr
  have hprod : (1/8:ℝ) ≤ ‖northLift p‖⁻¹*‖northLift q‖⁻¹*‖northLift r‖⁻¹ := by
    calc
      _ = (1/2:ℝ)*(1/2)*(1/2) := by norm_num
      _ ≤ _ := by gcongr
  have hsq : (1/64:ℝ) ≤ (‖northLift p‖⁻¹*‖northLift q‖⁻¹*‖northLift r‖⁻¹)^2 := by
    calc
      _ = (1/8:ℝ)^2 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hprod 2
  have hw : 0 ≤ ‖q-p‖^2*‖r-p‖^2-(inner ℝ (q-p) (r-p))^2 := by
    have hc := pow_le_pow_left₀ (abs_nonneg (inner ℝ (q-p) (r-p)))
      (abs_real_inner_le_norm (q-p) (r-p)) 2
    rw [sq_abs,mul_pow] at hc
    exact sub_nonneg.mpr hc
  rw [gnomonic_tripleGram]
  exact mul_le_mul hsq (northLift_tripleGram_lower p q r) hw (sq_nonneg _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicPairGram
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pair transversality retains the original affine separation -/

namespace Falconer
variable {n : ℕ}

theorem pairGram_nonneg {d : ℕ} (u v : Space d) : 0 ≤ pairGram u v := by
  have hh := pow_le_pow_left₀ (abs_nonneg (inner ℝ u v))
    (abs_real_inner_le_norm u v) 2
  rw [sq_abs,mul_pow] at hh
  exact sub_nonneg.mpr hh

theorem pairGram_smul {d : ℕ} (u v : Space d) (a b : ℝ) :
    pairGram (a • u) (b • v) = (a*b)^2*pairGram u v := by
  simp only [pairGram,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_left,real_inner_smul_right]
  ring

theorem northLift_pairGram (p q : Space n) :
    pairGram (northLift p) (northLift q) = ‖q-p‖^2+pairGram p q := by
  rw [pairGram,northLift_norm_sq,northLift_norm_sq,northLift_inner,
    norm_sub_sq_real]
  simp only [pairGram]
  rw [real_inner_comm q p]
  ring

theorem gnomonic_pairGram (p q : Space n) :
    pairGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)) =
      (‖northLift p‖⁻¹*‖northLift q‖⁻¹)^2*pairGram (northLift p) (northLift q) := by
  exact pairGram_smul _ _ _ _

theorem gnomonic_pairGram_lower {p q : Space n} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    (1/16:ℝ)*‖q-p‖^2 ≤
      pairGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)) := by
  have hinv (x : Space n) (hx : ‖x‖ ≤ 1) : (1/2:ℝ) ≤ ‖northLift x‖⁻¹ := by
    rw [← one_div (‖northLift x‖)]
    apply (div_le_div_iff₀ (by norm_num) (norm_pos_iff.mpr (northLift_ne_zero x))).mpr
    simpa only [one_mul] using northLift_norm_le_two hx
  have hprod : (1/4:ℝ) ≤ ‖northLift p‖⁻¹*‖northLift q‖⁻¹ := by
    calc
      _ = (1/2:ℝ)*(1/2) := by norm_num
      _ ≤ _ := mul_le_mul (hinv p hp) (hinv q hq) (by norm_num)
        (inv_nonneg.mpr (norm_nonneg _))
  have hsq : (1/16:ℝ) ≤ (‖northLift p‖⁻¹*‖northLift q‖⁻¹)^2 := by
    nlinarith
  rw [gnomonic_pairGram,northLift_pairGram]
  exact mul_le_mul hsq (le_add_of_nonneg_right (pairGram_nonneg p q))
    (sq_nonneg _) (sq_nonneg _)

theorem gnomonic_pair_separation {p q : Space n} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    ‖q-p‖ ≤ 4*‖perpendicularPart (gnomonicChart p : Space (n+1))
      (gnomonicChart q : Space (n+1))‖ := by
  have hh := gnomonic_pairGram_lower hp hq
  have he := norm_perpendicularPart_sq (sphere_norm (gnomonicChart p))
    (gnomonicChart q : Space (n+1))
  simp only [pairGram,sphere_norm,one_pow,one_mul] at hh
  rw [sphere_norm] at he
  nlinarith [norm_nonneg (q-p),norm_nonneg
    (perpendicularPart (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)))]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicTripleAngle
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The affine displacement angle controls the spherical triple determinant -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem displacementAngle_nonneg (p q r : Space n) : 0 ≤ displacementAngle p q r :=
  norm_nonneg _

theorem displacement_pairGram (p q r : Space n) (hq : q ≠ p) (hr : r ≠ p) :
    pairGram (q-p) (r-p) = (‖q-p‖*‖r-p‖*displacementAngle p q r)^2 := by
  have hq0 : q-p ≠ 0 := sub_ne_zero.mpr hq
  have hr0 : r-p ≠ 0 := sub_ne_zero.mpr hr
  have hnq := norm_normalize hq0
  have hnr := norm_normalize hr0
  have hh := norm_perpendicularPart_sq hnq (normalize (r-p))
  rw [hnr] at hh
  have hg : pairGram (normalize (q-p)) (normalize (r-p)) =
      (displacementAngle p q r)^2 := by
    simp only [pairGram,hnq,hnr,one_pow,one_mul]
    simpa only [one_pow,displacementAngle] using hh.symm
  rw [NormedSpace.normalize,NormedSpace.normalize,pairGram_smul] at hg
  have hqn : ‖q-p‖ ≠ 0 := norm_ne_zero_iff.mpr hq0
  have hrn : ‖r-p‖ ≠ 0 := norm_ne_zero_iff.mpr hr0
  field_simp at hg
  nlinarith [sq_nonneg (displacementAngle p q r)]

theorem gnomonic_triple_sqrt_lower {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (hpq : q ≠ p) (hpr : r ≠ p) :
    ‖q-p‖*‖r-p‖*displacementAngle p q r/8 ≤
      Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
        (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))) := by
  have hh := gnomonic_tripleGram_lower hp hq hr
  change (1/64:ℝ)*pairGram (q-p) (r-p) ≤ _ at hh
  rw [displacement_pairGram p q r hpq hpr] at hh
  have hs := Real.sq_sqrt (tripleGram_nonnegative
    (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1))
    (gnomonicChart r : Space (n+1)))
  nlinarith [Real.sqrt_nonneg (tripleGram (gnomonicChart p : Space (n+1))
    (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))),
    mul_nonneg (mul_nonneg (norm_nonneg (q-p)) (norm_nonneg (r-p)))
      (displacementAngle_nonneg p q r)]

theorem displacementAngle_lt_of_tripleGram {p q r : Space n}
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    {b W : ℝ} (hb : 0 < b) (hpq : b ≤ ‖q-p‖) (hpr : b ≤ ‖r-p‖)
    (hsmall : Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
      (gnomonicChart q : Space (n+1)) (gnomonicChart r : Space (n+1))) < W) :
    displacementAngle p q r < 8*W/b^2 := by
  have hqne : q ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpq
    linarith
  have hrne : r ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpr
    linarith
  have hh := (gnomonic_triple_sqrt_lower hp hq hr hqne hrne).trans_lt hsmall
  have hm : b^2*displacementAngle p q r ≤ ‖q-p‖*‖r-p‖*displacementAngle p q r := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hpq hpr hb.le (norm_nonneg _))
      (displacementAngle_nonneg p q r)
  apply (lt_div_iff₀ (sq_pos_of_pos hb)).mpr
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMultiband
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian multi-vector bands with their exact coordinate determinant -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d j : ℕ}

theorem bandCoordinateMap_det_ne_zero (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (hspan : Submodule.span ℝ (range w) = V) (b : V ≃ₗᵢ[ℝ] Space j) :
    LinearMap.det (bandCoordinateMap w V b : Space j →ₗ[ℝ] Space j) ≠ 0 := by
  rw [ne_eq,LinearMap.det_eq_zero_iff_ker_ne_bot,not_not]
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hi (i : Fin j) : inner ℝ (w i) (b.symm x : Space d) = 0 := by
    have hh := congrArg (fun z : Space j => z i) hx
    simpa using hh
  have hall (u : Space d) (hu : u ∈ Submodule.span ℝ (range w)) :
      inner ℝ u (b.symm x : Space d) = 0 := by
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨i,rfl⟩ := hu; exact hi i
    | zero => simp
    | add u v hu hv ihu ihv => simp [inner_add_left,ihu,ihv]
    | smul a u hu ihu => simp [inner_smul_left,ihu]
  have hy : (b.symm x : Space d) = 0 := inner_self_eq_zero.mp
    (hall _ (by rw [hspan]; exact (b.symm x).property))
  have hz : b.symm x = 0 := Subtype.ext hy
  exact b.symm.injective (by simpa using hz)

theorem gaussian_projected_coordinates (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space j) :
    (stdGaussian (Space d)).map (fun x => b (V.orthogonalProjectionOnto x)) =
      stdGaussian (Space j) := by
  change (stdGaussian (Space d)).map (b ∘ V.orthogonalProjectionOnto) = _
  rw [← Measure.map_map b.continuous.measurable V.orthogonalProjectionOnto.continuous.measurable,
    gaussian_orthogonal_projection,stdGaussian_map]

theorem gaussian_multi_vector_band (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (hw : ∀ i, w i ∈ V) (b : V ≃ₗᵢ[ℝ] Space j)
    (hdet : LinearMap.det (bandCoordinateMap w V b : Space j →ₗ[ℝ] Space j) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space d) {x | ∀ i, |inner ℝ (w i) x| ≤ r} ≤
      ENNReal.ofReal (gaussianVolumeNormalization j*
        |(LinearMap.det (bandCoordinateMap w V b : Space j →ₗ[ℝ] Space j))⁻¹| * (2*r)^j) := by
  let F : Space d → Space j := fun x => b (V.orthogonalProjectionOnto x)
  have he : {x : Space d | ∀ i, |inner ℝ (w i) x| ≤ r} =
      F ⁻¹' {y : Space j | ∀ i, |bandCoordinateMap w V b y i| ≤ r} := by
    ext x
    simp only [mem_preimage,mem_ofPred_eq,F,bandCoordinateMap_apply,b.symm_apply_apply]
    have hi (i : Fin j) : inner ℝ (w i) (V.orthogonalProjectionOnto x : Space d) =
        inner ℝ (w i) x :=
      V.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨w i,hw i⟩ x
    simp only [hi]
  rw [he,← Measure.map_apply (by dsimp [F]; fun_prop) (by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const),gaussian_projected_coordinates]
  exact gaussian_linear_bands _ hdet hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianGram
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate-free determinant in the Gaussian multi-band bound -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d j : ℕ}

theorem bandCoordinateMap_adjoint_basis (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (hw : ∀ i, w i ∈ V) (b : V ≃ₗᵢ[ℝ] Space j) (i : Fin j) :
    (bandCoordinateMap w V b).adjoint (EuclideanSpace.basisFun (Fin j) ℝ i) = b ⟨w i,hw i⟩ := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left,EuclideanSpace.basisFun_inner,
    bandCoordinateMap_apply]
  have hi := b.inner_map_map ⟨w i,hw i⟩ (b.symm x)
  simpa only [b.apply_symm_apply,Submodule.coe_inner] using hi.symm

theorem bandCoordinateMap_det_sq (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (hw : ∀ i, w i ∈ V) (b : V ≃ₗᵢ[ℝ] Space j) :
    (LinearMap.det (bandCoordinateMap w V b : Space j →ₗ[ℝ] Space j))^2 =
      (Matrix.gram ℝ w).det := by
  let L := bandCoordinateMap w V b
  have hh := L.adjoint.toLinearMap.normDet_sq_eq_det_gram (EuclideanSpace.basisFun (Fin j) ℝ)
  change (L.adjoint.toLinearMap.normDet : ℝ)^2 =
    (Matrix.gram ℝ (fun i => L.adjoint (EuclideanSpace.basisFun (Fin j) ℝ i))).det at hh
  have he : Matrix.gram ℝ (fun i => L.adjoint (EuclideanSpace.basisFun (Fin j) ℝ i)) =
      Matrix.gram ℝ w := by
    ext i k
    simp only [Matrix.gram_apply,L,bandCoordinateMap_adjoint_basis w V hw b,
      b.inner_map_map]
    rfl
  rw [he,LinearMap.normDet_eq_norm_det] at hh
  have hd : LinearMap.det L.adjoint.toLinearMap = LinearMap.det L.toLinearMap := by
    rw [← ContinuousLinearMap.adjoint_toLinearMap,
      ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin j) ℝ).toBasis,
      LinearMap.toMatrix_adjoint,Matrix.det_conjTranspose]
    simp only [star_trivial,LinearMap.det_toMatrix]
  rw [hd] at hh
  simpa only [Real.norm_eq_abs,sq_abs] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianTripleBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian bands for a nonsingular triple of actual direction vectors -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_three_vector_band (v : Fin 3 → Space d)
    (hv : 0 < (Matrix.gram ℝ v).det) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space d) {x | ∀ j, |inner ℝ (v j) x| ≤ r} ≤
      ENNReal.ofReal (gaussianVolumeNormalization 3*(Real.sqrt (Matrix.gram ℝ v).det)⁻¹*(2*r)^3) := by
  let V := Submodule.span ℝ (range v)
  have hlin : LinearIndependent ℝ v := Matrix.linearIndependent_of_det_gram_ne_zero (ne_of_gt hv)
  have hdim : Module.finrank ℝ V = 3 := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hlin
  let e := sliceCoordinates V hdim
  have hw (j : Fin 3) : v j ∈ V := Submodule.subset_span (mem_range_self j)
  have hd := bandCoordinateMap_det_ne_zero v V rfl e
  have hs : Real.sqrt (Matrix.gram ℝ v).det =
      |LinearMap.det (bandCoordinateMap v V e : Space 3 →ₗ[ℝ] Space 3)| := by
    rw [← bandCoordinateMap_det_sq v V hw e,Real.sqrt_sq_eq_abs]
  have hh := gaussian_multi_vector_band v V hw e hd hr
  simpa only [abs_inv,hs] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianTripleNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation of the three direction-slice normalization factors -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_cubed_band_normalization {r C : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^3*ENNReal.ofReal ((C*r^3)^h) =
      ENNReal.ofReal (C^h) := by
  rw [← ENNReal.ofReal_pow (by positivity),← ENNReal.ofReal_mul (by positivity),
    Real.rpow_neg hr.le,Real.rpow_natCast,mul_pow]
  congr 1
  have he : (r^3)^h = (r^h)^3 := by
    simp only [← pow_mul]
    congr 1
    omega
  rw [he]
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianTruncatedTriple
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A three-band bound that includes singular triples -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianTripleBandConstant_pos : 0 < gaussianTripleBandConstant := by
  have hv : 0 < gaussianVolumeNormalization 3 := by
    unfold gaussianVolumeNormalization
    positivity
  unfold gaussianTripleBandConstant
  positivity

theorem gaussian_three_vector_truncated (v : Fin 3 → Space d)
    (hu : ‖v 0‖ = 1) (hv : ‖v 1‖ = 1)
    {r a α : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hsep : a ≤ ‖perpendicularPart (v 0) (v 1)‖)
    (hgram : a^2*α ≤ Real.sqrt (Matrix.gram ℝ v).det) :
    stdGaussian (Space d) {x | ∀ j, |inner ℝ (v j) x| ≤ r} ≤
      ENNReal.ofReal (gaussianTripleBandConstant*r^3/(a^2*max α r)) := by
  have hC0 := gaussianTripleBandConstant_pos
  have hC₂ : 2*gaussianBandConstant^2 ≤ gaussianTripleBandConstant := by
    have hp : 0 ≤ gaussianVolumeNormalization 3 := by
      unfold gaussianVolumeNormalization
      positivity
    unfold gaussianTripleBandConstant
    linarith
  have hC₃ : 8*gaussianVolumeNormalization 3 ≤ gaussianTripleBandConstant := by
    unfold gaussianTripleBandConstant
    nlinarith [sq_nonneg gaussianBandConstant]
  by_cases hα : α ≤ r
  · rw [max_eq_right hα]
    have hne : perpendicularPart (v 0) (v 1) ≠ 0 :=
      norm_pos_iff.mp (ha.trans_le hsep)
    have hsub : {x : Space d | ∀ j, |inner ℝ (v j) x| ≤ r} ⊆
        {x : Space d | |inner ℝ (v 0) x| ≤ r ∧ |inner ℝ (v 1) x| ≤ r} := by
      intro x hx
      exact ⟨hx 0,hx 1⟩
    apply ((measure_mono hsub).trans (gaussian_two_band_nondegenerate hu hv hr.le hne)).trans
    apply ENNReal.ofReal_le_ofReal
    have hden : a^2 ≤ ‖perpendicularPart (v 0) (v 1)‖ := by
      have : a^2 ≤ a := by nlinarith
      exact this.trans hsep
    calc
      _ ≤ gaussianTripleBandConstant*r^2/‖perpendicularPart (v 0) (v 1)‖ := by
        gcongr
      _ ≤ gaussianTripleBandConstant*r^2/a^2 := by gcongr
      _ = _ := by field_simp
  · have hαr : r < α := lt_of_not_ge hα
    have hα0 : 0 < α := hr.trans hαr
    have hg : 0 < (Matrix.gram ℝ v).det := by
      have : 0 < Real.sqrt (Matrix.gram ℝ v).det :=
        (mul_pos (sq_pos_of_pos ha) hα0).trans_le hgram
      exact Real.sqrt_pos.mp this
    rw [max_eq_left hαr.le]
    apply (gaussian_three_vector_band v hg hr.le).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = 8*gaussianVolumeNormalization 3*r^3/Real.sqrt (Matrix.gram ℝ v).det := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ gaussianTripleBandConstant*r^3/(a^2*α) := by
        gcongr

theorem gaussianRows_three_vector_truncated (v : Fin 3 → Space d)
    (hu : ‖v 0‖ = 1) (hv : ‖v 1‖ = 1)
    {r a α : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hsep : a ≤ ‖perpendicularPart (v 0) (v 1)‖)
    (hgram : a^2*α ≤ Real.sqrt (Matrix.gram ℝ v).det) :
    gaussianRows d h {A | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianTripleBandConstant*r^3/(a^2*max α r))^h) := by
  have hC0 := gaussianTripleBandConstant_pos
  have he : {A : Fin h → Space d | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | ∀ j, |inner ℝ (v j) x| ≤ r}) := by
    ext A
    simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal
        (gaussianTripleBandConstant*r^3/(a^2*max α r)) :=
      Finset.prod_le_prod' (fun _ _ => gaussian_three_vector_truncated v hu hv hr ha ha1 hsep hgram)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow]
      positivity

theorem gaussianRows_three_vector_truncated_normalized (v : Fin 3 → Space d)
    (hu : ‖v 0‖ = 1) (hv : ‖v 1‖ = 1)
    {r a α : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hsep : a ≤ ‖perpendicularPart (v 0) (v 1)‖)
    (hgram : a^2*α ≤ Real.sqrt (Matrix.gram ℝ v).det) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^3 *
      gaussianRows d h {A | ∀ i, ∀ j, |inner ℝ (v j) (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianTripleBandConstant/(a^2*max α r))^h) := by
  apply (mul_le_mul' le_rfl (gaussianRows_three_vector_truncated v hu hv hr ha ha1 hsep hgram)).trans_eq
  have he : gaussianTripleBandConstant*r^3/(a^2*max α r) =
      (gaussianTripleBandConstant/(a^2*max α r))*r^3 := by ring
  rw [he,gaussian_cubed_band_normalization hr]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicTripleKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The truncated Gaussian kernel of three original chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gnomonic_triple_kernel (p q s : Space n)
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hs : ‖s‖ ≤ 1)
    {b r : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hr : 0 < r)
    (hpq : b ≤ ‖q-p‖) (hps : b ≤ ‖s-p‖) :
    (ENNReal.ofReal (r^(-(h:ℝ))))^3 *
      gaussianRows (n+1) h {A | ∀ i,
        |inner ℝ (gnomonicChart p : Space (n+1)) (A i)| ≤ r ∧
        |inner ℝ (gnomonicChart q : Space (n+1)) (A i)| ≤ r ∧
        |inner ℝ (gnomonicChart s : Space (n+1)) (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianTripleBandConstant/
        ((b/4)^2*max (displacementAngle p q s) r))^h) := by
  let v : Fin 3 → Space (n+1) :=
    ![(gnomonicChart p : Space (n+1)),(gnomonicChart q : Space (n+1)),
      (gnomonicChart s : Space (n+1))]
  have hsep : b/4 ≤ ‖perpendicularPart (v 0) (v 1)‖ := by
    have hh := gnomonic_pair_separation hp hq
    dsimp [v]
    linarith
  have hqne : q ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpq
    linarith
  have hsne : s ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hps
    linarith
  have hgram : (b/4)^2*displacementAngle p q s ≤ Real.sqrt (Matrix.gram ℝ v).det := by
    have hh := gnomonic_triple_sqrt_lower hp hq hs hqne hsne
    have hmul : b^2*displacementAngle p q s ≤
        ‖q-p‖*‖s-p‖*displacementAngle p q s := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hpq hps hb.le (norm_nonneg _)) (displacementAngle_nonneg p q s)
    change _ ≤ Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
      (gnomonicChart q : Space (n+1)) (gnomonicChart s : Space (n+1)))
    nlinarith [displacementAngle_nonneg p q s]
  have hh := gaussianRows_three_vector_truncated_normalized (h := h) v
    (sphere_norm (gnomonicChart p)) (sphere_norm (gnomonicChart q))
    hr (by positivity : 0 < b/4) (by linarith : b/4 ≤ 1) hsep hgram
  simpa only [v,Fin.forall_fin_succ,Fin.forall_fin_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.tail_cons,and_true] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SmallGnomonicCap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small chart law lies in the unit cube used by radial pruning -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

lemma gnomonic_cap_coordinates_norm_le (w : Sphere (n+1)) {ρ : ℝ}
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ ρ) (hρ : ρ ≤ 1/2) :
    ‖gnomonicCoordinates w‖ ≤ 2*ρ := by
  have hw0 := gnomonic_cap_first_coordinate w (hw.trans hρ)
  have hp : 0 < (w:Space (n+1)) 0 := by linarith
  let v : Space (n+1) := (w:Space (n+1))-northLift 0
  let t : Space n := WithLp.toLp 2 (fun i => v i.succ)
  have ht : ‖t‖ ≤ ‖v‖ := by
    have hs : ‖t‖^2 ≤ ‖v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
      simp only [t]
      exact le_add_of_nonneg_left (sq_nonneg (v 0))
    nlinarith [norm_nonneg t,norm_nonneg v]
  have hv : ‖v‖ ≤ ρ := by
    simpa only [v,Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
  have he : gnomonicCoordinates w = ((w:Space (n+1)) 0)⁻¹ • t := by
    ext i
    simp only [gnomonicCoordinates_apply,PiLp.smul_apply,smul_eq_mul,t,
      v,PiLp.sub_apply,northLift_succ,PiLp.zero_apply,sub_zero,div_eq_mul_inv]
    ring
  have hi : ((w:Space (n+1)) 0)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    linarith
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact (mul_le_mul_of_nonneg_left (ht.trans hv) (inv_nonneg.mpr hp.le)).trans
    (mul_le_mul_of_nonneg_right hi (by linarith [norm_nonneg v]))

lemma small_gnomonic_cap_law (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space n)) ≤ 1/8) :
    ∀ᵐ p ∂Measure.map gnomonicCoordinates ν, ‖p‖ ≤ 1/4 := by
  rw [ae_map_iff gnomonicCoordinates_measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  filter_upwards [hν] with w hw
  have hh := gnomonic_cap_coordinates_norm_le w hw (by norm_num : (1/8:ℝ) ≤ 1/2)
  norm_num at hh ⊢
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_WeakRadialDeletionBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning the two actual local incidence losses into a pair deletion bound -/

namespace Falconer
open scoped ENNReal

theorem weak_radial_two_costs {A B u v c : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hu : c < u) (hv : c < v) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A*((2:ℝ)^N)^(-u)+B*((2:ℝ)^N)^(-v) ≤ ((2:ℝ)^N)^(-c) := by
  let m := min (u-c) (v-c)
  have hm : 0 < m := lt_min (sub_pos.mpr hu) (sub_pos.mpr hv)
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hm (A+B)
  refine ⟨N₀,fun N hN => ?_⟩
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hu' : -u ≤ -c-m := by have := min_le_left (u-c) (v-c); dsimp [m]; linarith
  have hv' : -v ≤ -c-m := by have := min_le_right (u-c) (v-c); dsimp [m]; linarith
  calc
    _ ≤ A*R^(-c-m)+B*R^(-c-m) := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hu') hA)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hv') hB)
    _ = (A+B)*R^(-c-m) := by ring
    _ ≤ R^m*R^(-c-m) := mul_le_mul_of_nonneg_right (hN₀ N hN) (Real.rpow_nonneg hRp.le _)
    _ = R^(-c) := by rw [← Real.rpow_add hRp]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialScaleWindow
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative estimates on the retained interval of dyadic scales -/

namespace Falconer
open scoped BigOperators ENNReal

lemma radial_scale_window_half {K N : ℕ} (hK : 0 < K) (hN : 2*K ≤ N) :
    N ≤ 2*K*(N/K) := by
  have hq : 2 ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by omega)
  have hr := Nat.mod_lt N hK
  have he := Nat.div_add_mod N K
  nlinarith

lemma radial_scale_window_loss {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^N)^(a/(2*(K:ℝ))) ≤ ((2:ℝ)^j)^a := by
  have he : (N:ℝ) ≤ 2*(K:ℝ)*(j:ℝ) := by
    exact_mod_cast (radial_scale_window_half hK hN).trans (Nat.mul_le_mul_left (2*K) hj)
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ) < 2*K)).mp
  have hh := mul_le_mul_of_nonneg_right he ha
  calc
    (2*K)*((N:ℝ)*(a/(2*(K:ℝ)))) = (N:ℝ)*a := by field_simp
    _ ≤ (2*(K:ℝ)*(j:ℝ))*a := hh
    _ = (2*K)*((j:ℝ)*a) := by ring

lemma radial_scale_window_decay {K N j : ℕ} (hK : 0 < K) (hN : 2*K ≤ N)
    (hj : N/K ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    ((2:ℝ)^j)^(-a) ≤ ((2:ℝ)^N)^(-(a/(2*(K:ℝ)))) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact inv_anti₀ (by positivity) (radial_scale_window_loss hK hN hj ha)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_EndpointRadialLosses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible losses for the endpoint bad-triple estimate -/

namespace Falconer

 theorem exists_endpoint_radial_losses (h : ℕ) {ell a : ℝ}
    (hell : (h:ℝ) < ell) (ha : 0 < a) :
    ∃ H : ℕ, 0 < H ∧ ∃ b e : ℝ, 0 < b ∧ 0 < e ∧
      1/(H:ℝ) < a-2*b ∧ 0 < (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e := by
  obtain ⟨H₀,hH₀⟩ := exists_nat_gt (4/a)
  let H := H₀+1
  have hH : 0 < H := by dsimp [H]; omega
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hHa : 4/a < (H:ℝ) := by dsimp [H]; push_cast; linarith
  have hinv : 1/(H:ℝ) < a/4 := by
    apply (div_lt_iff₀ hHr).mpr
    have hh := (div_lt_iff₀ ha).mp hHa
    nlinarith
  let b := min (a/8) ((ell-h)/(32*((h:ℝ)+1)*(H:ℝ)))
  let e := (ell-h)/(16*(H:ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hb₁ : b ≤ a/8 := min_le_left _ _
  have hb₂ : b ≤ (ell-h)/(32*((h:ℝ)+1)*(H:ℝ)) := min_le_right _ _
  have hprod : 2*(h:ℝ)*b ≤ (ell-h)/(16*(H:ℝ)) := by
    have hh : (h:ℝ) ≤ (h:ℝ)+1 := by linarith
    have ht := mul_le_mul_of_nonneg_left hb₂ (show 0 ≤ 2*((h:ℝ)+1) by positivity)
    have heq : 2*((h:ℝ)+1)*((ell-h)/(32*((h:ℝ)+1)*(H:ℝ))) =
        (ell-h)/(16*(H:ℝ)) := by field_simp; ring
    rw [heq] at ht
    exact (mul_le_mul_of_nonneg_right (by linarith : 2*(h:ℝ) ≤ 2*((h:ℝ)+1)) hb.le).trans ht
  refine ⟨H,hH,b,e,hb,he,by linarith,?_⟩
  have heq : (ell-h)/(2*(H:ℝ)) = 8*e := by dsimp [e]; ring
  rw [heq]
  change 0 < 8*e-2*(h:ℝ)*b-e
  change 2*(h:ℝ)*b ≤ e at hprod
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialAngleCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two radial caps control near-collinear affine triples -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem displacementAngle_measurable (p q : Space n) :
    Measurable (displacementAngle p q) := by
  unfold displacementAngle perpendicularPart NormedSpace.normalize
  fun_prop

theorem displacementAngle_two_caps (p q z : Space n) (hq : q ≠ p) (hz : z ≠ p)
    {r : ℝ} (hr : 0 < r) (ha : displacementAngle p q z ≤ r) :
    dist (normalize (z-p)) (normalize (q-p)) < 3*r ∨
      dist (normalize (z-p)) (-normalize (q-p)) < 3*r := by
  let u := normalize (q-p)
  let v := normalize (z-p)
  have hu : ‖u‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hv : ‖v‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; norm_num)
  rcases perpendicular_direction_two_caps hu hv0 ha with hl | hr'
  · left
    have hh : ‖u-v‖ ≤ 2*r := by
      simpa only [hv,inv_one,one_smul,div_one] using hl
    change ‖v-u‖ < 3*r
    rw [norm_sub_rev]
    linarith
  · right
    have hh : ‖u+v‖ ≤ 2*r := by
      simpa only [hv,inv_one,neg_smul,one_smul,div_one,sub_neg_eq_add] using hr'
    change ‖v-(-u)‖ < 3*r
    rw [sub_neg_eq_add,add_comm]
    linarith

theorem radial_angle_sublevel (μ : Measure (Space n)) (G : Set (Space n × Space n))
    (p q : Space n) (hq : q ≠ p) (hdiag : ∀ z, (p,z) ∈ G → z ≠ p)
    {r K ℓ : ℝ} (hr : 0 < r)
    (hcap : ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*r} ≤
        ENNReal.ofReal (K*(3*r)^ℓ)) :
    μ {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ r} ≤
      2*ENNReal.ofReal (K*(3*r)^ℓ) := by
  let u := normalize (q-p)
  have hu : ‖u‖ = 1 := norm_normalize (sub_ne_zero.mpr hq)
  have hsub : {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ r} ⊆
      {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*r} ∪
      {z | (p,z) ∈ G ∧ dist (normalize (z-p)) (-u) < 3*r} := by
    rintro z ⟨hz,ha⟩
    rcases displacementAngle_two_caps p q z hq (hdiag z hz) hr ha with h | h
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨hz,h⟩
  have hh := (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (hcap u hu) (hcap (-u) (by simpa only [norm_neg] using hu))))
  exact hh.trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic inverse potentials of a nonnegative measurable geometric statistic -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem regularized_scalar_potential (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  have hpre (j : ℕ) : a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^j) = {x | a x < 1/(2:ℝ)^j} := by
    ext x
    simp only [mem_preimage,mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (ha0 x),mem_ofPred_eq]
  have hball (j : ℕ) (hj : j ≤ g+k) :
      (Measure.map a μ) (ball (0:ℝ) (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (K*(1/(2:ℝ)^j)^q) := by
    rw [Measure.map_apply ha measurableSet_ball,hpre]
    exact hsmall j hj
  have hh := regularized_potential_frostman (Measure.map a μ) (0:ℝ) hK hs hsq g k hball
  have hf : Measurable (fun z : ℝ =>
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^s)) := by fun_prop
  have he : (∫⁻ z in ball (0:ℝ) (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^s) ∂Measure.map a μ) =
      ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball,lintegral_map
      (hf.indicator measurableSet_ball) ha,
      ← lintegral_indicator (measurableSet_lt ha measurable_const)]
    apply lintegral_congr
    intro x
    by_cases hx : a x < 1/(2:ℝ)^g
    · have hz : a x ∈ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∈ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_mem hz,indicator_of_mem (show x ∈ {x | a x < 1/(2:ℝ)^g} from hx)]
      simp only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (ha0 x)]
    · have hz : a x ∉ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∉ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_notMem hz,indicator_of_notMem (show x ∉ {x | a x < 1/(2:ℝ)^g} from hx)]
  rw [he] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TruncatedScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The maximum-truncated kernel and its dyadic sublevel bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem inverse_max_le_two_inverse_add {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) :
    1/max x r ≤ 2/(x+r) := by
  apply (div_le_div_iff₀ (hr.trans_le (le_max_right x r)) (by positivity)).mpr
  have h₁ := le_max_left x r
  have h₂ := le_max_right x r
  linarith

theorem truncated_scalar_potential (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (a x) (1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal ((2:ℝ)^s*(K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q))))) := by
  have hp (x : X) : (1/max (a x) (1/(2:ℝ)^(g+k)))^s ≤
      (2:ℝ)^s*(1/(a x+1/(2:ℝ)^(g+k)))^s := by
    have hax := ha0 x
    calc
      _ ≤ (2/(a x+1/(2:ℝ)^(g+k)))^s := Real.rpow_le_rpow (by positivity)
        (inverse_max_le_two_inverse_add (ha0 x) (by positivity)) hs
      _ = _ := by
        rw [show 2/(a x+1/(2:ℝ)^(g+k)) = 2*(1/(a x+1/(2:ℝ)^(g+k))) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((2:ℝ)^s)*ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal ((2:ℝ)^s)*(∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2:ℝ)^s)*ENNReal.ofReal
        (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) :=
      mul_le_mul' le_rfl (regularized_scalar_potential μ a ha ha0 hK hs hsq g k hsmall)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialAnglePotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Radial caps bound the singular part of the endpoint triple kernel -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem radial_angle_potential (μ : Measure (Space n)) (G : Set (Space n × Space n))
    (p q : Space n) (hq : q ≠ p) (hdiag : ∀ z, (p,z) ∈ G → z ≠ p)
    {K s ℓ : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsℓ : s < ℓ) (g k : ℕ)
    (hcap : ∀ j : ℕ, j ≤ g+k → ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (NormedSpace.normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
        ENNReal.ofReal (K*(3*(1/(2:ℝ)^j))^ℓ)) :
    (∫⁻ z in {z | displacementAngle p q z < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (displacementAngle p q z) (1/(2:ℝ)^(g+k)))^s)
        ∂μ.restrict {z | (p,z) ∈ G}) ≤
      ENNReal.ofReal ((2:ℝ)^s*((2*K*(3:ℝ)^ℓ)*(((2:ℝ)^g)^(s-ℓ))*
        (1+(2:ℝ)^s/(1-(2:ℝ)^(s-ℓ))))) := by
  have hsmall (j : ℕ) (hj : j ≤ g+k) :
      (μ.restrict {z | (p,z) ∈ G}) {z | displacementAngle p q z < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((2*K*(3:ℝ)^ℓ)*(1/(2:ℝ)^j)^ℓ) := by
    rw [Measure.restrict_apply (measurableSet_lt (displacementAngle_measurable p q) measurable_const)]
    calc
      _ ≤ μ {z | (p,z) ∈ G ∧ displacementAngle p q z ≤ 1/(2:ℝ)^j} := by
        apply measure_mono
        rintro z ⟨hz,hG⟩
        exact ⟨hG,hz.le⟩
      _ ≤ 2*ENNReal.ofReal (K*(3*(1/(2:ℝ)^j))^ℓ) :=
        radial_angle_sublevel μ G p q hq hdiag (by positivity) (hcap j hj)
      _ = _ := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num),Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        ring
  exact truncated_scalar_potential (μ.restrict {z | (p,z) ∈ G})
    (displacementAngle p q) (displacementAngle_measurable p q)
    (displacementAngle_nonneg p q) (by positivity) hs hsℓ g k hsmall

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_AnchoredTriplePotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Gaussian bad-triple weight is integrable on every retained anchor -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem anchored_bad_triple_potential (μ : Measure (Space n))
    (G : Set (Space n × Space n)) (E : Set (Space n)) (hE : MeasurableSet E)
    (p q : Space n) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    {b W K ℓ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hpq : b ≤ ‖q-p‖)
    (hK : 0 ≤ K) (hℓ : (h:ℝ) < ℓ) (g k : ℕ)
    (hW : 8*W/b^2 ≤ 1/(2:ℝ)^g)
    (hretained : ∀ z ∈ E, (p,z) ∈ G ∧ ‖z‖ ≤ 1 ∧ b ≤ ‖z-p‖ ∧
      Real.sqrt (tripleGram (gnomonicChart p : Space (n+1))
        (gnomonicChart q : Space (n+1)) (gnomonicChart z : Space (n+1))) < W)
    (hdiag : ∀ z, (p,z) ∈ G → z ≠ p)
    (hcap : ∀ j : ℕ, j ≤ g+k → ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (NormedSpace.normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
        ENNReal.ofReal (K*(3*(1/(2:ℝ)^j))^ℓ)) :
    (∫⁻ z in E, gaussianChartTripleWeight h (1/(2:ℝ)^(g+k)) p q z ∂μ) ≤
      ENNReal.ofReal ((gaussianTripleBandConstant/(b/4)^2)^h) *
      ENNReal.ofReal ((2:ℝ)^(h:ℝ)*((2*K*(3:ℝ)^ℓ)*(((2:ℝ)^g)^((h:ℝ)-ℓ))*
        (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ℓ))))) := by
  let r : ℝ := 1/(2:ℝ)^(g+k)
  let F : Space n → ℝ≥0∞ := fun z => ENNReal.ofReal ((1/max (displacementAngle p q z) r)^(h:ℝ))
  let C : ℝ≥0∞ := ENNReal.ofReal ((gaussianTripleBandConstant/(b/4)^2)^h)
  have hr : 0 < r := by dsimp [r]; positivity
  have hqne : q ≠ p := by
    intro he
    rw [he,sub_self,norm_zero] at hpq
    linarith
  have hbound (z : Space n) (hz : z ∈ E) : gaussianChartTripleWeight h r p q z ≤ C*F z := by
    obtain ⟨_,hz1,hpz,_⟩ := hretained z hz
    apply (gnomonic_triple_kernel p q z hp hq hz1 hb hb1 hr hpq hpz).trans_eq
    dsimp [C,F]
    have hCpos : 0 ≤ (gaussianTripleBandConstant/(b/4)^2)^h :=
      pow_nonneg (div_nonneg gaussianTripleBandConstant_pos.le (sq_nonneg _)) h
    rw [← ENNReal.ofReal_mul hCpos,Real.rpow_natCast]
    congr 1
    rw [← mul_pow]
    congr 1
    ring
  have hsub : E ⊆ {z | displacementAngle p q z < 1/(2:ℝ)^g} ∩ {z | (p,z) ∈ G} := by
    intro z hz
    obtain ⟨hG,hz1,hpz,hw⟩ := hretained z hz
    exact ⟨(displacementAngle_lt_of_tripleGram hp hq hz1 hb hpq hpz hw).trans_le hW,hG⟩
  have hm : μ.restrict E ≤ (μ.restrict {z | (p,z) ∈ G}).restrict
      {z | displacementAngle p q z < 1/(2:ℝ)^g} := by
    rw [Measure.restrict_restrict (measurableSet_lt (displacementAngle_measurable p q) measurable_const)]
    exact Measure.restrict_mono hsub le_rfl
  calc
    _ ≤ ∫⁻ z in E, C*F z ∂μ := lintegral_mono_ae (by
      filter_upwards [ae_restrict_mem hE] with z hz
      exact hbound z hz)
    _ = C * ∫⁻ z in E, F z ∂μ := lintegral_const_mul' C _ ENNReal.ofReal_ne_top
    _ ≤ C * ∫⁻ z in {z | displacementAngle p q z < 1/(2:ℝ)^g}, F z
        ∂μ.restrict {z | (p,z) ∈ G} := mul_le_mul' le_rfl (lintegral_mono' hm le_rfl)
    _ ≤ _ := mul_le_mul' le_rfl
      (radial_angle_potential μ G p q hqne hdiag hK (Nat.cast_nonneg _) hℓ g k hcap)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianChartTripleAverage
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Gaussian averaging on triples of the original affine chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem chartTripleBand_measurable (A : Fin h → Space (n+1)) (r : ℝ) :
    MeasurableSet (chartTripleBand A r) := by
  have hm := (gaussianDirectionBand_measurable A r).preimage (gnomonicChart_continuous n).measurable
  exact hm.prod (hm.prod hm)

theorem gaussian_chart_triple_identity (μ : Measure (Space n)) [SFinite μ]
    (A : Fin h → Space (n+1)) (r : ℝ) (E : Set (Space n × Space n × Space n))
    (hE : MeasurableSet E) :
    ((gaussianChartSliceMeasure μ A r).prod
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r))) E =
      (ENNReal.ofReal (r^(-(h:ℝ))))^3*(μ.prod (μ.prod μ)) (E ∩ chartTripleBand A r) := by
  simp only [gaussianChartSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hE,
    chartTripleBand,pow_succ,pow_zero,one_mul,mul_assoc]

theorem gaussian_chart_triple_average (μ : Measure (Space n)) [SFinite μ]
    (r : ℝ) (E : Set (Space n × Space n × Space n)) (hE : MeasurableSet E) :
    (∫⁻ A : Fin h → Space (n+1), ((gaussianChartSliceMeasure μ A r).prod
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r))) E
        ∂gaussianRows (n+1) h) =
      ∫⁻ w in E, gaussianChartTripleWeight h r w.1 w.2.1 w.2.2 ∂μ.prod (μ.prod μ) := by
  simp_rw [gaussian_chart_triple_identity μ _ r E hE]
  have hc : (ENNReal.ofReal (r^(-(h:ℝ))))^3 ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [lintegral_const_mul' _ _ hc]
  symm
  unfold gaussianChartTripleWeight
  rw [lintegral_const_mul' _ _ hc]
  congr 1
  let S : Set ((Fin h → Space (n+1)) × (Space n × Space n × Space n)) :=
    {p | ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2.2 : Space (n+1)) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    have h₁ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
        (gnomonicChart p.2.1 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    have h₂ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
        (gnomonicChart p.2.2.1 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    have h₃ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n × Space n) =>
        (gnomonicChart p.2.2.2 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_le (by fun_prop) measurable_const))
  have hs (A : Fin h → Space (n+1)) : Prod.mk A ⁻¹' S = chartTripleBand A r := by
    ext w
    simp only [S,chartTripleBand,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod,forall_and]
  calc
    _ = ((gaussianRows (n+1) h).prod ((μ.prod (μ.prod μ)).restrict E)) S :=
      (Measure.prod_apply_symm hS).symm
    _ = ∫⁻ A : Fin h → Space (n+1), ((μ.prod (μ.prod μ)).restrict E) (Prod.mk A ⁻¹' S)
        ∂gaussianRows (n+1) h := Measure.prod_apply hS
    _ = _ := by
      apply lintegral_congr
      intro A
      rw [hs,Measure.restrict_apply (chartTripleBand_measurable A r),inter_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianChartTripleKernelMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint measurability of the actual chart triple kernel -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gaussianChartTripleWeight_measurable (r : ℝ) :
    Measurable (fun w : Space n × Space n × Space n => gaussianChartTripleWeight h r w.1 w.2.1 w.2.2) := by
  let S : Set ((Space n × Space n × Space n) × (Fin h → Space (n+1))) :=
    {p | ∀ i, |inner ℝ (gnomonicChart p.1.1 : Space (n+1)) (p.2 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.1.2.1 : Space (n+1)) (p.2 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.1.2.2 : Space (n+1)) (p.2 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    have h₁ : Measurable (fun p : (Space n × Space n × Space n) × (Fin h → Space (n+1)) =>
        (gnomonicChart p.1.1 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    have h₂ : Measurable (fun p : (Space n × Space n × Space n) × (Fin h → Space (n+1)) =>
        (gnomonicChart p.1.2.1 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    have h₃ : Measurable (fun p : (Space n × Space n × Space n) × (Fin h → Space (n+1)) =>
        (gnomonicChart p.1.2.2 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_le (by fun_prop) measurable_const))
  exact (measurable_measure_prodMk_left (ν := gaussianRows (n+1) h) hS).const_mul _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBadTripleMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expected mass of nearly dependent retained original triples -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gaussian_bad_triple_mass (μ : Measure (Space n)) [SFinite μ]
    (G : Set (Space n × Space n)) (E : Set (Space n × Space n × Space n)) (hE : MeasurableSet E)
    {b W K ℓ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hK : 0 ≤ K) (hℓ : (h:ℝ) < ℓ)
    (g k : ℕ) (hW : 8*W/b^2 ≤ 1/(2:ℝ)^g)
    (hretained : ∀ w ∈ E, ‖w.1‖ ≤ 1 ∧ ‖w.2.1‖ ≤ 1 ∧ ‖w.2.2‖ ≤ 1 ∧
      b ≤ ‖w.2.1-w.1‖ ∧ b ≤ ‖w.2.2-w.1‖ ∧ (w.1,w.2.2) ∈ G ∧
      Real.sqrt (tripleGram (gnomonicChart w.1 : Space (n+1))
        (gnomonicChart w.2.1 : Space (n+1)) (gnomonicChart w.2.2 : Space (n+1))) < W)
    (hdiag : ∀ p z, (p,z) ∈ G → z ≠ p)
    (hcap : ∀ p, ∀ j : ℕ, j ≤ g+k → ∀ u : Space n, ‖u‖ = 1 →
      μ {z | (p,z) ∈ G ∧ dist (NormedSpace.normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
        ENNReal.ofReal (K*(3*(1/(2:ℝ)^j))^ℓ)) :
    (∫⁻ A : Fin h → Space (n+1),
      ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^(g+k))).prod
        ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^(g+k))).prod
          (gaussianChartSliceMeasure μ A (1/(2:ℝ)^(g+k))))) E ∂gaussianRows (n+1) h) ≤
      ENNReal.ofReal ((gaussianTripleBandConstant/(b/4)^2)^h) *
      ENNReal.ofReal ((2:ℝ)^(h:ℝ)*((2*K*(3:ℝ)^ℓ)*(((2:ℝ)^g)^((h:ℝ)-ℓ))*
        (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ℓ))))) * (μ univ)^2 := by
  classical
  let r : ℝ := 1/(2:ℝ)^(g+k)
  let F : Space n × Space n × Space n → ℝ≥0∞ :=
    fun w => gaussianChartTripleWeight h r w.1 w.2.1 w.2.2
  let C : ℝ≥0∞ := ENNReal.ofReal ((gaussianTripleBandConstant/(b/4)^2)^h) *
    ENNReal.ofReal ((2:ℝ)^(h:ℝ)*((2*K*(3:ℝ)^ℓ)*(((2:ℝ)^g)^((h:ℝ)-ℓ))*
      (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ℓ)))))
  have hm : Measurable (E.indicator F) := (gaussianChartTripleWeight_measurable r).indicator hE
  have hfiber (p q : Space n) : (∫⁻ z, E.indicator F (p,q,z) ∂μ) ≤ C := by
    let T : Set (Space n) := {z | (p,q,z) ∈ E}
    have hT : MeasurableSet T := hE.preimage (by fun_prop)
    have he : (fun z => E.indicator F (p,q,z)) =
        T.indicator (fun z => gaussianChartTripleWeight h r p q z) := rfl
    rw [he,lintegral_indicator hT]
    by_cases ht : T.Nonempty
    · obtain ⟨z,hz⟩ := ht
      obtain ⟨hp,hq,_,hpq,_,_,_⟩ := hretained (p,q,z) hz
      apply anchored_bad_triple_potential μ G T hT p q hp hq hb hb1 hpq hK hℓ g k hW
      · intro y hy
        obtain ⟨_,_,hy1,_,hpy,hG,hgram⟩ := hretained (p,q,y) hy
        exact ⟨hG,hy1,hpy,hgram⟩
      · exact hdiag p
      · exact hcap p
    · have he : T = ∅ := Set.not_nonempty_iff_eq_empty.mp ht
      simp only [he,Measure.restrict_empty,lintegral_zero_measure,zero_le]
  rw [gaussian_chart_triple_average μ _ E hE,← lintegral_indicator hE,
    lintegral_prod _ hm.aemeasurable]
  calc
    _ ≤ ∫⁻ p : Space n, ∫⁻ _q : Space n, C ∂μ ∂μ := by
      apply lintegral_mono
      intro p
      calc
        _ = ∫⁻ q : Space n, ∫⁻ z : Space n, E.indicator F (p,q,z) ∂μ ∂μ :=
          lintegral_prod _ (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable
        _ ≤ _ := lintegral_mono (hfiber p)
    _ = _ := by
      simp only [lintegral_const]
      change C*μ univ*μ univ = C*(μ univ)^2
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_BadTriplePower
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed power bound for the original bad-triple Gaussian average -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma bad_triple_distance_factor {R b C : ℝ} (hR : 0 < R) (h : ℕ) :
    (C/(R^(-b)/4)^2)^h = (16*C)^h*R^(2*(h:ℝ)*b) := by
  have he : C/(R^(-b)/4)^2 = (16*C)*R^(2*b) := by
    rw [div_pow,Real.rpow_neg hR.le]
    have hpow : (R^b)^2 = R^(2*b) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hR.le]
      congr 1
      ring
    rw [← hpow]
    field_simp
    ring
  rw [he,mul_pow,← Real.rpow_natCast (R^(2*b)) h,← Real.rpow_mul hR.le]
  congr 2
  ring

theorem bad_triple_power_budget (h H : ℕ) (hH : 0 < H) {ell a b e : ℝ}
    (_hb : 0 < b) (hell : (h:ℝ) < ell)
    (hscale : 1/(H:ℝ) < a-2*b)
    (hgap : 0 < (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      8*(2*((2:ℝ)^N)^(-a))/(((2:ℝ)^N)^(-b))^2 ≤ 1/(2:ℝ)^(N/H) ∧
      ENNReal.ofReal ((gaussianTripleBandConstant/((((2:ℝ)^N)^(-b))/4)^2)^h) *
        ENNReal.ofReal ((2:ℝ)^(h:ℝ)*((2*((2:ℝ)^N)^e*(3:ℝ)^ell)*
          (((2:ℝ)^(N/H))^((h:ℝ)-ell))*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ell))))) ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  let q := (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e
  let D := (16*gaussianTripleBandConstant)^h*(2:ℝ)^(h:ℝ)*
    (2*(3:ℝ)^ell)*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-ell)))
  obtain ⟨Ns,hs⟩ := Regularization.fixed_constant_absorbed (sub_pos.mpr hscale) (16:ℝ)
  obtain ⟨Nc,hc⟩ := Regularization.fixed_constant_absorbed (half_pos hgap) D
  refine ⟨q/2,half_pos hgap,2*H+Ns+Nc,?_⟩
  intro N hN
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hNh : 2*H ≤ N := by omega
  have hscale' : 16*R^(-(a-2*b)) ≤ R^(-(1/(H:ℝ))) := by
    calc
      _ ≤ R^(a-2*b-1/(H:ℝ))*R^(-(a-2*b)) :=
        mul_le_mul_of_nonneg_right (hs N (by omega)) (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  constructor
  · have he : 8*(2*R^(-a))/(R^(-b))^2 = 16*R^(-(a-2*b)) := by
      rw [← Real.rpow_natCast (R^(-b)) 2,← Real.rpow_mul hR.le]
      calc
        _ = 16*(R^(-a)*R^(-(-b*(2:ℝ)))) := by
          rw [div_eq_mul_inv,← Real.rpow_neg hR.le]
          ring_nf
        _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring_nf
    rw [he]
    apply hscale'.trans
    have hdiv : ((N/H:ℕ):ℝ) ≤ (N:ℝ)/(H:ℝ) := by
      apply (le_div_iff₀ hHr).mpr
      exact_mod_cast Nat.div_mul_le_self N H
    have hdy : 1/(2:ℝ)^(N/H) = (2:ℝ)^(-((N/H:ℕ):ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    rw [hdy,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [div_eq_mul_inv,mul_neg,one_mul] using neg_le_neg hdiv
  · have hC := gaussianTripleBandConstant_pos
    rw [← ENNReal.ofReal_mul (by positivity),bad_triple_distance_factor hR]
    apply ENNReal.ofReal_le_ofReal
    have hD : 0 ≤ D := by
      dsimp [D]
      have hpow : (2:ℝ)^((h:ℝ)-ell) < 1 := by
        exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have hC := gaussianTripleBandConstant_pos
      positivity
    have hd := radial_scale_window_decay hH hNh (j := N/H) le_rfl (sub_pos.mpr hell).le
    have he : ((2:ℝ)^(N/H))^((h:ℝ)-ell) = ((2:ℝ)^(N/H))^(-(ell-h)) := by congr 1; ring
    rw [he]
    calc
      _ = D*R^(2*(h:ℝ)*b+e)*(((2:ℝ)^(N/H))^(-(ell-h))) := by
        dsimp [D]
        rw [Real.rpow_add hR]
        ring
      _ ≤ D*R^(2*(h:ℝ)*b+e)*R^(-((ell-h)/(2*(H:ℝ)))) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hD (by positivity))
      _ = D*R^(-q) := by rw [mul_assoc,← Real.rpow_add hR]; congr 1; dsimp [q]; ring_nf
      _ ≤ R^(q/2)*R^(-q) := mul_le_mul_of_nonneg_right (hc N (by omega)) (by positivity)
      _ = R^(-(q/2)) := by rw [← Real.rpow_add hR]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointBadTriples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Power-small nearly dependent triples of retained original chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem endpoint_bad_triples (H : ℕ) (hH : 0 < H) {ell a b e : ℝ}
    (hb : 0 < b) (hell : (h:ℝ) < ell)
    (hscale : 1/(H:ℝ) < a-2*b)
    (hgap : 0 < (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ]
      (G : Set (Space n × Space n))
      (E : Set (Space n × Space n × Space n)), MeasurableSet E →
      (∀ w ∈ E, ‖w.1‖ ≤ 1 ∧ ‖w.2.1‖ ≤ 1 ∧ ‖w.2.2‖ ≤ 1 ∧
        ((2:ℝ)^N)^(-b) ≤ ‖w.2.1-w.1‖ ∧ ((2:ℝ)^N)^(-b) ≤ ‖w.2.2-w.1‖ ∧
        (w.1,w.2.2) ∈ G ∧
        Real.sqrt (tripleGram (gnomonicChart w.1 : Space (n+1))
          (gnomonicChart w.2.1 : Space (n+1)) (gnomonicChart w.2.2 : Space (n+1))) <
            2*((2:ℝ)^N)^(-a)) →
      (∀ p z, (p,z) ∈ G → z ≠ p) →
      (∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space n, ‖u‖ = 1 →
        μ {z | (p,z) ∈ G ∧ dist (NormedSpace.normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
          ENNReal.ofReal (((2:ℝ)^N)^e*(3*(1/(2:ℝ)^j))^ell)) →
      (∫⁻ A : Fin h → Space (n+1),
        ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
          ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
            (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)))) E ∂gaussianRows (n+1) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨c,hc,N₀,hN₀⟩ := bad_triple_power_budget h H hH hb hell hscale hgap
  refine ⟨c,hc,N₀,?_⟩
  intro N hN μ _ G E hE hretained hdiag hcap
  obtain ⟨hscaleN,hbudget⟩ := hN₀ N hN
  have hpow : 0 < ((2:ℝ)^N)^(-b) := by positivity
  have hpow1 : ((2:ℝ)^N)^(-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by linarith)
  have heq : N/H+(N-N/H) = N := Nat.add_sub_of_le (Nat.div_le_self N H)
  have hh := gaussian_bad_triple_mass (h := h) (K := ((2:ℝ)^N)^e) μ G E hE hpow hpow1 (by positivity) hell
    (N/H) (N-N/H) hscaleN hretained hdiag (by simpa only [heq] using hcap)
  simp only [heq,measure_univ,one_pow,mul_one] at hh
  exact hh.trans hbudget

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialPairSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating retained original pairs with their actual ball-mass cost -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

lemma original_close_pair_mass (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (r : ℝ) (K : ℝ≥0∞) (hball : ∀ x, μ (ball x r) ≤ K) :
    (μ.prod μ) {p : Space d × Space d | dist p.1 p.2 < r} ≤ K := by
  have hS : MeasurableSet {p : Space d × Space d | dist p.1 p.2 < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ _x, K ∂μ := lintegral_mono (fun x => by
      simpa only [preimage_ofPred_eq,Metric.ball,dist_comm] using hball x)
    _ = _ := by simp

lemma separatedRadialPairs_measurable {G : Set (Space d × Space d)} (hG : MeasurableSet G)
    (r : ℝ) : MeasurableSet (separatedRadialPairs G r) :=
  hG.inter (measurableSet_le measurable_const
    (show Measurable (fun p : Space d × Space d => dist p.1 p.2) from by fun_prop))

lemma separatedRadialPairs_subset (G : Set (Space d × Space d)) (r : ℝ) :
    separatedRadialPairs G r ⊆ G := fun _ hp => hp.1

lemma separatedRadialPairs_cost (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (G : Set (Space d × Space d)) (r : ℝ) (K : ℝ≥0∞)
    (hball : ∀ x, μ (ball x r) ≤ K) :
    (μ.prod μ) (separatedRadialPairs G r)ᶜ ≤ (μ.prod μ) Gᶜ+K := by
  have hs : (separatedRadialPairs G r)ᶜ ⊆ Gᶜ ∪ {p | dist p.1 p.2 < r} := by
    intro p hp
    by_cases hg : p ∈ G
    · right
      by_contra hd
      exact hp ⟨hg,le_of_not_gt hd⟩
    · exact Or.inl hg
  exact (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (original_close_pair_mass μ r K hball)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_BadTripleRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable bad-triple relation on retained original labels -/

namespace Falconer
open Set MeasureTheory
variable {n : ℕ}

lemma chartTripleVolume_measurable : Measurable (chartTripleVolume (n := n)) := by
  have h₁ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.1 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp measurable_fst)
  have h₂ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.2.1 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
  have h₃ : Measurable (fun w : Space n × Space n × Space n =>
      (gnomonicChart w.2.2 : Space (n+1))) :=
    measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
  unfold chartTripleVolume tripleGram
  simp only [Matrix.det_fin_three,Matrix.gram_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  fun_prop

lemma badChartTriples_measurable {G : Set (Space n × Space n)} (hG : MeasurableSet G)
    (W : ℝ) : MeasurableSet (badChartTriples G W) := by
  have h₁ := hG.preimage (show Measurable (fun w : Space n × Space n × Space n =>
    (w.1,w.2.1)) from by fun_prop)
  have h₂ := hG.preimage (show Measurable (fun w : Space n × Space n × Space n =>
    (w.1,w.2.2)) from by fun_prop)
  have hn₁ : MeasurableSet {w : Space n × Space n × Space n | ‖w.1‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hn₂ : MeasurableSet {w : Space n × Space n × Space n | ‖w.2.1‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hn₃ : MeasurableSet {w : Space n × Space n × Space n | ‖w.2.2‖ ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  exact hn₁.inter (hn₂.inter (hn₃.inter
    (h₁.inter (h₂.inter (measurableSet_lt chartTripleVolume_measurable measurable_const)))))

lemma badChartTriples_retained (G : Set (Space n × Space n)) (W b : ℝ)
    (hsep : ∀ p z, (p,z) ∈ G → b ≤ dist p z) :
    ∀ w ∈ badChartTriples G W, ‖w.1‖ ≤ 1 ∧ ‖w.2.1‖ ≤ 1 ∧ ‖w.2.2‖ ≤ 1 ∧
      b ≤ ‖w.2.1-w.1‖ ∧ b ≤ ‖w.2.2-w.1‖ ∧ (w.1,w.2.2) ∈ G ∧
      chartTripleVolume w < W := by
  intro w hw
  obtain ⟨h₁,h₂,h₃,hpq,hpz,hvol⟩ := hw
  refine ⟨h₁,h₂,h₃,?_,?_,hpz,hvol⟩
  · simpa only [dist_eq_norm,norm_sub_rev] using hsep _ _ hpq
  · simpa only [dist_eq_norm,norm_sub_rev] using hsep _ _ hpz

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointSelectionLosses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One loss parameter for radial pruning, row selection and endpoint counting -/

namespace Falconer

theorem exists_endpoint_radial_exponent (h : ℕ) :
    ∃ ell : ℝ, (h:ℝ) < ell ∧
      ell < (((h+1:ℕ):ℝ)/((h+1:ℕ)+1))*((h+1:ℕ):ℝ) := by
  let ell : ℝ := (h:ℝ)+1/(2*((h:ℝ)+2))
  have hp : 0 < (h:ℝ)+2 := by positivity
  have he : (((h+1:ℕ):ℝ)/((h+1:ℕ)+1))*((h+1:ℕ):ℝ) =
      (h:ℝ)+1/((h:ℝ)+2) := by
    push_cast
    field_simp
    ring
  refine ⟨ell,?_,?_⟩
  · dsimp [ell]
    exact lt_add_of_pos_right _ (one_div_pos.mpr (mul_pos (by norm_num) hp))
  · rw [he]
    dsimp [ell]
    have hi : 0 < 1/((h:ℝ)+2) := one_div_pos.mpr hp
    have hr : 1/(2*((h:ℝ)+2)) = (1/((h:ℝ)+2))/2 := by
      field_simp
    rw [hr]
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized line sections of the gnomonic chart

The first tangent coordinate is isolated exactly. The other coordinates
give a vector perpendicular to both the pole and the chosen tangent axis.
-/

namespace Falconer

theorem coordinateJoin_inner {n : ℕ} (x y : Space n) (u v : ℝ) :
    inner ℝ (coordinateJoin x u) (coordinateJoin y v) = u*v + inner ℝ x y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  simp [coordinateJoin_eq]
  ring

theorem coordinateJoin_norm_sq {n : ℕ} (x : Space n) (u : ℝ) :
    ‖coordinateJoin x u‖^2 = u^2+‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,coordinateJoin_inner,real_inner_self_eq_norm_sq]
  ring

@[simp] theorem chartPole_norm (n : ℕ) : ‖chartPole n‖ = 1 := by
  have h := coordinateJoin_norm_sq (0 : Space (n+1)) 1
  norm_num at h
  dsimp [chartPole]
  rcases h with h | h
  · exact h
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space (n+1)) 1)]

@[simp] theorem chartAxis_norm (n : ℕ) : ‖chartAxis n‖ = 1 := by
  have h₁ := coordinateJoin_norm_sq (0 : Space n) 1
  have h₂ := coordinateJoin_norm_sq (coordinateJoin (0 : Space n) 1) 0
  dsimp [chartAxis]
  norm_num at h₁ h₂
  rcases h₁ with h₁ | h₁
  · nlinarith
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]

@[simp] theorem transverseLift_norm {n : ℕ} (x : Space n) : ‖transverseLift x‖ = ‖x‖ := by
  have h₁ := coordinateJoin_norm_sq x 0
  have h₂ := coordinateJoin_norm_sq (coordinateJoin x 0) 0
  dsimp [transverseLift]
  norm_num at h₁ h₂
  nlinarith [norm_nonneg (coordinateJoin (coordinateJoin x 0) 0),norm_nonneg x]

@[simp] theorem chartPole_inner_transverse {n : ℕ} (x : Space n) :
    inner ℝ (chartPole n) (transverseLift x) = 0 := by
  simp [chartPole,transverseLift,coordinateJoin_inner]

@[simp] theorem chartPole_inner_axis (n : ℕ) :
    inner ℝ (chartPole n) (chartAxis n) = 0 := by
  simp [chartPole,chartAxis,coordinateJoin_inner]

@[simp] theorem transverseLift_inner_axis {n : ℕ} (x : Space n) :
    inner ℝ (transverseLift x) (chartAxis n) = 0 := by
  simp [transverseLift,chartAxis,coordinateJoin_inner]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_GnomonicAffinePlate
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine hyperplanes in chart coordinates come from linear spherical slabs -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {n : ℕ}

theorem coordinateJoin_one_eq_northLift (p : Space n) : coordinateJoin p 1 = northLift p := by
  rw [coordinateJoin_eq]
  rfl

theorem normalized_affine_chart_inner_le (v p : Space n) (s : ℝ) (hv : ‖v‖ = 1) :
    |inner ℝ (NormedSpace.normalize (coordinateJoin v (-s))) (gnomonicChart p : Space (n+1))| ≤
      |inner ℝ v p-s| := by
  have hn : 1 ≤ ‖coordinateJoin v (-s)‖ := by
    have hh := coordinateJoin_norm_sq v (-s)
    rw [hv] at hh
    nlinarith [norm_nonneg (coordinateJoin v (-s)),sq_nonneg s]
  have hp : 1 ≤ ‖northLift p‖ := by
    have hh := northLift_norm_sq p
    nlinarith [norm_nonneg (northLift p),sq_nonneg ‖p‖]
  have hn0 : 0 < ‖coordinateJoin v (-s)‖ := by linarith
  have hp0 : 0 < ‖northLift p‖ := by linarith
  have hni : ‖coordinateJoin v (-s)‖⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_iff₀ hn0).mpr (by simpa only [one_mul] using hn)
  have hpi : ‖northLift p‖⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_iff₀ hp0).mpr (by simpa only [one_mul] using hp)
  have hi : inner ℝ (coordinateJoin v (-s)) (northLift p) = inner ℝ v p-s := by
    rw [← coordinateJoin_one_eq_northLift,coordinateJoin_inner]
    ring
  change |inner ℝ (‖coordinateJoin v (-s)‖⁻¹ • coordinateJoin v (-s))
    (‖northLift p‖⁻¹ • northLift p)| ≤ _
  rw [inner_smul_left,inner_smul_right,conj_trivial,hi,abs_mul,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hn0.le),abs_of_nonneg (inv_nonneg.mpr hp0.le)]
  calc
    _ ≤ 1*(1*|inner ℝ v p-s|) :=
      mul_le_mul hni (mul_le_mul_of_nonneg_right hpi (abs_nonneg _))
        (by positivity) zero_le_one
    _ = _ := by ring

theorem gnomonic_affine_plate_transport (μ : Measure (Space n)) (v : Space n) (s r : ℝ)
    (hv : ‖v‖ = 1) :
    ∃ w : Sphere (n+1),
      μ {p | |inner ℝ v p-s| ≤ r} ≤
        (Measure.map gnomonicChart μ) {u | |inner ℝ (w:Space (n+1)) (u:Space (n+1))| ≤ r} := by
  have hn : coordinateJoin v (-s) ≠ 0 := by
    intro hz
    have hh := coordinateJoin_norm_sq v (-s)
    rw [hz,norm_zero,hv] at hh
    nlinarith [sq_nonneg s]
  let w : Sphere (n+1) := ⟨NormedSpace.normalize (coordinateJoin v (-s)),by
    rw [Metric.mem_sphere,dist_zero_right,norm_normalize hn]⟩
  refine ⟨w,?_⟩
  rw [Measure.map_apply (gnomonicChart_continuous n).measurable
    (measurableSet_le (by fun_prop) measurable_const)]
  apply measure_mono
  intro p hp
  exact (normalized_affine_chart_inner_le v p s hv).trans hp

theorem gnomonicCoordinates_map_affine_plate (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0)
    (v : Space n) (s r : ℝ) (hv : ‖v‖ = 1) :
    ∃ w : Sphere (n+1),
      (Measure.map gnomonicCoordinates ν) {p | |inner ℝ v p-s| ≤ r} ≤
        ν {u : Sphere (n+1) | |inner ℝ (w:Space (n+1)) (u:Space (n+1))| ≤ r} := by
  obtain ⟨w,hw⟩ := gnomonic_affine_plate_transport
    (Measure.map gnomonicCoordinates ν) v s r hv
  rw [gnomonicCoordinates_map_recover ν hν] at hw
  exact ⟨w,hw⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartFiniteScaleBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale ball and plate bounds for the original chart law -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem dyadic_ball_all_radius {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (N : ℕ) {L q : ℝ} (hL : 1 ≤ L) (hq : 0 ≤ q) (hμ : μ univ ≤ 1)
    (hball : ∀ x : X, ∀ j : ℕ, j ≤ N → μ (ball x (1/(2:ℝ)^j)) ≤
      ENNReal.ofReal (L*(1/(2:ℝ)^j)^q))
    (x : X) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) :
    μ (ball x r) ≤ ENNReal.ofReal (L*(2*r)^q) := by
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hr1 : r ≤ 1
  · obtain ⟨j,hj,hrj,hjr⟩ := Regularization.dyadic_radius_bracket hr hr1
    apply ((measure_mono (ball_subset_ball hrj)).trans (hball x j hj)).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hjr hq) (by linarith))
  · have hp : 1 ≤ (2*r)^q := Real.one_le_rpow (by linarith) hq
    apply ((measure_mono (subset_univ _)).trans hμ).trans
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)

theorem gnomonic_dyadic_ball_bound {n : ℕ}
    (ν : Measure (Sphere (n+1))) (N : ℕ) {L q : ℝ} (hL : 1 ≤ L) (hq : 0 ≤ q)
    (hν : ν univ ≤ 1) (hνpos : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0)
    (hball : ∀ x : Sphere (n+1), ∀ j : ℕ, j ≤ N → ν (ball x (1/(2:ℝ)^j)) ≤
      ENNReal.ofReal (L*(1/(2:ℝ)^j)^q))
    (p : Space n) {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) :
    (Measure.map gnomonicCoordinates ν) (ball p r) ≤ ENNReal.ofReal ((L*4^q)*r^q) := by
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  have hh := (gnomonicCoordinates_map_ball ν hνpos p r).trans
    (dyadic_ball_all_radius ν N hL hq hν hball (gnomonicChart p) (hr.trans (by linarith)))
  apply hh.trans_eq
  congr 1
  rw [show 2*(2*r) = 4*r by ring,Real.mul_rpow (by norm_num) hr0.le]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianChartPairAverage
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pair averaging on the original chart labels -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gaussian_chart_pair_average (μ : Measure (Space n)) [SFinite μ]
    (r : ℝ) (E : Set (Space n × Space n)) (hE : MeasurableSet E) :
    (∫⁻ A : Fin h → Space (n+1), ((gaussianChartSliceMeasure μ A r).prod
      (gaussianChartSliceMeasure μ A r)) E ∂gaussianRows (n+1) h) =
      ∫⁻ w in E, gaussianChartPairWeight h r w.1 w.2 ∂μ.prod μ := by
  let D : (Fin h → Space (n+1)) → Set (Space n) :=
    fun A => gnomonicChart ⁻¹' gaussianDirectionBand A r
  have hD (A : Fin h → Space (n+1)) : MeasurableSet (D A) :=
    (gaussianDirectionBand_measurable A r).preimage (gnomonicChart_continuous n).measurable
  have he (A : Fin h → Space (n+1)) :
      ((gaussianChartSliceMeasure μ A r).prod (gaussianChartSliceMeasure μ A r)) E =
        (ENNReal.ofReal (r^(-(h:ℝ))))^2*(μ.prod μ) (E ∩ (D A ×ˢ D A)) := by
    simp only [gaussianChartSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
      Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hE,D,pow_two,mul_assoc]
  simp_rw [he]
  have hc : (ENNReal.ofReal (r^(-(h:ℝ))))^2 ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [lintegral_const_mul' _ _ hc]
  unfold gaussianChartPairWeight
  rw [lintegral_const_mul' _ _ hc]
  congr 1
  let S : Set ((Fin h → Space (n+1)) × (Space n × Space n)) :=
    {p | ∀ i, |inner ℝ (gnomonicChart p.2.1 : Space (n+1)) (p.1 i)| ≤ r ∧
      |inner ℝ (gnomonicChart p.2.2 : Space (n+1)) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    have h₁ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n) =>
        (gnomonicChart p.2.1 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    have h₂ : Measurable (fun p : (Fin h → Space (n+1)) × (Space n × Space n) =>
        (gnomonicChart p.2.2 : Space (n+1))) :=
      measurable_subtype_coe.comp ((gnomonicChart_continuous n).measurable.comp (by fun_prop))
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hs (A : Fin h → Space (n+1)) : Prod.mk A ⁻¹' S = D A ×ˢ D A := by
    ext w
    simp only [S,D,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod,forall_and]
  calc
    _ = ∫⁻ A : Fin h → Space (n+1), ((μ.prod μ).restrict E) (Prod.mk A ⁻¹' S)
        ∂gaussianRows (n+1) h := by
      apply lintegral_congr
      intro A
      rw [hs,Measure.restrict_apply ((hD A).prod (hD A)),inter_comm]
    _ = ((gaussianRows (n+1) h).prod ((μ.prod μ).restrict E)) S := (Measure.prod_apply hS).symm
    _ = _ := Measure.prod_apply_symm hS

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianChartPairKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized pair kernel in the bounded gnomonic chart -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

 theorem gaussian_chart_pair_kernel {p q : Space n} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    gaussianChartPairWeight h r p q ≤
      ENNReal.ofReal ((4*gaussianPairBandConstant)^h) *
        ENNReal.ofReal ((1/(dist p q+r))^(h:ℝ)) := by
  have hC0 := gaussianPairBandConstant_pos
  let u : Space (n+1) := (gnomonicChart p : Space (n+1))
  let v : Space (n+1) := (gnomonicChart q : Space (n+1))
  have hu : ‖u‖ = 1 := sphere_norm (gnomonicChart p)
  have hv : ‖v‖ = 1 := sphere_norm (gnomonicChart q)
  have hsep : dist p q ≤ 4*‖perpendicularPart u v‖ := by
    simpa only [dist_eq_norm,norm_sub_rev,u,v] using gnomonic_pair_separation hp hq
  have hsingle : stdGaussian (Space (n+1)) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ≤
      ENNReal.ofReal (4*gaussianPairBandConstant*r^2/(dist p q+r)) := by
    apply (gaussian_two_band hu hv hr).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hC : 0 ≤ gaussianPairBandConstant*r^2 := by positivity
    calc
      _ ≤ (gaussianPairBandConstant*r^2)*(4*(‖perpendicularPart u v‖+r)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        linarith
      _ = _ := by ring
  have hrows : gaussianRows (n+1) h
      {A | ∀ i, |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ r} ≤
      ENNReal.ofReal ((4*gaussianPairBandConstant*r^2/(dist p q+r))^h) := by
    have he : {A : Fin h → Space (n+1) | ∀ i,
        |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ r} =
        Set.pi univ (fun _ => {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r}) := by ext A; simp
    rw [gaussianRows,he,Measure.pi_pi]
    calc
      _ ≤ ∏ _ : Fin h, ENNReal.ofReal (4*gaussianPairBandConstant*r^2/(dist p q+r)) :=
        Finset.prod_le_prod' (fun _ _ => hsingle)
      _ = _ := by
        rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow (by positivity)]
  apply (mul_le_mul' le_rfl hrows).trans_eq
  have he : (4*gaussianPairBandConstant*r^2/(dist p q+r))^h =
      ((4*gaussianPairBandConstant)*r^2)^h*(1/(dist p q+r))^(h:ℝ) := by
    rw [Real.rpow_natCast,div_pow,one_div,inv_pow,div_eq_mul_inv]
  rw [he,ENNReal.ofReal_mul (by positivity),← mul_assoc,
    gaussian_squared_band_normalization hr (by positivity)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartPairTransfer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring original exceptional pairs to the actual Gaussian slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem chart_exceptional_pair_transfer (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1) (E : Set (Space n × Space n)) (hE : MeasurableSet E)
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hball : ∀ x : Space n, ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ A : Fin h → Space (n+1), ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
      (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N))) E ∂gaussianRows (n+1) h) ≤
      ENNReal.ofReal ((4*gaussianPairBandConstant)^h) *
        (ENNReal.ofReal (((2:ℝ)^g)^(h:ℝ))*(μ.prod μ) E +
          ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
            (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))) := by
  let r := 1/(2:ℝ)^N
  let B : Set (Space n × Space n) := {p | dist p.1 p.2 < 1/(2:ℝ)^g}
  let f : Space n × Space n → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((1/(dist p.1 p.2+r))^(h:ℝ))
  let C := ENNReal.ofReal ((4*gaussianPairBandConstant)^h)
  let D := ENNReal.ofReal (((2:ℝ)^g)^(h:ℝ))
  have hB : MeasurableSet B := measurableSet_lt (by fun_prop) measurable_const
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hmass : ∀ᵐ p : Space n × Space n ∂(μ.prod μ).restrict E,
      ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1 := by
    apply ae_restrict_of_ae
    exact (Measure.quasiMeasurePreserving_fst.ae hμ).and (Measure.quasiMeasurePreserving_snd.ae hμ)
  have hpoint : ∀ p, f p ≤ B.indicator f p+D := by
    intro p
    by_cases hp : p ∈ B
    · rw [indicator_of_mem hp]
      exact le_add_right le_rfl
    · rw [indicator_of_notMem hp,zero_add]
      have hd : 1/(2:ℝ)^g ≤ dist p.1 p.2 := le_of_not_gt hp
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (by positivity) _ (Nat.cast_nonneg _)
      apply (div_le_iff₀ (by dsimp [r]; positivity : 0 < dist p.1 p.2+r)).mpr
      have hr : 0 ≤ r := by dsimp [r]; positivity
      calc
        1 = (2:ℝ)^g*(1/(2:ℝ)^g) := by field_simp
        _ ≤ (2:ℝ)^g*(dist p.1 p.2+r) := by gcongr; linarith
  rw [gaussian_chart_pair_average μ _ E hE]
  calc
    _ ≤ ∫⁻ p in E, C*f p ∂μ.prod μ := lintegral_mono_ae (by
      filter_upwards [hmass] with p hp
      exact gaussian_chart_pair_kernel hp.1 hp.2 (by positivity))
    _ = C*∫⁻ p in E, f p ∂μ.prod μ := lintegral_const_mul' C _ ENNReal.ofReal_ne_top
    _ ≤ C*(∫⁻ p in E, B.indicator f p+D ∂μ.prod μ) :=
      mul_le_mul' le_rfl (lintegral_mono hpoint)
    _ = C*((∫⁻ p in E, B.indicator f p ∂μ.prod μ)+D*(μ.prod μ) E) := by
      rw [lintegral_add_left (hf.indicator hB),lintegral_const,Measure.restrict_apply_univ]
    _ ≤ C*((∫⁻ p in B, f p ∂μ.prod μ)+D*(μ.prod μ) E) := by
      apply mul_le_mul' le_rfl
      apply add_le_add _ le_rfl
      rw [← lintegral_indicator hB]
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ _ := by
      have hh := regularized_pair_potential μ hK (Nat.cast_nonneg _) hq g N hg (by simp) hball
      change C*((∫⁻ p in B, f p ∂μ.prod μ)+D*(μ.prod μ) E) ≤ _
      rw [add_comm]
      exact mul_le_mul' le_rfl (add_le_add le_rfl hh)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartPairPower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Power-small original pair sets stay power-small after Gaussian slicing -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

 theorem chart_pair_power (h : ℕ) {q c₀ : ℝ} (hq : (h:ℝ) < q) (hc₀ : 0 < c₀) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ : Measure (Space n)) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1) → ∀ E : Set (Space n × Space n), MeasurableSet E →
      (μ.prod μ) E ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) →
      (∀ x : Space n, ∀ j : ℕ, j ≤ N →
        μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*(1/(2:ℝ)^j)^q)) →
      (∫⁻ A : Fin h → Space (n+1), ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
        (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N))) E ∂gaussianRows (n+1) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨H₀,hH₀⟩ := exists_nat_gt (2*(h:ℝ)/c₀)
  let H := H₀+1
  have hH : 0 < H := by dsimp [H]; omega
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hfar : 0 < c₀-(h:ℝ)/(H:ℝ) := by
    have hh : 2*(h:ℝ)/c₀ < (H:ℝ) := by dsimp [H]; push_cast; linarith
    have hh' := (div_lt_iff₀ hc₀).mp hh
    apply sub_pos.mpr
    apply (div_lt_iff₀ hHr).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  let ε := (q-h)/(4*(H:ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hnear : 0 < (q-h)/(2*(H:ℝ))-ε := by
    have heq : (q-h)/(2*(H:ℝ)) = 2*ε := by dsimp [ε]; ring
    rw [heq]
    linarith
  let C := (4*gaussianPairBandConstant)^h
  let L := 1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))
  have hC : 0 ≤ C := by have := gaussianPairBandConstant_pos; dsimp [C]; positivity
  have hL : 0 ≤ L := by
    have hh : (2:ℝ)^((h:ℝ)-q) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    dsimp [L]
    positivity
  let c := min (c₀-(h:ℝ)/(H:ℝ)) ((q-h)/(2*(H:ℝ))-ε)/2
  have hc : 0 < c := half_pos (lt_min hfar hnear)
  have hcf : c < c₀-(h:ℝ)/(H:ℝ) := by dsimp [c]; have := min_le_left (c₀-(h:ℝ)/(H:ℝ)) ((q-h)/(2*(H:ℝ))-ε); linarith
  have hcn : c < (q-h)/(2*(H:ℝ))-ε := by dsimp [c]; have := min_le_right (c₀-(h:ℝ)/(H:ℝ)) ((q-h)/(2*(H:ℝ))-ε); linarith
  obtain ⟨Nc,hcost⟩ := weak_radial_two_costs hC (mul_nonneg hC hL) hcf hcn
  refine ⟨ε,c,hε,hc,2*H+Nc,?_⟩
  intro N hN μ _ hμ E hE hmass hball
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hf : ((2:ℝ)^(N/H))^(h:ℝ) ≤ R^((h:ℝ)/(H:ℝ)) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hdiv : ((N/H:ℕ):ℝ) ≤ (N:ℝ)/(H:ℝ) := by
      apply (le_div_iff₀ hHr).mpr
      exact_mod_cast Nat.div_mul_le_self N H
    have hh := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (α := ℝ) h)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hn := radial_scale_window_decay hH (by omega : 2*H ≤ N)
    (j := N/H) le_rfl (sub_pos.mpr hq).le
  have hn' : ((2:ℝ)^(N/H))^((h:ℝ)-q) ≤ R^(-((q-h)/(2*(H:ℝ)))) := by
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  apply (chart_exceptional_pair_transfer μ hμ E hE (by positivity) hq (N/H) N
    (Nat.div_le_self N H) hball).trans
  apply (mul_le_mul' le_rfl (add_le_add
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hf) hmass)
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hn' (by positivity)) hL)))).trans
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = C*R^(-(c₀-(h:ℝ)/(H:ℝ)))+(C*L)*R^(-((q-h)/(2*(H:ℝ))-ε)) := by
      change C*(R^((h:ℝ)/(H:ℝ))*R^(-c₀)+
        R^ε*R^(-((q-h)/(2*(H:ℝ))))*L) = _
      have he₁ : R^((h:ℝ)/(H:ℝ))*R^(-c₀) = R^(-(c₀-(h:ℝ)/(H:ℝ))) := by
        rw [← Real.rpow_add hR]
        congr 1
        ring
      have he₂ : R^ε*R^(-((q-h)/(2*(H:ℝ)))) = R^(-((q-h)/(2*(H:ℝ))-ε)) := by
        rw [← Real.rpow_add hR]
        congr 1
        ring
      rw [he₁,he₂]
      ring
    _ ≤ _ := hcost N (by omega)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_EndpointRadialPreparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual original-law radial preparation for the endpoint angular proof -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory NormedSpace
open scoped ENNReal
variable {h : ℕ}

theorem endpoint_radial_preparation (hLW : PublishedFiniteLoomisWhitney)
    {ζ ell a : ℝ} (hζ : 0 < ζ) (hell : (h:ℝ) < ell)
    (hell' : ell < (((h+1:ℕ):ℝ)/((h+1:ℕ)+1))*((h+1:ℕ):ℝ)) (ha : 0 < a) :
    ∃ ε b e c₀ c₁ c₂ : ℝ, 0 < ε ∧ 0 < b ∧ 0 < e ∧ 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (μ : Measure (Space ((h+1)+1))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space ((h+1)+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^((h+1:ℕ):ℝ))) →
      (∀ w : Space ((h+1)+1), ‖w‖ = 1 → ∀ v r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-v| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space ((h+1)+1) × Space ((h+1)+1)), MeasurableSet G ∧
        (∀ p z, (p,z) ∈ G → ((2:ℝ)^N)^(-b) ≤ dist p z) ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) ∧
        (∫⁻ A : Fin h → Space (((h+1)+1)+1),
          ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
            (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N))) Gᶜ ∂gaussianRows (((h+1)+1)+1) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₁)) ∧
        (∫⁻ A : Fin h → Space (((h+1)+1)+1),
          ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
            ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
              (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N))))
                (badChartTriples G (2*((2:ℝ)^N)^(-a))) ∂gaussianRows (((h+1)+1)+1) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₂)) ∧
        ∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space ((h+1)+1),
          μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
            ENNReal.ofReal (((2:ℝ)^N)^e*(3*(1/(2:ℝ)^j))^ell) := by
  obtain ⟨H,hH,b₀,e,hb₀,he,hscale,hgap⟩ := exists_endpoint_radial_losses h hell ha
  let b := min b₀ (1/2)
  have hb : 0 < b := lt_min hb₀ (by norm_num)
  have hb₀' : b ≤ b₀ := min_le_left _ _
  have hb1 : b ≤ 1 := (min_le_right b₀ (1/2)).trans (by norm_num)
  have hscale' : 1/(H:ℝ) < a-2*b := by linarith
  have hgap' : 0 < (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e := by
    have hh := mul_le_mul_of_nonneg_left hb₀' (show 0 ≤ 2*(h:ℝ) by positivity)
    linarith
  have hell0 : 0 ≤ ell := (Nat.cast_nonneg h).trans hell.le
  obtain ⟨ew,cw,hew,hcw,Nw,hw⟩ := small_chart_weak_radial hLW (by omega : 1 ≤ h+1)
    hζ hell0 hell' he
  let q : ℝ := ((h+1:ℕ):ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqb : 0 < q*b/2 := by positivity
  let c₀ := min cw (q*b/2)/2
  have hc₀ : 0 < c₀ := half_pos (lt_min hcw (by positivity))
  have hc₀w : c₀ < cw := by dsimp [c₀]; have := min_le_left cw (q*b/2); linarith
  have hc₀b : c₀ < q*b/2 := by dsimp [c₀]; have := min_le_right cw (q*b/2); linarith
  obtain ⟨Nd,hd⟩ := weak_radial_two_costs (A := 1) (B := 1) (by norm_num) (by norm_num) hc₀w hc₀b
  obtain ⟨ep,cp,hep,hcp,Np,hp⟩ := chart_pair_power (n := (h+1)+1) h
    (q := q) (by dsimp [q]; push_cast; linarith) hc₀
  obtain ⟨ct,hct,Nt,ht⟩ := endpoint_bad_triples (n := (h+1)+1) (h := h)
    H hH hb hell hscale' hgap'
  let ε := min ew (min ep (q*b/4))
  have hε : 0 < ε := lt_min hew (lt_min hep (by positivity))
  have hεw : ε ≤ ew := min_le_left _ _
  have hεp : ε ≤ ep := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ q*b/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,b,e,c₀,cp,ct,hε,hb,he,hc₀,hcp,hct,Nw+Nd+Np+Nt,?_⟩
  intro N hN μ _ hμ hball hslab
  let R : ℝ := (2:ℝ)^N
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hlossw : R^ε ≤ R^ew := Real.rpow_le_rpow_of_exponent_le hR1 hεw
  have hlossp : R^ε ≤ R^ep := Real.rpow_le_rpow_of_exponent_le hR1 hεp
  obtain ⟨G₀,hG₀,hdiag₀,hcost₀,hcap₀⟩ := hw N (by omega) μ hμ
    (fun x r hr hr1 => (hball x r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hlossw (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
    (fun w hw v r hr hr1 => (hslab w hw v r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hlossw (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
  let G := separatedRadialPairs G₀ (R^(-b))
  have hG : MeasurableSet G := separatedRadialPairs_measurable hG₀ _
  have hsub : G ⊆ G₀ := separatedRadialPairs_subset _ _
  have hsep : ∀ p z, (p,z) ∈ G → R^(-b) ≤ dist p z := fun _ _ hp => hp.2
  have hdiag : ∀ p z, (p,z) ∈ G → z ≠ p := fun p z hp => hdiag₀ p z (hsub hp)
  have hrlo : R⁻¹ ≤ R^(-b) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hrhi : R^(-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR1 (by linarith)
  have hnear : ∀ x, μ (ball x (R^(-b))) ≤ ENNReal.ofReal (R^(-(q*b/2))) := by
    intro x
    apply (hball x (R^(-b)) hrlo hrhi).trans
    apply ENNReal.ofReal_le_ofReal
    change R^ε*(R^(-b))^q ≤ _
    rw [← Real.rpow_mul hR.le,← Real.rpow_add hR]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by nlinarith)
  have hcost : (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (R^(-c₀)) := by
    apply (separatedRadialPairs_cost μ G₀ _ _ hnear).trans
    apply (add_le_add hcost₀ le_rfl).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hd N (by omega))
  have hcap : ∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space ((h+1)+1),
      μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
        ENNReal.ofReal (R^e*(3*(1/(2:ℝ)^j))^ell) := by
    intro p j hj u
    have hsubcap : {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ⊆
        {z | (p,z) ∈ G₀ ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} :=
      fun _ hz => ⟨hsub hz.1,hz.2⟩
    exact (measure_mono hsubcap).trans (hcap₀ p j hj u)
  refine ⟨G,hG,hsep,hcost,?_,?_,hcap⟩
  · apply hp N (by omega) μ (by filter_upwards [hμ] with x hx; linarith) Gᶜ hG.compl hcost
    intro x j hj
    have hlo : R⁻¹ ≤ 1/(2:ℝ)^j := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hj)
    have hhi : 1/(2:ℝ)^j ≤ 1 := by
      rw [one_div]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    exact (hball x _ hlo hhi).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hlossp (by positivity)))
  · apply ht N (by omega) μ G (badChartTriples G (2*R^(-a))) (badChartTriples_measurable hG _)
      (badChartTriples_retained G _ _ hsep) hdiag
    exact fun p j hj u _ => hcap p j hj u

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointSphericalPreparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The radial endpoint costs from the original spherical direction law -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {h : ℕ}

theorem endpoint_spherical_preparation_oai (hLW : PublishedFiniteLoomisWhitney)
    {ζ a : ℝ} (hζ : 0 < ζ) (ha : 0 < a) :
    ∃ ε c₁ c₂ : ℝ, 0 < ε ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ν : Measure (Sphere (h+3))) [IsProbabilityMeasure ν],
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ 1/8) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (((2:ℝ)^N)^ε*(1/(2:ℝ)^j)^((h+1:ℕ):ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ν {v : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (v:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      let ν₀ := Measure.map gnomonicCoordinates ν
      ∃ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G ∧
        (∫⁻ A : Fin h → Space (h+3),
          ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
            (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))) Gᶜ ∂gaussianRows (h+3) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₁)) ∧
        (∫⁻ A : Fin h → Space (h+3),
          ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
            ((gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N)).prod
              (gaussianChartSliceMeasure ν₀ A (1/(2:ℝ)^N))))
            (badChartTriples G (2*((2:ℝ)^N)^(-a))) ∂gaussianRows (h+3) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₂)) := by
  obtain ⟨ell,hell,hell'⟩ := exists_endpoint_radial_exponent h
  obtain ⟨e,b,f,c₀,c₁,c₂,he,_,_,_,hc₁,hc₂,N₁,hprep⟩ :=
    endpoint_radial_preparation hLW hζ hell hell' ha
  let ε := e/2
  have hε : 0 < ε := half_pos he
  obtain ⟨N₂,hconstant⟩ := Regularization.fixed_constant_absorbed hε ((4:ℝ)^((h+1:ℕ):ℝ))
  refine ⟨ε,c₁,c₂,hε,hc₁,hc₂,N₁+N₂,?_⟩
  intro N hN ν _ hcap hball hslab ν₀
  let R : ℝ := (2:ℝ)^N
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hL : 1 ≤ R^ε := Real.one_le_rpow hR1 hε.le
  have hεe : ε ≤ e := by dsimp [ε]; linarith
  have hloss : R^ε ≤ R^e := Real.rpow_le_rpow_of_exponent_le hR1 hεe
  have hchartloss : R^ε*4^((h+1:ℕ):ℝ) ≤ R^e := by
    calc
      _ ≤ R^ε*R^ε := mul_le_mul_of_nonneg_left (hconstant N (by omega)) (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; dsimp [ε]; ring
  have hpos : ∀ᵐ (w : Sphere (h+3)) ∂ν, 0 < (w:Space (h+3)) 0 := by
    filter_upwards [hcap] with w hw
    have hh := gnomonic_cap_first_coordinate w (hw.trans (by norm_num : (1/8:ℝ) ≤ 1/2))
    linarith
  have hsmall : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1/4 := small_gnomonic_cap_law ν hcap
  have hchartball : ∀ p : Space (h+2), ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ν₀ (ball p r) ≤ ENNReal.ofReal (R^e*r^((h+1:ℕ):ℝ)) := by
    intro p r hr _
    have hh := gnomonic_dyadic_ball_bound ν N hL (by positivity) (by simp) hpos hball p
      (by simpa only [one_div] using hr)
    exact hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hchartloss
      (Real.rpow_nonneg (le_trans (by positivity) hr) _)))
  have hchartslab : ∀ w : Space (h+2), ‖w‖ = 1 → ∀ v r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
      ν₀ {p | |inner ℝ w p-v| ≤ r} ≤ ENNReal.ofReal (R^e*r^ζ) := by
    intro w hw v r hr hr1
    obtain ⟨u,hu⟩ := gnomonicCoordinates_map_affine_plate ν hpos w v r hw
    exact (hu.trans (hslab u r hr hr1)).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hloss (Real.rpow_nonneg (le_trans (by positivity) hr) _)))
  haveI : IsProbabilityMeasure ν₀ := Measure.isProbabilityMeasure_map gnomonicCoordinates_measurable.aemeasurable
  obtain ⟨G,hG,_,_,hp,ht,_⟩ := hprep N (by omega) ν₀ hsmall hchartball hchartslab
  exact ⟨G,hG,hp,ht⟩

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.endpoint_spherical_preparation_oai := @OAI.Falconer.endpoint_spherical_preparation_oai
