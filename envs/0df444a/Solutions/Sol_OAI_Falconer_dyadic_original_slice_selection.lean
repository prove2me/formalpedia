-- Prove2me | solution 1 for OAI.Falconer.dyadic_original_slice_selection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:11:56.743303+00:00
-- url     : https://prove2.me/submissions/f53faa6c-6557-4ff6-805f-8b41efdc945f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

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

theorem regularized_potential_global (μ : Measure X) (x : X)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (k : ℕ)
    (hmass : μ univ ≤ 1)
    (hball : ∀ n : ℕ, n ≤ k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y, ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^k))^s) ∂μ) ≤
      ENNReal.ofReal (K*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q))))+1 := by
  let f : X → ℝ≥0∞ := fun y => ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^k))^s)
  have hlocal := regularized_potential_frostman μ x hK hs hsq 0 k (by simpa using hball)
  have hout : (∫⁻ y in (ball x 1)ᶜ, f y ∂μ) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ in (ball x 1)ᶜ, (1 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' measurableSet_ball.compl
        intro y hy
        apply ENNReal.ofReal_le_one.mpr
        apply Real.rpow_le_one (by positivity) _ hs
        have hd : 1 ≤ dist x y := by simpa [mem_ball,dist_comm] using hy
        exact (div_le_one (by positivity)).mpr (by linarith [show (0:ℝ) < 1/(2:ℝ)^k by positivity])
      _ = μ ((ball x 1)ᶜ) := by simp
      _ ≤ 1 := (measure_mono (subset_univ _)).trans hmass
  rw [← lintegral_add_compl f measurableSet_ball]
  exact add_le_add (by simpa [f] using hlocal) hout

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
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BallTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enforcing ball bounds by deleting points of excessive local mass -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem measurable_ball_mass (μ : Measure X) [SFinite μ] (r : ℝ) :
    Measurable (fun x => μ (ball x r)) := by
  have hS : MeasurableSet {z : X × X | dist z.1 z.2 < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hm := measurable_measure_prodMk_left (ν := μ) hS
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  congr 1
  ext y
  simp only [mem_preimage,mem_ofPred_eq,mem_ball,dist_comm]

theorem ball_mass_pair_integral (μ : Measure X) [SFinite μ] (r : ℝ) :
    (∫⁻ x, μ (ball x r) ∂μ) = (μ.prod μ) {z | dist z.1 z.2 < r} := by
  rw [Measure.prod_apply (measurableSet_lt (by fun_prop) measurable_const)]
  apply lintegral_congr
  intro x
  congr 1
  ext y
  simp only [mem_preimage,mem_ofPred_eq,mem_ball,dist_comm]

theorem excessive_ball_mass (μ : Measure X) [SFinite μ] (r : ℝ)
    {B : ℝ≥0∞} (hB : B ≠ 0) :
    μ {x | B < μ (ball x r)} ≤ B⁻¹*(μ.prod μ) {z | dist z.1 z.2 < r} := by
  by_cases hTop : B = ∞
  · simp [hTop]
  calc
    _ ≤ μ {x | B ≤ μ (ball x r)} := measure_mono (show {x | B < μ (ball x r)} ⊆
        {x | B ≤ μ (ball x r)} from by
      intro x hx
      change B < μ (ball x r) at hx
      exact hx.le)
    _ ≤ (∫⁻ x, μ (ball x r) ∂μ)/B :=
      meas_ge_le_lintegral_div (measurable_ball_mass μ r).aemeasurable hB hTop
    _ = _ := by rw [ball_mass_pair_integral,div_eq_mul_inv,mul_comm]

omit [SecondCountableTopology X] in
theorem restricted_good_ball_bound (μ : Measure X) [SFinite μ] (r : ℝ) (B : ℝ≥0∞) :
    ∀ a : X, (μ.restrict {x | μ (ball x (2*r)) ≤ B}) (ball a r) ≤ B := by
  intro a
  rw [Measure.restrict_apply measurableSet_ball]
  by_cases hne : (ball a r ∩ {x | μ (ball x (2*r)) ≤ B}).Nonempty
  · obtain ⟨x,hxa,hx⟩ := hne
    have hsub : ball a r ∩ {x | μ (ball x (2*r)) ≤ B} ⊆ ball x (2*r) := by
      rintro y ⟨hy,_⟩
      rw [mem_ball] at hxa hy ⊢
      have htri := dist_triangle y a x
      rw [dist_comm a x] at htri
      linarith
    exact (measure_mono hsub).trans hx
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,measure_empty]
    exact bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteBallPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneously enforcing the finitely many slice ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X ι : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]

omit [SecondCountableTopology X] [BorelSpace X] in
theorem finiteBallGood_compl_mass (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) :
    μ (finiteBallGood μ r B)ᶜ ≤ ∑ i, μ {x | B i < μ (ball x (2*r i))} := by
  have he : (finiteBallGood μ r B)ᶜ = ⋃ i, {x | B i < μ (ball x (2*r i))} := by
    ext x
    simp [finiteBallGood,not_forall,not_le]
  rw [he]
  exact measure_iUnion_fintype_le _ _

omit [SecondCountableTopology X] [Fintype ι] in
theorem finiteBallGood_ball_bound (μ : Measure X) [SFinite μ]
    (r : ι → ℝ) (B : ι → ℝ≥0∞) (i : ι) (a : X) :
    (μ.restrict (finiteBallGood μ r B)) (ball a (r i)) ≤ B i := by
  calc
    _ ≤ (μ.restrict {x | μ (ball x (2*r i)) ≤ B i}) (ball a (r i)) :=
      Measure.restrict_mono_set μ (s := finiteBallGood μ r B)
        (t := {x | μ (ball x (2*r i)) ≤ B i}) (fun _ hx => hx i) _
    _ ≤ _ := restricted_good_ball_bound μ (r i) (B i) a

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DensityTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Truncation of radial densities

The integer-cap step `prep:integer-caps` deletes pairs on which either
radial density exceeds a threshold. These lemmas estimate the deleted
original product mass by the Lp moments and bound every remaining fiber
by the threshold times the angular reference measure.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

private theorem ennreal_le_threshold_tail {t T : ℝ≥0∞} {p : ℝ}
    (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) (ht : T ≤ t) :
    t ≤ T ^ (1 - p) * t ^ p := by
  have hpow := ENNReal.rpow_le_rpow ht (by linarith : 0 ≤ p - 1)
  have hprod : T ^ (p - 1) * t ≤ t ^ p := by
    calc
      T ^ (p - 1) * t ≤ t ^ (p - 1) * t := mul_le_mul_left hpow t
      _ = t ^ ((p - 1) + 1) := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
      _ = t ^ p := by congr 1; ring
  have hcancel : T ^ (1 - p) * T ^ (p - 1) = 1 := by
    rw [← ENNReal.rpow_add _ _ hT.ne' hTtop]
    convert (ENNReal.rpow_zero : T ^ (0 : ℝ) = 1) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  calc
    t = (T ^ (1 - p) * T ^ (p - 1)) * t := by rw [hcancel, one_mul]
    _ = T ^ (1 - p) * (T ^ (p - 1) * t) := mul_assoc _ _ _
    _ ≤ T ^ (1 - p) * t ^ p := mul_le_mul_right hprod _

/-- The density mass above `T` is bounded by `T^(1-p)` times its pth moment. -/
theorem density_tail_mass {A : Type*} [MeasurableSpace A]
    (σ : Measure A) (f : A → ℝ≥0∞) (hf : Measurable f)
    {T : ℝ≥0∞} {p : ℝ} (hT : 0 < T) (hTtop : T ≠ ∞) (hp : 1 < p) :
    (σ.withDensity f) {a | T < f a} ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ := by
  have hS : MeasurableSet {a | T < f a} := measurableSet_lt measurable_const hf
  rw [withDensity_apply _ hS]
  calc
    (∫⁻ a in {a | T < f a}, f a ∂σ) ≤
        ∫⁻ a in {a | T < f a}, T ^ (1 - p) * f a ^ p ∂σ := by
      apply setLIntegral_mono' hS
      intro a ha
      exact ennreal_le_threshold_tail hT hTtop hp ha.le
    _ = T ^ (1 - p) * ∫⁻ a in {a | T < f a}, f a ^ p ∂σ :=
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hT.ne' hTtop)
    _ ≤ T ^ (1 - p) * ∫⁻ a, f a ^ p ∂σ :=
      mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ProductRestrictionLoss
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incidence mass lost when either original marginal is restricted -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_restriction_incidence_loss (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E : Set (X × Y)) (hE : MeasurableSet E)
    (P : Set X) (Q : Set Y) :
    (μ.prod ν) E ≤ (μ.restrict P).prod (ν.restrict Q) E +
      μ Pᶜ*ν univ + μ univ*ν Qᶜ := by
  have hs : E ⊆ (E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ) ∪ (univ ×ˢ Qᶜ) := by
    intro z hz
    by_cases hp : z.1 ∈ P
    · by_cases hq : z.2 ∈ Q
      · exact Or.inl (Or.inl ⟨hz,hp,hq⟩)
      · exact Or.inr ⟨mem_univ _,hq⟩
    · exact Or.inl (Or.inr ⟨hp,mem_univ _⟩)
  rw [Measure.prod_restrict,Measure.restrict_apply hE]
  calc
    _ ≤ (μ.prod ν) ((E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ) ∪ (univ ×ˢ Qᶜ)) := measure_mono hs
    _ ≤ (μ.prod ν) ((E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ)) + (μ.prod ν) (univ ×ˢ Qᶜ) :=
      measure_union_le _ _
    _ ≤ ((μ.prod ν) (E ∩ (P ×ˢ Q)) + (μ.prod ν) (Pᶜ ×ˢ univ)) +
        (μ.prod ν) (univ ×ˢ Qᶜ) := add_le_add_left (measure_union_le _ _) _
    _ = _ := by rw [Measure.prod_prod,Measure.prod_prod]

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

theorem gaussian_two_band_projective_chart {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : 0 ≤ inner ℝ u v)
    {r : ℝ} (hr : 0 < r) :
    stdGaussian (Space d) {x | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r} ≤
      ENNReal.ofReal (2*gaussianPairBandConstant*r^2/(dist u v+r)) := by
  apply (gaussian_two_band hu hv hr).trans
  apply ENNReal.ofReal_le_ofReal
  have hh := unit_close_of_perpendicular hu hv huv
  have hp : 0 < dist u v+r := by positivity
  have hq : 0 < ‖perpendicularPart u v‖+r := by positivity
  apply (div_le_div_iff₀ hq hp).mpr
  have hc : 0 ≤ gaussianPairBandConstant*r^2 :=
    mul_nonneg gaussianPairBandConstant_pos.le (sq_nonneg _)
  calc
    _ ≤ (gaussianPairBandConstant*r^2)*(2*(‖perpendicularPart u v‖+r)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      rw [dist_eq_norm]
      linarith
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Gaussian rows used for the random-subspace estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRows_pair_band_chart {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : 0 ≤ inner ℝ u v)
    {r : ℝ} (hr : 0 < r) :
    gaussianRows d h {A | ∀ i, |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ r} ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant*r^2/(dist u v+r))^h) := by
  have he : {A : Fin h → Space d | ∀ i, |inner ℝ u (A i)| ≤ r ∧ |inner ℝ v (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | |inner ℝ u x| ≤ r ∧ |inner ℝ v x| ≤ r}) := by
    ext A
    simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal (2*gaussianPairBandConstant*r^2/(dist u v+r)) :=
      Finset.prod_le_prod' (fun _ _ => gaussian_two_band_projective_chart hu hv huv hr)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) gaussianPairBandConstant_pos.le)
        (sq_nonneg _)) (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
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

theorem gaussian_direction_band_second_moment (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (r : ℝ) :
    (∫⁻ A : Fin h → Space d, (ν (gaussianDirectionBand A r))^2 ∂gaussianRows d h) =
      ∫⁻ z : Sphere d × Sphere d,
        gaussianRows d h {A | ∀ i,
          |inner ℝ (z.1:Space d) (A i)| ≤ r ∧ |inner ℝ (z.2:Space d) (A i)| ≤ r} ∂ν.prod ν := by
  let S : Set ((Fin h → Space d) × (Sphere d × Sphere d)) := {p | ∀ i,
    |inner ℝ (p.2.1:Space d) (p.1 i)| ≤ r ∧ |inner ℝ (p.2.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hsection (A : Fin h → Space d) : Prod.mk A ⁻¹' S =
      (gaussianDirectionBand A r) ×ˢ (gaussianDirectionBand A r) := by
    ext z
    simp only [S,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod]
    exact forall_and
  calc
    _ = ∫⁻ A : Fin h → Space d, (ν.prod ν) (Prod.mk A ⁻¹' S) ∂gaussianRows d h := by
      apply lintegral_congr
      intro A
      rw [hsection,Measure.prod_prod,pow_two]
    _ = ((gaussianRows d h).prod (ν.prod ν)) S := (Measure.prod_apply hS).symm
    _ = _ := Measure.prod_apply_symm hS

theorem gaussian_direction_band_second_moment_bound (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 < r)
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν, 0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d, (ν (gaussianDirectionBand A r))^2 ∂gaussianRows d h) ≤
      ∫⁻ z : Sphere d × Sphere d,
        ENNReal.ofReal ((2*gaussianPairBandConstant*r^2/(dist z.1 z.2+r))^h) ∂ν.prod ν := by
  rw [gaussian_direction_band_second_moment]
  apply lintegral_mono_ae
  filter_upwards [hchart] with z hz
  simpa only [Subtype.dist_eq] using gaussianRows_pair_band_chart (h := h)
    (sphere_norm z.1) (sphere_norm z.2) hz hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale second moments of Gaussian direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_pair_kernel_factor (h : ℕ) (r a : ℝ) :
    (2*gaussianPairBandConstant*r^2/(a+r))^h =
      (2*gaussianPairBandConstant*r^2)^h*(1/(a+r))^(h:ℝ) := by
  rw [Real.rpow_natCast,div_pow,one_div,inv_pow,div_eq_mul_inv]

theorem gaussian_direction_second_moment_frostman
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (k : ℕ)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ k →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      (ν (gaussianDirectionBand A (1/(2:ℝ)^k)))^2 ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant*(1/(2:ℝ)^k)^2)^h)*
        (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1) := by
  let r : ℝ := 1/(2:ℝ)^k
  let C : ℝ≥0∞ := ENNReal.ofReal ((2*gaussianPairBandConstant*r^2)^h)
  let B : ℝ≥0∞ := ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1
  have hp (w : Sphere d) :
      (∫⁻ v, ENNReal.ofReal ((1/(dist w v+r))^(h:ℝ)) ∂ν) ≤ B :=
    regularized_potential_global ν w hK (Nat.cast_nonneg _) hq k hmass (hball w)
  apply (gaussian_direction_band_second_moment_bound ν (by positivity) hchart).trans
  calc
    _ = C * ∫⁻ z : Sphere d × Sphere d,
        ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂ν.prod ν := by
      change (∫⁻ z : Sphere d × Sphere d,
        ENNReal.ofReal ((2*gaussianPairBandConstant*r^2/(dist z.1 z.2+r))^h) ∂ν.prod ν) = _
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [gaussian_pair_kernel_factor,ENNReal.ofReal_mul
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          gaussianPairBandConstant_pos.le) (sq_nonneg r)) h)]
    _ = C * ∫⁻ w, ∫⁻ v, ENNReal.ofReal ((1/(dist w v+r))^(h:ℝ)) ∂ν ∂ν := by
      rw [lintegral_prod _ (by fun_prop)]
    _ ≤ C * ∫⁻ _ : Sphere d, B ∂ν := mul_le_mul_right (lintegral_mono hp) C
    _ = C*(B*ν univ) := by rw [lintegral_const]
    _ ≤ C*(B*1) := by gcongr
    _ = _ := by simp [C,B,r]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMean
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First moments of actual Gaussian direction slices -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_band_normalization {r C : ℝ} (hr : 0 < r) (_hC : 0 ≤ C) :
    ENNReal.ofReal (r^(-(h:ℝ)))*ENNReal.ofReal ((C*r)^h) = ENNReal.ofReal (C^h) := by
  rw [← ENNReal.ofReal_mul (by positivity),Real.rpow_neg hr.le,Real.rpow_natCast,mul_pow]
  congr 1
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
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

theorem gaussianDirectionMass_measurable (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ) :
    Measurable (gaussianDirectionMass (h := h) ν r) := by
  apply Measurable.const_mul
  let S : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

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

theorem gaussian_direction_mass_second_moment
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (k : ℕ)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ k →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      (gaussianDirectionMass ν (1/(2:ℝ)^k) A)^2 ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant)^h)*
        (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1) := by
  simp only [gaussianDirectionMass,mul_pow]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  calc
    _ ≤ (ENNReal.ofReal ((1/(2:ℝ)^k)^(-(h:ℝ))))^2*
        (ENNReal.ofReal ((2*gaussianPairBandConstant*(1/(2:ℝ)^k)^2)^h)*
          (ENNReal.ofReal (K*(1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))+1)) := by
      exact mul_le_mul_right
        (gaussian_direction_second_moment_frostman ν hK hq k hmass hball hchart) _
    _ = _ := by
      rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
        (mul_nonneg (by norm_num) gaussianPairBandConstant_pos.le)]
      rw [mul_pow]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianCloseMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Localized pairs in the actual Gaussian direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianDirectionSlice_close_identity (ν : Measure (Sphere d)) [SFinite ν]
    (A : Fin h → Space d) (r ρ : ℝ) :
    ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
        {z | dist z.1 z.2 < ρ} =
      (ENNReal.ofReal (r^(-(h:ℝ))))^2*gaussianDirectionCloseMass ν A r ρ := by
  have hD : MeasurableSet {z : Sphere d × Sphere d | dist z.1 z.2 < ρ} :=
    measurableSet_lt (by fun_prop) measurable_const
  simp only [gaussianDirectionSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hD,
    gaussianDirectionCloseMass,pow_two,mul_assoc]

theorem gaussian_direction_close_average (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) :
    (∫⁻ A : Fin h → Space d, gaussianDirectionCloseMass ν A r ρ ∂gaussianRows d h) =
      ∫⁻ z in {z : Sphere d × Sphere d | dist z.1 z.2 < ρ},
        gaussianRows d h {A | ∀ i,
          |inner ℝ (z.1:Space d) (A i)| ≤ r ∧ |inner ℝ (z.2:Space d) (A i)| ≤ r} ∂ν.prod ν := by
  let D : Set (Sphere d × Sphere d) := {z | dist z.1 z.2 < ρ}
  let S : Set ((Fin h → Space d) × (Sphere d × Sphere d)) := {p | ∀ i,
    |inner ℝ (p.2.1:Space d) (p.1 i)| ≤ r ∧ |inner ℝ (p.2.2:Space d) (p.1 i)| ≤ r}
  have hD : MeasurableSet D := measurableSet_lt (by fun_prop) measurable_const
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hsection (A : Fin h → Space d) : Prod.mk A ⁻¹' S =
      (gaussianDirectionBand A r) ×ˢ (gaussianDirectionBand A r) := by
    ext z
    simp only [S,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod]
    exact forall_and
  calc
    _ = ∫⁻ A : Fin h → Space d, ((ν.prod ν).restrict D) (Prod.mk A ⁻¹' S) ∂gaussianRows d h := by
      apply lintegral_congr
      intro A
      rw [hsection,Measure.restrict_apply
        ((gaussianDirectionBand_measurable A r).prod (gaussianDirectionBand_measurable A r))]
      simp only [gaussianDirectionCloseMass,D,inter_comm]
    _ = ((gaussianRows d h).prod ((ν.prod ν).restrict D)) S := (Measure.prod_apply hS).symm
    _ = _ := Measure.prod_apply_symm hS

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianCloseBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale close-pair bounds for normalized direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_close_frostman (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ N →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      gaussianDirectionCloseMass ν A (1/(2:ℝ)^N) (1/(2:ℝ)^g) ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant*(1/(2:ℝ)^N)^2)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  let r : ℝ := 1/(2:ℝ)^N
  let D : Set (Sphere d × Sphere d) := {z | dist z.1 z.2 < 1/(2:ℝ)^g}
  let C := ENNReal.ofReal ((2*gaussianPairBandConstant*r^2)^h)
  let B := ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
    (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))
  rw [gaussian_direction_close_average]
  calc
    _ ≤ ∫⁻ z in D, ENNReal.ofReal
        ((2*gaussianPairBandConstant*r^2/(dist z.1 z.2+r))^h) ∂ν.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hchart] with z hz
      simpa only [Subtype.dist_eq] using gaussianRows_pair_band_chart (h := h)
        (sphere_norm z.1) (sphere_norm z.2) hz (by positivity)
    _ = C * ∫⁻ z in D, ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂ν.prod ν := by
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [gaussian_pair_kernel_factor,ENNReal.ofReal_mul
        (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num)
          gaussianPairBandConstant_pos.le) (sq_nonneg r)) h)]
    _ ≤ C*B := mul_le_mul_right
      (regularized_pair_potential ν hK (Nat.cast_nonneg _) hq g N hg hmass hball) C

theorem gaussian_direction_slice_close_frostman (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ w : Sphere d, ∀ n : ℕ, n ≤ N →
      ν (ball w (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).prod
        (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)))
          {z | dist z.1 z.2 < 1/(2:ℝ)^g} ∂gaussianRows d h) ≤
      ENNReal.ofReal ((2*gaussianPairBandConstant)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  simp_rw [gaussianDirectionSlice_close_identity]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply (mul_le_mul_right (gaussian_direction_close_frostman ν hK hq g N hg hmass hball hchart) _).trans_eq
  rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
    (mul_nonneg (by norm_num) gaussianPairBandConstant_pos.le)]

end Falconer

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

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianVectorBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian bands for unnormalized point differences -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianVectorBandConstant_pos : 0 < gaussianVectorBandConstant := by
  unfold gaussianVectorBandConstant
  linarith [gaussianBandConstant_pos]

theorem gaussian_vector_band (z : Space d) {r : ℝ} (hr : 0 < r) :
    stdGaussian (Space d) {x | |inner ℝ z x| ≤ r} ≤
      ENNReal.ofReal (gaussianVectorBandConstant*r/(‖z‖+r)) := by
  have hc := gaussianBandConstant_pos
  have hd : 0 < ‖z‖+r := add_pos_of_nonneg_of_pos (norm_nonneg _) hr
  by_cases hz : ‖z‖ ≤ r
  · apply (prob_le_one : stdGaussian (Space d) {x | |inner ℝ z x| ≤ r} ≤ 1).trans
    apply ENNReal.one_le_ofReal.mpr
    apply (le_div_iff₀ hd).mpr
    unfold gaussianVectorBandConstant
    nlinarith
  · have hn : 0 < ‖z‖ := lt_trans hr (lt_of_not_ge hz)
    let u : Space d := ‖z‖⁻¹ • z
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,hn.ne']
    have he : {x : Space d | |inner ℝ z x| ≤ r} =
        {x : Space d | |inner ℝ u x| ≤ r/‖z‖} := by
      ext x
      simp only [mem_ofPred_eq,u,inner_smul_left,conj_trivial,abs_mul,abs_inv,abs_norm]
      rw [inv_mul_eq_div,div_le_div_iff_of_pos_right hn]
    rw [he]
    apply (gaussian_unit_inner_band hu (div_nonneg hr.le hn.le)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hn hd).mpr
    unfold gaussianVectorBandConstant
    have hh := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hz))
      (mul_nonneg hc.le hr.le)
    nlinarith [mul_pos hc (mul_pos hr hn)]

theorem gaussianRows_vector_band (z : Space d) {r : ℝ} (hr : 0 < r) :
    gaussianRows d h {A | ∀ i, |inner ℝ z (A i)| ≤ r} ≤
      ENNReal.ofReal ((gaussianVectorBandConstant*r/(‖z‖+r))^h) := by
  have he : {A : Fin h → Space d | ∀ i, |inner ℝ z (A i)| ≤ r} =
      Set.pi univ (fun _ => {x : Space d | |inner ℝ z x| ≤ r}) := by ext A; simp
  rw [gaussianRows,he,Measure.pi_pi]
  calc
    _ ≤ ∏ _ : Fin h, ENNReal.ofReal (gaussianVectorBandConstant*r/(‖z‖+r)) :=
      Finset.prod_le_prod' (fun _ _ => gaussian_vector_band z hr)
    _ = _ := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ← ENNReal.ofReal_pow (div_nonneg
          (mul_nonneg gaussianVectorBandConstant_pos.le hr.le) (by positivity))]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Point bands in the actual Gaussian row coordinates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianPointBand_measurable (A : Fin h → Space d) (z : Space h) (r : ℝ) :
    MeasurableSet (gaussianPointBand A z r) := by
  simp only [gaussianPointBand,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem gaussianPointBand_parameter_measure (A : Fin h → Space d) (x : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space h)) {z | x ∈ gaussianPointBand A z r} = ENNReal.ofReal ((2*r)^h) := by
  have he : {z : Space h | x ∈ gaussianPointBand A z r} =
      (fun z => z-gaussianRowCoordinates A x) ⁻¹' coordinateBox h r := by
    ext z
    simp only [gaussianPointBand,coordinateBox,gaussianRowCoordinates,mem_ofPred_eq,
      mem_preimage,PiLp.sub_apply,abs_sub_comm]
  rw [he]
  simpa only [sub_eq_add_neg] using
    (measure_preimage_add_right (volume : Measure (Space h)) (-gaussianRowCoordinates A x)
      (coordinateBox h r)).trans (coordinateBox_volume hr)

theorem gaussianPointBand_integrated_mass (μ : Measure (Space d)) [SFinite μ]
    (A : Fin h → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, μ (gaussianPointBand A z r)) = ENNReal.ofReal ((2*r)^h)*μ univ := by
  let S : Set (Space h × Space d) := {p | p.2 ∈ gaussianPointBand A p.1 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : Space h × Space d | ∀ i, |inner ℝ p.2 (A i)-p.1 i| ≤ r}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  calc
    _ = ((volume : Measure (Space h)).prod μ) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ x, (volume : Measure (Space h)) {z | x ∈ gaussianPointBand A z r} ∂μ :=
      Measure.prod_apply_symm hS
    _ = ∫⁻ _ : Space d, ENNReal.ofReal ((2*r)^h) ∂μ := by
      apply lintegral_congr
      intro x
      exact gaussianPointBand_parameter_measure A x hr
    _ = _ := lintegral_const _

theorem gaussianPointBand_pair_difference (A : Fin h → Space d) (z : Space h) {r : ℝ}
    {x y : Space d} (hx : x ∈ gaussianPointBand A z r) (hy : y ∈ gaussianPointBand A z r) :
    ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r := by
  intro i
  calc
    _ = |(inner ℝ x (A i)-z i)-(inner ℝ y (A i)-z i)| := by rw [inner_sub_left]; congr 1; ring
    _ ≤ |inner ℝ x (A i)-z i|+|inner ℝ y (A i)-z i| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (inner ℝ x (A i)-z i) (inner ℝ y (A i)-z i)
    _ ≤ 2*r := by linarith [hx i,hy i]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Point-pair overlap under the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianPointBand_pair_parameter_bound (A : Fin h → Space d) (x y : Space d)
    {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space h)) {z | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} ≤
      if ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r then ENNReal.ofReal ((2*r)^h) else 0 := by
  split_ifs with hh
  · exact (measure_mono (fun _ hz => hz.1)).trans_eq (gaussianPointBand_parameter_measure A x hr)
  · have he : {z : Space h | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hh (gaussianPointBand_pair_difference A z hz.1 hz.2)
    rw [he,measure_empty]

theorem gaussianPointBand_pair_average (x y : Space d) {r : ℝ} (hr : 0 ≤ r) :
    ((gaussianRows d h).prod (volume : Measure (Space h)))
      {p | x ∈ gaussianPointBand p.1 p.2 r ∧ y ∈ gaussianPointBand p.1 p.2 r} ≤
      ENNReal.ofReal ((2*r)^h)*gaussianRows d h {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r} := by
  let D : Set (Fin h → Space d) := {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r}
  have hD : MeasurableSet D := by
    simp only [D,ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  have hS : MeasurableSet {p : (Fin h → Space d) × Space h |
      x ∈ gaussianPointBand p.1 p.2 r ∧ y ∈ gaussianPointBand p.1 p.2 r} := by
    change MeasurableSet {p : (Fin h → Space d) × Space h |
      (∀ i, |inner ℝ x (p.1 i)-p.2 i| ≤ r) ∧ (∀ i, |inner ℝ y (p.1 i)-p.2 i| ≤ r)}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter <;> apply MeasurableSet.iInter <;> intro i <;>
      exact measurableSet_le (by fun_prop) measurable_const
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ A, D.indicator (fun _ => ENNReal.ofReal ((2*r)^h)) A ∂gaussianRows d h := by
      apply lintegral_mono
      intro A
      change (volume : Measure (Space h))
        {z | x ∈ gaussianPointBand A z r ∧ y ∈ gaussianPointBand A z r} ≤ _
      simpa only [D,indicator_apply,mem_ofPred_eq] using gaussianPointBand_pair_parameter_bound A x y hr
    _ = _ := lintegral_indicator_const hD _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Point-slice second moments from the original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_pair_kernel (x y : Space d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((2*r)^h)*gaussianRows d h
      {A | ∀ i, |inner ℝ (x-y) (A i)| ≤ 2*r} ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2/(dist x y+r))^h) := by
  have hC := gaussianVectorBandConstant_pos
  calc
    _ ≤ ENNReal.ofReal ((2*r)^h)*
        ENNReal.ofReal ((gaussianVectorBandConstant*(2*r)/(‖x-y‖+2*r))^h) :=
      mul_le_mul_right (gaussianRows_vector_band (x-y) (by positivity)) _
    _ = ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2/(dist x y+2*r))^h) := by
      rw [← ENNReal.ofReal_mul (by positivity),← mul_pow]
      congr 2
      rw [dist_eq_norm]
      field_simp
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized point slices in Gaussian row coordinates -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianPointSliceMeasure_univ (μ : Measure (Space d))
    (A : Fin h → Space d) (z : Space h) (r : ℝ) :
    gaussianPointSliceMeasure μ A z r univ = gaussianPointMass μ r (A,z) := by
  simp [gaussianPointSliceMeasure,gaussianPointMass,Measure.smul_apply]

theorem gaussianPointMass_measurable (μ : Measure (Space d)) [SFinite μ] (r : ℝ) :
    Measurable (gaussianPointMass (h := h) μ r) := by
  apply Measurable.const_mul
  let S : Set (((Fin h → Space d) × Space h) × Space d) :=
    {p | p.2 ∈ gaussianPointBand p.1.1 p.1.2 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
      ∀ i, |inner ℝ p.2 (p.1.1 i)-p.1.2 i| ≤ r}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

theorem gaussianPointMass_integrated (μ : Measure (Space d)) [SFinite μ]
    (A : Fin h → Space d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : Space h, gaussianPointMass μ r (A,z)) = ENNReal.ofReal ((2:ℝ)^h)*μ univ := by
  simp only [gaussianPointMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,gaussianPointBand_integrated_mass μ A hr.le,
    ← mul_assoc,gaussian_band_normalization hr (by norm_num : (0:ℝ) ≤ 2)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointClose
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Localized pairs of Gaussian point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianPointSlice_close_identity (μ : Measure (Space d)) [SFinite μ]
    (p : (Fin h → Space d) × Space h) (r ρ : ℝ) :
    ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
        {z | dist z.1 z.2 < ρ} =
      (ENNReal.ofReal (r^(-(h:ℝ))))^2*gaussianPointCloseMass μ p r ρ := by
  have hD : MeasurableSet {z : Space d × Space d | dist z.1 z.2 < ρ} :=
    measurableSet_lt (by fun_prop) measurable_const
  simp only [gaussianPointSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hD,
    gaussianPointCloseMass,pow_two,mul_assoc]

theorem gaussian_point_close_average (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) (ρ : ℝ) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointCloseMass μ p r ρ
      ∂(gaussianRows d h).prod volume) ≤
      ∫⁻ z in {z : Space d × Space d | dist z.1 z.2 < ρ}, ENNReal.ofReal ((2*r)^h)*
        gaussianRows d h {A | ∀ i, |inner ℝ (z.1-z.2) (A i)| ≤ 2*r} ∂μ.prod μ := by
  let D : Set (Space d × Space d) := {z | dist z.1 z.2 < ρ}
  let S : Set (((Fin h → Space d) × Space h) × (Space d × Space d)) :=
    {p | p.2.1 ∈ gaussianPointBand p.1.1 p.1.2 r ∧ p.2.2 ∈ gaussianPointBand p.1.1 p.1.2 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × (Space d × Space d) |
      (∀ i, |inner ℝ p.2.1 (p.1.1 i)-p.1.2 i| ≤ r) ∧
      (∀ i, |inner ℝ p.2.2 (p.1.1 i)-p.1.2 i| ≤ r)}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter <;> apply MeasurableSet.iInter <;> intro i <;>
      exact measurableSet_le (by fun_prop) measurable_const
  have hsection (p : (Fin h → Space d) × Space h) : Prod.mk p ⁻¹' S =
      (gaussianPointBand p.1 p.2 r) ×ˢ (gaussianPointBand p.1 p.2 r) := rfl
  calc
    _ = ∫⁻ p : (Fin h → Space d) × Space h, ((μ.prod μ).restrict D) (Prod.mk p ⁻¹' S)
        ∂(gaussianRows d h).prod volume := by
      apply lintegral_congr
      intro p
      rw [hsection,Measure.restrict_apply
        ((gaussianPointBand_measurable p.1 p.2 r).prod (gaussianPointBand_measurable p.1 p.2 r))]
      simp only [gaussianPointCloseMass,D,inter_comm]
    _ = (((gaussianRows d h).prod volume).prod ((μ.prod μ).restrict D)) S :=
      (Measure.prod_apply hS).symm
    _ = ∫⁻ z in D, ((gaussianRows d h).prod (volume : Measure (Space h)))
        {p | z.1 ∈ gaussianPointBand p.1 p.2 r ∧ z.2 ∈ gaussianPointBand p.1 p.2 r} ∂μ.prod μ :=
      Measure.prod_apply_symm hS
    _ ≤ _ := lintegral_mono (fun z => gaussianPointBand_pair_average z.1 z.2 hr)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointCloseBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Localized finite-scale second moments for point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_close_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ N →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointCloseMass μ p (1/(2:ℝ)^N) (1/(2:ℝ)^g) ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant*(1/(2:ℝ)^N)^2)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  let r : ℝ := 1/(2:ℝ)^N
  let D : Set (Space d × Space d) := {z | dist z.1 z.2 < 1/(2:ℝ)^g}
  let C := ENNReal.ofReal ((4*gaussianVectorBandConstant*r^2)^h)
  let B := ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
    (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q))))
  have hC := gaussianVectorBandConstant_pos
  apply (gaussian_point_close_average μ (by positivity) (1/(2:ℝ)^g)).trans
  calc
    _ ≤ ∫⁻ z in D, ENNReal.ofReal
        ((4*gaussianVectorBandConstant*r^2/(dist z.1 z.2+r))^h) ∂μ.prod μ :=
      lintegral_mono (fun z => gaussian_point_pair_kernel z.1 z.2 (by dsimp [r]; positivity))
    _ = C * ∫⁻ z in D, ENNReal.ofReal ((1/(dist z.1 z.2+r))^(h:ℝ)) ∂μ.prod μ := by
      rw [← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      rw [Real.rpow_natCast,← ENNReal.ofReal_mul (by positivity),← mul_pow]
      congr 2
      ring
    _ ≤ C*B := mul_le_mul_right
      (regularized_pair_potential μ hK (Nat.cast_nonneg _) hq g N hg hmass hball) C

theorem gaussian_point_slice_close_frostman (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {K q : ℝ} (hK : 0 ≤ K) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ n : ℕ, n ≤ N →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)).prod
        (gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)))
          {z | dist z.1 z.2 < 1/(2:ℝ)^g} ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal ((4*gaussianVectorBandConstant)^h)*
        ENNReal.ofReal (K*((2:ℝ)^g)^((h:ℝ)-q)*
          (1+(2:ℝ)^(h:ℝ)/(1-(2:ℝ)^((h:ℝ)-q)))) := by
  simp_rw [gaussianPointSlice_close_identity]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply (mul_le_mul_right (gaussian_point_close_frostman μ hK hq g N hg hmass hball) _).trans_eq
  rw [← mul_assoc,gaussian_squared_band_normalization (by positivity)
    (mul_nonneg (by norm_num) gaussianVectorBandConstant_pos.le)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMomentWeights
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dyadic weights of the actual point and direction pair moments -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_moment_weight
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {Kt t C : ℝ} (hKt : 0 ≤ Kt) (ht : (h:ℝ) < t) (g N : ℕ) (hg : g ≤ N)
    (hmass : μ univ ≤ 1)
    (hball : ∀ x : Space d, ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kt*(1/(2:ℝ)^j)^t))
    (hC : (4*gaussianVectorBandConstant)^h*Kt*gaussianFrostmanFactor h t ≤ C) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)).prod
        (gaussianPointSliceMeasure μ p.1 p.2 (1/(2:ℝ)^N)))
        {z | dist z.1 z.2 < 2*((1/(2:ℝ)^g)/2)} ∂(gaussianRows d h).prod volume) ≤
      ENNReal.ofReal (C*((2:ℝ)^g)^((h:ℝ)-t)) := by
  have hVC := gaussianVectorBandConstant_pos
  have hr : (2:ℝ)*((1/(2:ℝ)^g)/2) = 1/(2:ℝ)^g := by ring
  rw [hr]
  apply (gaussian_point_slice_close_frostman μ hKt ht g N hg hmass hball).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (4*gaussianVectorBandConstant)^h)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ((4*gaussianVectorBandConstant)^h*Kt*gaussianFrostmanFactor h t)*
      ((2:ℝ)^g)^((h:ℝ)-t) := by unfold gaussianFrostmanFactor; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)

theorem gaussian_direction_moment_weight
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {Kq q C : ℝ} (hKq : 0 ≤ Kq) (hq : (h:ℝ) < q) (g N : ℕ) (hg : g ≤ N)
    (hmass : ν univ ≤ 1)
    (hball : ∀ x : Sphere d, ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d))
    (hC : (2*gaussianPairBandConstant)^h*Kq*gaussianFrostmanFactor h q ≤ C) :
    (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).prod
        (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)))
        {z | dist z.1 z.2 < 2*((1/(2:ℝ)^g)/2)} ∂gaussianRows d h) ≤
      ENNReal.ofReal (C*((2:ℝ)^g)^((h:ℝ)-q)) := by
  have hPC := gaussianPairBandConstant_pos
  have hr : (2:ℝ)*((1/(2:ℝ)^g)/2) = 1/(2:ℝ)^g := by ring
  rw [hr]
  apply (gaussian_direction_slice_close_frostman ν hKq hq g N hg hmass hball hchart).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*gaussianPairBandConstant)^h)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ((2*gaussianPairBandConstant)^h*Kq*gaussianFrostmanFactor h q)*
      ((2:ℝ)^g)^((h:ℝ)-q) := by unfold gaussianFrostmanFactor; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)

theorem gaussian_direction_total_moment_bound
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {Kq q C : ℝ} (hKq : 0 ≤ Kq) (hq : (h:ℝ) < q) (N : ℕ)
    (hmass : ν univ ≤ 1)
    (hball : ∀ x : Sphere d, ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Kq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space d) (z.2:Space d))
    (hC : (2*gaussianPairBandConstant)^h*(|Kq*gaussianFrostmanFactor h q|+1) ≤ C) :
    (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν (1/(2:ℝ)^N) A)^2
      ∂gaussianRows d h) ≤ ENNReal.ofReal C := by
  have hPC := gaussianPairBandConstant_pos
  apply (gaussian_direction_mass_second_moment ν hKq hq N hmass hball hchart).trans
  have hb : ENNReal.ofReal (Kq*gaussianFrostmanFactor h q)+1 ≤
      ENNReal.ofReal (|Kq*gaussianFrostmanFactor h q|+1) := by
    rw [ENNReal.ofReal_add (abs_nonneg _) zero_le_one,ENNReal.ofReal_one]
    exact add_le_add (ENNReal.ofReal_le_ofReal (le_abs_self _)) le_rfl
  apply (mul_le_mul' le_rfl hb).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*gaussianPairBandConstant)^h)]
  exact ENNReal.ofReal_le_ofReal hC

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowMap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear maps and kernel planes for the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem coordinate_norm_le_card_mul (x : Space h) {r : ℝ}
    (hx : ∀ i, |x i| ≤ r) : ‖x‖ ≤ (h:ℝ)*r := by
  calc
    _ = ‖∑ i : Fin h, x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := by
      exact congrArg norm ((EuclideanSpace.basisFun (Fin h) ℝ).sum_repr x).symm
    _ ≤ ∑ i : Fin h, ‖x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := norm_sum_le _ _
    _ = ∑ i : Fin h, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one,mul_one]
    _ ≤ ∑ _ : Fin h, r := Finset.sum_le_sum (fun i _ => hx i)
    _ = _ := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSlabBox
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive Gaussian mass in a bounded coordinate slab -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

theorem gaussian_lower_volume_bounded (S : Set (Space n)) (hS : MeasurableSet S)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x ∈ S, ‖x‖ ≤ B) :
    ENNReal.ofReal (gaussianVolumeNormalization n*Real.exp (-(1/2:ℝ)*B^2))*volume S ≤
      stdGaussian (Space n) S := by
  rw [← normalizedGaussianLebesgue_eq_standard,normalizedGaussianLebesgue,
    Measure.smul_apply,smul_eq_mul,gaussianLebesgue,withDensity_apply _ hS,
    ENNReal.ofReal_mul (by unfold gaussianVolumeNormalization; positivity)]
  rw [mul_assoc]
  apply mul_le_mul_right
  rw [← setLIntegral_const]
  apply setLIntegral_mono' hS
  intro x hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hh := hbound x hx
  nlinarith [norm_nonneg x]

theorem coordinateSlabBox_measurable (c : Space (n+1)) (r ρ : ℝ) :
    MeasurableSet (coordinateSlabBox c r ρ) := by
  simp only [coordinateSlabBox,ofPred_and,ofPred_forall]
  exact (measurableSet_le (by fun_prop) measurable_const).inter
    (MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const))

theorem coordinateSlabBox_volume (c : Space (n+1)) {r ρ : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) :
    volume (coordinateSlabBox c r ρ) = ENNReal.ofReal ((2*r)*(2*ρ)^n) := by
  rw [← (PiLp.volume_preserving_toLp (Fin (n+1))).measure_preimage
    (coordinateSlabBox_measurable c r ρ).nullMeasurableSet]
  have he : (@WithLp.toLp 2 (Fin (n+1) → ℝ)) ⁻¹' coordinateSlabBox c r ρ =
      Set.pi univ (Fin.cases (Icc (-r) r)
        (fun i : Fin n => Icc (c i.succ-ρ) (c i.succ+ρ))) := by
    ext x
    simp only [mem_preimage,coordinateSlabBox,mem_ofPred_eq,mem_pi,mem_univ,true_implies,
      Fin.forall_fin_succ,Fin.cases_zero,Fin.cases_succ,mem_Icc,abs_le]
    constructor
    · rintro ⟨hx,ht⟩
      exact ⟨hx,fun i => by have hh := ht i; constructor <;> linarith [hh.1,hh.2]⟩
    · rintro ⟨hx,ht⟩
      exact ⟨hx,fun i => by have hh := ht i; constructor <;> linarith [hh.1,hh.2]⟩
  rw [he,volume_pi_pi,Fin.prod_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Real.volume_Icc,sub_neg_eq_add,
    ← two_mul,show ∀ a : ℝ, a+ρ-(a-ρ) = 2*ρ by intro a; ring,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*ρ),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)]

theorem coordinateSlabBox_distance (c : Space (n+1)) {r ρ : ℝ}
    (hrρ : r ≤ ρ) (hc : |c 0| ≤ ρ) {x : Space (n+1)}
    (hx : x ∈ coordinateSlabBox c r ρ) : ‖x-c‖ ≤ (n+1:ℝ)*(2*ρ) := by
  rw [show (n+1:ℝ) = ((n+1:ℕ):ℝ) by norm_cast]
  apply coordinate_norm_le_card_mul
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change |x 0-c 0| ≤ 2*ρ
    calc
      _ ≤ |x 0|+|c 0| := abs_sub _ _
      _ ≤ 2*ρ := by linarith [hx.1]
  · change |x j.succ-c j.succ| ≤ 2*ρ
    have hnonneg : 0 ≤ ρ := (abs_nonneg _).trans hc
    exact (hx.2 j).trans (by linarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLocalBand
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Band mass inside a fixed neighborhood of a transverse row -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

theorem gaussian_local_band_lower {w b : Space (n+1)}
    (hw : ‖w‖ = 1) (hb : ‖b‖ ≤ 1) {r ρ : ℝ}
    (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwb : |inner ℝ w b| ≤ ρ) :
    ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) ≤
      stdGaussian (Space (n+1))
        {x | ‖x-b‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r} := by
  let u : Space (n+1) := EuclideanSpace.basisFun (Fin (n+1)) ℝ 0
  let e : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) := (ℝ ∙ (u-w))ᗮ.reflection
  have he : e u = w := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0).trans hw.symm)
  let c := e.symm b
  have hc : |c 0| ≤ ρ := by
    have hi : c 0 = inner ℝ w b := by
      rw [← he,← e.apply_symm_apply b,e.inner_map_map]
      exact (EuclideanSpace.basisFun_inner (Fin (n+1)) ℝ _ 0).symm
    rwa [hi]
  have hn (x : Space (n+1)) (hx : x ∈ coordinateSlabBox c r ρ) :
      ‖x‖ ≤ 1+(n+1:ℝ)*(2*ρ) := by
    calc
      _ ≤ ‖x-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (x-c) c
      _ ≤ (n+1:ℝ)*(2*ρ)+1 := add_le_add (coordinateSlabBox_distance c hrρ hc hx)
        (by simpa only [c,e.symm.norm_map] using hb)
      _ = _ := by ring
  have hl := gaussian_lower_volume_bounded (coordinateSlabBox c r ρ)
    (coordinateSlabBox_measurable c r ρ) (by positivity) hn
  rw [coordinateSlabBox_volume c hr hρ,← ENNReal.ofReal_mul
    (by unfold gaussianVolumeNormalization; positivity)] at hl
  have hl' : ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) ≤
      stdGaussian (Space (n+1)) (coordinateSlabBox c r ρ) := by
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    unfold gaussianLocalBandConstant
    congr 1
    ring
  let T : Set (Space (n+1)) :=
    {x | ‖x-b‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r}
  have hT : MeasurableSet T := by
    simp only [T,ofPred_and]
    apply MeasurableSet.inter
    · exact measurableSet_le (by fun_prop) measurable_const
    · exact measurableSet_le (by fun_prop) measurable_const
  have hs : coordinateSlabBox c r ρ ⊆ e ⁻¹' T := by
    intro x hx
    constructor
    · rw [← e.apply_symm_apply b,← e.map_sub,e.norm_map]
      exact coordinateSlabBox_distance c hrρ hc hx
    · rw [← he,e.inner_map_map]
      simpa only [u,EuclideanSpace.basisFun_inner] using hx.1
  calc
    _ ≤ stdGaussian (Space (n+1)) (coordinateSlabBox c r ρ) := hl'
    _ ≤ stdGaussian (Space (n+1)) (e ⁻¹' T) := measure_mono hs
    _ = stdGaussian (Space (n+1)) T := by
      rw [← Measure.map_apply e.continuous.measurable hT,stdGaussian_map]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianControlledRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive band mass on uniformly controlled Gaussian row parameters -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem gaussianRowNeighborhood_measurable (B : Fin h → Space (n+1)) (ε : ℝ) :
    MeasurableSet (gaussianRowNeighborhood B ε) := by
  simp only [gaussianRowNeighborhood,ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianRows_controlled_band_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) {w : Space (n+1)} (hw : ‖w‖ = 1)
    {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ i, |inner ℝ w (B i)| ≤ ρ) :
    ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h) ≤
      gaussianRows (n+1) h ({A | ∀ i, |inner ℝ w (A i)| ≤ r} ∩
        gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  have he : {A : Fin h → Space (n+1) | ∀ i, |inner ℝ w (A i)| ≤ r} ∩
      gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)) =
      Set.pi univ (fun i => {x | ‖x-B i‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r}) := by
    ext A
    simp only [mem_inter_iff,mem_ofPred_eq,gaussianRowNeighborhood,mem_pi,mem_univ,true_implies]
    constructor
    · rintro ⟨ha,hb⟩ i
      exact ⟨hb i,ha i⟩
    · intro ha
      exact ⟨fun i => (ha i).2,fun i => (ha i).1⟩
  rw [he,gaussianRows,Measure.pi_pi]
  calc
    _ = ∏ _ : Fin h, ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow]
      unfold gaussianLocalBandConstant gaussianVolumeNormalization
      positivity
    _ ≤ _ := Finset.prod_le_prod' (fun i _ => gaussian_local_band_lower hw (hB i) hr hrρ hρ (hwB i))

theorem direction_band_first_moment {d : ℕ}
    (γ : Measure (Fin h → Space d)) [SFinite γ]
    (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ) :
    (∫⁻ A : Fin h → Space d, ν (gaussianDirectionBand A r) ∂γ) =
      ∫⁻ w : Sphere d, γ {A | ∀ i, |inner ℝ (w:Space d) (A i)| ≤ r} ∂ν := by
  let S : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact (Measure.prod_apply hS).symm.trans (Measure.prod_apply_symm hS)

theorem gaussian_controlled_direction_mean_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) (ν : Measure (Sphere (n+1))) [SFinite ν]
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ) :
    ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*ν univ ≤
      ∫⁻ A : Fin h → Space (n+1), gaussianDirectionMass ν r A
        ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  simp only [gaussianDirectionMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,direction_band_first_moment]
  have hl : ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h)*ν univ ≤
      ∫⁻ w : Sphere (n+1), ((gaussianRows (n+1) h).restrict
        (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))
        {A | ∀ i, |inner ℝ (w:Space (n+1)) (A i)| ≤ r} ∂ν := by
    rw [← lintegral_const]
    apply lintegral_mono_ae
    filter_upwards [hwB] with w hw
    rw [Measure.restrict_apply]
    · exact gaussianRows_controlled_band_lower B hB (sphere_norm w) hr.le hrρ hρ hw
    · simp only [ofPred_forall]
      exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  calc
    _ = ENNReal.ofReal (r^(-(h:ℝ)))*
        (ENNReal.ofReal ((gaussianLocalBandConstant n ρ*r)^h)*ν univ) := by
      rw [← mul_assoc,gaussian_band_normalization hr]
      unfold gaussianLocalBandConstant gaussianVolumeNormalization
      positivity
    _ ≤ _ := mul_le_mul_right hl _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianIncidenceAverage
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incidence averaging for the original point and direction labels -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_band_label_average
    (ξ : Measure (Space d × Sphere d)) [SFinite ξ]
    (A : Fin h → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, ξ {t | t.1 ∈ gaussianPointBand A z r}) =
      ENNReal.ofReal ((2*r)^h)*ξ univ := by
  let S : Set (Space h × (Space d × Sphere d)) := {p | p.2.1 ∈ gaussianPointBand A p.1 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : Space h × (Space d × Sphere d) |
      ∀ i, |inner ℝ p.2.1 (A i)-p.1 i| ≤ r}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  calc
    _ = ((volume : Measure (Space h)).prod ξ) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ t : Space d × Sphere d, (volume : Measure (Space h))
        {z | t.1 ∈ gaussianPointBand A z r} ∂ξ := Measure.prod_apply_symm hS
    _ = ∫⁻ _ : Space d × Sphere d, ENNReal.ofReal ((2*r)^h) ∂ξ := by
      apply lintegral_congr
      intro t
      exact gaussianPointBand_parameter_measure A t.1 hr
    _ = _ := lintegral_const _

theorem gaussian_incidence_raw_point_average
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (_hE : MeasurableSet E)
    (A : Fin h → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r)))) =
      ENNReal.ofReal ((2*r)^h)*(μ.prod ν) (E ∩ (univ ×ˢ (gaussianDirectionBand A r))) := by
  let F := E ∩ (univ ×ˢ (gaussianDirectionBand A r))
  have hh := gaussian_point_band_label_average ((μ.prod ν).restrict F) A hr
  have he (z : Space h) : ((μ.prod ν).restrict F) {t | t.1 ∈ gaussianPointBand A z r} =
      (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r))) := by
    rw [Measure.restrict_apply (show MeasurableSet {t : Space d × Sphere d |
      t.1 ∈ gaussianPointBand A z r} from
        (gaussianPointBand_measurable A z r).preimage measurable_fst)]
    congr 1
    ext t
    simp only [F,mem_inter_iff,mem_prod,mem_univ,mem_ofPred_eq,true_and]
    tauto
  simpa only [he,Measure.restrict_apply_univ,F] using hh

theorem gaussian_slice_incidence_point_average
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (A : Fin h → Space d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
      (gaussianDirectionSliceMeasure ν A r) E) =
      ENNReal.ofReal ((2:ℝ)^h)*
        gaussianDirectionMass (((μ.prod ν).restrict E).map Prod.snd) r A := by
  have he (z : Space h) : (gaussianPointSliceMeasure μ A z r).prod
      (gaussianDirectionSliceMeasure ν A r) E =
      (ENNReal.ofReal (r^(-(h:ℝ))))^2*
        (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r))) := by
    simp only [gaussianPointSliceMeasure,gaussianDirectionSliceMeasure,Measure.prod_smul_left,
      Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,
      Measure.restrict_apply hE,pow_two,mul_assoc]
  simp_rw [he]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    gaussian_incidence_raw_point_average μ ν E hE A hr.le]
  have hmap : (((μ.prod ν).restrict E).map Prod.snd) (gaussianDirectionBand A r) =
      (μ.prod ν) (E ∩ (univ ×ˢ (gaussianDirectionBand A r))) := by
    rw [Measure.map_apply measurable_snd (gaussianDirectionBand_measurable A r),
      Measure.restrict_apply ((gaussianDirectionBand_measurable A r).preimage measurable_snd)]
    congr 1
    ext t
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]
    tauto
  rw [gaussianDirectionMass,hmap,pow_two]
  calc
    _ = (ENNReal.ofReal (r^(-(h:ℝ)))*ENNReal.ofReal ((2*r)^h))*
        (ENNReal.ofReal (r^(-(h:ℝ)))*(μ.prod ν) (E ∩ (univ ×ˢ gaussianDirectionBand A r))) := by ac_rfl
    _ = _ := by rw [gaussian_band_normalization hr (by norm_num : (0:ℝ) ≤ 2)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianControlledIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-label incidence on the uniformly controlled row chart -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem incidence_direction_ae (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space (n+1) × Sphere (n+1))) {P : Sphere (n+1) → Prop}
    (hP : ∀ᵐ w ∂ν, P w) :
    ∀ᵐ w ∂(((μ.prod ν).restrict E).map Prod.snd), P w := by
  have hd : ((μ.prod ν).restrict E).map Prod.snd ≤ (μ univ) • ν := by
    calc
      _ ≤ (μ.prod ν).map Prod.snd := Measure.map_mono Measure.restrict_le_self measurable_snd
      _ = _ := Measure.map_snd_prod
  exact (Measure.absolutelyContinuous_of_le hd).ae_le (Measure.ae_smul_measure hP _)

theorem gaussian_controlled_incidence_mean_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E ≤
      ∫⁻ A : Fin h → Space (n+1), (∫⁻ z : Space h,
        (gaussianPointSliceMeasure μ A z r).prod (gaussianDirectionSliceMeasure ν A r) E)
        ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  simp_rw [gaussian_slice_incidence_point_average μ ν E hE _ hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hh := gaussian_controlled_direction_mean_lower B hB
    (((μ.prod ν).restrict E).map Prod.snd) hr hrρ hρ (incidence_direction_ae μ ν E hwB)
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply_univ] at hh
  simpa only [mul_assoc] using mul_le_mul_right hh (ENNReal.ofReal ((2:ℝ)^h))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBallTruncation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball-mass deletion for the Gaussian direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_ball_deletion (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {r ρ : ℝ} {T B : ℝ≥0∞} (hT : 0 < T)
    (hpair : (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
        {z | dist z.1 z.2 < ρ} ∂gaussianRows d h) ≤ B) :
    (∫⁻ A : Fin h → Space d,
      gaussianDirectionSliceMeasure ν A r
        {w | T < gaussianDirectionSliceMeasure ν A r (ball w ρ)} ∂gaussianRows d h) ≤ T⁻¹*B := by
  calc
    _ ≤ ∫⁻ A : Fin h → Space d, T⁻¹*
        ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
          {z | dist z.1 z.2 < ρ} ∂gaussianRows d h :=
      lintegral_mono (fun A => excessive_ball_mass (gaussianDirectionSliceMeasure ν A r) ρ hT.ne')
    _ = T⁻¹*∫⁻ A : Fin h → Space d,
        ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
          {z | dist z.1 z.2 < ρ} ∂gaussianRows d h :=
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hT.ne')
    _ ≤ _ := mul_le_mul_right hpair _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPointTruncation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ball-mass deletion for the Gaussian point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_ball_deletion (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {r ρ : ℝ} {T B : ℝ≥0∞} (hT : 0 < T)
    (hpair : (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
        {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume) ≤ B) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointSliceMeasure μ p.1 p.2 r
        {x | T < gaussianPointSliceMeasure μ p.1 p.2 r (ball x ρ)}
          ∂(gaussianRows d h).prod volume) ≤ T⁻¹*B := by
  calc
    _ ≤ ∫⁻ p : (Fin h → Space d) × Space h, T⁻¹*
        ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
          {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume :=
      lintegral_mono (fun p => excessive_ball_mass (gaussianPointSliceMeasure μ p.1 p.2 r) ρ hT.ne')
    _ = T⁻¹*∫⁻ p : (Fin h → Space d) × Space h,
        ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
          {z | dist z.1 z.2 < ρ} ∂(gaussianRows d h).prod volume :=
      lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hT.ne')
    _ ≤ _ := mul_le_mul_right hpair _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBallMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint measurability of the ball tests used to prune Gaussian slices -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_ball_mass_measurable (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) :
    Measurable (fun p : (Fin h → Space d) × Sphere d =>
      gaussianDirectionSliceMeasure ν p.1 r (ball p.2 ρ)) := by
  simp only [gaussianDirectionSliceMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_ball]
  apply Measurable.const_mul
  let S : Set (((Fin h → Space d) × Sphere d) × Sphere d) :=
    {p | dist p.2 p.1.2 < ρ ∧ ∀ i, |inner ℝ (p.2:Space d) (p.1.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_and,ofPred_forall]
    apply MeasurableSet.inter (measurableSet_lt (by fun_prop) measurable_const)
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  convert (measurable_measure_prodMk_left (ν := ν) hS) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  congr 1

theorem gaussian_point_ball_mass_measurable (μ : Measure (Space d)) [SFinite μ] (r ρ : ℝ) :
    Measurable (fun p : ((Fin h → Space d) × Space h) × Space d =>
      gaussianPointSliceMeasure μ p.1.1 p.1.2 r (ball p.2 ρ)) := by
  simp only [gaussianPointSliceMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_ball]
  apply Measurable.const_mul
  let S : Set ((((Fin h → Space d) × Space h) × Space d) × Space d) :=
    {p | dist p.2 p.1.2 < ρ ∧ ∀ i, |inner ℝ p.2 (p.1.1.1 i)-p.1.1.2 i| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_and,ofPred_forall]
    apply MeasurableSet.inter (measurableSet_lt (by fun_prop) measurable_const)
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  convert (measurable_measure_prodMk_left (ν := μ) hS) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  congr 1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRestrictedMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Jointly measurable restrictions of the actual Gaussian slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem parameter_restricted_mass_measurable {P X : Type*} [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (B G : Set (P × X)) (hB : MeasurableSet B) (hG : MeasurableSet G) :
    Measurable (fun p : P => (μ.restrict {x | (p,x) ∈ B}) {x | (p,x) ∈ G}) := by
  convert (measurable_measure_prodMk_left (ν := μ) (hG.inter hB)) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  rw [Measure.restrict_apply (show MeasurableSet {x | (p,x) ∈ G} from
    hG.preimage measurable_prodMk_left)]
  rfl

theorem gaussian_direction_restriction_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (r : ℝ)
    (G : Set ((Fin h → Space d) × Sphere d)) (hG : MeasurableSet G) :
    Measurable (fun A : Fin h → Space d =>
      gaussianDirectionSliceMeasure ν A r {w | (A,w) ∈ G}) := by
  simp only [gaussianDirectionSliceMeasure,Measure.smul_apply,smul_eq_mul]
  apply Measurable.const_mul
  let B : Set ((Fin h → Space d) × Sphere d) :=
    {p | ∀ i, |inner ℝ (p.2:Space d) (p.1 i)| ≤ r}
  have hB : MeasurableSet B := by
    simp only [B,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact parameter_restricted_mass_measurable ν B G hB hG

theorem gaussian_point_restriction_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (r : ℝ)
    (G : Set (((Fin h → Space d) × Space h) × Space d)) (hG : MeasurableSet G) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      gaussianPointSliceMeasure μ p.1 p.2 r {x | (p,x) ∈ G}) := by
  simp only [gaussianPointSliceMeasure,Measure.smul_apply,smul_eq_mul]
  apply Measurable.const_mul
  let B : Set (((Fin h → Space d) × Space h) × Space d) :=
    {p | ∀ i, |inner ℝ p.2 (p.1.1 i)-p.1.2 i| ≤ r}
  have hB : MeasurableSet B := by
    simp only [B,ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  exact parameter_restricted_mass_measurable μ B G hB hG

theorem gaussian_direction_bad_ball_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) (T : ℝ≥0∞) :
    Measurable (fun A : Fin h → Space d =>
      gaussianDirectionSliceMeasure ν A r
        {w | T < gaussianDirectionSliceMeasure ν A r (Metric.ball w ρ)}) :=
  gaussian_direction_restriction_mass_measurable ν r _
    (measurableSet_lt measurable_const (gaussian_direction_ball_mass_measurable ν r ρ))

theorem gaussian_point_bad_ball_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (r ρ : ℝ) (T : ℝ≥0∞) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      gaussianPointSliceMeasure μ p.1 p.2 r
        {x | T < gaussianPointSliceMeasure μ p.1 p.2 r (Metric.ball x ρ)}) :=
  gaussian_point_restriction_mass_measurable μ r _
    (measurableSet_lt measurable_const (gaussian_point_ball_mass_measurable μ r ρ))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianFinitePruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous Gaussian slice pruning at the required finite scales -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_direction_finite_ball_deletion
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ C i) :
    (∫⁻ A : Fin h → Space d, gaussianDirectionSliceMeasure ν A δ
      (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)ᶜ ∂gaussianRows d h) ≤
        ∑ i, (T i)⁻¹*C i := by
  classical
  calc
    _ ≤ ∫⁻ A : Fin h → Space d, ∑ i,
        gaussianDirectionSliceMeasure ν A δ
          {w | T i < gaussianDirectionSliceMeasure ν A δ (ball w (2*r i))}
          ∂gaussianRows d h :=
      lintegral_mono (fun A => finiteBallGood_compl_mass _ r T)
    _ = ∑ i, ∫⁻ A : Fin h → Space d, gaussianDirectionSliceMeasure ν A δ
        {w | T i < gaussianDirectionSliceMeasure ν A δ (ball w (2*r i))}
        ∂gaussianRows d h := lintegral_finsetSum _
          (fun i _ => gaussian_direction_bad_ball_mass_measurable ν δ (2*r i) (T i))
    _ ≤ _ := Finset.sum_le_sum (fun i _ => gaussian_direction_ball_deletion ν (hT i) (hp i))

theorem gaussian_point_finite_ball_deletion
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointSliceMeasure μ p.1 p.2 δ
      (finiteBallGood (gaussianPointSliceMeasure μ p.1 p.2 δ) r T)ᶜ
        ∂(gaussianRows d h).prod volume) ≤ ∑ i, (T i)⁻¹*C i := by
  classical
  calc
    _ ≤ ∫⁻ p : (Fin h → Space d) × Space h, ∑ i,
        gaussianPointSliceMeasure μ p.1 p.2 δ
          {x | T i < gaussianPointSliceMeasure μ p.1 p.2 δ (ball x (2*r i))}
          ∂(gaussianRows d h).prod volume :=
      lintegral_mono (fun p => finiteBallGood_compl_mass _ r T)
    _ = ∑ i, ∫⁻ p : (Fin h → Space d) × Space h, gaussianPointSliceMeasure μ p.1 p.2 δ
        {x | T i < gaussianPointSliceMeasure μ p.1 p.2 δ (ball x (2*r i))}
        ∂(gaussianRows d h).prod volume := lintegral_finsetSum _
          (fun i _ => gaussian_point_bad_ball_mass_measurable μ δ (2*r i) (T i))
    _ ≤ _ := Finset.sum_le_sum (fun i _ => gaussian_point_ball_deletion μ (hT i) (hp i))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPairRestrictions
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable original-pair relations in Gaussian slices -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_pair_restriction_mass_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [SFinite μ] [SFinite ν]
    (r : ℝ) (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)))
    (hG : MeasurableSet G) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianDirectionSliceMeasure ν p.1 r)
        {t | (p,t) ∈ G}) := by
  let B : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {p | p.2.1 ∈ gaussianPointBand p.1.1 p.1.2 r ∧ p.2.2 ∈ gaussianDirectionBand p.1.1 r}
  have hB : MeasurableSet B := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × (Space d × Sphere d) |
      (∀ i, |inner ℝ p.2.1 (p.1.1 i)-p.1.2 i| ≤ r) ∧
      ∀ i, |inner ℝ (p.2.2:Space d) (p.1.1 i)| ≤ r}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter
    · exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
    · exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  have hm := parameter_restricted_mass_measurable (μ.prod ν) B G hB hG
  convert (hm.const_mul (ENNReal.ofReal (r^(-(h:ℝ))))).const_mul
    (ENNReal.ofReal (r^(-(h:ℝ)))) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [gaussianPointSliceMeasure,gaussianDirectionSliceMeasure,Measure.prod_smul_left,
    Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,Measure.prod_restrict]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPruningSets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual measurable restrictions used in Gaussian slice selection -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussianPointGood_measurable_joint (μ : Measure (Space d)) [SFinite μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
      p.2 ∈ gaussianPointGood μ δ r T p.1} := by
  change MeasurableSet {p : ((Fin h → Space d) × Space h) × Space d |
    ∀ i, gaussianPointSliceMeasure μ p.1.1 p.1.2 δ (ball p.2 (2*r i)) ≤ T i}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    (gaussian_point_ball_mass_measurable μ δ (2*r i)) measurable_const)

theorem gaussianDirectionGood_measurable_joint (ν : Measure (Sphere d)) [SFinite ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) :
    MeasurableSet {p : (Fin h → Space d) × Sphere d | p.2 ∈ gaussianDirectionGood ν δ r T M p.1} := by
  change MeasurableSet {p : (Fin h → Space d) × Sphere d |
    gaussianDirectionMass ν δ p.1 ≤ M ∧
    ∀ i, gaussianDirectionSliceMeasure ν p.1 δ (ball p.2 (2*r i)) ≤ T i}
  simp only [ofPred_and,ofPred_forall]
  apply MeasurableSet.inter
  · exact measurableSet_le ((gaussianDirectionMass_measurable ν δ).comp measurable_fst) measurable_const
  · exact MeasurableSet.iInter (fun i => measurableSet_le
      (gaussian_direction_ball_mass_measurable ν δ (2*r i)) measurable_const)

omit [Fintype ι] in
theorem gaussianPointGood_ball (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (p : (Fin h → Space d) × Space h) (i : ι) (a : Space d) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p))
      (ball a (r i)) ≤ T i := finiteBallGood_ball_bound _ r T i a

omit [Fintype ι] in
theorem gaussianDirectionGood_mass (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) (M : ℝ≥0∞) (A : Fin h → Space d) :
    ((gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r T M A)) univ ≤ M := by
  by_cases hm : gaussianDirectionMass ν δ A ≤ M
  · calc
      _ ≤ gaussianDirectionSliceMeasure ν A δ univ := Measure.restrict_le_self _
      _ = gaussianDirectionMass ν δ A := by
        simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
      _ ≤ _ := hm
  · have he : gaussianDirectionGood ν δ r T M A = ∅ := by ext w; simp [gaussianDirectionGood,hm]
    simp only [he,Measure.restrict_empty,Measure.coe_zero,Pi.zero_apply]
    exact zero_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incidence on the original labels after the marginal slice restrictions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussianPrunedIncidence_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    Measurable (gaussianPrunedIncidence (h := h) μ ν δ r TP TD M E) := by
  let G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {q | q.2 ∈ E ∧ q.2.1 ∈ gaussianPointGood μ δ r TP q.1 ∧
      q.2.2 ∈ gaussianDirectionGood ν δ r TD M q.1.1}
  have hG : MeasurableSet G := by
    have hp := (gaussianPointGood_measurable_joint (h := h) μ δ r TP).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1,q.2.1)) from by fun_prop)
    have hd := (gaussianDirectionGood_measurable_joint (h := h) ν δ r TD M).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1.1,q.2.2)) from by fun_prop)
    exact (hE.preimage measurable_snd).inter (hp.inter hd)
  convert gaussian_pair_restriction_mass_measurable μ ν δ G hG using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  rw [gaussianPrunedIncidence,Measure.prod_restrict,Measure.restrict_apply hE]
  congr 1

omit [Fintype ι] in
theorem gaussian_pruning_pointwise_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (p : (Fin h → Space d) × Space h) :
    (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E ≤
      gaussianPrunedIncidence μ ν δ r TP TD M E p +
      gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r TP p)ᶜ*M +
      gaussianPointMass μ δ p*gaussianDirectionSliceMeasure ν p.1 δ
        (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)ᶜ +
      (if M < gaussianDirectionMass ν δ p.1 then
        gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 else 0) := by
  have hm : gaussianDirectionSliceMeasure ν p.1 δ univ = gaussianDirectionMass ν δ p.1 := by
    simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
  by_cases hM : gaussianDirectionMass ν δ p.1 ≤ M
  · have hd : gaussianDirectionGood ν δ r TD M p.1 =
        finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD := by
      ext w
      simp only [gaussianDirectionGood,mem_ofPred_eq,hM,true_and]
    have hl := product_restriction_incidence_loss (gaussianPointSliceMeasure μ p.1 p.2 δ)
      (gaussianDirectionSliceMeasure ν p.1 δ) E hE (gaussianPointGood μ δ r TP p)
      (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)
    rw [gaussianPointSliceMeasure_univ,hm] at hl
    simp only [not_lt_of_ge hM,ite_false, if_false,add_zero,gaussianPrunedIncidence,hd]
    exact hl.trans (add_le_add (add_le_add le_rfl (mul_le_mul_right hM _)) le_rfl)
  · have hl : (gaussianPointSliceMeasure μ p.1 p.2 δ).prod
        (gaussianDirectionSliceMeasure ν p.1 δ) E ≤
        gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 := by
      calc
        _ ≤ (gaussianPointSliceMeasure μ p.1 p.2 δ).prod
            (gaussianDirectionSliceMeasure ν p.1 δ) univ := measure_mono (subset_univ _)
        _ = _ := by rw [← univ_prod_univ,Measure.prod_prod,gaussianPointSliceMeasure_univ,hm]
    simp only [lt_of_not_ge hM,ite_true, if_true]
    exact hl.trans (show _ ≤ _ + _ from by
      exact (zero_add _).symm.le.trans (add_le_add bot_le le_rfl))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSliceTail
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianLebesgue_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.normalizedGaussianLebesgue_finite _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direction-slice mass deletion using the proved second moment -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_mass_tail (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {r : ℝ} {T B : ℝ≥0∞} (hT : 0 < T) (hTtop : T ≠ ∞)
    (hmoment : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν r A)^2
      ∂gaussianRows d h) ≤ B) :
    (∫⁻ A in {A : Fin h → Space d | T < gaussianDirectionMass ν r A},
      gaussianDirectionMass ν r A ∂gaussianRows d h) ≤ T⁻¹*B := by
  have hm := gaussianDirectionMass_measurable (h := h) ν r
  have hh := density_tail_mass (gaussianRows d h) (gaussianDirectionMass ν r) hm
    (p := 2) hT hTtop (by norm_num)
  rw [withDensity_apply _ (measurableSet_lt measurable_const hm)] at hh
  norm_num only [show (1-(2:ℝ)) = -1 by norm_num,ENNReal.rpow_neg_one,ENNReal.rpow_two] at hh
  exact hh.trans (mul_le_mul_right hmoment _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLabelCost
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating direction-label deletion costs against the point slices -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_point_weighted_label_integral
    (μ : Measure (Space d)) [SFinite μ] {δ : ℝ} (hδ : 0 < δ)
    (f : (Fin h → Space d) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointMass μ δ p*f p.1
      ∂(gaussianRows d h).prod volume) =
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*∫⁻ A, f A ∂gaussianRows d h := by
  rw [lintegral_prod (fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*f p.1)
    (show AEMeasurable (fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*f p.1)
      ((gaussianRows d h).prod volume) from
        ((gaussianPointMass_measurable μ δ).mul (hf.comp measurable_fst)).aemeasurable)]
  have hi (A : Fin h → Space d) :
      (∫⁻ z : Space h, gaussianPointMass μ δ (A,z)*f A) =
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*f A := by
    rw [lintegral_mul_const (f A) (show Measurable (fun z : Space h => gaussianPointMass μ δ (A,z)) from
      (gaussianPointMass_measurable μ δ).comp
        (show Measurable (fun z : Space h => (A,z)) from by fun_prop)),gaussianPointMass_integrated μ A hδ]
  simp_rw [hi]
  exact lintegral_const_mul _ hf

theorem gaussian_direction_good_compl_mass_measurable
    (ν : Measure (Sphere d)) [SFinite ν] (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    Measurable (fun A : Fin h → Space d => gaussianDirectionSliceMeasure ν A δ
      (finiteBallGood (gaussianDirectionSliceMeasure ν A δ) r T)ᶜ) := by
  have hg : MeasurableSet {p : (Fin h → Space d) × Sphere d |
      p.2 ∈ finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r T} := by
    change MeasurableSet {p : (Fin h → Space d) × Sphere d |
      ∀ i, gaussianDirectionSliceMeasure ν p.1 δ (Metric.ball p.2 (2*r i)) ≤ T i}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (gaussian_direction_ball_mass_measurable ν δ (2*r i)) measurable_const)
  exact gaussian_direction_restriction_mass_measurable ν δ _ hg.compl

theorem gaussian_point_good_compl_mass_measurable
    (μ : Measure (Space d)) [SFinite μ] (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞) :
    Measurable (fun p : (Fin h → Space d) × Space h => gaussianPointSliceMeasure μ p.1 p.2 δ
      (gaussianPointGood μ δ r T p)ᶜ) :=
  gaussian_point_restriction_mass_measurable μ δ _
    (gaussianPointGood_measurable_joint μ δ r T).compl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPruningCosts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All three marginal-pruning costs under the original joint slice law -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_point_pruning_incidence_cost
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (δ : ℝ)
    (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i) (M : ℝ≥0∞)
    (hp : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r T p)ᶜ*M
        ∂(gaussianRows d h).prod volume) ≤ (∑ i, (T i)⁻¹*C i)*M := by
  rw [lintegral_mul_const _ (gaussian_point_good_compl_mass_measurable μ δ r T)]
  exact mul_le_mul_left (gaussian_point_finite_ball_deletion μ δ r T C hT hp) M

theorem gaussian_direction_pruning_incidence_cost
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (hδ : 0 < δ) (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointMass μ δ p*
      gaussianDirectionSliceMeasure ν p.1 δ
        (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r T)ᶜ
        ∂(gaussianRows d h).prod volume) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (T i)⁻¹*C i) := by
  rw [gaussian_point_weighted_label_integral μ hδ _
    (gaussian_direction_good_compl_mass_measurable ν δ r T)]
  exact mul_le_mul_right (gaussian_direction_finite_ball_deletion ν δ r T C hT hp) _

theorem gaussian_mass_pruning_incidence_cost
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (hδ : 0 < δ) {M B : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hp : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν δ A)^2 ∂gaussianRows d h) ≤ B) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      gaussianPointMass μ δ p*(if M < gaussianDirectionMass ν δ p.1 then
        gaussianDirectionMass ν δ p.1 else 0) ∂(gaussianRows d h).prod volume) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
  let S : Set (Fin h → Space d) := {A | M < gaussianDirectionMass ν δ A}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (gaussianDirectionMass_measurable ν δ)
  have hf : Measurable (S.indicator (gaussianDirectionMass ν δ)) :=
    (gaussianDirectionMass_measurable ν δ).indicator hS
  have he (A : Fin h → Space d) :
      (if M < gaussianDirectionMass ν δ A then gaussianDirectionMass ν δ A else 0) =
        S.indicator (gaussianDirectionMass ν δ) A := by
    simp only [Set.indicator_apply,S,mem_ofPred_eq]
  simp_rw [he]
  rw [gaussian_point_weighted_label_integral μ hδ _ hf,lintegral_indicator hS]
  exact mul_le_mul_right (gaussian_direction_mass_tail ν hM hMtop hp) _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPruningLedger
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The combined incidence ledger for the three marginal slice deletions -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_pruning_integral_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure ((Fin h → Space d) × Space h)) (hξ : ξ ≤ (gaussianRows d h).prod volume)
    {δ : ℝ} (hδ : 0 < δ) (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    {M B : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν δ A)^2 ∂gaussianRows d h) ≤ B)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E ∂ξ) ≤
      (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
  let f := gaussianPrunedIncidence (h := h) μ ν δ r TP TD M E
  let a := fun p : (Fin h → Space d) × Space h =>
    gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r TP p)ᶜ*M
  let b := fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*
    gaussianDirectionSliceMeasure ν p.1 δ (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)ᶜ
  let c := fun p : (Fin h → Space d) × Space h =>
    if M < gaussianDirectionMass ν δ p.1 then gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 else 0
  have hf : Measurable f := gaussianPrunedIncidence_measurable μ ν δ r TP TD M E hE
  have ha : Measurable a := (gaussian_point_good_compl_mass_measurable μ δ r TP).mul_const M
  have hb : Measurable b := (gaussianPointMass_measurable μ δ).mul
    ((gaussian_direction_good_compl_mass_measurable ν δ r TD).comp measurable_fst)
  have hia : (∫⁻ p, a p ∂ξ) ≤ (∑ i, (TP i)⁻¹*CP i)*M :=
    (lintegral_mono' hξ le_rfl).trans (gaussian_point_pruning_incidence_cost μ δ r TP CP hTP M hpoint)
  have hib : (∫⁻ p, b p ∂ξ) ≤ (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) :=
    (lintegral_mono' hξ le_rfl).trans (gaussian_direction_pruning_incidence_cost μ ν hδ r TD CD hTD hdir)
  have hic : (∫⁻ p, c p ∂ξ) ≤ (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
    apply (lintegral_mono' hξ le_rfl).trans
    simpa only [c,mul_ite,mul_zero] using gaussian_mass_pruning_incidence_cost μ ν hδ hM hMtop hmoment
  calc
    _ ≤ ∫⁻ p, f p+a p+b p+c p ∂ξ :=
      lintegral_mono (fun p => gaussian_pruning_pointwise_loss μ ν δ r TP TD M E hE p)
    _ = ((∫⁻ p, f p ∂ξ)+(∫⁻ p, a p ∂ξ))+(∫⁻ p, b p ∂ξ)+(∫⁻ p, c p ∂ξ) := by
      rw [lintegral_add_left (show Measurable (fun p => f p+a p+b p) from (hf.add ha).add hb),
        lintegral_add_left (show Measurable (fun p => f p+a p) from hf.add ha),lintegral_add_left hf]
    _ ≤ _ := add_le_add (add_le_add (add_le_add le_rfl hia) hib) hic

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianControlledLedger
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original incidence survives controlled-row marginal pruning -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_controlled_pruning_ledger
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    {M Q : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E ≤
      (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict
          (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)))).prod volume) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*Q) := by
  let G := gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))
  let ξ := ((gaussianRows (n+1) h).restrict G).prod (volume : Measure (Space h))
  have hlo := gaussian_controlled_incidence_mean_lower B hB μ ν E hE hδ hδρ
    (hδ.le.trans hδρ) hwB
  have hraw : Measurable (fun p : (Fin h → Space (n+1)) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E) :=
    gaussian_pair_restriction_mass_measurable μ ν δ (Prod.snd ⁻¹' E) (hE.preimage measurable_snd)
  rw [← lintegral_prod _ (show AEMeasurable
    (fun p : (Fin h → Space (n+1)) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E) ξ
      from hraw.aemeasurable)] at hlo
  exact hlo.trans (gaussian_pruning_integral_loss μ ν ξ
    (Measure.prod_mono Measure.restrict_le_self le_rfl) hδ r TP TD CP CD hTP hTD hM hMtop
    hpoint hdir hmoment E hE)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active original tube-anchor counts in the Gaussian point parameter -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianActiveAnchorCount_eq_sum (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) (z : Space h) :
    (gaussianActiveAnchorCount A S a r z : ℝ≥0∞) =
      ∑ i ∈ S, {v : Space h | a i ∈ gaussianPointBand A v r}.indicator (fun _ => (1:ℝ≥0∞)) z := by
  classical
  simp only [gaussianActiveAnchorCount,Finset.natCast_card_filter,Set.indicator_apply,mem_ofPred_eq]

theorem measurable_gaussianActiveAnchorCount (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) (r : ℝ) :
    Measurable (fun z : Space h => (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)) := by
  simp_rw [gaussianActiveAnchorCount_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  change MeasurableSet {v : Space h | ∀ j, |inner ℝ (a i) (A j)-v j| ≤ r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianActiveAnchorCount_integral (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)) =
      (S.card:ℝ≥0∞)*ENNReal.ofReal ((2*r)^h) := by
  simp_rw [gaussianActiveAnchorCount_eq_sum]
  have hm (i : ι) : MeasurableSet {v : Space h | a i ∈ gaussianPointBand A v r} := by
    change MeasurableSet {v : Space h | ∀ j, |inner ℝ (a i) (A j)-v j| ≤ r}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  rw [lintegral_finsetSum S (fun i _ => measurable_const.indicator (hm i))]
  simp only [lintegral_indicator_const (hm _),one_mul,gaussianPointBand_parameter_measure A _ hr,
    Finset.sum_const,nsmul_eq_mul]

theorem gaussianActiveAnchorCount_exceptional (A : Fin h → Space d)
    (S : Finset ι) (a : ι → Space d) {r : ℝ} (hr : 0 ≤ r)
    {T : ℝ≥0∞} (hT : T ≠ 0) (hTfin : T ≠ ∞) :
    volume {z : Space h | T < (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} ≤
      ((S.card:ℝ≥0∞)*ENNReal.ofReal ((2*r)^h))/T := by
  apply (measure_mono (show {z : Space h | T < (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} ⊆
      {z : Space h | T ≤ (gaussianActiveAnchorCount A S a r z : ℝ≥0∞)} from
    fun _ hz => (show T < _ from hz).le)).trans
  rw [← gaussianActiveAnchorCount_integral A S a hr]
  exact meas_ge_le_lintegral_div (measurable_gaussianActiveAnchorCount A S a r).aemeasurable hT hTfin

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveFamily
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active counts for measurable original-label tube lists -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussianActiveFamily_measurable (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (r : ℝ) :
    Measurable (fun p : ((Fin h → Space d) × Space h) × Sphere d =>
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞)) := by
  classical
  have he (p : ((Fin h → Space d) × Space h) × Sphere d) :
      (gaussianActiveAnchorCount p.1.1 (J p.2) a r p.1.2 : ℝ≥0∞) =
      ∑ i : ι, {q : ((Fin h → Space d) × Space h) × Sphere d |
        i ∈ J q.2 ∧ a i ∈ gaussianPointBand q.1.1 q.1.2 r}.indicator (fun _ => (1:ℝ≥0∞)) p := by
    rw [gaussianActiveAnchorCount_eq_sum]
    simp only [Set.indicator_apply,mem_ofPred_eq]
    calc
      _ = ∑ i ∈ J p.2, (if i ∈ J p.2 ∧ a i ∈ gaussianPointBand p.1.1 p.1.2 r then
          (1:ℝ≥0∞) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hi,true_and]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp only [hi,false_and,ite_false, if_false])
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  apply ((hJ i).preimage measurable_snd).inter
  change MeasurableSet {q : ((Fin h → Space d) × Space h) × Sphere d |
    ∀ j, |inner ℝ (a i) (q.1.1 j)-q.1.2 j| ≤ r}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

omit [Fintype ι] [DecidableEq ι] in
theorem gaussianActiveFamily_exceptional_bound
    (A : Fin h → Space d) (J : Sphere d → Finset ι) (a : ι → Space d)
    {r : ℝ} (hr : 0 ≤ r) {N T : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞) (w : Sphere d) :
    (volume : Measure (Space h)) {z | T < (gaussianActiveAnchorCount A (J w) a r z : ℝ≥0∞)} ≤
      N*ENNReal.ofReal ((2*r)^h)/T := by
  apply (gaussianActiveAnchorCount_exceptional A (J w) a hr hT hTfin).trans
  simp only [div_eq_mul_inv]
  exact mul_le_mul_left (mul_le_mul_left (hN w) _) _

theorem gaussianActiveFamily_slice_count_measurable
    (A : Fin h → Space d) (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (R : ℝ) :
    Measurable (fun p : Space h × Sphere d =>
      (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)) := by
  classical
  have he (p : Space h × Sphere d) :
      (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞) =
      ∑ i : ι, {q : Space h × Sphere d | i ∈ J q.2 ∧ a i ∈ gaussianPointBand A q.1 R}.indicator
        (fun _ => (1:ℝ≥0∞)) p := by
    rw [gaussianActiveAnchorCount_eq_sum]
    simp only [Set.indicator_apply,mem_ofPred_eq]
    calc
      _ = ∑ i ∈ J p.2, (if i ∈ J p.2 ∧ a i ∈ gaussianPointBand A p.1 R then
          (1:ℝ≥0∞) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [hi,true_and]
      _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
        simp only [hi,false_and,ite_false, if_false])
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  apply ((hJ i).preimage measurable_snd).inter
  change MeasurableSet {q : Space h × Sphere d |
    ∀ j, |inner ℝ (a i) (A j)-q.1 j| ≤ R}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)

theorem gaussianActiveFamily_slice_measurable
    (A : Fin h → Space d) (J : Sphere d → Finset ι)
    (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : ι → Space d) (R : ℝ) (T : ℝ≥0∞) :
    MeasurableSet {p : Space h × Sphere d |
      T < (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)} :=
  measurableSet_lt measurable_const (gaussianActiveFamily_slice_count_measurable A J hJ a R)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform masses and support of the pruned original slice laws -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussianPointSliceMeasure_ae_of_ae
    (μ : Measure (Space d)) (A : Fin h → Space d) (z : Space h) (δ : ℝ)
    {P : Space d → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂gaussianPointSliceMeasure μ A z δ, P x := by
  exact Measure.ae_smul_measure (ae_restrict_of_ae hP) _

theorem gaussianPointGood_mass
    (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (δ : ℝ) (r : ι → ℝ) (T : ι → ℝ≥0∞)
    (p : (Fin h → Space d) × Space h) {D : ℝ}
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (i : ι) (hi : D < r i) :
    ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)) univ ≤ T i := by
  let α := (gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r T p)
  have ha : ∀ᵐ x ∂α, x ∈ ball 0 (r i) := by
    filter_upwards [ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ p.1 p.2 δ hμ)] with x hx
    simpa only [mem_ball,dist_zero_right] using hx.trans_lt hi
  have he : α (ball 0 (r i)) = α univ := measure_congr (by
    filter_upwards [ha] with x hx
    exact propext ⟨fun _ => mem_univ x,fun _ => hx⟩)
  rw [← he]
  exact gaussianPointGood_ball μ δ r T p i 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceDirectionDeletion
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incidence cost of direction-dependent exceptional slice parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {Z X W : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace W]

theorem slice_direction_deletion_cost
    (ζ : Measure Z) (α : Z → Measure X) (β : Measure W)
    [SFinite ζ] [SFinite β] [∀ z, SFinite (α z)]
    (D : Set (Z × W)) (hD : MeasurableSet D) (E : Set (X × W))
    {P C : ℝ≥0∞} (hP : ∀ z, α z univ ≤ P)
    (hC : ∀ w, ζ {z | (z,w) ∈ D} ≤ C) :
    (∫⁻ z, ((α z).prod β) (E ∩ (univ ×ˢ {w | (z,w) ∈ D})) ∂ζ) ≤ P*C*β univ := by
  have hm : Measurable (fun z => β {w | (z,w) ∈ D}) := measurable_measure_prodMk_left hD
  calc
    _ ≤ ∫⁻ z, P*β {w | (z,w) ∈ D} ∂ζ := by
      apply lintegral_mono
      intro z
      calc
        _ ≤ ((α z).prod β) (univ ×ˢ {w | (z,w) ∈ D}) := measure_mono inter_subset_right
        _ = α z univ*β {w | (z,w) ∈ D} := by rw [Measure.prod_prod]
        _ ≤ _ := mul_le_mul_left (hP z) _
    _ = P*(ζ.prod β) D := by
      rw [lintegral_const_mul _ hm]
      exact congrArg (fun t => P*t) (Measure.prod_apply hD).symm
    _ ≤ P*(C*β univ) := by
      apply mul_le_mul_right
      rw [Measure.prod_apply_symm hD]
      exact (lintegral_mono hC).trans_eq (lintegral_const _)
    _ = _ := (mul_assoc _ _ _).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveLoss
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cost of deleting excessive active original tube lists -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype κ] [DecidableEq κ]

theorem gaussian_active_loss_in_row
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (A : Fin h → Space d) (E : Set (Space d × Sphere d))
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ z, ((gaussianPointSliceMeasure μ A z δ).restrict
      (gaussianPointGood μ δ r TP (A,z))) univ ≤ P) :
    (∫⁻ z : Space h, gaussianPrunedIncidence μ ν δ r TP TD M
      (E ∩ (univ ×ˢ {w | T < (gaussianActiveAnchorCount A (J w) a R z : ℝ≥0∞)})) (A,z)) ≤
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  let β := (gaussianDirectionSliceMeasure ν A δ).restrict (gaussianDirectionGood ν δ r TD M A)
  let α := fun z : Space h => (gaussianPointSliceMeasure μ A z δ).restrict
    (gaussianPointGood μ δ r TP (A,z))
  have : IsFiniteMeasure β := by change IsFiniteMeasure (Measure.restrict _ _); infer_instance
  have : ∀ z, SFinite (α z) := fun z => by change SFinite (Measure.restrict _ _); infer_instance
  let D : Set (Space h × Sphere d) :=
    {p | T < (gaussianActiveAnchorCount A (J p.2) a R p.1 : ℝ≥0∞)}
  have hD : MeasurableSet D := gaussianActiveFamily_slice_measurable A J hJ a R T
  have hc : ∀ w, (volume : Measure (Space h)) {z | (z,w) ∈ D} ≤
      N*ENNReal.ofReal ((2*R)^h)/T :=
    gaussianActiveFamily_exceptional_bound A J a hR hN hT hTfin
  change (∫⁻ z : Space h, ((α z).prod β) (E ∩ (univ ×ˢ {w | (z,w) ∈ D}))) ≤ _
  have hl := slice_direction_deletion_cost (Z := Space h) (X := Space d) (W := Sphere d)
    (volume : Measure (Space h)) α β D hD E hP hc
  exact hl.trans (mul_le_mul_right (gaussianDirectionGood_mass ν δ r TD M A) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianParameterSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded point-parameter region for bounded original source laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRowNeighborhood_norm {n : ℕ} (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} {A : Fin h → Space (n+1)}
    (hA : A ∈ gaussianRowNeighborhood B ε) (i : Fin h) : ‖A i‖ ≤ ε+1 := by
  calc
    _ ≤ ‖A i-B i‖+‖B i‖ := by simpa only [sub_add_cancel] using norm_add_le (A i-B i) (B i)
    _ ≤ _ := add_le_add (hA i) (hB i)

theorem gaussianPointBand_parameter_bound (A : Fin h → Space d)
    {M D r : ℝ} (_hM : 0 ≤ M) (hA : ∀ i, ‖A i‖ ≤ M)
    {x : Space d} (hx : ‖x‖ ≤ D) {z : Space h} (hz : x ∈ gaussianPointBand A z r) :
    z ∈ coordinateBox h (D*M+r) := by
  intro i
  calc
    |z i| ≤ |inner ℝ x (A i)|+|inner ℝ x (A i)-z i| := by
      calc
        _ = |inner ℝ x (A i)-(inner ℝ x (A i)-z i)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    _ ≤ ‖x‖*‖A i‖+r := add_le_add (abs_real_inner_le_norm _ _) (hz i)
    _ ≤ D*M+r := add_le_add
      (mul_le_mul hx (hA i) (norm_nonneg _) ((norm_nonneg x).trans hx)) le_rfl

theorem gaussian_point_mass_zero_outside_box
    (μ : Measure (Space d)) (A : Fin h → Space d)
    {M D r : ℝ} (hM : 0 ≤ M) (hA : ∀ i, ‖A i‖ ≤ M)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) {z : Space h} (hz : z ∉ coordinateBox h (D*M+r)) :
    gaussianPointMass μ r (A,z) = 0 := by
  have hs : gaussianPointBand A z r ⊆ {x | ¬‖x‖ ≤ D} := by
    intro x hx hnorm
    exact hz (gaussianPointBand_parameter_bound A hM hA hnorm hx)
  have he : μ (gaussianPointBand A z r) = 0 := measure_mono_null hs (ae_iff.mp hμ)
  simp only [gaussianPointMass,he,mul_zero]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceSelectionMean
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a retained slice from its quantitative mean -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem exists_large_slice_of_mean (μ : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : X → ℝ≥0∞) (hsupport : ∀ᵐ x ∂μ, x ∉ S → f x = 0) {a : ℝ≥0∞}
    (hmean : a*μ S < ∫⁻ x, f x ∂μ) :
    ∃ x ∈ S, a < f x := by
  by_contra! hn
  have hle : f ≤ᵐ[μ] S.indicator (fun _ => a) := by
    filter_upwards [hsupport] with x hx
    by_cases hxs : x ∈ S
    · simpa only [indicator_of_mem hxs] using hn x hxs
    · simp only [hx hxs,indicator_of_notMem hxs,le_refl]
  have hi := lintegral_mono_ae hle
  rw [lintegral_indicator_const hS] at hi
  exact (not_le_of_gt hmean) hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSelectPruned
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative selection of a retained slice in the controlled row chart -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι : Type*}

theorem gaussian_pruned_incidence_zero_of_point_mass
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1)))
    (p : (Fin h → Space (n+1)) × Space h) (hp : gaussianPointMass μ δ p = 0) :
    gaussianPrunedIncidence μ ν δ r TP TD M E p = 0 := by
  have hz : gaussianPointSliceMeasure μ p.1 p.2 δ = 0 :=
    Measure.measure_univ_eq_zero.mp (by rw [gaussianPointSliceMeasure_univ]; exact hp)
  simp only [gaussianPrunedIncidence,hz,Measure.restrict_zero,Measure.zero_prod,Measure.coe_zero,Pi.zero_apply]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPrunedPair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable parameter-dependent incidence on the retained original laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussianPrunedPairMass_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d))) (hG : MeasurableSet G) :
    Measurable (gaussianPrunedPairMass μ ν δ r TP TD M G) := by
  let F : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {q | q ∈ G ∧ q.2.1 ∈ gaussianPointGood μ δ r TP q.1 ∧
      q.2.2 ∈ gaussianDirectionGood ν δ r TD M q.1.1}
  have hF : MeasurableSet F := by
    have hp := (gaussianPointGood_measurable_joint (h := h) μ δ r TP).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1,q.2.1)) from by fun_prop)
    have hd := (gaussianDirectionGood_measurable_joint (h := h) ν δ r TD M).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1.1,q.2.2)) from by fun_prop)
    exact hG.inter (hp.inter hd)
  convert gaussian_pair_restriction_mass_measurable μ ν δ F hF using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  rw [gaussianPrunedPairMass,gaussianPrunedIncidence,Measure.prod_restrict,
    Measure.restrict_apply (show MeasurableSet {t | (p,t) ∈ G} from
      hG.preimage measurable_prodMk_left)]
  congr 1

omit [Fintype ι] in
theorem gaussianPrunedPairMass_parameter_support {n : ℕ}
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space (n+1)) × Space h) × (Space (n+1) × Sphere (n+1)))) :
    ∀ᵐ p ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p ∉ (gaussianRowNeighborhood B ε) ×ˢ (coordinateBox h (D*(ε+1)+δ)) →
      gaussianPrunedPairMass μ ν δ r TP TD M G p = 0 := by
  have ha : ∀ᵐ p : (Fin h → Space (n+1)) × Space h
      ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume,
      p.1 ∈ gaussianRowNeighborhood B ε :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (gaussianRowNeighborhood_measurable B ε))
  filter_upwards [ha] with p hp hnot
  apply gaussian_pruned_incidence_zero_of_point_mass μ ν δ r TP TD M _ p
  apply gaussian_point_mass_zero_outside_box μ p.1 (by linarith)
    (gaussianRowNeighborhood_norm B hB hp) hμ
  exact fun hz => hnot ⟨hp,hz⟩

omit [Fintype ι] in
theorem gaussian_select_pruned_pair {n : ℕ}
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (G : Set (((Fin h → Space (n+1)) × Space h) × (Space (n+1) × Sphere (n+1))))
    {a : ℝ≥0∞}
    (hmean : a*volume (coordinateBox h (D*(ε+1)+δ)) <
      ∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M G p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      a < gaussianPrunedPairMass μ ν δ r TP TD M G (A,z) := by
  let U := gaussianRowNeighborhood B ε
  let Z := coordinateBox h (D*(ε+1)+δ)
  let ξ := ((gaussianRows (n+1) h).restrict U).prod (volume : Measure (Space h))
  have hmass : ξ (U ×ˢ Z) ≤ volume Z := by
    rw [Measure.prod_prod]
    have hg : ((gaussianRows (n+1) h).restrict U) U ≤ 1 := by
      calc
        _ ≤ gaussianRows (n+1) h U := Measure.restrict_le_self _
        _ ≤ gaussianRows (n+1) h univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    simpa only [one_mul] using mul_le_mul_left hg (volume Z)
  have hgt : a*ξ (U ×ˢ Z) < ∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M G p ∂ξ :=
    (mul_le_mul_right hmass a).trans_lt hmean
  obtain ⟨⟨A,z⟩,hAz,hi⟩ := exists_large_slice_of_mean ξ (U ×ˢ Z)
    ((gaussianRowNeighborhood_measurable B ε).prod (coordinateBox_measurable _)) _
    (gaussianPrunedPairMass_parameter_support B hB hε μ ν hμ δ r TP TD M G) hgt
  exact ⟨A,hAz.1,z,hAz.2,hi⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianActiveRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-pair incidence after the active-cover deletion -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] in
theorem gaussianActiveRelation_measurable (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R : ℝ) (T : ℝ≥0∞) (good : Bool) :
    MeasurableSet (gaussianActiveRelation (h := h) E J a R T good) := by
  have hm := (gaussianActiveFamily_measurable (h := h) J hJ a R).comp
    (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
      (q.1,q.2.2)) from by fun_prop)
  cases good
  · exact (hE.preimage measurable_snd).inter (measurableSet_lt measurable_const hm)
  · exact (hE.preimage measurable_snd).inter (measurableSet_le hm measurable_const)

theorem gaussian_active_bad_integral
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P) :
    (∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M
      (gaussianActiveRelation E J a R T false) p ∂(gaussianRows d h).prod volume) ≤
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  rw [lintegral_prod _ (show AEMeasurable
    (gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T false))
    ((gaussianRows d h).prod volume) from
    (gaussianPrunedPairMass_measurable μ ν δ r TP TD M _
      (gaussianActiveRelation_measurable E hE J hJ a R T false)).aemeasurable)]
  calc
    _ ≤ ∫⁻ _ : Fin h → Space d, P*(N*ENNReal.ofReal ((2*R)^h)/T)*M ∂gaussianRows d h := by
      apply lintegral_mono
      intro A
      have he (z : Space h) : {t | ((A,z),t) ∈ gaussianActiveRelation E J a R T false} =
          E ∩ (univ ×ˢ {w | T < (gaussianActiveAnchorCount A (J w) a R z : ℝ≥0∞)}) := by
        ext t
        simp [gaussianActiveRelation]
      simp only [gaussianPrunedPairMass,he]
      exact gaussian_active_loss_in_row μ ν δ r TP TD M A E J hJ a hR hN hT hTfin
        (fun z => hP (A,z))
    _ = _ := by rw [lintegral_const,measure_univ,mul_one]

theorem gaussian_active_pruning_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure ((Fin h → Space d) × Space h)) (hξ : ξ ≤ (gaussianRows d h).prod volume)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P) :
    (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ) ≤
      (∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) p ∂ξ) +
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  let f := gaussianPrunedPairMass (h := h) μ ν δ r TP TD M (gaussianActiveRelation E J a R T true)
  let g := gaussianPrunedPairMass (h := h) μ ν δ r TP TD M (gaussianActiveRelation E J a R T false)
  have hf : Measurable f := gaussianPrunedPairMass_measurable μ ν δ r TP TD M _
    (gaussianActiveRelation_measurable E hE J hJ a R T true)
  have hg : (∫⁻ p, g p ∂ξ) ≤ P*(N*ENNReal.ofReal ((2*R)^h)/T)*M :=
    (lintegral_mono' hξ le_rfl).trans
      (gaussian_active_bad_integral μ ν δ r TP TD M E hE J hJ a hR hN hT hTfin hP)
  calc
    _ ≤ ∫⁻ p, f p+g p ∂ξ := by
      apply lintegral_mono
      intro p
      apply (measure_mono (show E ⊆
        {t | (p,t) ∈ gaussianActiveRelation E J a R T true} ∪
        {t | (p,t) ∈ gaussianActiveRelation E J a R T false} from ?_)).trans (measure_union_le _ _)
      intro t ht
      rcases le_or_gt (gaussianActiveAnchorCount p.1 (J t.2) a R p.2 : ℝ≥0∞) T with hle | hgt
      · exact Or.inl ⟨ht,hle⟩
      · exact Or.inr ⟨ht,hgt⟩
    _ = (∫⁻ p, f p ∂ξ)+(∫⁻ p, g p ∂ξ) := lintegral_add_left hf _
    _ ≤ _ := add_le_add le_rfl hg

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianSelectActive
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing a quantitatively nonempty slice with its original active tube covers -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem gaussian_select_active_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space (n+1))
    {R : ℝ} (hR : 0 ≤ R) {N T P b : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P)
    (hmean : b*volume (coordinateBox h (D*(ε+1)+δ)) + P*(N*ENNReal.ofReal ((2*R)^h)/T)*M <
      ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      b < gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) (A,z) := by
  have hξ : ((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod
      (volume : Measure (Space h)) ≤ (gaussianRows (n+1) h).prod volume :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hl := gaussian_active_pruning_loss μ ν _ hξ δ r TP TD M E hE J hJ a hR hN hT hTfin hP
  apply gaussian_select_pruned_pair B hB hε μ ν hμ δ r TP TD M _
  exact lt_of_add_lt_add_right (hmean.trans_le hl)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianOriginalSlice
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A retained original-label slice from the explicit four-cost budget -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem gaussian_select_original_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D δ ρ : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    (i₀ : ι) (hi₀ : D < r i₀)
    {M Q : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space (n+1))
    {R : ℝ} (hR : 0 ≤ R) {N T b : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hbudget : (b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) +
      TP i₀*(N*ENNReal.ofReal ((2*R)^h)/T)*M) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*Q) <
      ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ),
      b < gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) (A,z) := by
  have hρ : 0 ≤ ρ := hδ.le.trans hδρ
  have hlo := gaussian_controlled_pruning_ledger B hB μ ν hδ hδρ hwB r TP TD CP CD
    hTP hTD hM hMtop hpoint hdir hmoment E hE
  have hlt := hbudget.trans_le hlo
  have hmean := lt_of_add_lt_add_right (lt_of_add_lt_add_right (lt_of_add_lt_add_right hlt))
  apply gaussian_select_active_slice B hB (by positivity) μ ν hμ δ r TP TD M E hE J hJ a
    hR hN hT hTfin (fun p => gaussianPointGood_mass μ δ r TP p hμ i₀ hi₀)
  exact hmean

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SlicePruningRatios
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the dyadic weights in the simultaneous pruning costs -/

namespace Falconer
open scoped ENNReal
variable {ι : Type*} [Fintype ι]

theorem pruning_real_weighted_sum {H C : ℝ} (hH : 0 < H)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    (∑ i, (ENNReal.ofReal (H*w i))⁻¹*B i) ≤
      ENNReal.ofReal ((Fintype.card ι:ℝ)*C/H) := by
  have hi (i : ι) : (ENNReal.ofReal (H*w i))⁻¹*B i ≤ ENNReal.ofReal (C/H) := by
    apply (mul_le_mul_right (hB i) _).trans_eq
    rw [mul_comm]
    change ENNReal.ofReal (C*w i) / ENNReal.ofReal (H*w i) = _
    rw [← ENNReal.ofReal_div_of_pos (mul_pos hH (hw i))]
    congr 1
    field_simp [(hw i).ne']
  calc
    _ ≤ ∑ _i : ι, ENNReal.ofReal (C/H) := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Fintype.card ι:ℝ≥0∞)*ENNReal.ofReal (C/H) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = _ := by
      rw [show (Fintype.card ι:ℝ≥0∞) = ENNReal.ofReal (Fintype.card ι:ℝ) by simp,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The four deletion costs fit inside the original incidence budget -/

namespace Falconer
open scoped ENNReal

theorem slice_four_cost_budget_real {K B A : ℝ} (hK : 0 < K)
    (hlarge : 4*(1+2*B+A) ≤ K) :
    1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2 < 1/K := by
  have he : 1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2 =
      (K/4+(1+2*B+A))/K^2 := by field_simp; ring
  rw [he]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hK) hK).mpr
  have hh := mul_le_mul_of_nonneg_right hlarge hK.le
  nlinarith

theorem slice_four_cost_budget {K B A : ℝ} (hK : 0 < K) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hlarge : 4*(1+2*B+A) ≤ K)
    {base point direction mass active : ℝ≥0∞}
    (hb : base ≤ ENNReal.ofReal (1/(4*K))) (hp : point ≤ ENNReal.ofReal (1/K^2))
    (hd : direction ≤ ENNReal.ofReal (B/K^2)) (hm : mass ≤ ENNReal.ofReal (B/K^2))
    (ha : active ≤ ENNReal.ofReal (A/K^2)) :
    base+point+direction+mass+active < ENNReal.ofReal (1/K) := by
  calc
    _ ≤ ENNReal.ofReal (1/(4*K))+ENNReal.ofReal (1/K^2)+ENNReal.ofReal (B/K^2)+
        ENNReal.ofReal (B/K^2)+ENNReal.ofReal (A/K^2) :=
      add_le_add (add_le_add (add_le_add (add_le_add hb hp) hd) hm) ha
    _ = ENNReal.ofReal (1/(4*K)+1/K^2+B/K^2+B/K^2+A/K^2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (slice_four_cost_budget_real hK hlarge)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianScaleBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete polynomial thresholds in Gaussian slice selection -/

namespace Falconer
open scoped ENNReal
variable {ι : Type*} [Fintype ι]

theorem slice_cube_ratio_le {K X : ℝ} (hK : 0 < K) (hX : X ≤ K) :
    X/K^3 ≤ 1/K^2 := by
  apply (div_le_iff₀ (pow_pos hK 3)).mpr
  calc
    X ≤ K := hX
    _ = (1/K^2)*K^3 := by field_simp

theorem gaussian_point_scale_cost {K C : ℝ} (hK : 0 < K)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*B i)*ENNReal.ofReal (K^3) ≤
      ENNReal.ofReal (1/K^2) := by
  have hs := pruning_real_weighted_sum (pow_pos hK 6) w hw B hB
  have he : ((Fintype.card ι:ℝ)*C/K^6)*K^3 = (Fintype.card ι:ℝ)*C/K^3 := by
    field_simp
  calc
    _ ≤ ENNReal.ofReal ((Fintype.card ι:ℝ)*C/K^6)*ENNReal.ofReal (K^3) := mul_le_mul' hs le_rfl
    _ = ENNReal.ofReal (((Fintype.card ι:ℝ)*C/K^6)*K^3) := by
      rw [← ENNReal.ofReal_mul' (by positivity : 0 ≤ K^3)]
    _ ≤ _ := by rw [he]; exact ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hcard)

theorem gaussian_direction_scale_cost {K C S : ℝ} (hK : 0 < K) (hS : 0 ≤ S)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ι → ℝ≥0∞)
    (hB : ∀ i, B i ≤ ENNReal.ofReal (C*w i)) :
    ENNReal.ofReal S*(∑ i, (ENNReal.ofReal (K^3*w i))⁻¹*B i) ≤
      ENNReal.ofReal (S/K^2) := by
  have hs := (pruning_real_weighted_sum (pow_pos hK 3) w hw B hB).trans
    (ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hcard))
  calc
    _ ≤ ENNReal.ofReal S*ENNReal.ofReal (1/K^2) := mul_le_mul' le_rfl hs
    _ = _ := by rw [← ENNReal.ofReal_mul hS]; congr 1; ring

theorem gaussian_mass_scale_cost {K C S : ℝ} (hK : 0 < K) (hS : 0 ≤ S)
    (hC : C ≤ K) {Q : ℝ≥0∞} (hQ : Q ≤ ENNReal.ofReal C) :
    ENNReal.ofReal S*((ENNReal.ofReal (K^3))⁻¹*Q) ≤ ENNReal.ofReal (S/K^2) := by
  have hs : (ENNReal.ofReal (K^3))⁻¹*Q ≤ ENNReal.ofReal (1/K^2) := by
    calc
      _ ≤ (ENNReal.ofReal (K^3))⁻¹*ENNReal.ofReal C := mul_le_mul' le_rfl hQ
      _ = ENNReal.ofReal (C/K^3) := by
        rw [mul_comm]
        change ENNReal.ofReal C / ENNReal.ofReal (K^3) = _
        rw [← ENNReal.ofReal_div_of_pos (pow_pos hK 3)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (slice_cube_ratio_le hK hC)
  calc
    _ ≤ ENNReal.ofReal S*ENNReal.ofReal (1/K^2) := mul_le_mul' le_rfl hs
    _ = _ := by rw [← ENNReal.ofReal_mul hS]; congr 1; ring

theorem gaussian_active_scale_cost {K w N R : ℝ} (hK : 0 < K) (hw : 0 < w)
    (hN : 0 < N) (hR : 0 < R) (h : ℕ) :
    ENNReal.ofReal (K^6*w)*
      (ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
        ENNReal.ofReal (K^11*(w*(N*(2*R)^h))))*ENNReal.ofReal (K^3) =
      ENNReal.ofReal (1/K^2) := by
  have hp : 0 < (2*R)^h := pow_pos (by positivity) h
  have hd : 0 < K^11*(w*(N*(2*R)^h)) := by positivity
  rw [← ENNReal.ofReal_mul hN.le,← ENNReal.ofReal_div_of_pos hd,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ K^6*w),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (K^6*w)*((N*(2*R)^h)/(K^11*(w*(N*(2*R)^h)))))]
  congr 1
  field_simp [hK.ne',hw.ne',hN.ne',hp.ne']

theorem gaussian_four_polynomial_costs {K C S w₀ N R : ℝ}
    (hK : 0 < K) (hS : 0 ≤ S) (hw₀ : 0 < w₀) (hN : 0 < N) (hR : 0 < R)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K) (hC : C ≤ K)
    (hlarge : 4*(1+2*S+1) ≤ K)
    (w v : ι → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (CP CD : ι → ℝ≥0∞) (hCP : ∀ i, CP i ≤ ENNReal.ofReal (C*w i))
    (hCD : ∀ i, CD i ≤ ENNReal.ofReal (C*v i))
    (h : ℕ) {base Q : ℝ≥0∞}
    (hbase : base ≤ ENNReal.ofReal (1/(4*K))) (hQ : Q ≤ ENNReal.ofReal C) :
    base + (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*CP i)*ENNReal.ofReal (K^3) +
      ENNReal.ofReal S*(∑ i, (ENNReal.ofReal (K^3*v i))⁻¹*CD i) +
      ENNReal.ofReal S*((ENNReal.ofReal (K^3))⁻¹*Q) +
      ENNReal.ofReal (K^6*w₀)*
        (ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
          ENNReal.ofReal (K^11*(w₀*(N*(2*R)^h))))*ENNReal.ofReal (K^3) <
      ENNReal.ofReal (1/K) := by
  apply slice_four_cost_budget hK hS (show (0:ℝ) ≤ 1 by norm_num) hlarge hbase
    (gaussian_point_scale_cost hK hcard w hw CP hCP)
    (gaussian_direction_scale_cost hK hS hcard v hv CD hCD)
    (gaussian_mass_scale_cost hK hS hC hQ)
  exact (gaussian_active_scale_cost hK hw₀ hN hR h).le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPolynomialSlice
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A retained original slice with the explicit polynomial pruning thresholds -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

private theorem original_cost_order (a b c d e : ℝ≥0∞) :
    (a+e)+b+c+d = a+b+c+d+e := by ac_rfl

theorem gaussian_select_polynomial_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D δ ρ : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r w v : ι → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (CP CD : ι → ℝ≥0∞) (Q : ℝ≥0∞)
    {K C S N R : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hN : 0 < N) (hR : 0 < R)
    (hcard : (Fintype.card ι:ℝ)*C ≤ K) (hC : C ≤ K) (hlarge : 4*(1+2*S+1) ≤ K)
    (hCP : ∀ i, CP i ≤ ENNReal.ofReal (C*w i))
    (hCD : ∀ i, CD i ≤ ENNReal.ofReal (C*v i)) (hQ : Q ≤ ENNReal.ofReal C)
    (hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal S)
    (i₀ : ι) (hi₀ : D < r i₀)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {u | i ∈ J u})
    (a : κ → Space (n+1)) (hJN : ∀ u, ((J u).card : ℝ≥0∞) ≤ ENNReal.ofReal N)
    (hmean : ENNReal.ofReal (1/K) ≤ ENNReal.ofReal ((2:ℝ)^h)*
      ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E)
    {b : ℝ≥0∞}
    (hbase : b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) ≤
      ENNReal.ofReal (1/(4*K))) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ),
      b < gaussianPrunedPairMass μ ν δ r
        (fun i => ENNReal.ofReal (K^6*w i)) (fun i => ENNReal.ofReal (K^3*v i))
        (ENNReal.ofReal (K^3))
        (gaussianActiveRelation E J a R
          (ENNReal.ofReal (K^11*(w i₀*(N*(2*R)^h)))) true) (A,z) := by
  have hw₀ := hw i₀
  apply gaussian_select_original_slice B hB μ ν hμ hδ hδρ hwB r
    (fun i => ENNReal.ofReal (K^6*w i)) (fun i => ENNReal.ofReal (K^3*v i)) CP CD
    (fun i => ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hK 6) (hw i)))
    (fun i => ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hK 3) (hv i))) i₀ hi₀
    (ENNReal.ofReal_pos.mpr (pow_pos hK 3)) ENNReal.ofReal_ne_top
    hpoint hdir hmoment E hE J hJ a hR.le hJN
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))) ENNReal.ofReal_ne_top
  have hc := gaussian_four_polynomial_costs hK hS (hw i₀) hN hR hcard hC hlarge
    w v hw hv CP CD hCP hCD h hbase hQ
  apply lt_of_le_of_lt _ (hc.trans_le hmean)
  calc
    _ = b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) +
        (∑ i, (ENNReal.ofReal (K^6*w i))⁻¹*CP i)*ENNReal.ofReal (K^3) +
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (ENNReal.ofReal (K^3*v i))⁻¹*CD i) +
        (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*((ENNReal.ofReal (K^3))⁻¹*Q) +
        ENNReal.ofReal (K^6*w i₀)*(ENNReal.ofReal N*ENNReal.ofReal ((2*R)^h)/
          ENNReal.ofReal (K^11*(w i₀*(N*(2*R)^h))))*ENNReal.ofReal (K^3) :=
      original_cost_order _ _ _ _ _
    _ ≤ _ := add_le_add
      (add_le_add (add_le_add le_rfl (mul_le_mul' hfactor le_rfl))
        (mul_le_mul' hfactor le_rfl)) le_rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_DyadicSliceSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a slice directly from the two original finite-scale ball bounds -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem dyadic_original_slice_selection_oai
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ)
    {D ρ Lt Lq t q : ℝ} (hD : D < 1/2) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hδρ : 1/(2:ℝ)^N ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t) (hq : (h:ℝ) < q)
    (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
    (hμball : ∀ x : Space (n+1), ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
    (hνball : ∀ x : Sphere (n+1), ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere (n+1) × Sphere (n+1) ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space (n+1)) (z.2:Space (n+1)))
    {K C S Nc R : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hNc : 0 < Nc) (hR : 0 < R)
    (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C)
    (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C)
    (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C)
    (hcard : ((N+1:ℕ):ℝ)*C ≤ K) (hC : C ≤ K) (hlarge : 4*(1+2*S+1) ≤ K)
    (hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal S)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
    (hmean : ENNReal.ofReal (1/K) ≤ ENNReal.ofReal ((2:ℝ)^h)*
      ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E)
    {b : ℝ≥0∞}
    (hbase : b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)) ≤
      ENNReal.ofReal (1/(4*K))) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N),
      b < gaussianPrunedPairMass μ ν (1/(2:ℝ)^N) (gaussianPruningRadius (N := N))
        (fun i => ENNReal.ofReal (K^6*gaussianPruningWeight h t i))
        (fun i => ENNReal.ofReal (K^3*gaussianPruningWeight h q i)) (ENNReal.ofReal (K^3))
        (gaussianActiveRelation E J a R (ENNReal.ofReal (K^11*(Nc*(2*R)^h))) true) (A,z) := by
  let r : Fin (N+1) → ℝ := gaussianPruningRadius
  let w : Fin (N+1) → ℝ := gaussianPruningWeight h t
  let v : Fin (N+1) → ℝ := gaussianPruningWeight h q
  let CP : Fin (N+1) → ℝ≥0∞ := fun i => ENNReal.ofReal (C*w i)
  let CD : Fin (N+1) → ℝ≥0∞ := fun i => ENNReal.ofReal (C*v i)
  have hp (i : Fin (N+1)) := gaussian_point_moment_weight μ hLt ht i.val N
    (Nat.le_of_lt_succ i.isLt) hμmass hμball hCpoint
  have hd (i : Fin (N+1)) := gaussian_direction_moment_weight ν hLq hq i.val N
    (Nat.le_of_lt_succ i.isLt) hνmass hνball hchart hCdir
  have hm := gaussian_direction_total_moment_bound ν hLq hq N hνmass hνball hchart hCmass
  have hi₀ : D < r 0 := by simpa only [r,gaussianPruningRadius,Fin.val_zero,pow_zero,div_one] using hD
  have hh := gaussian_select_polynomial_slice B hB μ ν hμ (by positivity) hδρ hwB r w v
    (fun i => by dsimp [w,gaussianPruningWeight]; positivity)
    (fun i => by dsimp [v,gaussianPruningWeight]; positivity)
    CP CD (ENNReal.ofReal C) hK hS hNc hR
    (by simpa only [Fintype.card_fin] using hcard) hC hlarge
    (fun _ => le_rfl) (fun _ => le_rfl) le_rfl hfactor 0 hi₀ hp hd hm
    E hE J hJ a hJN hmean hbase
  simpa only [w,v,r,gaussianPruningWeight,Fin.val_zero,pow_zero,Real.one_rpow,one_mul] using hh

end Falconer

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Falconer.dyadic_original_slice_selection_oai.{u_1} := @OAI.Falconer.dyadic_original_slice_selection_oai.{u_1}
