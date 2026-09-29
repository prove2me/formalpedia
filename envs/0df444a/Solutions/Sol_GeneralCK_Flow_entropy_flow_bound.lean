-- Prove2me | solution 1 for GeneralCK.Flow.entropy_flow_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:23:39.271386+00:00
-- url     : https://prove2.me/submissions/cea5dedd-074d-47de-932b-18e1f1a19aea

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_cube_analysis
import Definitions.Def_GeneralCK_energy_generator
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_entropy_flow
import Definitions.Def_GeneralCK_information
import Definitions.Def_GeneralCK_noise_evolution
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_Comparison_entropy_lower_bound
import Theorems.Thm_GeneralCK_CubeAnalysis_static_induction
import Theorems.Thm_GeneralCK_Energy_energy_eq_generator
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_Noise_hasDerivAt_applyNoise
import Theorems.Thm_GeneralCK_noiseKernel_sum

open scoped BigOperators
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)





theorem H_complement (p : ℝ) : H (1 - p) = H p := by simp [H]



theorem H_le_one (p : ℝ) : H p ≤ 1 := by
  rw [H, div_le_one log_two_pos]
  exact Real.binEntropy_le_log_two

theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK

namespace GeneralCK
open scoped BigOperators

theorem noiseKernel_nonneg {n : ℕ} {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1)
    (x y : Cube n) : 0 ≤ noiseKernel p x y := by
  unfold noiseKernel
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith







end GeneralCK

namespace GeneralCK.Information
open scoped BigOperators







theorem weight_sum (n : ℕ) : (∑ _ : Cube n, cubeWeight n) = 1 := by
  simp [cubeWeight, Cube, zpow_neg, zpow_natCast]

theorem kernel_symm {n : ℕ} (p : ℝ) (x y : Cube n) :
    noiseKernel p x y = noiseKernel p y x := by
  simp only [noiseKernel, eq_comm]

theorem kernel_column_sum {n : ℕ} (p : ℝ) (y : Cube n) :
    ∑ x, noiseKernel p x y = 1 := by
  simp_rw [kernel_symm p _ y]
  exact noiseKernel_sum p y

































end GeneralCK.Information

namespace GeneralCK.CubeAnalysis
open scoped BigOperators













theorem mean_const (n : ℕ) (c : ℝ) : mean (fun _ : Cube n => c) = c := by
  simp [mean, Cube, zpow_neg, zpow_natCast]



theorem mean_strictMono {n : ℕ} {v w : Cube n → ℝ} (h : ∀ x, v x < w x) :
    mean v < mean w := by
  unfold mean
  apply mul_lt_mul_of_pos_left _ (by positivity)
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun x _ => h x











end GeneralCK.CubeAnalysis

namespace GeneralCK.Noise
open scoped BigOperators



















@[simp] theorem crossover_zero : crossover 0 = 0 := by simp [crossover]

theorem crossover_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ crossover t := by
  unfold crossover
  have h : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  positivity

theorem crossover_lt_half (t : ℝ) : crossover t < 1 / 2 := by
  have h := Real.exp_pos (-2 * t)
  unfold crossover
  linarith

theorem applyNoise_const {n : ℕ} (p c : ℝ) (y : Cube n) :
    applyNoise p (fun _ => c) y = c := by
  simp [applyNoise, ← Finset.sum_mul, Information.kernel_column_sum]

theorem applyNoise_bounds {n : ℕ} {p a b : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1)
    (v : Cube n → ℝ) (hv : ∀ x, a ≤ v x ∧ v x ≤ b) (y : Cube n) :
    a ≤ applyNoise p v y ∧ applyNoise p v y ≤ b := by
  constructor
  · rw [← applyNoise_const p a y]
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hv x).1 (noiseKernel_nonneg h₀ h₁ x y)
  · rw [← applyNoise_const p b y]
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (hv x).2 (noiseKernel_nonneg h₀ h₁ x y)



theorem applyNoise_sum {n : ℕ} (p : ℝ) (v : Cube n → ℝ) :
    ∑ y, applyNoise p v y = ∑ x, v x := by
  unfold applyNoise
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul, noiseKernel_sum]





theorem kernel_zero {n : ℕ} (x y : Cube n) :
    noiseKernel 0 x y = if x = y then 1 else 0 := by
  classical
  by_cases h : x = y
  · subst y; simp [noiseKernel]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

@[simp] theorem applyNoise_zero {n : ℕ} (v : Cube n → ℝ) (y : Cube n) :
    applyNoise 0 v y = v y := by
  classical
  simp [applyNoise, kernel_zero]







end GeneralCK.Noise

namespace GeneralCK.Comparison
open Set













theorem hasDerivAt_H {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt H (J p) p := by
  have hl : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
    Real.log_div (by linarith) (ne_of_gt hp)
  simpa [H, J, hl] using!
    (Real.hasDerivAt_binEntropy (ne_of_gt hp) (by linarith)).div_const (Real.log 2)







end GeneralCK.Comparison

namespace GeneralCK.Flow
open scoped BigOperators
open CubeAnalysis

















theorem regularized_bounds {n : ℕ} (f : Cube n → Bool) {eps : ℝ}
    (he : eps ≤ 1 / 2) (x : Cube n) :
    eps ≤ regularized f eps x ∧ regularized f eps x ≤ 1 - eps := by
  cases h : f x <;> simp only [regularized, h, Bool.false_eq_true, ite_false, ite_true,
    mul_zero, mul_one, add_zero] <;> constructor <;> linarith

theorem flow_bounds {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : eps ≤ 1 / 2) (ht : 0 ≤ t) (x : Cube n) :
    eps ≤ flow f eps t x ∧ flow f eps t x ≤ 1 - eps := by
  exact Noise.applyNoise_bounds (Noise.crossover_nonneg ht)
    (le_trans (Noise.crossover_lt_half t).le (by norm_num))
    (regularized f eps) (regularized_bounds f he) x

theorem flow_interior {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) (x : Cube n) :
    0 < flow f eps t x ∧ flow f eps t x < 1 := by
  have h := flow_bounds f he'.le ht x
  constructor <;> linarith

theorem mean_flow {n : ℕ} (f : Cube n → Bool) (eps t : ℝ) :
    mean (flow f eps t) = initialMean f eps := by
  simp only [mean, flow, Noise.applyNoise_sum, initialMean]

theorem entropy_mean_le {n : ℕ} (v : Cube n → ℝ)
    (hv : ∀ x, 0 ≤ v x ∧ v x ≤ 1) : mean (H ∘ v) ≤ H (mean v) := by
  have hj := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun _ : Cube n => Information.cubeWeight n) (p := v)
    (fun _ _ => by unfold Information.cubeWeight; positivity)
    (Information.weight_sum n) (fun x _ => hv x)
  have h := div_le_div_of_nonneg_right hj GeneralCK.log_two_pos.le
  simpa only [smul_eq_mul, ← Finset.mul_sum, div_eq_mul_inv, ← Finset.sum_mul,
    mul_assoc, mean, H, Function.comp_apply, Information.cubeWeight] using h

theorem delta_range {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) : delta f eps t ∈ Set.Ioc 0 1 := by
  have hv := flow_interior f he he' ht
  have hp : 0 < gamma f eps t := by
    have h := mean_strictMono (fun x => H_pos (hv x).1 (hv x).2)
    simpa only [mean_const, gamma, Function.comp_def] using h
  have hcap := entropy_mean_le (flow f eps t) (fun x => ⟨(hv x).1.le, (hv x).2.le⟩)
  rw [mean_flow] at hcap
  have hm := H_le_one (initialMean f eps)
  change 0 < gamma f eps t + 1 - H (initialMean f eps) ∧
    gamma f eps t + 1 - H (initialMean f eps) ≤ 1
  dsimp only [gamma] at hp ⊢
  constructor <;> linarith

theorem flow_continuous {n : ℕ} (f : Cube n → Bool) (eps : ℝ) (x : Cube n) :
    Continuous (fun t => flow f eps t x) := by
  exact continuous_iff_continuousAt.mpr fun t =>
    (Noise.hasDerivAt_applyNoise (regularized f eps) x t).continuousAt

theorem delta_continuous {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : Continuous (delta f eps) := by
  have hg : Continuous (gamma f eps) := by
    unfold gamma mean
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro x _
    exact H_continuous.comp (flow_continuous f eps x)
  exact (hg.add_const 1).sub continuous_const

theorem hasDerivAt_gamma {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    HasDerivAt (gamma f eps) (energy n (flow f eps t)) t := by
  have hv := flow_interior f he he' ht
  have h := (HasDerivAt.fun_sum (u := Finset.univ) (fun (x : Cube n) _ =>
    (Comparison.hasDerivAt_H (hv x).1 (hv x).2).comp t
      (Noise.hasDerivAt_applyNoise (regularized f eps) x t))).const_mul ((2 : ℝ)^(-(n : ℤ)))
  rw [Energy.energy_eq_generator]
  exact h

theorem hasDerivAt_delta {n : ℕ} (f : Cube n → Bool) {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    HasDerivAt (delta f eps) (energy n (flow f eps t)) t :=
  ((hasDerivAt_gamma f he he' ht).add_const 1).sub_const _

theorem delta_production (hB : FiniteHybridBellman) {n : ℕ} (f : Cube n → Bool)
    {eps t : ℝ} (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    eta (delta f eps t) ≤ energy n (flow f eps t) := by
  have h := static_induction hB n (flow f eps t) (flow_interior f he he' ht)
  have hpsi := le_max_right (phi (mean (flow f eps t)) (gamma f eps t))
    (psi (mean (flow f eps t)) (gamma f eps t))
  have hm := mean_flow f eps t
  simpa only [B, psi, hm, delta, gamma] using hpsi.trans h

theorem regularized_entropy {n : ℕ} (f : Cube n → Bool) (eps : ℝ) (x : Cube n) :
    H (regularized f eps x) = H eps := by
  cases h : f x
  · simp [regularized, h]
  · have he : regularized f eps x = 1 - eps := by simp [regularized, h]; ring
    rw [he, H_complement]

theorem gamma_zero {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : gamma f eps 0 = H eps := by
  have h : H ∘ flow f eps 0 = fun _ : Cube n => H eps := by
    funext x
    simp only [Function.comp_apply, flow, Noise.crossover_zero, Noise.applyNoise_zero,
      regularized_entropy]
  unfold gamma
  rw [h, mean_const]

theorem delta_initial {n : ℕ} (f : Cube n → Bool) (eps : ℝ) : H eps ≤ delta f eps 0 := by
  have h := H_le_one (initialMean f eps)
  unfold delta
  rw [gamma_zero]
  linarith



end GeneralCK.Flow
namespace GeneralCK.Flow
end GeneralCK.Flow

open GeneralCK GeneralCK.Flow in
open scoped BigOperators in
open CubeAnalysis in
theorem solution (hB : FiniteHybridBellman) {n : ℕ} (f : Cube n → Bool)
    {eps T : ℝ} (he : 0 < eps) (he' : eps < 1 / 2) (hT : 0 ≤ T) :
    H (Comparison.noiseParameter eps T) ≤ delta f eps T := by
  apply Comparison.entropy_lower_bound he he' hT (delta_continuous f eps).continuousOn
    (delta' := fun t => energy n (flow f eps t))
  · intro t ht
    exact (hasDerivAt_delta f he he' ht.1).hasDerivWithinAt
  · intro t ht
    exact delta_range f he he' ht.1
  · intro t ht
    exact delta_production hB f he he' ht.1
  · exact delta_initial f eps
