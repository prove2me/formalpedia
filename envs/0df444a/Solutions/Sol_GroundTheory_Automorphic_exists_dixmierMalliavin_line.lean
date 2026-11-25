-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_dixmierMalliavin_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:03:06.118208+00:00
-- url     : https://prove2.me/submissions/8094ad20-9873-44a8-b4cd-2538e937b7aa

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_Rs_radii_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_weight_pos
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_weight_mul_abs_le
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_eventually_good
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_mul_of_support
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_le_weight
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_remSum
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_remSum_subset
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_hasSum_integral_remSum
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_tendsto_fourier_Kc
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_decay_fourier_Kc
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_tendsto_coef
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_climit_le_weight
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_climit_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_Kc_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_coef_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_KC
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_Kc__49dcd9
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_Kc_le_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_stage_identity
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_Kc_subset
import Theorems.Thm_GroundTheory_Automorphic_exists_smooth_weak_limit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open LineKernel
namespace GroundTheory.Automorphic
theorem _root_.solution (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → ℝ) (g h : ℝ → ℂ), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      tsupport g ⊆ Set.Icc (-ε) ε ∧ tsupport h ⊆ Set.Icc (-ε) ε ∧
      Summable (fun p => |c p| * M p) ∧
      ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → (∀ p, ∀ t ∈ Set.Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p) →
        F 0 = (∑' p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t) + ∫ t, F t * h t := by
  choose a hg using fun j => (eventually_good M hε j).exists
  have ha := fun j => (hg j).1
  have hr := radii_pos hε
  have hKs : ∀ N, support (Kc a (radii ε) N) ⊆ Icc 0 (ε / 2) := fun N t ht =>
    ⟨(support_Kc_subset ha hr N ht).1, (support_Kc_subset ha hr N ht).2.trans (Rs_radii_le hε N)⟩
  obtain ⟨g, hgs, hgt, hgl⟩ := exists_smooth_weak_limit (K := Kc a (radii ε)) (a := 0)
    (b := ε / 2) (integrable_Kc ha hr) (Kc_nonneg ha hr) (integral_Kc_le_one ha hr) hKs
    (tendsto_fourier_Kc hε hg) (decay_fourier_Kc hε hg)
  have hsub : Icc 0 (ε / 2) ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) (by linarith)
  refine ⟨fun p => (-1) ^ p * climit (a := a) p, g, remSum (ε := ε) (a := a), hgs,
    contDiff_remSum hε hg, hgt.trans hsub,
    (closure_minimal (support_remSum_subset hε hg) isClosed_Icc).trans hsub, ?_, ?_⟩
  · refine Summable.of_norm_bounded
      (summable_geometric_two.mul_right (max 1 |M 0|)) fun p => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (climit_nonneg hε hg p)]
    exact (mul_le_mul_of_nonneg_right (climit_le_weight hε hg p) (abs_nonneg _)).trans
      (weight_mul_abs_le M p)
  · intro F hF hFM

    have hA : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), ∫ t, F t * ρ a (radii ε) j t) atTop
        (𝓝 (∫ t, F t * remSum (ε := ε) (a := a) t)) :=
      ((hasSum_integral_remSum hε hg hF.continuous (fun t ht => by
        simpa using hFM 0 t ht)).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

    have hB : Tendsto (fun n => ∫ u, opT a (n + 1) F u * KC a (radii ε) n u) atTop
        (𝓝 (∑' p, (((-1) ^ p * climit (a := a) p : ℝ) : ℂ) *
          ∫ t, iteratedDeriv p F t * g t)) := by
      have hcont : ∀ p, Continuous (iteratedDeriv p F) := fun p =>
        hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
      have hKsC : ∀ n, support (KC a (radii ε) n) ⊆ Icc 0 (ε / 2) := fun n u hu =>
        hKs n (by simpa [KC] using hu)
      have hsplit : ∀ n, ∫ u, opT a (n + 1) F u * KC a (radii ε) n u =
          ∑' p, sc a (n + 1) p * ∫ u, iteratedDeriv p F u * KC a (radii ε) n u := by
        intro n
        rw [tsum_eq_sum (s := Finset.range (n + 2)) fun p hp => by
          rw [Finset.mem_range, not_lt] at hp
          simp [sc, coef_eq_zero a (by omega : n + 1 < p)]]
        simp only [opT, Finset.sum_mul]
        rw [integral_finsetSum (Finset.range (n + 1 + 1))
          (f := fun p u => sc a (n + 1) p * iteratedDeriv p F u * KC a (radii ε) n u)
          fun p _ => integrable_mul_of_support (φ := fun u => sc a (n + 1) p * iteratedDeriv p F u)
          (continuous_const.mul (hcont p)) (integrable_KC ha hr n) (hKsC n)]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← integral_const_mul]; congr 1; funext u; ring
      rw [show (fun n => ∫ u, opT a (n + 1) F u * KC a (radii ε) n u) =
          fun n => ∑' p, sc a (n + 1) p * ∫ u, iteratedDeriv p F u * KC a (radii ε) n u from
        funext hsplit]
      refine tendsto_tsum_of_dominated_convergence (bound := fun p => weight M p * |M p|) ?_ ?_ ?_
      · exact Summable.of_nonneg_of_le (fun p => mul_nonneg (weight_pos M p).le (abs_nonneg _))
          (weight_mul_abs_le M) (summable_geometric_two.mul_right _)
      · intro p
        have h1 : Tendsto (fun n => sc a (n + 1) p) atTop
            (𝓝 ((((-1) ^ p * climit (a := a) p : ℝ) : ℂ))) := by
          have := ((Complex.continuous_ofReal.tendsto _).comp
            ((tendsto_coef hε hg p).comp (tendsto_add_atTop_nat 1))).const_mul ((-1 : ℂ) ^ p)
          simpa [sc, Function.comp_def] using this
        exact h1.mul (hgl _ (hcont p))
      · refine Eventually.of_forall fun n p => ?_
        rw [norm_mul]
        have hsc : ‖sc a (n + 1) p‖ ≤ weight M p := by
          simp only [sc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (coef_nonneg ha _ _)]
          exact coef_le_weight hε hg _ _
        have hint : ‖∫ u, iteratedDeriv p F u * KC a (radii ε) n u‖ ≤ |M p| := by
          refine (norm_integral_le_integral_norm _).trans ?_
          calc ∫ u, ‖iteratedDeriv p F u * KC a (radii ε) n u‖
              ≤ ∫ u, |M p| * Kc a (radii ε) n u := by
                refine integral_mono (integrable_mul_of_support (hcont p) (integrable_KC ha hr n)
                  (hKsC n)).norm ((integrable_Kc ha hr n).const_mul _) fun u => ?_
                rw [norm_mul]
                simp only [KC, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (Kc_nonneg ha hr n u)]
                by_cases hu : Kc a (radii ε) n u = 0
                · simp [hu]
                · exact mul_le_mul_of_nonneg_right ((hFM p u (hsub (hKs n hu))).trans
                    (le_abs_self _)) (Kc_nonneg ha hr n u)
            _ = |M p| * ∫ u, Kc a (radii ε) n u := integral_const_mul _ _
            _ ≤ |M p| := by
                have := integral_Kc_le_one ha hr n
                have h0 : 0 ≤ |M p| := abs_nonneg _
                nlinarith
        exact mul_le_mul hsc hint (norm_nonneg _) (weight_pos M p).le
    have hlim := hB.add hA
    have hconst : (fun n => F 0) = fun n => (∫ u, opT a (n + 1) F u * KC a (radii ε) n u) +
        ∑ j ∈ Finset.range (n + 1), ∫ t, F t * ρ a (radii ε) j t :=
      funext fun n => stage_identity ha hr hF n
    rw [← hconst] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
end GroundTheory.Automorphic
