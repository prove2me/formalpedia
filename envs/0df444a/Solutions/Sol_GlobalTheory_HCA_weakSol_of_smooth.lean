-- Prove2me | solution 1 for GlobalTheory.HCA.weakSol_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:28:40.684473+00:00
-- url     : https://prove2.me/submissions/5c9ef7dc-7267-4446-8e6a-ccb69d820579

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolution
import Theorems.Thm_GlobalTheory_HCA_integrable_mul_of_continuousOn_of_tsupport
import Theorems.Thm_GlobalTheory_HCA_dw_hasCompactSupport_tsupport
import Theorems.Thm_GlobalTheory_HCA_contDiff_mul_of_contDiffOn_of_tsupport
import Theorems.Thm_GlobalTheory_T_dw_contDiffOn_local_linear
import Theorems.Thm_GlobalTheory_T_integral_mul_iterPartialDeriv_eq_neg_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution :
    ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ),
      (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U →
      (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by
  intro d m U hU a ha u hu hap i φ hφ hc hs
  show ∫ x, u x * trOp m a φ x = 0
  have hψ : ∀ n w, ContDiff ℝ ∞ (fun y => a n w y * φ y) := fun n w =>
    contDiff_mul_of_contDiffOn_of_tsupport hU (ha n w) hφ hs
  have hψc : ∀ n w, HasCompactSupport (fun y => a n w y * φ y) := fun n w => hc.mul_left
  have hψs : ∀ n w, tsupport (fun y => a n w y * φ y) ⊆ U := fun n w =>
    (tsupport_mul_subset_right).trans hs
  have hI1 : ∀ n (w : Fin n → Fin d),
      Integrable (fun x => u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)) := by
    intro n w
    have hdc := dw_hasCompactSupport_tsupport (List.ofFn w) (hψc n w)
    have hcont : Continuous (dw (List.ofFn w) (fun y => a n w y * φ y)) := by
      have := (GlobalTheory.T.dw_contDiffOn_local_linear d Set.univ isOpen_univ (List.ofFn w)).1 _ (hψ n w).contDiffOn
      exact (contDiffOn_univ.1 this).continuous
    have := integrable_mul_of_continuousOn_of_tsupport hU hu.continuousOn
      (g := fun x => (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)
      (continuous_const.mul hcont) (hdc.1.mul_left)
      ((tsupport_mul_subset_right).trans (hdc.2.trans (hψs n w)))
    exact this
  have hI2 : ∀ n (w : Fin n → Fin d),
      Integrable (fun x => dw (List.ofFn w) u x * (a n w x * φ x)) := by
    intro n w
    exact integrable_mul_of_continuousOn_of_tsupport hU
      ((GlobalTheory.T.dw_contDiffOn_local_linear d U hU (List.ofFn w)).1 u hu).continuousOn (hψ n w).continuous (hψc n w) (hψs n w)
  have hterm : ∀ n (w : Fin n → Fin d),
      ∫ x, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) =
        ∫ x, dw (List.ofFn w) u x * (a n w x * φ x) := by
    intro n w
    have hibp := GlobalTheory.T.integral_mul_iterPartialDeriv_eq_neg_pow d U hU (List.ofFn w) u (fun y => a n w y * φ y) hu (hψ n w) (hψc n w)
      (hψs n w)
    rw [List.length_ofFn] at hibp
    have e1 : (fun x => u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)) =
        fun x => (-1 : ℂ) ^ n * (u x * dw (List.ofFn w) (fun y => a n w y * φ y) x) := by
      funext x; ring
    rw [e1, integral_const_mul, hibp, ← mul_assoc, ← mul_pow]
    norm_num
  have hsplit : (fun x => u x * trOp m a φ x) = fun x => ∑ n ∈ Finset.range (m + 1),
      ∑ w : Fin n → Fin d, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) := by
    funext x
    simp only [trOp, Finset.mul_sum]
  rw [hsplit, integral_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => hI1 n w))]
  have hin : ∀ n ∈ Finset.range (m + 1),
      ∫ x, ∑ w : Fin n → Fin d, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) =
        ∫ x, ∑ w : Fin n → Fin d, dw (List.ofFn w) u x * (a n w x * φ x) := by
    intro n _
    rw [integral_finset_sum _ (fun w _ => hI1 n w), integral_finset_sum _ (fun w _ => hI2 n w)]
    exact Finset.sum_congr rfl fun w _ => hterm n w
  rw [Finset.sum_congr rfl hin,
    ← integral_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => hI2 n w))]
  have hzero : (fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      dw (List.ofFn w) u x * (a n w x * φ x)) = fun _ => (0 : ℂ) := by
    funext x
    by_cases hx : x ∈ U
    · have h := hap x hx
      have e : (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          dw (List.ofFn w) u x * (a n w x * φ x)) = apOp m a u x * φ x := by
        simp only [apOp, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
        ring
      rw [e, h, zero_mul]
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
      simp [h0]
  rw [hzero, integral_zero]
end GlobalTheory.HCA
