-- Prove2me | solution 1 for GlobalTheory.GoodHeight.local_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:05:09.39665+00:00
-- url     : https://prove2.me/submissions/eda3889a-c466-4a0c-8b57-2164c6d4c253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Theorems.Thm_GlobalTheory_LWide_logDeriv_LFunction_strip
import Theorems.Thm_GlobalTheory_LogDerivZeros_main
import Theorems.Thm_GlobalTheory_ZetaWide_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GoodHeight
namespace GlobalTheory.GoodHeight
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → LFunction χ s ≠ 0 →
    ∃ Z : Finset ℂ, (∀ w, w ∈ Z ↔ ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ LFunction χ w = 0) ∧
      ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℝ) ≤ C * Real.log (N * (|s.im| + 2)) ∧
      ‖deriv (LFunction χ) s / LFunction χ s
        - ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖
        ≤ C * Real.log (N * (|s.im| + 2)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.ZetaWide.main
  refine ⟨C₁ + C₂ + 1, by positivity, ?_⟩
  intro N _ χ hprim s hs1 hs2 ht hLs
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog : 1 ≤ Real.log (N * (|s.im| + 2)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  by_cases hχ : χ = 1
  · have hN : N = 1 := by
      have h := hprim
      rw [DirichletCharacter.IsPrimitive, hχ, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    simp only [LFunction_modOne_eq] at hLs ⊢
    simp only [Nat.cast_one, one_mul] at hlog ⊢
    have hs1' : s ≠ 1 := by
      rintro rfl
      norm_num at ht
    obtain ⟨hfin, hcount, hbound⟩ := h₂ s hs1 hs2 hs1' hLs
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hbound
    refine ⟨hfin.toFinset, fun w => by simp, ?_, ?_⟩
    · nlinarith
    · have hinv : ‖1 / (s - 1)‖ ≤ 1 / 2 := by
        have h : 2 ≤ ‖s - 1‖ := le_trans ht (by simpa using Complex.abs_im_le_norm (s - 1))
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le (by norm_num) h
      calc ‖deriv riemannZeta s / riemannZeta s
            - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖
          = ‖(deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
            - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)) - 1 / (s - 1)‖ := by
            congr 1; ring
        _ ≤ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)
            - ∑ w ∈ hfin.toFinset, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ + ‖1 / (s - 1)‖ :=
            norm_sub_le _ _
        _ ≤ C₂ * Real.log (|s.im| + 2) + 1 / 2 := add_le_add hbound hinv
        _ ≤ (C₁ + C₂ + 1) * Real.log (|s.im| + 2) := by nlinarith
  · obtain ⟨hfin, hcount, hbound⟩ := h₁ N χ hχ s hs1 hs2 hLs
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hcount hbound
    refine ⟨hfin.toFinset, fun w => ?_, ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => LFunction_apply_one_ne_zero hχ (h ▸ h2), h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    · nlinarith
    · nlinarith
end GlobalTheory.GoodHeight
