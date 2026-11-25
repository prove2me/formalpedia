-- Prove2me | solution 1 for GlobalTheory.ZeroWindow.count_zeros_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:14.374674+00:00
-- url     : https://prove2.me/submissions/4b951595-789f-475a-9d29-e9a62ffe0e54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
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
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
namespace GlobalTheory.ZeroWindow
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma norm_sub_two_add_le_of_mem_strip {ρ : ℂ} {t : ℝ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (ht : |ρ.im - t| ≤ 1) : ‖ρ - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hre : (ρ - (2 + (t : ℂ) * I)).re = ρ.re - 2 := by simp
  have him : (ρ - (2 + (t : ℂ) * I)).im = ρ.im - t := by simp
  rw [hre, him, abs_of_neg (by linarith)]
  linarith
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
private lemma finsum_mem_le_of_subset_of_nonneg {S D : Set ℂ} (f : ℂ → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hD : D.Finite) (hSD : S ⊆ D) :
    ∑ᶠ x ∈ S, f x ≤ ∑ᶠ x ∈ D, f x := by
  rw [finsum_mem_eq_finite_toFinset_sum f (hD.subset hSD), finsum_mem_eq_finite_toFinset_sum f hD]
  exact Finset.sum_le_sum_of_subset_of_nonneg (by simpa using hSD) (fun x _ _ => hf x)
end GlobalTheory.ZeroWindow
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ZeroWindow
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
namespace GlobalTheory.ZeroWindow
namespace _root_.GlobalTheory.ZeroWindow
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0}.Finite ∧
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) ≤ C * Real.log (N * (|t| + 2)) := by
  obtain ⟨C1, hC1, hL⟩ := _root_.GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C2, hC2, hZ⟩ := _root_.GlobalTheory.ZetaWide.main
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun N _ χ hχ t => ?_⟩
  set s : ℂ := 2 + (t : ℂ) * I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  by_cases h1χ : χ = 1
  · have hN : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, h1χ, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    have hLz : LFunction χ = riemannZeta := LFunction_modOne_eq
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hsre] at this
      norm_num at this
    obtain ⟨hfin, hsum, -⟩ := hZ s (by rw [hsre]; norm_num) (by rw [hsre]) hs1
      (riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; norm_num))
    rw [hsim] at hfin hsum
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0} ⊆
        {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0} := by
      rintro ρ ⟨h0, h1, h2, h3⟩
      refine ⟨norm_sub_two_add_le_of_mem_strip h0 h1 h2, ?_, by rwa [hLz] at h3⟩
      rintro rfl
      simp at h1
    refine ⟨hfin.subset hsub, ?_⟩
    calc ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ)
        ≤ ∑ᶠ ρ ∈ {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ w ≠ 1 ∧ riemannZeta w = 0},
          ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
          rw [hLz]
          exact finsum_mem_le_of_subset_of_nonneg _ (fun _ => Nat.cast_nonneg _) hfin
            (by rw [hLz] at hsub; exact hsub)
      _ ≤ C2 * Real.log (|t| + 2) := hsum
      _ ≤ max C1 C2 * Real.log (((1 : ℕ) : ℝ) * (|t| + 2)) := by
          rw [Nat.cast_one, one_mul]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.log_nonneg (by linarith))
  · have hLs : LFunction χ s ≠ 0 :=
      LFunction_ne_zero_of_one_le_re χ (Or.inl h1χ) (by rw [hsre]; norm_num)
    obtain ⟨hfin, hsum, -⟩ := hL N χ h1χ s (by rw [hsre]; norm_num) (by rw [hsre]) hLs
    rw [hsim] at hfin hsum
    have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0} ⊆
        {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0} := by
      rintro ρ ⟨h0, h1, h2, h3⟩
      exact ⟨norm_sub_two_add_le_of_mem_strip h0 h1 h2, h3⟩
    refine ⟨hfin.subset hsub, ?_⟩
    calc ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ)
        ≤ ∑ᶠ ρ ∈ {w : ℂ | ‖w - (2 + (t : ℂ) * I)‖ ≤ 7 / 2 ∧ LFunction χ w = 0},
          ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) :=
          finsum_mem_le_of_subset_of_nonneg _ (fun _ => Nat.cast_nonneg _) hfin hsub
      _ ≤ C1 * Real.log (N * (|t| + 2)) := hsum
      _ ≤ max C1 C2 * Real.log (N * (|t| + 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.log_nonneg (by nlinarith))
end _root_.GlobalTheory.ZeroWindow
end GlobalTheory.ZeroWindow
