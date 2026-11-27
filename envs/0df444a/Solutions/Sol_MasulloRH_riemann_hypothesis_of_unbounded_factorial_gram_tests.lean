-- Prove2me | solution 1 for MasulloRH.riemann_hypothesis_of_unbounded_factorial_gram_tests
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:29:45.43063+00:00
-- url     : https://prove2.me/submissions/f5ad2cae-1821-4dd4-ba12-4b16930e0da6

import Theorems.Thm_MasulloRH_fixed_gaussian_tail_iff_factorial_gram_tests
import Theorems.Thm_MasulloRH_thirty_seven_shift_gram_passes_first_16666_tests
import Theorems.Thm_MasulloRH_fixed_gaussian_cofinal_tests_iff_each_window
import Definitions.Def_MasulloRH_FixedGaussianTest
import Theorems.Thm_MasulloRH_fixed_gaussian_energy_lower_at_every_zeta_zero
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation

private lemma edges (k : ℕ) : fullCenter k-fullWidth k=left k ∧ fullCenter k+fullWidth k=upper k := by
  unfold fullCenter fullWidth
  constructor <;> ring

private lemma inside (k : ℕ) :
    (1/2:ℝ)<left k ∧ left k<upper k ∧ upper k<1 := by
  have hden : (1:ℝ) ≤ (k:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have h1 := div_le_self (by norm_num : (0:ℝ) ≤ 12287/32768) hden
  have lo : 0<(12287/32768:ℝ)/((k:ℝ)+1) := by positivity
  have hl : left k<right := by unfold left right;linarith
  exact ⟨by unfold left;linarith,hl.trans_le (le_max_left _ _),
    max_lt (by norm_num [right]) (sub_lt_self _ (by positivity))⟩

private lemma covers (x : ℝ) (hl : 1/2<x) (hr : x<1) :
    ∃ k : ℕ, left k<x ∧ x<upper k := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (1/(x-1/2)) (1/(1-x)))
  have ha := (div_lt_iff₀ (by linarith : 0<x-1/2)).1 ((le_max_left _ _).trans_lt hk)
  have hb := (div_lt_iff₀ (by linarith : 0<1-x)).1 ((le_max_right _ _).trans_lt hk)
  have h₂ : (12287/32768:ℝ)/((k:ℝ)+1)<x-1/2 := (div_lt_iff₀ (by positivity)).2 (by nlinarith)
  have h₃ : 1/((k:ℝ)+1)<1-x := (div_lt_iff₀ (by positivity)).2 (by nlinarith)
  exact ⟨k,by unfold left;linarith, (show x<1-1/((k:ℝ)+1) by linarith).trans_le (le_max_right _ _)⟩

private theorem excludes (c b : ℝ) (hl : 0<c-b) (hr : c+b<1) (s : ℂ) (hx : |s.re-c|<b)
    (approx : ∀ ε : ℝ, 0<ε → ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy c b (residual 0 (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ))) < ε) :
    riemannZeta s≠0 := by
  intro hz
  have hb : 0<b := (abs_nonneg _).trans_lt hx
  have sign := mul_pos (sub_pos.mpr (abs_lt.mp hx).2) (show 0<b+(s.re-c) by linarith [(abs_lt.mp hx).1])
  let ε := Real.exp ((s.re^2-s.im^2)/2)*((b^2-(s.re-c)^2)/b)
  have pos : 0<ε := mul_pos (Real.exp_pos _) (div_pos (by nlinarith) hb)
  obtain ⟨m,a,y,he⟩ := approx ε pos
  exact he.not_ge (MasulloRH.fixed_gaussian_energy_lower_at_every_zeta_zero c b hl hr
    (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I) (fun i => (y i:ℝ)) s hx hz)

theorem solution (h : ∀ j : ℕ, 16666 ≤ j → ∃ n : ℕ, MasulloRH.RationalThetaGrid.passes j n) : RiemannHypothesis := by
  have allTests (j : ℕ) : ∃ n : ℕ, MasulloRH.RationalThetaGrid.passes j n := by
    by_cases hj : j < 16666
    · exact ⟨3,MasulloRH.thirty_seven_shift_gram_passes_first_16666_tests j hj⟩
    · exact h j (Nat.le_of_not_gt hj)
  have tail := MasulloRH.fixed_gaussian_tail_iff_factorial_gram_tests.2 (fun j _ => allTests j)
  have h : ∀ k : ℕ, FullApprox k := by
    apply MasulloRH.fixed_gaussian_cofinal_tests_iff_each_window.2
    intro j hj
    obtain ⟨k,hk,m,a,y,he⟩ := tail (max j 16384) (le_max_right _ _)
    have co : j+1 ≤ k := (Nat.succ_le_succ (le_max_left j 16384)).trans hk
    have cm : (j:ℝ) ≤ (max j 16384:ℕ) := by exact_mod_cast le_max_left j 16384
    exact ⟨k,co,m,a,y,he.trans_le (one_div_le_one_div_of_le (by positivity) (by linarith only [cm]))⟩
  have nozero (s : ℂ) (hx : 1/2<s.re) (hx' : s.re<1) : riemannZeta s≠0 := by
    obtain ⟨k,hl,hr⟩ := covers s.re hx hx'
    apply excludes (fullCenter k) (fullWidth k) (by rw [(edges k).1];linarith [(inside k).1])
      (by rw [(edges k).2];exact (inside k).2.2) s
      (abs_lt.mpr ⟨by linarith [(edges k).1],by linarith [(edges k).2]⟩) (h k)
  apply riemannHypothesis_iff_zeros_in_strip_on_line.2
  intro s hz h₀ h₁
  rcases lt_trichotomy s.re (1/2) with hlt|heq|hgt
  · have hnat (n : ℕ) : s≠ -n := by
      intro eq
      have re := congrArg Complex.re eq
      simp at re
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hne : s≠1 := by intro e;simp [e] at h₁
    have reflected : riemannZeta (1-s)=0 := by rw [riemannZeta_one_sub hnat hne,hz,mul_zero]
    exact (nozero (1-s) (by simp only [Complex.sub_re,Complex.one_re];linarith)
      (by simp only [Complex.sub_re,Complex.one_re];linarith) reflected).elim
  · exact heq
  · exact (nozero s hgt h₁ hz).elim
