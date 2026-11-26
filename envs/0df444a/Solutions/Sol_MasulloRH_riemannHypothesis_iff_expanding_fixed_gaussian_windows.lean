-- Prove2me | solution 1 for MasulloRH.riemannHypothesis_iff_expanding_fixed_gaussian_windows
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:26:26.334706+00:00
-- url     : https://prove2.me/submissions/55ea4e90-8552-4dab-b42f-9336282fe86a

import Definitions.Def_MasulloRH_FixedGaussianTest
import Theorems.Thm_MasulloRH_fixed_gaussian_energy_lower_at_every_zeta_zero
import Theorems.Thm_MasulloRH_finite_theta_energy_approximation_of_mertens_bound
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation

private lemma edges (k : ℕ) : fullCenter k-fullWidth k=left k ∧ fullCenter k+fullWidth k=upper k := by
  unfold fullCenter fullWidth
  constructor <;> ring

private lemma inside (k : ℕ) :
    (1/2:ℝ)<left k ∧ left k<upper k ∧ upper k<1 := by
  have hden : (1:ℝ)≤(k:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have h1 := div_le_self (by norm_num : (0:ℝ)≤12287/32768) hden
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

/-- A single fixed Gaussian tested on windows exhausting the right half of the critical strip characterizes RH. -/
theorem solution : RiemannHypothesis ↔ ∀ k : ℕ, FullApprox k := by
  constructor
  · intro hRH k ε hε
    obtain ⟨hL,hLR,hR⟩ := inside k
    let t := (left k-1/2)/2
    have ht : 0<t := by dsimp [t];linarith
    have hM := moebius_summatory_rpow_bound_of_riemannHypothesis hRH t ht
    obtain ⟨m,a,y,_,he⟩ := MasulloRH.finite_theta_energy_approximation_of_mertens_bound
      (1/2+t) (fullCenter k) (fullWidth k) 0 ε (by linarith) (by dsimp [fullWidth];linarith)
      (by norm_num) (by rw [(edges k).1];dsimp [t];linarith) (by rwa [(edges k).2]) hM hε
    exact ⟨m,a,y,he⟩
  · intro h
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
