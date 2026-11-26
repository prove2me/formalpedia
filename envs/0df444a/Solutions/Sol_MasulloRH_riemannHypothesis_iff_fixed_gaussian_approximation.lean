-- Prove2me | solution 1 for MasulloRH.riemannHypothesis_iff_fixed_gaussian_approximation
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:26:25.480647+00:00
-- url     : https://prove2.me/submissions/b6368427-229e-4957-a869-8c2c7285fea2

import Definitions.Def_MasulloRH_FixedGaussianTest
import Theorems.Thm_MasulloRH_fixed_gaussian_energy_lower_at_every_zeta_zero
import Theorems.Thm_MasulloRH_fixed_gaussian_approximation_above_mertens_boundary
import Theorems.Thm_MasulloRH_finite_theta_energy_approximation_of_mertens_bound
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.FixedGaussianTest MasulloRH.GaussianApproximation

private lemma edges (k : ℕ) : center k-width k=left k ∧ center k+width k=right := by
  unfold center width
  constructor <;> ring

private lemma inside (k : ℕ) :
    (1/2:ℝ)<left k ∧ left k<right ∧ right<1 := by
  have hden : (1:ℝ)≤(k:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have h1 := div_le_self (by norm_num : (0:ℝ)≤12287/32768) hden
  have lo : 0<(12287/32768:ℝ)/((k:ℝ)+1) := by positivity
  unfold left right
  exact ⟨by linarith,by linarith,by linarith⟩

private lemma covers (x : ℝ) (hl : 1/2<x) (hr : x<right) :
    ∃ k : ℕ, left k<x ∧ x<right := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/(x-1/2))
  have h₁ := (div_lt_iff₀ (by linarith : 0<x-1/2)).1 hk
  have h₂ : (12287/32768:ℝ)/((k:ℝ)+1)<x-1/2 := (div_lt_iff₀ (by positivity)).2 (by nlinarith)
  exact ⟨k,by dsimp [left];linarith,hr⟩

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

/-- RH is equivalent to approximating a single fixed Gaussian on a countable
family of windows ending at seven eighths, to arbitrarily small weighted error. -/
theorem solution : RiemannHypothesis ↔ ∀ k : ℕ, Approximates k := by
  constructor
  · intro hRH k ε hε
    obtain ⟨hL,hLR,hR⟩ := inside k
    let t := (left k-1/2)/2
    have ht : 0<t := by dsimp [t];linarith
    have hM := moebius_summatory_rpow_bound_of_riemannHypothesis hRH t ht
    obtain ⟨m,a,y,_,he⟩ := MasulloRH.finite_theta_energy_approximation_of_mertens_bound
      (1/2+t) (center k) (width k) 0 ε (by linarith) (by dsimp [width];linarith)
      (by norm_num) (by rw [(edges k).1];dsimp [t];linarith) (by rwa [(edges k).2]) hM hε
    exact ⟨m,a,y,he⟩
  · intro h
    have nozero (s : ℂ) (hx : 1/2<s.re) (hx' : s.re<1) : riemannZeta s≠0 := by
      by_cases capped : s.re<right
      · obtain ⟨k,hl,hr⟩ := covers s.re hx capped
        apply excludes (center k) (width k) (by rw [(edges k).1];linarith [(inside k).1])
          (by rw [(edges k).2];exact (inside k).2.2) s
          (abs_lt.mpr ⟨by linarith [(edges k).1],by linarith [(edges k).2]⟩) (h k)
      · have above : (0.8749570698:ℝ)<s.re := by dsimp [right] at capped;linarith
        let l := ((0.8749570698:ℝ)+s.re)/2
        let r := (s.re+1)/2
        let c := (l+r)/2
        let b := (r-l)/2
        have ea : c-b=l := by dsimp [c,b];ring
        have eb : c+b=r := by dsimp [c,b];ring
        have ha : (0.8749570698:ℝ)<c-b := by rw [ea];dsimp [l];linarith
        have hb : c+b<1 := by rw [eb];dsimp [r];linarith
        have inw : |s.re-c|<b := abs_lt.mpr ⟨by dsimp [c,b,r,l];linarith,by dsimp [c,b,r,l];linarith⟩
        apply excludes c b (by linarith) hb s inw
        intro ε hε
        exact MasulloRH.fixed_gaussian_approximation_above_mertens_boundary 0 c b ε
          (by norm_num) ((abs_nonneg _).trans inw.le) ha hb hε
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
