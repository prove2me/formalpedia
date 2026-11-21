-- Prove2me | solution 1 for NymanBeurling.damped_moebius_limit_profile_tail_tightness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T04:07:26.66887+00:00
-- url     : https://prove2.me/submissions/64609eb4-5039-4a3f-be69-410f5304346d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_moebius_polynomial_critical_strip_bound
import Theorems.Thm_NymanBeurling_shifted_zeta_critical_line_ratio_bound
import Theorems.Thm_NymanBeurling_damped_mellin_completion_of_polynomial_bound
import Theorems.Thm_NymanBeurling_damped_spectral_vanishing_of_ratio_bound
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ (H₀ : ℕ) (ε₀ : ℝ), 0 < ε₀ ∧ ε₀ ≤ 1/2 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ H : ℕ,
        (∑ n ∈ Finset.Ico H₀ H,
          (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
            ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by
  obtain ⟨ε₀,hε₀,hhalf,hsmall⟩ :=
    NymanBeurling.damped_spectral_vanishing_of_ratio_bound
      NymanBeurling.shifted_zeta_critical_line_ratio_bound
      (2*Real.pi*δ) (by positivity)
  refine ⟨0,ε₀,hε₀,hhalf,?_⟩
  intro ε hε hεsmall H
  obtain ⟨hsumm,hintegrable,hparseval⟩ :=
    (NymanBeurling.damped_mellin_completion_of_polynomial_bound
      NymanBeurling.moebius_polynomial_critical_strip_bound).2
      ε hε (hεsmall.trans_le hhalf)
  have hspec := (hsmall ε hε hεsmall).2
  rw [hparseval] at hspec
  have htotal : (∑' n : ℕ, (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
      ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by
    exact (mul_lt_mul_iff_right₀ (by positivity : 0 < 2*Real.pi)).mp hspec
  have hprefix : (∑ n ∈ Finset.Ico 0 H,
      (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) ≤
      ∑' n : ℕ, (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ)) := by
    exact hsumm.sum_le_tsum (Finset.Ico 0 H) (fun n _ => by positivity)
  exact hprefix.trans_lt htotal
