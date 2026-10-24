-- Prove2me | solution 1 for NetFeePlatform.InteropFee.proposition_7b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:19:25.709552+00:00
-- url     : https://prove2.me/submissions/2938671d-a320-4004-906c-ec656ad9e779

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_InteropFee_Symmetric
import Theorems.Thm_NetFeePlatform_InteropFee_xi_characterization
import Theorems.Thm_NetFeePlatform_InteropFee_xi_sub
import Theorems.Thm_NetFeePlatform_InteropFee_xi_pos_below

open NetFeePlatform.InteropFee

theorem solution {J : ℕ} (hJ : 2 ≤ J) (w c γ lamLo lamHi tLo : ℝ) (hw : 0 ≤ w)
    (hγ : 0 < γ) (hγ' : γ ≤ 27 / 8) (hlo : 0 ≤ lamLo) (hlt : lamLo < lamHi) (hhi : lamHi ≤ 1)
    (htLo : NetFeePlatform.Competition.IsEquilibrium w c γ lamLo (fun _ : Fin J => tLo)) :
    ((3 ≤ J ∨ 0 < w) → ∃ tHi : ℝ, tHi < tLo ∧ NetFeePlatform.Competition.IsEquilibrium w c γ lamHi (fun _ : Fin J => tHi)) ∧
      (J = 2 → w = 0 → NetFeePlatform.Competition.IsEquilibrium w c γ lamHi (fun _ : Fin J => tLo)) := by
  have hhi0 : 0 ≤ lamHi := le_of_lt (lt_of_le_of_lt hlo hlt)
  have hlo1 : lamLo ≤ 1 := le_trans hlt.le hhi
  have hxiLo : xi w c γ lamLo J tLo = 0 :=
    (xi_characterization hJ w c γ lamLo tLo hw hlo hlo1).1 htLo
  have hJR : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  -- positivity / bounds on the symmetric share
  have hden : ∀ τ : ℝ, 0 < w + (J : ℝ) * Real.exp (-τ) := fun τ => by
    have := Real.exp_pos (-τ); nlinarith
  have hnpos : ∀ τ : ℝ, 0 < nSym w J τ := fun τ => by
    unfold nSym; exact div_pos (Real.exp_pos _) (hden τ)
  have hnlt : ∀ τ : ℝ, nSym w J τ < 1 := fun τ => by
    unfold nSym; rw [div_lt_one (hden τ)]
    have := Real.exp_pos (-τ); nlinarith
  have hcontn : Continuous (fun τ => nSym w J τ) := by
    unfold nSym
    exact Continuous.div (by fun_prop) (by fun_prop) (fun τ => (hden τ).ne')
  have hcont : Continuous (fun τ => xi w c γ lamHi J τ) := by
    have h1 : ∀ τ, 1 - nSym w J τ ≠ 0 := fun τ => by linarith [hnlt τ]
    have hc1 : Continuous (fun τ => 1 / (1 - nSym w J τ)) :=
      Continuous.div continuous_const (continuous_const.sub hcontn) h1
    have hc2 : Continuous (fun τ => phiSym w J τ) := by
      unfold phiSym
      exact Continuous.div (continuous_const.mul hcontn) (continuous_const.sub hcontn) h1
    unfold xi
    fun_prop
  refine ⟨fun hcase => ?_, fun hJ2 hw0 => ?_⟩
  · obtain ⟨hsub, hpos, -⟩ := xi_sub hJ w c γ lamLo lamHi tLo hw
    have hneg : xi w c γ lamHi J tLo < 0 := by
      rw [hsub, hxiLo]
      have := mul_pos (mul_pos (mul_pos hγ (sub_pos.mpr hlt)) (hpos hcase)) (hnpos tLo)
      linarith
    set τ0 := min (tLo - 1) (c - 2 * γ - γ * lamHi * ((J : ℝ) - 1) - 1) with hτ0
    have hτ0a : τ0 < tLo := by
      have := min_le_left (tLo - 1) (c - 2 * γ - γ * lamHi * ((J : ℝ) - 1) - 1); linarith
    have hτ0b : τ0 < c - 2 * γ - γ * lamHi * ((J : ℝ) - 1) := by
      have := min_le_right (tLo - 1) (c - 2 * γ - γ * lamHi * ((J : ℝ) - 1) - 1); linarith
    have hposτ0 : 0 < xi w c γ lamHi J τ0 :=
      xi_pos_below hJ w c γ lamHi hw hγ.le hhi0 hhi τ0 hτ0b
    have hivt := intermediate_value_Icc' hτ0a.le hcont.continuousOn
    have hmem : (0 : ℝ) ∈ Set.Icc (xi w c γ lamHi J tLo) (xi w c γ lamHi J τ0) :=
      ⟨hneg.le, hposτ0.le⟩
    obtain ⟨tHi, ⟨_, htHi2⟩, hzero⟩ := hivt hmem
    have hne : tHi ≠ tLo := by
      intro h; rw [h] at hzero; linarith
    refine ⟨tHi, lt_of_le_of_ne htHi2 hne, ?_⟩
    exact (xi_characterization hJ w c γ lamHi tHi hw hhi0 hhi).2 hγ' hzero
  · obtain ⟨hsub, -, hzero⟩ := xi_sub hJ w c γ lamLo lamHi tLo hw
    have : xi w c γ lamHi J tLo = 0 := by
      rw [hsub, hxiLo, hzero hJ2 hw0]; ring
    exact (xi_characterization hJ w c γ lamHi tLo hw hhi0 hhi).2 hγ' this
