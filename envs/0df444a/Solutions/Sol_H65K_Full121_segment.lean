-- Prove2me | solution 1 for H65K.Full121.segment
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:52:29.325217+00:00
-- url     : https://prove2.me/submissions/494f9261-9e58-4e48-8db2-2a0b9d68e271

import Theorems.Thm_Arb4_H1000_E_T121_hAH
import Theorems.Thm_Arb4_H1000_S_L121_clear
import Theorems.Thm_Arb4_Q_cv_add
import Theorems.Thm_Arb4_Q_cv_frac
import Theorems.Thm_Arb4_Q_cv_nat
import Theorems.Thm_Arb4_Q_cv_sub
import Theorems.Thm_Arb4_k6side_of_B
import Theorems.Thm_BandGlue_BandData_CapGeom_of_sqrt
import Theorems.Thm_H11K_boxCert_of_parts_sharp
import Theorems.Thm_H11K_validS_of_B
import Theorems.Thm_H65K_Count121_chk
import Theorems.Thm_H65K_Edge_hAH
import Theorems.Thm_H65K_Platform_Bridge520_zeros
import Theorems.Thm_H65K_Platform_High_zeros
import Theorems.Thm_H65K_Platform_Low121_zeros
import Theorems.Thm_H65K_Platform_Low_zeros
import Theorems.Thm_H65K_Slab_clear
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_BandZeros_hLine
import Theorems.Thm_RS5_BandZeros_mono
import Theorems.Thm_ZeroFreeBridge_dlvpRateC_lower
import Theorems.Thm_ZetaZeroConfinement_zero_in_band
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Complex Arb4 Arb4.Q

namespace H65K.Capstone121NoFloor

noncomputable def G_T121 : GamD := H65K.Count121.G0
noncomputable def G_T65000 : GamD := H65K.Count121.G1
noncomputable def cB : ℂ := ⟨1 / 2, 65121 / 2⟩
noncomputable def RB : ℝ := Real.sqrt (4209284657 / 4)

theorem hs1B : (1 : ℂ) ∉ Metric.ball cB RB := by
  rw [Metric.mem_ball, Complex.dist_eq_re_im]
  unfold cB RB
  intro hlt
  simp only [Complex.one_re, Complex.one_im] at hlt
  have hle : Real.sqrt (4209284657 / 4 : ℝ) ≤
      Real.sqrt (((1 : ℝ) - (1 / 2)) ^ 2 + ((0 : ℝ) - 65121 / 2) ^ 2) :=
    Real.sqrt_le_sqrt (by norm_num)
  linarith [hlt, hle]

noncomputable def band : BandGlue.BandData :=
  ⟨121, 65000, 85250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cB, RB, hs1B⟩

noncomputable def E : EnclQ := H65K.Count121.E

theorem chk : (H11K.validBS (Q.ofNat 121) (Q.ofNat 65000) (Q.frac 65121 2)
    (Q.frac 4209284657 4) 85250 E && k6sideB G_T121 G_T65000 E) = true := by
  exact H65K.Count121.chk

def LineHyp : Prop := ∃ xs : List ℝ, xs.length = 85250 ∧ xs.IsChain (· < ·) ∧
  (∀ t ∈ xs, (121 : ℝ) ≤ t ∧ t ≤ (65000 : ℝ)) ∧
  (∀ t ∈ xs, completedRiemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)

theorem box (hLine : LineHyp) : BandGlue.BoxCert (1 / 4000000) (3999999 / 4000000) 121 65000 := by
  have hc := chk
  rw [Bool.and_eq_true] at hc
  have hT0 : band.T0 = (Q.ofNat 121).val := (Q.cv_nat 121).symm
  have hT1 : band.T1 = (Q.ofNat 65000).val := (Q.cv_nat 65000).symm
  have hcc : band.c = (⟨1 / 2, (Q.frac 65121 2).val⟩ : ℂ) := by rw [Q.cv_frac 65121 2]; rfl
  have hR : band.R = Real.sqrt (Q.frac 4209284657 4).val := by rw [Q.cv_frac 4209284657 4]; rfl
  have hG : band.CapGeom (5773 / 100000) (3 / 1000) :=
    BandGlue.BandData.CapGeom.of_sqrt 121 65000 (65121 / 2) (4209284657 / 4) rfl rfl rfl rfl
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine H11K.boxCert_of_parts_sharp band E (show (121 : ℝ) ≤ 121 from le_rfl)
    (show (65000 : ℝ) ≤ 65000 from le_rfl)
    (H11K.validS_of_B _ _ _ _ _ E hT0 hT1 hcc hR hc.1) hG
    ?_ ?_ ?_ (k6side_of_B _ G_T121 G_T65000 E hT0 hT1 hc.2) ?_ ?_
  · exact hLine
  · exact Arb4.H1000.S_L121_clear
  · exact H65K.Slab.clear
  · exact H65K.Edge.hAH
  · exact Arb4.H1000.E_T121_hAH

theorem haC_65000 : (1 / 4000000 : ℝ) ≤ ZeroFreeBridge.dlvpRateC / Real.log 65000 := by
  have hlog : Real.log 65000 ≤ 12 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h12 : Real.exp 12 = (Real.exp 1) ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) he1 12
    rw [h12]; nlinarith [hpow]
  have hpos : 0 < Real.log 65000 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos]
  calc (1 / 4000000 : ℝ) * Real.log 65000
      ≤ (1 / 4000000) * 12 := by nlinarith [hlog, hpos]
    _ ≤ 9 / 1369088 := by norm_num
    _ ≤ ZeroFreeBridge.dlvpRateC := ZeroFreeBridge.dlvpRateC_lower

noncomputable def bnd : ℕ → ℝ := fun i => if i = 0 then 121 else 65000

theorem bnd_mono : Monotone bnd := by
  intro i j hij
  unfold bnd
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem segment (hLine : LineHyp) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (121 : ℝ) ≤ ρ.im →
      ρ.im ≤ 65000 → ρ.re = 1 / 2 := by
  intro ρ hz him0 himA himB
  have hγ : (55 / 16 : ℝ) ≤ |ρ.im| := by
    rw [abs_of_pos him0]
    linarith
  obtain ⟨hlo, hhi⟩ := ZetaZeroConfinement.zero_in_band
    (1 / 4000000) 65000 haC_65000 (by norm_num) (by norm_num) hz him0 himB hγ
  have hre_eq : (1 : ℝ) - 1 / 4000000 = 3999999 / 4000000 := by norm_num
  obtain ⟨d, hdlo, hdhi, hStmt, hInputs⟩ := box hLine
  exact hStmt hInputs.1 hInputs.2 ρ ⟨hlo, by linarith [hhi, hre_eq]⟩
    ⟨le_trans hdlo himA, le_trans himB hdhi⟩ hz

end H65K.Capstone121NoFloor


theorem solution :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → (121 : ℝ) ≤ ρ.im →
      ρ.im ≤ 65000 → ρ.re = 1 / 2 := by

  have h0 := H65K.Platform.Low121.zeros.glue (by norm_num) (by norm_num)
    H65K.Platform.Bridge520.zeros
  have h1 := h0.glue (by norm_num) (by norm_num) H65K.Platform.Low.zeros
  have h2 := h1.glue (by norm_num) (by norm_num) H65K.Platform.High.zeros
  have h := h2.mono (show (121 : ℝ) ≤ 121 from le_rfl)
    (show (4259840000 : ℝ) / 65536 ≤ 65000 by norm_num)
  exact H65K.Capstone121NoFloor.segment h.hLine
