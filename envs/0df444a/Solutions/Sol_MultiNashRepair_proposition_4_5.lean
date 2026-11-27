-- Prove2me | solution 1 for MultiNashRepair.proposition_4_5
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:40:39.659913+00:00
-- url     : https://prove2.me/submissions/a62417b4-7091-44dc-b8f2-62b6e4290ead

import Mathlib
import Definitions.Def_MultiNashRepair_Controls

open MultiNashRepair

theorem MNR45d_sigmaStar_ge_one : (1 : ℝ) ≤ sigmaStar := by
  unfold sigmaStar
  apply le_csSup
  · refine ⟨2, ?_⟩
    rintro s ⟨_, h2, _⟩; exact h2
  · refine ⟨le_rfl, by norm_num, ?_⟩
    unfold sigmaPoly; norm_num

theorem MNR45d_U_nonneg : (0 : ℝ) ≤ U (3/5) := by
  unfold U
  apply le_csInf
  · exact ⟨_, Set.mem_image_of_mem _ (⟨le_rfl, by norm_num⟩ : (0:ℝ) ∈ Set.Icc 0 (3/5))⟩
  · rintro _ ⟨H, ⟨h0, h1⟩, rfl⟩
    unfold Kf
    apply div_nonneg
    · apply mul_nonneg (by linarith); nlinarith
    · apply mul_nonneg (by norm_num) (by linarith)

theorem MNR45d_uOf : uOf 10 = 1/288 := by
  unfold uOf; norm_num [min_def]

theorem MNR45d_etaOf : etaOf 10 = 1/8 := by
  unfold etaOf; norm_num [min_def]

def MNR45d_ctrl : Controls (-100) where
  d := 10
  d_pos := by norm_num
  d_reserve := by
    have := MNR45d_sigmaStar_ge_one
    push_cast; linarith
  f0 := 3/5
  f0_ge := by norm_num
  f0_le := by norm_num
  f0_U := by
    have := MNR45d_U_nonneg
    push_cast; linarith
  f0_inv := by push_cast; norm_num
  m0 := 100000000
  m0_ge_d := by push_cast; norm_num
  m0_ge_u := by rw [MNR45d_uOf]; push_cast; norm_num
  m0_ge_d' := by push_cast; norm_num

theorem MNR45d_knobs : MNR45d_ctrl.knobs = ⟨3/5, 1/288⟩ := by
  have hu : MNR45d_ctrl.u = 1/288 := MNR45d_uOf
  simp only [Controls.knobs, hu]
  have hf : MNR45d_ctrl.f0 = 3/5 := rfl
  rw [hf]; push_cast; rfl

theorem MNR45d_eta : (MNR45d_ctrl.η : ℝ) = 1/8 := by
  have : MNR45d_ctrl.η = 1/8 := MNR45d_etaOf
  rw [this]; norm_num

theorem MNR45d_Su : (⟨3/5, 1/288⟩ : Knobs).Su (1/2) < 15 := by
  norm_num [Knobs.Su, Knobs.Cu, Knobs.R0, Knobs.rho, Knobs.beta, Knobs.c, Knobs.t, Knobs.u0,
    Knobs.Q, Knobs.nu]

theorem MNR45d_L0 : (1/2 : ℝ) ≤ (⟨3/5, 1/288⟩ : Knobs).L0 := by
  norm_num [Knobs.L0, Knobs.c, Knobs.t]

theorem solution : ¬ (∀ {σ : ℚ} (ctrl : Controls σ) {m : ℕ} (hm : ctrl.m0 ≤ m) (ς H : ℝ)
    (hH0 : 0 < H) (hHL : H ≤ ctrl.knobs.L0) (hς : ς < σ),
    let k := ctrl.knobs
    let d : ℝ := ctrl.d
    let η : ℝ := ctrl.η
    let mu := ctrl.mu ς H
    (∀ Z P ς' H' : ℝ, 0 ≤ Z → Z ≤ 1 → 1 - η * Z ≤ P → P ≤ 1 →
      P * ((1 + η * Z) * ς + η * mu) ≤ ς' → H' = P * H →
      η * d / 2 ≤ H * (k.Phihat d ς' H' - k.Phihat d ς H)) ∧
    (∀ E ς' H' : ℝ, 0 ≤ E → E ≤ 120 * (ctrl.u : ℝ) / m →
      k.c * ς + k.Dsh H - E ≤ ς' → H' = k.c * (H + k.t) →
      3 * d * (1 - k.c) ≤ H * (k.Phihat d ς' H' - k.Phihat d ς H)) ∧
    0 < η * d / 2 ∧ 0 < 3 * d * (1 - k.c)) := by
  intro h
  have hk := MNR45d_knobs
  have hη := MNR45d_eta
  have hL : (1/2 : ℝ) ≤ MNR45d_ctrl.knobs.L0 := by rw [hk]; exact MNR45d_L0
  have hh := (h MNR45d_ctrl (m := 100000000) le_rfl (-101) (1/2) (by norm_num) hL
    (by push_cast; norm_num)).1
  have hd : ((MNR45d_ctrl.d : ℚ) : ℝ) = 10 := by
    show (((10 : ℚ)) : ℝ) = 10; norm_num
  set S := MNR45d_ctrl.knobs.Su (1/2) with hS
  have hS15 : S < 15 := by rw [hS, hk]; exact MNR45d_Su
  have hmu : MNR45d_ctrl.mu (-101) (1/2) = S - (-101) - 10 := by
    simp only [Controls.mu, hd]; rfl
  have := hh 1 1 ((1 + (MNR45d_ctrl.η : ℝ) * 1) * (-101) + (MNR45d_ctrl.η : ℝ) * MNR45d_ctrl.mu (-101) (1/2))
    (1 * (1/2)) (by norm_num) le_rfl (by rw [hη]; norm_num) le_rfl (by rw [one_mul]) rfl
  simp only [Knobs.Phihat, Knobs.Phiu, one_mul] at this
  rw [hmu, hη, hd] at this
  have e : (1 / 2 : ℝ) * (((1 + 1 / 8 * 1) * -101 + 1 / 8 * (S - -101 - 10)) / (1 / 2)
      + MultiNashRepair.Knobs.Fu MNR45d_ctrl.knobs (1 / 2) + 2 * 10 / (1 / 2)
      - (-101 / (1 / 2) + MultiNashRepair.Knobs.Fu MNR45d_ctrl.knobs (1 / 2) + 2 * 10 / (1 / 2)))
      = (S - 10) / 8 := by ring
  rw [e] at this
  linarith
