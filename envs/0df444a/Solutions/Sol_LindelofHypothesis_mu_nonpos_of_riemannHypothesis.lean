-- Prove2me | solution 1 for LindelofHypothesis.mu_nonpos_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:26:14.794972+00:00
-- url     : https://prove2.me/submissions/0e02651c-9ddf-4a38-8558-35c93355043f

import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_logarithmic_control
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_exists_holomorphic_log_normalized
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_borel_caratheodory_closedBall
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_le_of_re_pos
import Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

set_option autoImplicit false

open Complex Metric Set

namespace RHInvZeta

/-- The value `∑ n^{-3/2}`, a uniform bound for `‖ζ‖` on `Re ≥ 3/2`. -/
noncomputable def K₀ : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

lemma summable_K₀ : Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

lemma norm_term_le (z : ℂ) (hz : 3 / 2 ≤ z.re) (n : ℕ) :
    ‖1 / (n : ℂ) ^ z‖ ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz; linarith
    simp [Complex.zero_cpow hz0]
  · rw [norm_div, norm_one, norm_natCast_cpow_of_pos hn, one_div]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le h1 hz)

lemma norm_zeta_le_K₀ {z : ℂ} (hz : 3 / 2 ≤ z.re) : ‖riemannZeta z‖ ≤ K₀ := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by linarith)]
  have hsum : Summable (fun n : ℕ => ‖1 / (n : ℂ) ^ z‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_term_le z hz) summable_K₀
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum (norm_term_le z hz) summable_K₀)

lemma pi_sq_div_six_lt : Real.pi ^ 2 / 6 < 5 / 3 := by
  have h1 := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

lemma norm_zeta_ge {s : ℂ} (hs : 2 ≤ s.re) : 2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := Zeta23.RvM.norm_riemannZeta_sub_one_le hs
  have h2 : ‖(1 : ℂ)‖ ≤ ‖riemannZeta s‖ + ‖riemannZeta s - 1‖ := by
    have := norm_sub_le (riemannZeta s) (riemannZeta s - 1)
    simpa using this
  simp at h2
  linarith

lemma norm_zeta_le_two {s : ℂ} (hs : 2 ≤ s.re) : ‖riemannZeta s‖ ≤ 2 := by
  have h := Zeta23.RvM.norm_riemannZeta_sub_one_le hs
  have h2 : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := by
    have := norm_add_le (riemannZeta s - 1) 1
    simpa using this
  have := pi_sq_div_six_lt
  simp at h2
  linarith

lemma lower_pos : 0 < 2 - Real.pi ^ 2 / 6 := by
  have := pi_sq_div_six_lt; linarith

/-- Under RH, no zeros in `Re s > 1/2` other than possibly `s = 1`. -/
lemma zeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro h0
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s h0 htriv hs1
  linarith

/-- `|log x| ≤ x + 1/x` for `x > 0`. -/
lemma abs_log_le (x : ℝ) (hx : 0 < x) : |Real.log x| ≤ x + x⁻¹ := by
  rw [abs_le]
  constructor
  · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at this
    have : 0 < x := hx
    linarith
  · have := Real.log_le_sub_one_of_pos hx
    have : 0 < x⁻¹ := inv_pos.mpr hx
    linarith

lemma norm_log_le (w : ℂ) (hw : w ≠ 0) : ‖Complex.log w‖ ≤ ‖w‖ + ‖w‖⁻¹ + Real.pi := by
  have h1 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| := Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 := abs_log_le ‖w‖ (norm_pos_iff.mpr hw)
  have h3 : |w.arg| ≤ Real.pi := Complex.abs_arg_le_pi w
  linarith

/-! ### A holomorphic logarithm of `ζ` near `Re s = 2`, bounded uniformly in the height -/

noncomputable def Mre : ℝ := |Real.log K₀| + 1
noncomputable def Ac : ℝ := 2 + (2 - Real.pi ^ 2 / 6)⁻¹ + Real.pi
noncomputable def A₁ : ℝ :=
  max (2 * Mre * (49 / 100) / (1 / 2 - 49 / 100) + Ac * (1 / 2 + 49 / 100) / (1 / 2 - 49 / 100)) 1

lemma Mre_pos : 0 < Mre := by unfold Mre; positivity

lemma Ac_nonneg : 0 ≤ Ac := by
  unfold Ac; have := lower_pos; have := Real.pi_pos; positivity

lemma re_sub_le {z c : ℂ} {r : ℝ} (hz : z ∈ ball c r) : |z.re - c.re| < r := by
  rw [mem_ball, dist_eq_norm] at hz
  have := Complex.abs_re_le_norm (z - c)
  rw [sub_re] at this
  linarith

lemma im_sub_le {z c : ℂ} {r : ℝ} (hz : z ∈ ball c r) : |z.im - c.im| < r := by
  rw [mem_ball, dist_eq_norm] at hz
  have := Complex.abs_im_le_norm (z - c)
  rw [sub_im] at this
  linarith

lemma exists_log_small (c : ℂ) (hc : c.re = 2) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball c (1 / 2)) ∧
      EqOn (Complex.exp ∘ E) riemannZeta (ball c (1 / 2)) ∧
      ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A₁ := by
  have hre : ∀ z ∈ ball c (1 / 2), 3 / 2 < z.re := by
    intro z hz
    have := re_sub_le hz
    rw [hc] at this
    linarith [(abs_lt.mp this).1]
  have hne1 : ∀ z ∈ ball c (1 / 2), z ≠ 1 := by
    intro z hz h
    have := hre z hz
    rw [h] at this
    norm_num at this
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c (1 / 2)) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hnz : ∀ z ∈ ball c (1 / 2), riemannZeta z ≠ 0 := fun z hz =>
    riemannZeta_ne_zero_of_one_lt_re (by linarith [hre z hz])
  have hc0 : riemannZeta c ≠ 0 := hnz c (mem_ball_self (by norm_num))
  obtain ⟨E, hEd, hEeq, hEc⟩ :=
    OAI.SevenEighths.LogarithmicControl.exists_holomorphic_log_normalized (by norm_num) hdiff hnz
      (Complex.exp_log hc0)
  refine ⟨E, hEd, hEeq, ?_⟩
  intro z hz
  have hRe : ∀ w ∈ ball c (1 / 2), (E w).re ≤ Mre := by
    intro w hw
    have h1 : Complex.exp (E w) = riemannZeta w := hEeq hw
    have h2 : Real.exp (E w).re = ‖riemannZeta w‖ := by rw [← Complex.norm_exp, h1]
    have h3 : (E w).re = Real.log ‖riemannZeta w‖ := by rw [← h2, Real.log_exp]
    rw [h3]
    have hpos : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr (hnz w hw)
    have hle := norm_zeta_le_K₀ (le_of_lt (hre w hw))
    have h4 : Real.log ‖riemannZeta w‖ ≤ Real.log K₀ := Real.log_le_log hpos hle
    unfold Mre
    linarith [le_abs_self (Real.log K₀)]
  have hcA : ‖E c‖ ≤ Ac := by
    rw [hEc]
    refine (norm_log_le _ hc0).trans ?_
    have hge := norm_zeta_ge (s := c) (by rw [hc])
    have hle := norm_zeta_le_two (s := c) (by rw [hc])
    have hinv : ‖riemannZeta c‖⁻¹ ≤ (2 - Real.pi ^ 2 / 6)⁻¹ := inv_anti₀ lower_pos hge
    unfold Ac
    linarith
  have hbc := OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall
    (g := E) (c := c) (r := 49 / 100) (R := 1 / 2) (M := Mre) (A := Ac)
    (by norm_num) (by norm_num) Mre_pos Ac_nonneg hEd hRe hcA hz
  exact hbc.trans (le_max_left _ _)

/-! ### The main estimate for `|Im s| ≥ 2`, `1/2 + δ ≤ Re s ≤ 2` -/

lemma main_bound (hRH : RiemannHypothesis) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ D * (|s.im| + 4) ^ ε := by
  set e : ℝ := min (δ / 6) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have he6 : 6 * e ≤ δ := by have := min_le_left (δ / 6) (1 / 2000); linarith
  obtain ⟨D, hD, hDprop⟩ := OAI.SevenEighths.LogarithmicControl.logarithmic_control
    (e := e) (A := A₁) (M := 2) (ε := ε) he he' (le_max_right _ _) (by norm_num) hε
  refine ⟨D, hD, ?_⟩
  intro s hs1 hs2 ht
  set c : ℂ := 2 + (s.im : ℂ) * I with hc_def
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = s.im := by simp [c]
  obtain ⟨E, hEd, hEeq, hEb⟩ := exists_log_small c hcre
  -- geometry of the big disc
  have hgeo : ∀ z ∈ ball c (2 - 1 / 2 - 2 * e),
      1 / 2 + 2 * e < z.re ∧ z.re < 4 ∧ 1 / 2 < |z.im| ∧ |z.im| < |s.im| + 3 / 2 := by
    intro z hz
    have h1 := abs_lt.mp (re_sub_le hz)
    have h2 := abs_lt.mp (im_sub_le hz)
    rw [hcre] at h1
    rw [hcim] at h2
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · rcases le_or_gt 0 s.im with h | h
      · rw [abs_of_nonneg h] at ht
        rw [lt_abs]; left; linarith
      · rw [abs_of_neg h] at ht
        rw [lt_abs]; right; linarith
    · rcases le_or_gt 0 s.im with h | h
      · rw [abs_of_nonneg h]; rw [abs_lt]; constructor <;> linarith
      · rw [abs_of_neg h]; rw [abs_lt]; constructor <;> linarith
  have hne1 : ∀ z ∈ ball c (2 - 1 / 2 - 2 * e), z ≠ 1 := by
    intro z hz h
    have := (hgeo z hz).2.2.1
    rw [h] at this
    norm_num at this
  have hL : DifferentiableOn ℂ riemannZeta (ball c (2 - 1 / 2 - 2 * e)) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have h0 : ∀ z ∈ ball c (2 - 1 / 2 - 2 * e), riemannZeta z ≠ 0 := fun z hz =>
    zeta_ne_zero_of_RH hRH (by linarith [(hgeo z hz).1]) (hne1 z hz)
  have hsub : ball c (2 - 1 / 2 - 3 * e) ⊆ ball c (2 - 1 / 2 - 2 * e) :=
    ball_subset_ball (by linarith)
  have hpoly : ∀ z ∈ ball c (2 - 1 / 2 - 3 * e), ‖riemannZeta z‖ ≤ (|s.im| + 4) ^ (2 : ℝ) := by
    intro z hz
    obtain ⟨hzre, hzre4, hzim, hzim2⟩ := hgeo z (hsub hz)
    have hzre0 : 0 < z.re := by linarith
    have hb := Zeta23.RvM.norm_riemannZeta_le_of_re_pos hzre0 (hne1 z (hsub hz))
    have h1 : 1 / 2 < ‖1 - z‖ := by
      have := Complex.abs_im_le_norm (1 - z)
      simp only [sub_im, one_im, zero_sub, abs_neg] at this
      linarith
    have h2 : 1 / ‖1 - z‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have h3 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hzre0] at h3
    have h4 : ‖z‖ / z.re ≤ 2 * ‖z‖ := by
      rw [div_le_iff₀ hzre0]; nlinarith [norm_nonneg z]
    rw [Real.rpow_two]
    have habs : 0 ≤ |s.im| := abs_nonneg _
    nlinarith
  have hC : Real.exp 1 ≤ |s.im| + 4 := by
    have := Real.exp_one_lt_d9
    linarith
  have hs_mem : s ∈ closedBall c (2 - 1 / 2 - 6 * e) := by
    rw [mem_closedBall, dist_eq_norm]
    have hsc : s - c = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have key := (hDprop (1 / 2) (|s.im| + 4) riemannZeta E c (le_refl _) (by norm_num) hC hL h0
    hpoly hEd hEeq hEb).1 s hs_mem
  linarith [norm_nonneg (riemannZeta s)⁻¹]

end RHInvZeta


open RHInvZeta Complex Filter Asymptotics in
theorem solution (hRH : RiemannHypothesis) (σ : ℝ) (hσ : 1 / 2 < σ) :
    LindelofHypothesis.mu σ ≤ 0 := by
  have hbig : ∀ ε : ℝ, 0 < ε →
      (fun T : ℝ => riemannZeta (σ + T * I)) =O[atTop] (fun T : ℝ => T ^ ε) := by
    intro ε hε
    by_cases h2 : σ ≤ 2
    · obtain ⟨D, hD, hmain⟩ := main_bound hRH (σ - 1 / 2) ε (by linarith) hε
      refine Asymptotics.IsBigO.of_bound (D * 3 ^ ε) ?_
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
      have hre : ((σ : ℂ) + T * I).re = σ := by simp
      have him : ((σ : ℂ) + T * I).im = T := by simp
      have hs := hmain ((σ : ℂ) + T * I) (by rw [hre]; linarith) (by rw [hre]; exact h2)
        (by rw [him, abs_of_pos (by linarith)]; exact hT)
      rw [him, abs_of_pos (by linarith)] at hs
      have hTpos : 0 < T := by linarith
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hTpos.le _)]
      have h3 : (T + 4) ^ ε ≤ 3 ^ ε * T ^ ε := by
        rw [← Real.mul_rpow (by norm_num) hTpos.le]
        exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
      calc ‖riemannZeta ((σ : ℂ) + T * I)‖ ≤ D * (T + 4) ^ ε := hs
        _ ≤ D * (3 ^ ε * T ^ ε) := mul_le_mul_of_nonneg_left h3 hD.le
        _ = D * 3 ^ ε * T ^ ε := by ring
    · push_neg at h2
      refine Asymptotics.IsBigO.of_bound 2 ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hle := norm_zeta_le_two (s := (σ : ℂ) + T * I) (by simp; linarith)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      have : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
      nlinarith
  unfold LindelofHypothesis.mu
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  exact sInf_le ⟨z, hbig z hz', rfl⟩
