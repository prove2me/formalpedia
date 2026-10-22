-- Prove2me | solution 1 for KendallBD.Cumul.cumulative_law
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:21:13.228364+00:00
-- url     : https://prove2.me/submissions/4652dde9-8f00-4a0e-85b8-c54efbd0340d

import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting
open Filter Topology


namespace KendallBD.Cumul

lemma g84_choose_succ (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) = Ring.choose a n * (a - n) / (n + 1) := by
  rw [eq_div_iff (by positivity)]
  simp only [Ring.choose_eq_smul, Nat.factorial_succ, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_one]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

noncomputable def g84u (M : ℕ) : ℝ := (Nat.centralBinom M : ℝ) / (4 ^ M * (2 * (M : ℝ) - 1))

lemma g84_u_zero : g84u 0 = -1 := by simp [g84u]

lemma g84_choose_half (n : ℕ) : Ring.choose (1 / 2 : ℝ) n * (-1) ^ n = - g84u n := by
  induction n with
  | zero => simp [g84u]
  | succ n ih =>
    rw [g84_choose_succ, pow_succ]
    have h1 := Nat.succ_mul_centralBinom_succ n
    have h1' : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) = 2 * (2 * n + 1) * Nat.centralBinom n := by
      exact_mod_cast h1
    have hn : (2 * (n : ℝ) - 1) ≠ 0 := by
      intro h
      have : (2 * (n : ℝ)) = 1 := by linarith
      have h2 : (2 * n : ℕ) = 1 := by exact_mod_cast this
      omega
    have h4 : 2 * (((n + 1 : ℕ) : ℝ)) - 1 = 2 * n + 1 := by push_cast; ring
    have hu : g84u (n + 1) = g84u n * (2 * n - 1) / (2 * n + 2) := by
      unfold g84u
      have : (Nat.centralBinom (n + 1) : ℝ) = 2 * (2 * n + 1) * Nat.centralBinom n / (n + 1) := by
        rw [eq_div_iff (by positivity)]; linarith
      rw [this, h4]
      have h3 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hu]
    have : Ring.choose (1 / 2 : ℝ) n * (1 / 2 - n) / (n + 1) * ((-1) ^ n * (-1))
        = (Ring.choose (1 / 2 : ℝ) n * (-1) ^ n) * ((n - 1 / 2) / (n + 1)) := by
      field_simp; ring
    rw [this, ih]
    field_simp

lemma g84_sqrt_series {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ => g84u n * y ^ n) (- Real.sqrt (1 - y)) := by
  have h := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (1 / 2 : ℝ))
  have hmem : (-y) ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [edist_dist, Real.dist_eq, abs_neg] using (by simpa using hy : ‖-y‖ < 1)
  have hs := h.hasSum hmem
  have e : (1 + (0 + -y)) = 1 - y := by ring
  simp only [zero_add, binomialSeries_apply, List.ofFn_const, List.prod_replicate, e] at hs
  rw [← Real.sqrt_eq_rpow] at hs
  have h2 := hs.neg
  rw [show (1 + -y) = 1 - y by ring] at h2
  have e2 : (fun n : ℕ => g84u n * y ^ n) = fun b : ℕ => -(Ring.choose (1 / 2 : ℝ) b • (-y) ^ b) := by
    funext n
    have := g84_choose_half n
    rw [smul_eq_mul, neg_pow]
    linear_combination (y ^ n) * this
  rw [e2]; exact h2


section series
variable {lam0 mu0 : ℝ}

lemma g84_x_pos (hlam : 0 < lam0) (hle : lam0 ≤ mu0) : 0 < x lam0 mu0 := by
  unfold x
  have : 0 < mu0 := lt_of_lt_of_le hlam hle
  positivity

lemma g84_x_le_one (hlam : 0 < lam0) (hle : lam0 ≤ mu0) : x lam0 mu0 ≤ 1 := by
  unfold x
  have : 0 < mu0 := lt_of_lt_of_le hlam hle
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (mu0 - lam0)]

lemma g84_u_pos {M : ℕ} (hM : 1 ≤ M) : 0 < g84u M := by
  unfold g84u
  have : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have := Nat.centralBinom_pos M
  have : (0 : ℝ) < Nat.centralBinom M := by exact_mod_cast this
  have h2 : 0 < 2 * (M : ℝ) - 1 := by linarith
  positivity

lemma g84_factorial_div (M : ℕ) :
    ((Nat.factorial (2 * M) : ℝ) / (2 ^ (2 * M) * (Nat.factorial M : ℝ) ^ 2))
      = (Nat.centralBinom M : ℝ) / 4 ^ M := by
  have h := Nat.choose_mul_factorial_mul_factorial (show M ≤ 2 * M by omega)
  rw [show 2 * M - M = M by omega] at h
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h' : ((2 * M).choose M : ℝ) * (M.factorial : ℝ) * (M.factorial : ℝ) = (2 * M).factorial := by
    exact_mod_cast h
  rw [← h']
  have : (M.factorial : ℝ) ≠ 0 := by positivity
  rw [pow_mul]
  field_simp
  norm_num

lemma g84_Q_eq (M : ℕ) (hM : 1 ≤ M) :
    Q lam0 mu0 M = (lam0 + mu0) / (2 * lam0) * (g84u M * x lam0 mu0 ^ M) := by
  have : M ≠ 0 := by omega
  unfold Q
  rw [if_neg this, g84_factorial_div]
  unfold g84u
  have h1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h2 : 2 * (M : ℝ) - 1 ≠ 0 := by linarith
  field_simp

lemma g84_Q_nonneg (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (M : ℕ) : 0 ≤ Q lam0 mu0 M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [Q]
  · rw [g84_Q_eq M hM]
    have := g84_u_pos hM
    have := g84_x_pos hlam hle
    have : 0 < mu0 := lt_of_lt_of_le hlam hle
    positivity

noncomputable def g84q (y : ℝ) (M : ℕ) : ℝ := if M = 0 then 0 else g84u M * y ^ M

lemma g84_q_series {y : ℝ} (hy : |y| < 1) : HasSum (g84q y) (1 - Real.sqrt (1 - y)) := by
  have h := g84_sqrt_series hy
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, g84q] at h1 ⊢
  simpa [g84_u_zero, sub_eq_add_neg, add_comm] using h1

lemma g84_Q_w (M : ℕ) (w : ℝ) :
    Q lam0 mu0 M * w ^ M = (lam0 + mu0) / (2 * lam0) * g84q (x lam0 mu0 * w) M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [Q, g84q]
  · rw [g84_Q_eq M hM]
    have : M ≠ 0 := by omega
    simp only [g84q, if_neg this, mul_pow]
    ring

end series



/-- generic derivative computation -/
lemma g84_core (m A B w z t : ℝ)
    (hD : (B - z) + (z - A) * Real.exp (-(m * (B - A)) * t) ≠ 0) :
    ∃ a b : ℝ,
      HasDerivAt (fun s => w * ((A * (B - z) + B * (z - A) * Real.exp (-(m * (B - A)) * s))
        / ((B - z) + (z - A) * Real.exp (-(m * (B - A)) * s)))) a t ∧
      HasDerivAt (fun y => w * ((A * (B - y) + B * (y - A) * Real.exp (-(m * (B - A)) * t))
        / ((B - y) + (y - A) * Real.exp (-(m * (B - A)) * t)))) b z ∧
      a = (m * (z - A) * (z - B)) * b := by
  set E := Real.exp (-(m * (B - A)) * t) with hE
  have hEt : HasDerivAt (fun s => Real.exp (-(m * (B - A)) * s)) (E * (-(m * (B - A)))) t := by
    have := ((hasDerivAt_id' t).const_mul (-(m * (B - A)))).exp
    simpa [hE, mul_comm] using this
  have hDt : HasDerivAt (fun s => (B - z) + (z - A) * Real.exp (-(m * (B - A)) * s))
      ((z - A) * (E * (-(m * (B - A))))) t := (hEt.const_mul (z - A)).const_add (B - z)
  have hNt : HasDerivAt (fun s => A * (B - z) + B * (z - A) * Real.exp (-(m * (B - A)) * s))
      (B * (z - A) * (E * (-(m * (B - A))))) t := (hEt.const_mul (B * (z - A))).const_add _
  have ht := (hNt.div hDt hD).const_mul w
  have hy1 : HasDerivAt (fun y => (B - y)) (-1) z := by
    simpa using (hasDerivAt_id' z).const_sub B
  have hy2 : HasDerivAt (fun y => (y - A)) 1 z := (hasDerivAt_id' z).sub_const A
  have hNz : HasDerivAt (fun y => A * (B - y) + B * (y - A) * E) (A * (-1) + B * 1 * E) z :=
    ((hy1.const_mul A).add ((hy2.const_mul B).mul_const E))
  have hDz : HasDerivAt (fun y => (B - y) + (y - A) * E) (-1 + 1 * E) z :=
    hy1.add (hy2.mul_const E)
  have hz := (hNz.div hDz hD).const_mul w
  refine ⟨_, _, ht, hz, ?_⟩
  simp only [← hE]
  clear_value E
  field_simp
  ring



section facts
variable {lam0 mu0 w : ℝ}

lemma g84_disc_pos (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    0 < disc lam0 mu0 w := by
  obtain ⟨h0, h1⟩ := hw
  unfold disc
  have : 0 < lam0 * mu0 := mul_pos hlam (lt_of_lt_of_le hlam hle)
  nlinarith [sq_nonneg (mu0 - lam0), mul_pos this (sub_pos.2 h1)]

lemma g84_sqrt_sq (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    Real.sqrt (disc lam0 mu0 w) ^ 2 = disc lam0 mu0 w :=
  Real.sq_sqrt (g84_disc_pos hlam hle hw).le

lemma g84_s_pos (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    0 < Real.sqrt (disc lam0 mu0 w) := Real.sqrt_pos.2 (g84_disc_pos hlam hle hw)

lemma g84_s_lt (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    Real.sqrt (disc lam0 mu0 w) < lam0 + mu0 := by
  have h := g84_sqrt_sq hlam hle hw
  have hs := g84_s_pos hlam hle hw
  have hd : disc lam0 mu0 w < (lam0 + mu0) ^ 2 := by
    unfold disc
    have : 0 < lam0 * mu0 := mul_pos hlam (lt_of_lt_of_le hlam hle)
    nlinarith [hw.1]
  nlinarith

lemma g84_beta_sub_alpha (hlam : 0 < lam0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    beta lam0 mu0 w - alpha lam0 mu0 w = Real.sqrt (disc lam0 mu0 w) / (lam0 * w) := by
  have := hw.1
  unfold beta alpha
  field_simp
  ring

lemma g84_m_mul (hlam : 0 < lam0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) = Real.sqrt (disc lam0 mu0 w) := by
  have := hw.1
  rw [g84_beta_sub_alpha hlam hw]
  field_simp

lemma g84_alpha_pos (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    0 < alpha lam0 mu0 w := by
  have := hw.1
  have := g84_s_lt hlam hle hw
  unfold alpha
  apply div_pos (by linarith) (by positivity)

lemma g84_alpha_lt_beta (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    alpha lam0 mu0 w < beta lam0 mu0 w := by
  have h := g84_beta_sub_alpha (mu0 := mu0) hlam hw
  have := g84_s_pos hlam hle hw
  have := hw.1
  have : 0 < beta lam0 mu0 w - alpha lam0 mu0 w := by rw [h]; positivity
  linarith

lemma g84_one_lt_beta (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    1 < beta lam0 mu0 w := by
  have := hw.1
  have := hw.2
  have := g84_s_pos hlam hle hw
  unfold beta
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

lemma g84_quad (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1) (z : ℝ) :
    lam0 * w * z ^ 2 - (lam0 + mu0) * z + mu0
      = (lam0 * w) * (z - alpha lam0 mu0 w) * (z - beta lam0 mu0 w) := by
  have := hw.1
  have h : Real.sqrt (disc lam0 mu0 w) ^ 2 = (lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w := by
    rw [g84_sqrt_sq hlam hle hw]; rfl
  unfold alpha beta
  field_simp
  nlinarith [h]

end facts



section psi
variable {lam0 mu0 w : ℝ}

lemma g84_psi_eq (z t : ℝ) :
    psi lam0 mu0 z w t = w * ((alpha lam0 mu0 w * (beta lam0 mu0 w - z)
      + beta lam0 mu0 w * (z - alpha lam0 mu0 w)
        * Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t))
      / ((beta lam0 mu0 w - z) + (z - alpha lam0 mu0 w)
        * Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t))) := by
  unfold psi
  have : -lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w) * t
      = -(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t := by ring
  rw [this]

lemma g84_E_bounds (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    0 < Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t) ∧
    Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t) ≤ 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_le_one_iff, g84_m_mul hlam hw]
  have := g84_s_pos hlam hle hw
  nlinarith

lemma g84_D_pos (hlam : 0 < lam0) (hle : lam0 ≤ mu0) (hw : w ∈ Set.Ioo (0:ℝ) 1)
    {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    0 < (beta lam0 mu0 w - z) + (z - alpha lam0 mu0 w)
      * Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t) := by
  obtain ⟨hE0, hE1⟩ := g84_E_bounds hlam hle hw ht
  have hb := g84_one_lt_beta hlam hle hw
  have hab := g84_alpha_lt_beta hlam hle hw
  obtain ⟨hz0, hz1⟩ := hz
  set E := Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t)
  rcases le_or_gt 0 (z - alpha lam0 mu0 w) with h | h
  · nlinarith [mul_nonneg h hE0.le]
  · nlinarith [mul_nonneg (neg_nonneg.2 h.le) (sub_nonneg.2 hE1)]

theorem g84_psi_solves (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    ∀ w ∈ Set.Ioo (0:ℝ) 1,
      (∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t → SolvesPDE lam0 mu0 (psi lam0 mu0) z w t) ∧
      ∀ z : ℝ, psi lam0 mu0 z w 0 = z * w := by
  intro w hw
  refine ⟨fun z hz t ht => ?_, fun z => ?_⟩
  · have hD := (g84_D_pos hlam hle hw hz ht).ne'
    obtain ⟨a, b, h1, h2, h3⟩ := g84_core (lam0 * w) (alpha lam0 mu0 w) (beta lam0 mu0 w) w z t
      (by simpa using hD)
    refine ⟨a, b, ?_, ?_, ?_⟩
    · have : (fun s => psi lam0 mu0 z w s) = _ := funext (fun s => g84_psi_eq (lam0 := lam0)
        (mu0 := mu0) (w := w) z s)
      rw [this]; exact h1
    · have : (fun y => psi lam0 mu0 y w t) = _ := funext (fun y => g84_psi_eq (lam0 := lam0)
        (mu0 := mu0) (w := w) y t)
      rw [this]; exact h2
    · rw [h3, g84_quad hlam hle hw]
  · have hab := g84_alpha_lt_beta hlam hle hw
    rw [g84_psi_eq]
    simp only [mul_zero, Real.exp_zero, mul_one]
    have : beta lam0 mu0 w - z + (z - alpha lam0 mu0 w) = beta lam0 mu0 w - alpha lam0 mu0 w := by ring
    rw [this]
    have h2 : beta lam0 mu0 w - alpha lam0 mu0 w ≠ 0 := by linarith
    field_simp
    ring

theorem g84_psi_limit (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    ∀ w ∈ Set.Ioo (0:ℝ) 1,
      Tendsto (fun t => psi lam0 mu0 1 w t) atTop (𝓝 (w * alpha lam0 mu0 w)) ∧
      w * alpha lam0 mu0 w
        = (lam0 + mu0 - Real.sqrt ((lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w)) / (2 * lam0) := by
  intro w hw
  have hw0 := hw.1
  refine ⟨?_, ?_⟩
  · have hb := g84_one_lt_beta hlam hle hw
    have hs := g84_s_pos hlam hle hw
    have hE : Tendsto (fun t : ℝ => Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t))
        atTop (𝓝 0) := by
      rw [g84_m_mul hlam hw]
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    have hlim : Tendsto (fun t : ℝ => w * ((alpha lam0 mu0 w * (beta lam0 mu0 w - 1)
      + beta lam0 mu0 w * (1 - alpha lam0 mu0 w)
        * Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t))
      / ((beta lam0 mu0 w - 1) + (1 - alpha lam0 mu0 w)
        * Real.exp (-(lam0 * w * (beta lam0 mu0 w - alpha lam0 mu0 w)) * t)))) atTop
        (𝓝 (w * ((alpha lam0 mu0 w * (beta lam0 mu0 w - 1) + beta lam0 mu0 w * (1 - alpha lam0 mu0 w) * 0)
          / ((beta lam0 mu0 w - 1) + (1 - alpha lam0 mu0 w) * 0)))) := by
      refine Tendsto.const_mul _ (Tendsto.div ?_ ?_ ?_)
      · exact tendsto_const_nhds.add (hE.const_mul _)
      · exact tendsto_const_nhds.add (hE.const_mul _)
      · simp; linarith
    have e : w * ((alpha lam0 mu0 w * (beta lam0 mu0 w - 1) + beta lam0 mu0 w * (1 - alpha lam0 mu0 w) * 0)
          / ((beta lam0 mu0 w - 1) + (1 - alpha lam0 mu0 w) * 0)) = w * alpha lam0 mu0 w := by
      have : beta lam0 mu0 w - 1 ≠ 0 := by linarith
      rw [mul_zero, mul_zero, add_zero, add_zero, mul_div_cancel_right₀ _ this]
    rw [e] at hlim
    refine hlim.congr (fun t => ?_)
    rw [g84_psi_eq]
  · unfold alpha disc
    field_simp

end psi


section final
variable {lam0 mu0 : ℝ}

noncomputable def g84G (lam0 mu0 w : ℝ) : ℝ := (lam0 + mu0) / (2 * lam0) * (1 - Real.sqrt (1 - x lam0 mu0 * w))

lemma g84_sqrt_one_sub_x (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    Real.sqrt (1 - x lam0 mu0) = (mu0 - lam0) / (lam0 + mu0) := by
  have hmu : 0 < mu0 := lt_of_lt_of_le hlam hle
  have h : 1 - x lam0 mu0 = ((mu0 - lam0) / (lam0 + mu0)) ^ 2 := by
    unfold x
    field_simp
    ring
  rw [h]
  exact Real.sqrt_sq (by apply div_nonneg <;> linarith)

lemma g84_G_one (hlam : 0 < lam0) (hle : lam0 ≤ mu0) : g84G lam0 mu0 1 = 1 := by
  have hmu : 0 < mu0 := lt_of_lt_of_le hlam hle
  unfold g84G
  rw [mul_one, g84_sqrt_one_sub_x hlam hle]
  field_simp
  ring

lemma g84_G_le (hlam : 0 < lam0) (hle : lam0 ≤ mu0) {w : ℝ} (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    g84G lam0 mu0 w ≤ 1 := by
  have hmu : 0 < mu0 := lt_of_lt_of_le hlam hle
  have hx := g84_x_pos hlam hle
  have hx1 := g84_x_le_one hlam hle
  have h1 : (mu0 - lam0) / (lam0 + mu0) ≤ Real.sqrt (1 - x lam0 mu0 * w) := by
    rw [← g84_sqrt_one_sub_x hlam hle]
    apply Real.sqrt_le_sqrt
    nlinarith [hw.1, hw.2]
  rw [← g84_G_one hlam hle]
  unfold g84G
  rw [mul_one, g84_sqrt_one_sub_x hlam hle]
  have : 0 < (lam0 + mu0) / (2 * lam0) := by positivity
  nlinarith

lemma g84_G_val (hlam : 0 < lam0) (hle : lam0 ≤ mu0) {w : ℝ} (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    g84G lam0 mu0 w = (lam0 + mu0 - Real.sqrt ((lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w)) / (2 * lam0) := by
  have hmu : 0 < mu0 := lt_of_lt_of_le hlam hle
  have hpos : 0 < lam0 + mu0 := by linarith
  have h1 : 1 - x lam0 mu0 * w = ((lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w) / (lam0 + mu0) ^ 2 := by
    unfold x
    field_simp
  have hd : 0 ≤ (lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w := (g84_disc_pos hlam hle hw).le
  unfold g84G
  rw [h1, Real.sqrt_div hd, Real.sqrt_sq hpos.le]
  field_simp

lemma g84_gen (hlam : 0 < lam0) (hle : lam0 ≤ mu0) {w : ℝ} (hw : w ∈ Set.Ioo (0:ℝ) 1) :
    HasSum (fun M : ℕ => Q lam0 mu0 M * w ^ M) (g84G lam0 mu0 w) := by
  have hx := g84_x_pos hlam hle
  have hx1 := g84_x_le_one hlam hle
  have hy : |x lam0 mu0 * w| < 1 := by
    rw [abs_of_pos (mul_pos hx hw.1)]
    nlinarith [hw.1, hw.2]
  have hq := (g84_q_series hy).mul_left ((lam0 + mu0) / (2 * lam0))
  have e : (fun M : ℕ => Q lam0 mu0 M * w ^ M)
      = fun M => (lam0 + mu0) / (2 * lam0) * g84q (x lam0 mu0 * w) M := funext (fun M => g84_Q_w M w)
  rw [e]
  exact hq

theorem g84_Q_hasSum (hlam : 0 < lam0) (hle : lam0 ≤ mu0) : HasSum (Q lam0 mu0) 1 := by
  have hnn := g84_Q_nonneg hlam hle
  have hpartial : ∀ N, ∑ i ∈ Finset.range N, Q lam0 mu0 i ≤ 1 := by
    intro N
    have ht : Tendsto (fun w : ℝ => ∑ i ∈ Finset.range N, Q lam0 mu0 i * w ^ i) (𝓝[<] 1)
        (𝓝 (∑ i ∈ Finset.range N, Q lam0 mu0 i * 1 ^ i)) :=
      ((continuous_finsetSum _ (fun i _ => by fun_prop)).tendsto 1).mono_left nhdsWithin_le_nhds
    simp only [one_pow, mul_one] at ht
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with w hw
    exact (sum_le_hasSum _ (fun i _ => mul_nonneg (hnn i) (pow_nonneg hw.1.le i))
      (g84_gen hlam hle hw)).trans (g84_G_le hlam hle hw)
  have hsum : Summable (Q lam0 mu0) := summable_of_sum_range_le hnn hpartial
  have hle1 : ∑' M, Q lam0 mu0 M ≤ 1 := Real.tsum_le_of_sum_range_le hnn hpartial
  have hge1 : 1 ≤ ∑' M, Q lam0 mu0 M := by
    have ht : Tendsto (fun w : ℝ => g84G lam0 mu0 w) (𝓝[<] 1) (𝓝 (g84G lam0 mu0 1)) := by
      have : Continuous (fun w : ℝ => g84G lam0 mu0 w) := by
        unfold g84G; fun_prop
      exact (this.tendsto 1).mono_left nhdsWithin_le_nhds
    rw [g84_G_one hlam hle] at ht
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with w hw
    exact hasSum_le (fun M => mul_le_of_le_one_right (hnn M) (pow_le_one₀ hw.1.le hw.2.le))
      (g84_gen hlam hle hw) hsum.hasSum
  have : ∑' M, Q lam0 mu0 M = 1 := le_antisymm hle1 hge1
  rw [← this]
  exact hsum.hasSum

theorem g84_main (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    (∀ w ∈ Set.Ioo (0:ℝ) 1,
      (∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t → SolvesPDE lam0 mu0 (psi lam0 mu0) z w t) ∧
      ∀ z : ℝ, psi lam0 mu0 z w 0 = z * w) ∧
    (∀ w ∈ Set.Ioo (0:ℝ) 1,
      Summable (fun M : ℕ => Q lam0 mu0 M * w ^ M) ∧
      Tendsto (fun t => psi lam0 mu0 1 w t) atTop (𝓝 (∑' M : ℕ, Q lam0 mu0 M * w ^ M))) ∧
    ((∀ M : ℕ, 0 ≤ Q lam0 mu0 M) ∧ HasSum (Q lam0 mu0) 1) := by
  refine ⟨g84_psi_solves hlam hle, fun w hw => ⟨(g84_gen hlam hle hw).summable, ?_⟩,
    g84_Q_nonneg hlam hle, g84_Q_hasSum hlam hle⟩
  obtain ⟨h1, h2⟩ := g84_psi_limit hlam hle w hw
  rw [(g84_gen hlam hle hw).tsum_eq, g84_G_val hlam hle hw, ← h2]
  exact h1

end final

end KendallBD.Cumul

open KendallBD.Cumul


theorem solution (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    (∀ w ∈ Set.Ioo (0:ℝ) 1,
      (∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t → SolvesPDE lam0 mu0 (psi lam0 mu0) z w t) ∧
      ∀ z : ℝ, psi lam0 mu0 z w 0 = z * w) ∧
    (∀ w ∈ Set.Ioo (0:ℝ) 1,
      Summable (fun M : ℕ => Q lam0 mu0 M * w ^ M) ∧
      Tendsto (fun t => psi lam0 mu0 1 w t) atTop (𝓝 (∑' M : ℕ, Q lam0 mu0 M * w ^ M))) ∧
    ((∀ M : ℕ, 0 ≤ Q lam0 mu0 M) ∧ HasSum (Q lam0 mu0) 1) := by
  exact g84_main hlam hle
