-- Prove2me | solution 1 for InfoBargaining.Uniform.proposition2_seller_payoff_jumps
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T17:44:39.661039+00:00
-- url     : https://prove2.me/submissions/92c59d66-5af2-4a11-9ae9-7b64f4d67c46

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

set_option autoImplicit false

namespace InfoBargaining.Uniform

open InfoBargaining.Uniform

noncomputable def P (x : ℝ) : ℝ := (max x 0) ^ 2

theorem continuous_P : Continuous P := by
  unfold P; fun_prop

theorem hasDerivAt_P_ne (x : ℝ) (hx : x ≠ 0) : HasDerivAt P (2 * max x 0) x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have h : P =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [P, max_eq_right hy.le]
    rw [max_eq_right hx.le, mul_zero]
    exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq h
  · have h : P =ᶠ[nhds x] fun y => y ^ 2 := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp [P, max_eq_left hy.le]
    rw [max_eq_left hx.le]
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    exact h2.congr_of_eventuallyEq h

theorem hasDerivAt_P (x : ℝ) : HasDerivAt P (2 * max x 0) x := by
  by_cases hx : x = 0
  · subst hx
    exact hasDerivAt_of_hasDerivAt_of_ne (g := fun y => 2 * max y 0)
      (fun y hy => hasDerivAt_P_ne y hy) continuous_P.continuousAt (by fun_prop)
  · exact hasDerivAt_P_ne x hx

theorem A_closed (α c : ℝ) (hα : 0 < α) :
    A α c = (P ((1 + α) / 2 - c) - P ((1 - α) / 2 - c)) / (2 * α) := by
  unfold A
  have hderiv : ∀ w ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun w => P (α * w + (1 - α) / 2 - c) / (2 * α))
        (max (α * w + (1 - α) / 2 - c) 0) w := by
    intro w _
    have h1 : HasDerivAt (fun w => α * w + (1 - α) / 2 - c) α w := by
      simpa using (((hasDerivAt_id w).const_mul α).add_const ((1 - α) / 2)).sub_const c
    have h2 := ((hasDerivAt_P _).comp w h1).div_const (2 * α)
    refine h2.congr_deriv ?_
    rw [div_eq_iff (mul_pos two_pos hα).ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have e1 : P (α * 1 + (1 - α) / 2 - c) = P ((1 + α) / 2 - c) := by congr 1; ring
  have e0 : P (α * 0 + (1 - α) / 2 - c) = P ((1 - α) / 2 - c) := by congr 1; ring
  beta_reduce
  rw [e1, e0]
  ring

theorem A_left (α x : ℝ) (hα : 0 < α) (hx : x ≤ 1 / 2) :
    2 * α * A α x = ((1 + α) / 2 - x) ^ 2 - (max ((1 - α) / 2 - x) 0) ^ 2 := by
  rw [A_closed α x hα]
  unfold P
  rw [max_eq_left (show (0:ℝ) ≤ (1 + α) / 2 - x by linarith)]
  field_simp

theorem A_right (α x : ℝ) (hα : 0 < α) (hx : 1 / 2 ≤ x) :
    2 * α * A α x = (max ((1 + α) / 2 - x) 0) ^ 2 := by
  rw [A_closed α x hα]
  unfold P
  rw [max_eq_right (show (1 - α) / 2 - x ≤ 0 by linarith)]
  field_simp
  ring

theorem A_nonneg (α c : ℝ) : 0 ≤ A α c :=
  intervalIntegral.integral_nonneg (by norm_num) (fun w _ => le_max_right _ _)

theorem A_anti (α : ℝ) {c c' : ℝ} (h : c ≤ c') : A α c' ≤ A α c := by
  unfold A
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro w _
    apply max_le_max _ le_rfl
    linarith

theorem A_lip (α : ℝ) {c c' : ℝ} (h : c ≤ c') : A α c ≤ A α c' + (c' - c) := by
  unfold A
  have hI : ∫ w in (0:ℝ)..1, (max (α * w + (1 - α) / 2 - c') 0 + (c' - c)) =
      (∫ w in (0:ℝ)..1, max (α * w + (1 - α) / 2 - c') 0) + (c' - c) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const]
    · simp
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [← hI]
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro w _
    apply max_le
    · linarith [le_max_left (α * w + (1 - α) / 2 - c') 0]
    · linarith [le_max_right (α * w + (1 - α) / 2 - c') 0]

theorem A_convex (a b c t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    A (t * a + (1 - t) * b) c ≤ t * A a c + (1 - t) * A b c := by
  unfold A
  have hR : t * (∫ w in (0:ℝ)..1, max (a * w + (1 - a) / 2 - c) 0) +
      (1 - t) * (∫ w in (0:ℝ)..1, max (b * w + (1 - b) / 2 - c) 0) =
      ∫ w in (0:ℝ)..1, (t * max (a * w + (1 - a) / 2 - c) 0 +
        (1 - t) * max (b * w + (1 - b) / 2 - c) 0) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hR]
  refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro w _
    have h1 := le_max_left (a * w + (1 - a) / 2 - c) 0
    have h2 := le_max_left (b * w + (1 - b) / 2 - c) 0
    have h3 := le_max_right (a * w + (1 - a) / 2 - c) 0
    have h4 := le_max_right (b * w + (1 - b) / 2 - c) 0
    have ht1' : 0 ≤ 1 - t := by linarith
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left h1 ht0, mul_le_mul_of_nonneg_left h2 ht1']
    · nlinarith [mul_nonneg ht0 h3, mul_nonneg ht1' h4]

/-! Polynomial comparison of the two surpluses. -/

noncomputable def Kl (H L x : ℝ) : ℝ :=
  L * (((1 + H) / 2 - x) ^ 2 - (max ((1 - H) / 2 - x) 0) ^ 2) -
    H * (((1 + L) / 2 - x) ^ 2 - (max ((1 - L) / 2 - x) 0) ^ 2)

noncomputable def Kr (H L x : ℝ) : ℝ :=
  L * (max ((1 + H) / 2 - x) 0) ^ 2 - H * (max ((1 + L) / 2 - x) 0) ^ 2

theorem Kl_nonneg (H L x : ℝ) (hL : 0 < L) (hLH : L < H) (hx : x ≤ 1 / 2) : 0 ≤ Kl H L x := by
  unfold Kl
  rcases le_or_gt x ((1 - H) / 2) with h1 | h1
  · rw [max_eq_left (show (0:ℝ) ≤ (1 - H) / 2 - x by linarith),
      max_eq_left (show (0:ℝ) ≤ (1 - L) / 2 - x by linarith)]
    nlinarith
  · rw [max_eq_right (show (1 - H) / 2 - x ≤ 0 by linarith)]
    rcases le_or_gt x ((1 - L) / 2) with h2 | h2
    · rw [max_eq_left (show (0:ℝ) ≤ (1 - L) / 2 - x by linarith)]
      nlinarith [mul_nonneg hL.le (sq_nonneg (H / 2 - (1 / 2 - x)))]
    · rw [max_eq_right (show (1 - L) / 2 - x ≤ 0 by linarith)]
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ H - L by linarith)
        (show (0:ℝ) ≤ x - (1 - L) / 2 by linarith)) (show (0:ℝ) ≤ (1 + L) / 2 - x by linarith),
        mul_nonneg hL.le (sq_nonneg (H - L))]

theorem Kr_nonneg (H L x : ℝ) (hL : 0 < L) (hLH : L < H) (hx : 1 / 2 ≤ x) : 0 ≤ Kr H L x := by
  unfold Kr
  rcases le_or_gt ((1 + H) / 2) x with h1 | h1
  · rw [max_eq_right (show (1 + H) / 2 - x ≤ 0 by linarith),
      max_eq_right (show (1 + L) / 2 - x ≤ 0 by linarith)]
    norm_num
  · rw [max_eq_left (show (0:ℝ) ≤ (1 + H) / 2 - x by linarith)]
    rcases le_or_gt ((1 + L) / 2) x with h2 | h2
    · rw [max_eq_right (show (1 + L) / 2 - x ≤ 0 by linarith)]
      nlinarith [mul_nonneg hL.le (sq_nonneg ((1 + H) / 2 - x))]
    · rw [max_eq_left (show (0:ℝ) ≤ (1 + L) / 2 - x by linarith)]
      nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ) ≤ H - L by linarith)
        (show (0:ℝ) ≤ (1 + L) / 2 - x by linarith)) (show (0:ℝ) ≤ x - (1 - L) / 2 by linarith),
        mul_nonneg hL.le (sq_nonneg (H - L))]

theorem Kl_strict (H L c d : ℝ) (hL : 0 < L) (hLH : L < H) (hcd : c < d) (hd : d ≤ 1 / 2)
    (hpos : 0 < Kl H L c) : Kl H L c < Kl H L d := by
  unfold Kl at *
  rcases le_or_gt c ((1 - H) / 2) with h1 | h1
  · rw [max_eq_left (show (0:ℝ) ≤ (1 - H) / 2 - c by linarith),
      max_eq_left (show (0:ℝ) ≤ (1 - L) / 2 - c by linarith)] at hpos
    nlinarith
  · rw [max_eq_right (show (1 - H) / 2 - c ≤ 0 by linarith),
      max_eq_right (show (1 - H) / 2 - d ≤ 0 by linarith)]
    rcases le_or_gt c ((1 - L) / 2) with h2 | h2
    · rw [max_eq_left (show (0:ℝ) ≤ (1 - L) / 2 - c by linarith)]
      rcases le_or_gt d ((1 - L) / 2) with h3 | h3
      · rw [max_eq_left (show (0:ℝ) ≤ (1 - L) / 2 - d by linarith)]
        nlinarith [mul_pos (mul_pos hL (sub_pos.2 hcd)) (show 0 < c + d - (1 - H) by linarith)]
      · rw [max_eq_right (show (1 - L) / 2 - d ≤ 0 by linarith)]
        nlinarith [mul_nonneg (mul_nonneg hL.le (show (0:ℝ) ≤ (1 - L) / 2 - c by linarith))
          (show (0:ℝ) ≤ (H - L) - ((1 - L) / 2 - c) by linarith),
          mul_pos (mul_pos (show (0:ℝ) < (H - L) / 2 by linarith)
            (show (0:ℝ) < d - (1 - L) / 2 by linarith))
            (show (0:ℝ) < L - (d - (1 - L) / 2) by linarith)]
    · rw [max_eq_right (show (1 - L) / 2 - c ≤ 0 by linarith),
        max_eq_right (show (1 - L) / 2 - d ≤ 0 by linarith)]
      nlinarith [mul_pos (mul_pos (sub_pos.2 hLH) (sub_pos.2 hcd)) (show 0 < 1 - c - d by linarith)]

theorem Kr_strict (H L c d : ℝ) (hL : 0 < L) (hLH : L < H) (hd : 1 / 2 ≤ d) (hdc : d < c)
    (hpos : 0 < Kr H L c) : Kr H L c < Kr H L d := by
  unfold Kr at *
  rcases le_or_gt ((1 + H) / 2) c with h1 | h1
  · rw [max_eq_right (show (1 + H) / 2 - c ≤ 0 by linarith),
      max_eq_right (show (1 + L) / 2 - c ≤ 0 by linarith)] at hpos
    norm_num at hpos
  · rw [max_eq_left (show (0:ℝ) ≤ (1 + H) / 2 - c by linarith),
      max_eq_left (show (0:ℝ) ≤ (1 + H) / 2 - d by linarith)]
    rcases le_or_gt ((1 + L) / 2) c with h2 | h2
    · rw [max_eq_right (show (1 + L) / 2 - c ≤ 0 by linarith)]
      rcases le_or_gt ((1 + L) / 2) d with h3 | h3
      · rw [max_eq_right (show (1 + L) / 2 - d ≤ 0 by linarith)]
        nlinarith [mul_pos (mul_pos hL (sub_pos.2 hdc)) (show 0 < (1 + H) - c - d by linarith)]
      · rw [max_eq_left (show (0:ℝ) ≤ (1 + L) / 2 - d by linarith)]
        nlinarith [mul_nonneg (mul_nonneg hL.le (show (0:ℝ) ≤ c - (1 + L) / 2 by linarith))
          (show (0:ℝ) ≤ (H - L) - (c - (1 + L) / 2) by linarith),
          mul_pos (mul_pos (show (0:ℝ) < (H - L) / 2 by linarith)
            (show (0:ℝ) < (1 + L) / 2 - d by linarith))
            (show (0:ℝ) < L - ((1 + L) / 2 - d) by linarith)]
    · rw [max_eq_left (show (0:ℝ) ≤ (1 + L) / 2 - c by linarith),
        max_eq_left (show (0:ℝ) ≤ (1 + L) / 2 - d by linarith)]
      nlinarith [mul_pos (mul_pos (sub_pos.2 hLH) (sub_pos.2 hdc)) (show 0 < c + d - 1 by linarith)]

/-! The gain `A(ᾱ,c) − A(α̲,c)`. -/

theorem gain_Kl (M : Model) (c : ℝ) (hc : c ≤ 1 / 2) :
    2 * M.αhi * M.αlo * M.gain c = Kl M.αhi M.αlo c := by
  have hL := M.αlo_pos
  have hH : 0 < M.αhi := by linarith [M.αlo_lt_αhi]
  have e1 := A_left M.αhi c hH hc
  have e2 := A_left M.αlo c hL hc
  unfold Model.gain Kl
  rw [← e1, ← e2]
  ring

theorem gain_Kr (M : Model) (c : ℝ) (hc : 1 / 2 ≤ c) :
    2 * M.αhi * M.αlo * M.gain c = Kr M.αhi M.αlo c := by
  have hL := M.αlo_pos
  have hH : 0 < M.αhi := by linarith [M.αlo_lt_αhi]
  have e1 := A_right M.αhi c hH hc
  have e2 := A_right M.αlo c hL hc
  unfold Model.gain Kr
  rw [← e1, ← e2]
  ring

theorem two_pos' (M : Model) : 0 < 2 * M.αhi * M.αlo := by
  have hL := M.αlo_pos
  have hH : 0 < M.αhi := by linarith [M.αlo_lt_αhi]
  positivity

theorem gain_nonneg (M : Model) (c : ℝ) : 0 ≤ M.gain c := by
  have h4 := two_pos' M
  have hL := M.αlo_pos
  have hLH := M.αlo_lt_αhi
  have key : 0 ≤ 2 * M.αhi * M.αlo * M.gain c := by
    rcases le_total c (1 / 2) with hc | hc
    · rw [gain_Kl M c hc]; exact Kl_nonneg _ _ _ hL hLH hc
    · rw [gain_Kr M c hc]; exact Kr_nonneg _ _ _ hL hLH hc
  by_contra hneg
  push Not at hneg
  nlinarith [mul_neg_of_pos_of_neg h4 hneg]

theorem gain_strict_left (M : Model) {c d : ℝ} (hcd : c < d) (hd : d ≤ 1 / 2)
    (hpos : 0 < M.gain c) : M.gain c < M.gain d := by
  have h4 := two_pos' M
  have h := Kl_strict M.αhi M.αlo c d M.αlo_pos M.αlo_lt_αhi hcd hd
    (by rw [← gain_Kl M c (by linarith)]; exact mul_pos h4 hpos)
  rw [← gain_Kl M c (by linarith), ← gain_Kl M d hd] at h
  exact lt_of_mul_lt_mul_left h h4.le

theorem gain_strict_right (M : Model) {c d : ℝ} (hd : 1 / 2 ≤ d) (hdc : d < c)
    (hpos : 0 < M.gain c) : M.gain c < M.gain d := by
  have h4 := two_pos' M
  have h := Kr_strict M.αhi M.αlo c d M.αlo_pos M.αlo_lt_αhi hd hdc
    (by rw [← gain_Kr M c (by linarith)]; exact mul_pos h4 hpos)
  rw [← gain_Kr M c (by linarith), ← gain_Kr M d hd] at h
  exact lt_of_mul_lt_mul_left h h4.le

theorem gain_low (M : Model) {c : ℝ} (hc : c ≤ (1 - M.αhi) / 2) : M.gain c = 0 := by
  have h4 := two_pos' M
  have hLH := M.αlo_lt_αhi
  have h : Kl M.αhi M.αlo c = 0 := by
    unfold Kl
    rw [max_eq_left (show (0:ℝ) ≤ (1 - M.αhi) / 2 - c by linarith),
      max_eq_left (show (0:ℝ) ≤ (1 - M.αlo) / 2 - c by linarith)]
    ring
  have e := gain_Kl M c (by linarith [M.αhi_lt_one, M.αlo_pos])
  rw [h] at e
  exact (mul_eq_zero.mp e).resolve_left h4.ne'

theorem gain_high (M : Model) {c : ℝ} (hc : (1 + M.αhi) / 2 ≤ c) : M.gain c = 0 := by
  have h4 := two_pos' M
  have hLH := M.αlo_lt_αhi
  have h : Kr M.αhi M.αlo c = 0 := by
    unfold Kr
    rw [max_eq_right (show (1 + M.αhi) / 2 - c ≤ 0 by linarith),
      max_eq_right (show (1 + M.αlo) / 2 - c ≤ 0 by linarith)]
    ring
  have e := gain_Kr M c (by linarith [M.αhi_lt_one, M.αlo_pos])
  rw [h] at e
  exact (mul_eq_zero.mp e).resolve_left h4.ne'

/-! Optimal information levels. -/

theorem opt_conv (M : Model) {θb c α : ℝ} (hθ : 0 ≤ θb) (h : α ∈ M.optSet θb c) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ α = t * M.αlo + (1 - t) * M.αhi ∧
      θb * A α c ≤ θb * (t * A M.αlo c + (1 - t) * A M.αhi c) ∧
      M.Ub θb c α = θb * A α c - (1 - t) * M.kbar := by
  have hLH := M.αlo_lt_αhi
  have hd : 0 < M.αhi - M.αlo := by linarith
  obtain ⟨⟨h1, h2⟩, _⟩ := h
  refine ⟨(M.αhi - α) / (M.αhi - M.αlo), ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (by linarith) hd.le
  · rw [div_le_one hd]; linarith
  · field_simp; ring
  · apply mul_le_mul_of_nonneg_left _ hθ
    have ht0 : 0 ≤ (M.αhi - α) / (M.αhi - M.αlo) := div_nonneg (by linarith) hd.le
    have ht1 : (M.αhi - α) / (M.αhi - M.αlo) ≤ 1 := by rw [div_le_one hd]; linarith
    have hα : α = (M.αhi - α) / (M.αhi - M.αlo) * M.αlo +
        (1 - (M.αhi - α) / (M.αhi - M.αlo)) * M.αhi := by field_simp; ring
    have := A_convex M.αlo M.αhi c _ ht0 ht1
    rwa [← hα] at this
  · unfold Model.Ub Model.k
    field_simp
    ring

theorem Ub_lo (M : Model) (θb c : ℝ) : M.Ub θb c M.αlo = θb * A M.αlo c := by
  unfold Model.Ub Model.k; simp

theorem Ub_hi (M : Model) (θb c : ℝ) : M.Ub θb c M.αhi = θb * A M.αhi c - M.kbar := by
  have hd : M.αhi - M.αlo ≠ 0 := by linarith [M.αlo_lt_αhi]
  unfold Model.Ub Model.k; field_simp

theorem lo_mem (M : Model) : M.αlo ∈ Set.Icc M.αlo M.αhi := ⟨le_rfl, M.αlo_lt_αhi.le⟩
theorem hi_mem (M : Model) : M.αhi ∈ Set.Icc M.αlo M.αhi := ⟨M.αlo_lt_αhi.le, le_rfl⟩

theorem opt_hi (M : Model) {θb c α : ℝ} (h : α ∈ M.optSet θb c)
    (hg : M.kbar < θb * M.gain c) : α = M.αhi := by
  have hk := M.kbar_pos
  have hg0 := gain_nonneg M c
  have hθ : 0 ≤ θb := by
    by_contra hn; push Not at hn; nlinarith [mul_nonpos_of_nonpos_of_nonneg hn.le hg0]
  obtain ⟨t, ht0, ht1, hα, hA, hU⟩ := opt_conv M hθ h
  have hopt := h.2 M.αhi (hi_mem M)
  rw [hU, Ub_hi] at hopt
  unfold Model.gain at hg
  have h2 : t * (θb * (A M.αhi c - A M.αlo c) - M.kbar) ≤ 0 := by nlinarith
  have ht : t ≤ 0 := by
    by_contra hn; push Not at hn
    nlinarith [mul_pos hn (show 0 < θb * (A M.αhi c - A M.αlo c) - M.kbar by linarith)]
  have : t = 0 := le_antisymm ht ht0
  rw [hα, this]; ring

theorem opt_lo (M : Model) {θb c α : ℝ} (hθ : 0 ≤ θb) (h : α ∈ M.optSet θb c)
    (hg : θb * M.gain c < M.kbar) : α = M.αlo := by
  obtain ⟨t, ht0, ht1, hα, hA, hU⟩ := opt_conv M hθ h
  have hopt := h.2 M.αlo (lo_mem M)
  rw [hU, Ub_lo] at hopt
  unfold Model.gain at hg
  have h2 : 0 ≤ (1 - t) * (θb * (A M.αhi c - A M.αlo c) - M.kbar) := by nlinarith
  have ht : 1 - t ≤ 0 := by
    by_contra hn; push Not at hn
    nlinarith [mul_pos hn (show 0 < M.kbar - θb * (A M.αhi c - A M.αlo c) by linarith)]
  have : t = 1 := by linarith
  rw [hα, this]; ring

theorem opt_bounds (M : Model) {θb c α : ℝ} (hθ : 0 < θb) (h : α ∈ M.optSet θb c) :
    A M.αlo c ≤ A α c ∧ A α c ≤ A M.αhi c := by
  have hk := M.kbar_pos
  have hg0 := gain_nonneg M c
  unfold Model.gain at hg0
  obtain ⟨t, ht0, ht1, hα, hA, hU⟩ := opt_conv M hθ.le h
  have hopt := h.2 M.αlo (lo_mem M)
  rw [hU, Ub_lo] at hopt
  constructor
  · by_contra hn; push Not at hn
    nlinarith [mul_pos hθ (show 0 < A M.αlo c - A α c by linarith),
      mul_nonneg (show 0 ≤ 1 - t by linarith) hk.le]
  · by_contra hn; push Not at hn
    nlinarith [mul_pos hθ (show 0 < A α c - A M.αhi c by linarith),
      mul_nonneg (mul_nonneg hθ.le ht0) hg0]

end InfoBargaining.Uniform

namespace InfoBargaining.Uniform

open InfoBargaining.Uniform

theorem regions (M : Model) (θb : ℝ) (hθ : θb ∈ Set.Ioo (0:ℝ) 1) (cl ch : ℝ)
    (hcl : cl ≤ 1 / 2) (hch : 1 / 2 ≤ ch)
    (hiff : ∀ c ∈ Set.Ioo (0:ℝ) 1, (cl < c ∧ c < ch ↔ M.kbar < θb * M.gain c))
    (σ : ℝ → ℝ) (hσ : ∀ c ∈ Set.Ioo (0:ℝ) 1, σ c ∈ M.optSet θb c) :
    0 < cl ∧ ch < 1 ∧
    (∀ c, cl < c → c < ch → σ c = M.αhi) ∧
    (∀ c, 0 < c → c < cl → σ c = M.αlo) ∧
    (∀ c, ch < c → c < 1 → σ c = M.αlo) ∧
    (∀ c, 0 < c → c < 1 → A M.αlo c ≤ A (σ c) c ∧ A (σ c) c ≤ A M.αhi c) := by
  have hk := M.kbar_pos
  have hH1 := M.αhi_lt_one
  have hL := M.αlo_pos
  have hLH := M.αlo_lt_αhi
  obtain ⟨hθ0, hθ1⟩ := hθ
  -- cl > 0
  have hcl0 : 0 < cl := by
    set c1 := (1 - M.αhi) / 4 with hc1
    have hg := gain_low M (show c1 ≤ (1 - M.αhi) / 2 by rw [hc1]; linarith)
    have h := hiff c1 ⟨by rw [hc1]; linarith, by rw [hc1]; linarith⟩
    rw [hg, mul_zero] at h
    by_contra hn; push Not at hn
    have : M.kbar < 0 := h.1 ⟨by rw [hc1]; linarith, by rw [hc1]; linarith⟩
    linarith
  have hch1 : ch < 1 := by
    set c0 := (3 + M.αhi) / 4 with hc0
    have hg := gain_high M (show (1 + M.αhi) / 2 ≤ c0 by rw [hc0]; linarith)
    have h := hiff c0 ⟨by rw [hc0]; linarith, by rw [hc0]; linarith⟩
    rw [hg, mul_zero] at h
    by_contra hn; push Not at hn
    have : M.kbar < 0 := h.1 ⟨by rw [hc0]; linarith, by rw [hc0]; linarith⟩
    linarith
  refine ⟨hcl0, hch1, ?_, ?_, ?_, ?_⟩
  · intro c h1 h2
    exact opt_hi M (hσ c ⟨by linarith, by linarith⟩) ((hiff c ⟨by linarith, by linarith⟩).1 ⟨h1, h2⟩)
  · intro c h0 h1
    have hmem := hσ c ⟨h0, by linarith⟩
    apply opt_lo M hθ0.le hmem
    have hle : θb * M.gain c ≤ M.kbar := by
      by_contra hn; push Not at hn
      have := (hiff c ⟨h0, by linarith⟩).2 hn
      linarith [this.1]
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hgpos : 0 < M.gain c := by
        by_contra hn; push Not at hn
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hθ0.le hn]
      set d := (c + cl) / 2 with hd
      have hs := gain_strict_left M (show c < d by rw [hd]; linarith)
        (show d ≤ 1 / 2 by rw [hd]; linarith) hgpos
      have : M.kbar < θb * M.gain d := by rw [← heq]; exact mul_lt_mul_of_pos_left hs hθ0
      have := (hiff d ⟨by rw [hd]; linarith, by rw [hd]; linarith⟩).2 this
      rw [hd] at this
      linarith [this.1]
  · intro c h0 h1
    have hmem := hσ c ⟨by linarith, h1⟩
    apply opt_lo M hθ0.le hmem
    have hle : θb * M.gain c ≤ M.kbar := by
      by_contra hn; push Not at hn
      have := (hiff c ⟨by linarith, h1⟩).2 hn
      linarith [this.2]
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      have hgpos : 0 < M.gain c := by
        by_contra hn; push Not at hn
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hθ0.le hn]
      set d := (ch + c) / 2 with hd
      have hs := gain_strict_right M (show 1 / 2 ≤ d by rw [hd]; linarith)
        (show d < c by rw [hd]; linarith) hgpos
      have : M.kbar < θb * M.gain d := by rw [← heq]; exact mul_lt_mul_of_pos_left hs hθ0
      have := (hiff d ⟨by rw [hd]; linarith, by rw [hd]; linarith⟩).2 this
      rw [hd] at this
      linarith [this.2]
  · intro c h0 h1
    exact opt_bounds M hθ0 (hσ c ⟨h0, h1⟩)

/-- Both surpluses vary at most 1-Lipschitz; a margin lemma for the jumps. -/
theorem gain_near (M : Model) {c e : ℝ} (he : 0 ≤ e) :
    M.gain c - e ≤ M.gain (c + e) ∧ M.gain c - e ≤ M.gain (c - e) := by
  unfold Model.gain
  constructor
  · have h1 := A_anti M.αlo (show c ≤ c + e by linarith)
    have h2 := A_lip M.αhi (show c ≤ c + e by linarith)
    linarith
  · have h1 := A_anti M.αhi (show c - e ≤ c by linarith)
    have h2 := A_lip M.αlo (show c - e ≤ c by linarith)
    linarith

end InfoBargaining.Uniform

open InfoBargaining.Uniform in
theorem solution (M : Model) :
    -- (i) payoffs in the seller's bargaining power θs = 1 − θb, jump down at θs = 1 − θ̃
    (∀ c ∈ Set.Ioo (0:ℝ) 1, ∀ σ : ℝ → ℝ,
      (∀ θs ∈ Set.Ioo (0:ℝ) 1, σ θs ∈ M.optSet (1 - θs) c) →
      MonotoneOn (fun θs => θs * A (σ θs) c) (Set.Ioo 0 (1 - M.thetaTilde c)) ∧
      MonotoneOn (fun θs => θs * A (σ θs) c) (Set.Ioo (1 - M.thetaTilde c) 1) ∧
      MonotoneOn (fun θs => c + θs * A (σ θs) c) (Set.Ioo 0 (1 - M.thetaTilde c)) ∧
      MonotoneOn (fun θs => c + θs * A (σ θs) c) (Set.Ioo (1 - M.thetaTilde c) 1) ∧
      (M.thetaTilde c < 1 → ∃ ε > 0, ∀ θ ∈ Set.Ioo (0:ℝ) 1, ∀ θ' ∈ Set.Ioo (0:ℝ) 1,
        1 - M.thetaTilde c - ε < θ → θ < 1 - M.thetaTilde c →
        1 - M.thetaTilde c < θ' → θ' < 1 - M.thetaTilde c + ε →
        θ' * A (σ θ') c < θ * A (σ θ) c ∧ c + θ' * A (σ θ') c < c + θ * A (σ θ) c)) ∧
    -- (ii) U*_s in the material cost c, jump up at c = c_l
    (∀ θb ∈ Set.Ioo (0:ℝ) 1, ∀ cl ch : ℝ, cl ≤ 1 / 2 → 1 / 2 ≤ ch →
      (∀ c ∈ Set.Ioo (0:ℝ) 1, (cl < c ∧ c < ch ↔ M.kbar < θb * M.gain c)) →
      ∀ σ : ℝ → ℝ, (∀ c ∈ Set.Ioo (0:ℝ) 1, σ c ∈ M.optSet θb c) →
      AntitoneOn (fun c => (1 - θb) * A (σ c) c) (Set.Ioo 0 cl) ∧
      AntitoneOn (fun c => (1 - θb) * A (σ c) c) (Set.Ioo cl 1) ∧
      (cl < ch → ∃ ε > 0, ∀ c ∈ Set.Ioo (0:ℝ) 1, ∀ c' ∈ Set.Ioo (0:ℝ) 1,
        cl - ε < c → c < cl → cl < c' → c' < cl + ε →
        (1 - θb) * A (σ c) c < (1 - θb) * A (σ c') c')) ∧
    -- (iii) V*_s in the opportunity cost c, jump down at c = c_h
    (∀ θb ∈ Set.Ioo (0:ℝ) 1, ∀ cl ch : ℝ, cl ≤ 1 / 2 → 1 / 2 ≤ ch →
      (∀ c ∈ Set.Ioo (0:ℝ) 1, (cl < c ∧ c < ch ↔ M.kbar < θb * M.gain c)) →
      ∀ σ : ℝ → ℝ, (∀ c ∈ Set.Ioo (0:ℝ) 1, σ c ∈ M.optSet θb c) →
      MonotoneOn (fun c => c + (1 - θb) * A (σ c) c) (Set.Ioo 0 ch) ∧
      MonotoneOn (fun c => c + (1 - θb) * A (σ c) c) (Set.Ioo ch 1) ∧
      (cl < ch → ∃ ε > 0, ∀ c ∈ Set.Ioo (0:ℝ) 1, ∀ c' ∈ Set.Ioo (0:ℝ) 1,
        ch - ε < c → c < ch → ch < c' → c' < ch + ε →
        c' + (1 - θb) * A (σ c') c' < c + (1 - θb) * A (σ c) c)) := by
  have hk := M.kbar_pos
  have hH1 := M.αhi_lt_one
  have hL := M.αlo_pos
  have hLH := M.αlo_lt_αhi
  refine ⟨?_, ?_, ?_⟩
  · -- (i)
    intro c hc σ hσ
    have hg0 := gain_nonneg M c
    have hTc : (M.gain c ≤ M.kbar ∧ M.thetaTilde c = 1) ∨
        (M.kbar < M.gain c ∧ M.thetaTilde c = M.kbar / M.gain c) := by
      unfold Model.thetaTilde
      split_ifs with h
      · exact Or.inl ⟨h, rfl⟩
      · exact Or.inr ⟨lt_of_not_ge h, rfl⟩
    have hT0 : 0 < M.thetaTilde c ∧ M.thetaTilde c ≤ 1 := by
      rcases hTc with ⟨_, hT⟩ | ⟨hg, hT⟩
      · rw [hT]; norm_num
      · rw [hT]
        exact ⟨div_pos hk (by linarith), by rw [div_le_one (by linarith)]; linarith⟩
    have hhi : ∀ θs, 0 < θs → θs < 1 - M.thetaTilde c → σ θs = M.αhi := by
      intro θs h0 h1
      have hmem := hσ θs ⟨h0, by linarith [hT0.1]⟩
      apply opt_hi M hmem
      rcases hTc with ⟨_, hT⟩ | ⟨hg, hT⟩
      · rw [hT] at h1; linarith
      · rw [hT] at h1
        have h2 : M.kbar / M.gain c < 1 - θs := by linarith
        rwa [div_lt_iff₀ (by linarith)] at h2
    have hlo : ∀ θs, 1 - M.thetaTilde c < θs → θs < 1 → σ θs = M.αlo := by
      intro θs h0 h1
      have hθs0 : 0 < θs := by linarith [hT0.2]
      have hmem := hσ θs ⟨hθs0, h1⟩
      apply opt_lo M (by linarith) hmem
      rcases hTc with ⟨hg, _⟩ | ⟨hg, hT⟩
      · nlinarith [mul_nonneg (show 0 ≤ 1 - θs by linarith) (show 0 ≤ M.kbar - M.gain c by linarith),
          mul_pos hθs0 hk]
      · rw [hT] at h0
        have h2 : 1 - θs < M.kbar / M.gain c := by linarith
        rwa [lt_div_iff₀ (by linarith)] at h2
    have hAH := A_nonneg M.αhi c
    have hAL := A_nonneg M.αlo c
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only
      rw [hhi a ha.1 ha.2, hhi b hb.1 hb.2]
      exact mul_le_mul_of_nonneg_right hab hAH
    · intro a ha b hb hab
      simp only
      rw [hlo a ha.1 ha.2, hlo b hb.1 hb.2]
      exact mul_le_mul_of_nonneg_right hab hAL
    · intro a ha b hb hab
      simp only
      rw [hhi a ha.1 ha.2, hhi b hb.1 hb.2]
      linarith [mul_le_mul_of_nonneg_right hab hAH]
    · intro a ha b hb hab
      simp only
      rw [hlo a ha.1 ha.2, hlo b hb.1 hb.2]
      linarith [mul_le_mul_of_nonneg_right hab hAL]
    · intro hT1
      have hg : M.kbar < M.gain c := by
        rcases hTc with ⟨_, hT⟩ | ⟨hg, _⟩
        · rw [hT] at hT1; norm_num at hT1
        · exact hg
      have hgain : M.gain c = A M.αhi c - A M.αlo c := rfl
      set t0 := 1 - M.thetaTilde c with ht0def
      have ht0 : 0 < t0 := by rw [ht0def]; linarith
      have hgp : 0 < M.gain c := by linarith
      have hden : 0 < 2 * (A M.αlo c + A M.αhi c + 1) := by linarith
      refine ⟨t0 * M.gain c / (2 * (A M.αlo c + A M.αhi c + 1)), by positivity, ?_⟩
      intro θ hθ θ' hθ' h1 h2 h3 h4
      have hε : t0 * M.gain c / (2 * (A M.αlo c + A M.αhi c + 1)) *
          (2 * (A M.αlo c + A M.αhi c + 1)) = t0 * M.gain c := by field_simp
      set ε := t0 * M.gain c / (2 * (A M.αlo c + A M.αhi c + 1)) with hεdef
      have hεpos : 0 < ε := by rw [hεdef]; positivity
      rw [hhi θ hθ.1 h2, hlo θ' h3 hθ'.2]
      have key : θ' * A M.αlo c < θ * A M.αhi c := by
        nlinarith [mul_le_mul_of_nonneg_right (show θ' ≤ t0 + ε by linarith) hAL,
          mul_le_mul_of_nonneg_right (show t0 - ε ≤ θ by linarith) hAH,
          mul_nonneg hεpos.le hAL, mul_nonneg hεpos.le hAH]
      exact ⟨key, by linarith⟩
  · -- (ii)
    intro θb hθ cl ch hcl hch hiff σ hσ
    obtain ⟨hcl0, hch1, hmid, hlow, hhigh, hbd⟩ := regions M θb hθ cl ch hcl hch hiff σ hσ
    have h1θ : 0 < 1 - θb := by linarith [hθ.2]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only
      rw [hlow a ha.1 ha.2, hlow b hb.1 hb.2]
      exact mul_le_mul_of_nonneg_left (A_anti _ hab) h1θ.le
    · intro a ha b hb hab
      simp only
      apply mul_le_mul_of_nonneg_left _ h1θ.le
      rcases lt_trichotomy a ch with hac | hac | hac
      · rw [hmid a ha.1 hac]
        exact (hbd b (by linarith [ha.1]) hb.2).2.trans (A_anti _ hab)
      · rcases eq_or_lt_of_le hab with hab' | hab'
        · subst hab'; exact le_rfl
        · rw [hhigh b (by linarith) hb.2]
          exact (A_anti _ hab).trans (hbd a (by linarith [ha.1]) ha.2).1
      · rw [hhigh a hac ha.2, hhigh b (by linarith) hb.2]
        exact A_anti _ hab
    · intro hlt
      set δ := min (min (M.kbar / 2) ((ch - cl) / 2)) (1 / 4) with hδ
      have hδ1 : δ ≤ M.kbar / 2 := (min_le_left _ _).trans (min_le_left _ _)
      have hδ2 : δ ≤ (ch - cl) / 2 := (min_le_left _ _).trans (min_le_right _ _)
      have hδ3 : δ ≤ 1 / 4 := min_le_right _ _
      have hδ0 : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      have hg1 : M.kbar < θb * M.gain (cl + δ) :=
        (hiff (cl + δ) ⟨by linarith, by linarith⟩).1 ⟨by linarith, by linarith⟩
      have hg1' : M.kbar < M.gain (cl + δ) := by
        have := gain_nonneg M (cl + δ)
        nlinarith [mul_nonneg (show 0 ≤ 1 - θb by linarith) this]
      have hgcl : 0 < M.gain cl := by
        have := (gain_near M (c := cl + δ) hδ0.le).2
        rw [show cl + δ - δ = cl by ring] at this
        linarith
      refine ⟨min δ (M.gain cl / 3), lt_min hδ0 (by linarith), ?_⟩
      intro c hc c' hc' h1 h2 h3 h4
      have he1 : min δ (M.gain cl / 3) ≤ δ := min_le_left _ _
      have he2 : min δ (M.gain cl / 3) ≤ M.gain cl / 3 := min_le_right _ _
      rw [hlow c hc.1 h2, hmid c' h3 (by linarith)]
      apply mul_lt_mul_of_pos_left _ h1θ
      have l1 := A_lip M.αlo h2.le
      have l2 := A_lip M.αhi h3.le
      have hgain : M.gain cl = A M.αhi cl - A M.αlo cl := rfl
      linarith
  · -- (iii)
    intro θb hθ cl ch hcl hch hiff σ hσ
    obtain ⟨hcl0, hch1, hmid, hlow, hhigh, hbd⟩ := regions M θb hθ cl ch hcl hch hiff σ hσ
    have h1θ : 0 < 1 - θb := by linarith [hθ.2]
    have hθ0 := hθ.1
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only
      by_cases hbcl : b ≤ cl
      · rcases eq_or_lt_of_le hab with h | h
        · subst h; exact le_rfl
        · rw [hlow a ha.1 (by linarith)]
          have hb' := (hbd b (by linarith [ha.1]) (by linarith [hb.2])).1
          have l := A_lip M.αlo hab
          nlinarith [mul_le_mul_of_nonneg_left hb' h1θ.le, mul_le_mul_of_nonneg_left l h1θ.le,
            mul_nonneg hθ0.le (show 0 ≤ b - a by linarith)]
      · push Not at hbcl
        rw [hmid b hbcl hb.2]
        have ha' := (hbd a ha.1 (by linarith [hb.2])).2
        have l := A_lip M.αhi hab
        nlinarith [mul_le_mul_of_nonneg_left ha' h1θ.le, mul_le_mul_of_nonneg_left l h1θ.le,
          mul_nonneg hθ0.le (show 0 ≤ b - a by linarith)]
    · intro a ha b hb hab
      simp only
      rw [hhigh a ha.1 ha.2, hhigh b hb.1 hb.2]
      have l := A_lip M.αlo hab
      nlinarith [mul_le_mul_of_nonneg_left l h1θ.le, mul_nonneg hθ0.le (show 0 ≤ b - a by linarith)]
    · intro hlt
      set δ := min (min (M.kbar / 2) ((ch - cl) / 2)) (1 / 4) with hδ
      have hδ1 : δ ≤ M.kbar / 2 := (min_le_left _ _).trans (min_le_left _ _)
      have hδ2 : δ ≤ (ch - cl) / 2 := (min_le_left _ _).trans (min_le_right _ _)
      have hδ3 : δ ≤ 1 / 4 := min_le_right _ _
      have hδ0 : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      have hg1 : M.kbar < θb * M.gain (ch - δ) :=
        (hiff (ch - δ) ⟨by linarith, by linarith⟩).1 ⟨by linarith, by linarith⟩
      have hg1' : M.kbar < M.gain (ch - δ) := by
        have := gain_nonneg M (ch - δ)
        nlinarith [mul_nonneg (show 0 ≤ 1 - θb by linarith) this]
      have hgch : 0 < M.gain ch := by
        have := (gain_near M (c := ch - δ) hδ0.le).1
        rw [show ch - δ + δ = ch by ring] at this
        linarith
      have hm : 0 < (1 - θb) * M.gain ch := mul_pos h1θ hgch
      refine ⟨min δ ((1 - θb) * M.gain ch / 3), lt_min hδ0 (by linarith), ?_⟩
      intro c hc c' hc' h1 h2 h3 h4
      have he1 : min δ ((1 - θb) * M.gain ch / 3) ≤ δ := min_le_left _ _
      have he2 : min δ ((1 - θb) * M.gain ch / 3) ≤ (1 - θb) * M.gain ch / 3 := min_le_right _ _
      rw [hmid c (by linarith) h2, hhigh c' h3 hc'.2]
      have l1 := A_anti M.αhi h2.le
      have l2 := A_anti M.αlo h3.le
      have hgain : M.gain ch = A M.αhi ch - A M.αlo ch := rfl
      have hprod : (1 - θb) * M.gain ch ≤ (1 - θb) * (A M.αhi c - A M.αlo c') := by
        apply mul_le_mul_of_nonneg_left _ h1θ.le
        linarith
      nlinarith
