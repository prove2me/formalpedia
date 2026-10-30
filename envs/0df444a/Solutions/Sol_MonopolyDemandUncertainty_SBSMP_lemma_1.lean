-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:16:47.317546+00:00
-- url     : https://prove2.me/submissions/eb987547-e09e-4d83-bf1c-b3b178901bd0

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting
import Theorems.Thm_MonopolyDemandUncertainty_SBSMP_fact_1

open MeasureTheory Set

namespace Aux_MDU_P1
open MonopolyDemandUncertainty.SBSMP

noncomputable def w (E : Economy) (i : Fin 2) (v : ℝ) : ℝ := E.prob i * E.dens i v
noncomputable def J (E : Economy) (i : Fin 2) (x v : ℝ) : ℝ := if x ≤ v then w E i v else 0
noncomputable def Tl (E : Economy) (i : Fin 2) (x : ℝ) : ℝ := E.prob i * E.D i (max x E.vlo)

lemma prob_pos (E : Economy) (hE : E.Valid) (i : Fin 2) : 0 < E.prob i := by
  fin_cases i
  · simp [Economy.prob]; linarith [hE.α₁_pos]
  · simp [Economy.prob]; linarith [hE.α₁_lt_one]

lemma dens_pos (E : Economy) (h1 : E.Condition1) (i : Fin 2) (v : ℝ) (hv : v ∈ E.V) :
    0 < E.dens i v := by
  unfold Economy.dens; linarith [h1.2 i v hv]

lemma w_pos (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (v : ℝ)
    (hv : v ∈ E.V) : 0 < w E i v :=
  mul_pos (prob_pos E hE i) (dens_pos E h1 i v hv)

lemma dens_cont (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Continuous (E.dens i) := by
  unfold Economy.dens
  exact ((h1.1 i).continuous_deriv (by norm_num)).neg

lemma w_cont (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Continuous (w E i) :=
  continuous_const.mul (dens_cont E h1 i)

lemma D_diff (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Differentiable ℝ (E.D i) :=
  (h1.1 i).differentiable (by norm_num)

lemma Z_strictAnti (E : Economy) (h2 : E.Condition2) : StrictAntiOn E.Z E.V := by
  have hd : ∀ v ∈ E.V, DifferentiableAt ℝ E.Z v := fun v hv =>
    differentiableAt_of_deriv_ne_zero (ne_of_lt (h2 v hv))
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun v hv => (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    exact h2 v (interior_subset hv)

/-- likelihood ratio `w₁/w₀` is nondecreasing: `w₀(v) w₁(s) ≤ w₀(s) w₁(v)` for `s ≤ v`. -/
lemma ratio_mono (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (s v : ℝ) (hs : s ∈ E.V) (hv : v ∈ E.V) (hsv : s ≤ v) :
    w E 0 v * w E 1 s ≤ w E 0 s * w E 1 v := by
  unfold w
  rcases eq_or_lt_of_le hsv with h | h
  · rw [← h]
  · have hz := Z_strictAnti E h2 hs hv h
    unfold Economy.Z at hz
    rw [div_lt_div_iff₀ (dens_pos E h1 1 v hv) (dens_pos E h1 1 s hs)] at hz
    have := mul_lt_mul_of_pos_left hz (mul_pos (prob_pos E hE 0) (prob_pos E hE 1))
    nlinarith

lemma transfer (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (u v X Y : ℝ) (hu : u ∈ E.V) (hv : v ∈ E.V) (huv : u ≤ v) (hY : 0 ≤ Y)
    (h : X * w E 0 u ≤ Y * w E 1 u) : X * w E 0 v ≤ Y * w E 1 v := by
  have hr := ratio_mono E hE h1 h2 u v hu hv huv
  have hA := w_pos E hE h1 0 u hu
  have hC := w_pos E hE h1 0 v hv
  have s1 : X * w E 0 u * w E 0 v ≤ Y * w E 1 u * w E 0 v :=
    mul_le_mul_of_nonneg_right h hC.le
  have s2 : Y * (w E 0 v * w E 1 u) ≤ Y * (w E 0 u * w E 1 v) :=
    mul_le_mul_of_nonneg_left hr hY
  have : (X * w E 0 v) * w E 0 u ≤ (Y * w E 1 v) * w E 0 u := by nlinarith
  exact le_of_mul_le_mul_right this hA

lemma w_mono (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h3 : E.Condition3) (i : Fin 2)
    (s v : ℝ) (hs : s ∈ E.V) (hv : v ∈ E.V) (hsv : s ≤ v) : w E i s ≤ w E i v := by
  unfold w
  apply mul_le_mul_of_nonneg_left _ (prob_pos E hE i).le
  apply (strictMonoOn_of_deriv_pos (convex_Icc _ _) (dens_cont E h1 i).continuousOn _).monotoneOn
    hs hv hsv
  intro x hx
  have hx' := interior_subset hx
  have : deriv (E.dens i) x = - deriv (deriv (E.D i)) x := by
    unfold Economy.dens
    exact deriv.neg
  rw [this]; linarith [h3 i x hx']

lemma w1_lt_w0 (E : Economy) (h4 : E.Condition4ii) (v : ℝ) (hv : v ∈ E.V) :
    w E 1 v < w E 0 v := h4 v hv

lemma int_w (E : Economy) (h1 : E.Condition1) (i : Fin 2) (a b : ℝ) :
    ∫ s in a..b, w E i s = E.prob i * (E.D i a - E.D i b) := by
  unfold w Economy.dens
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg,
    intervalIntegral.integral_deriv_eq_sub (fun x _ => D_diff E h1 i x)
    (((h1.1 i).continuous_deriv (by norm_num)).intervalIntegrable _ _)]
  ring

lemma J_eq (E : Economy) (i : Fin 2) (x : ℝ) : J E i x = (Ici x).indicator (w E i) := by
  ext v; simp [J, Set.indicator_apply, mem_Ici]

lemma J_integrable (E : Economy) (h1 : E.Condition1) (i : Fin 2) (x : ℝ) :
    IntegrableOn (J E i x) E.V := by
  rw [J_eq]
  exact ((w_cont E h1 i).integrableOn_Icc).indicator measurableSet_Ici

lemma int_J (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (x : ℝ)
    (hx : x ≤ E.vhi) : ∫ v in E.V, J E i x v = Tl E i x := by
  rw [J_eq, setIntegral_indicator measurableSet_Ici]
  have hset : E.V ∩ Ici x = Icc (max x E.vlo) E.vhi := by
    ext v; simp only [Economy.V, mem_inter_iff, mem_Icc, mem_Ici, max_le_iff]
    tauto
  have hle : max x E.vlo ≤ E.vhi := max_le hx hE.vlo_lt_vhi.le
  rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle, int_w E h1,
    hE.D_vhi i, Tl]
  ring

lemma int_sum (E : Economy) (hE : E.Valid) (h1 : E.Condition1) {n : ℕ} (c : Fin n → ℝ)
    (I : Fin n → Fin 2) (X : Fin n → ℝ) (hX : ∀ k, X k ≤ E.vhi) :
    ∫ v in E.V, ∑ k, c k * J E (I k) (X k) v = ∑ k, c k * Tl E (I k) (X k) := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, int_J E hE h1 _ _ (hX k)]
  · intro k _
    exact (J_integrable E h1 (I k) (X k)).const_mul (c k)

lemma sum_integrable (E : Economy) (h1 : E.Condition1) {n : ℕ} (c : Fin n → ℝ)
    (I : Fin n → Fin 2) (X : Fin n → ℝ) :
    IntegrableOn (fun v => ∑ k, c k * J E (I k) (X k) v) E.V := by
  apply integrable_finset_sum
  intro k _
  exact (J_integrable E h1 (I k) (X k)).const_mul (c k)

lemma D_antitone (E : Economy) (h1 : E.Condition1) (i : Fin 2) : AntitoneOn (E.D i) E.V := by
  apply (strictAntiOn_of_deriv_neg (convex_Icc _ _) (D_diff E h1 i).continuous.continuousOn _).antitoneOn
  intro v hv; exact h1.2 i v (interior_subset hv)

lemma D_nonneg (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (v : ℝ)
    (hv : v ∈ E.V) : 0 ≤ E.D i v := by
  have := D_antitone E h1 i hv ⟨hE.vlo_lt_vhi.le, le_refl _⟩ hv.2
  rw [hE.D_vhi i] at this; exact this

lemma Tl_nonneg (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (x : ℝ)
    (hx : x ≤ E.vhi) : 0 ≤ Tl E i x := by
  unfold Tl
  exact mul_nonneg (prob_pos E hE i).le
    (D_nonneg E hE h1 i _ ⟨le_max_right _ _, max_le hx hE.vlo_lt_vhi.le⟩)

lemma Tl_cont (E : Economy) (h1 : E.Condition1) (i : Fin 2) : Continuous (Tl E i) := by
  unfold Tl
  exact continuous_const.mul ((D_diff E h1 i).continuous.comp (continuous_id.max continuous_const))

/-- `x T_i(x)` is at most the monopoly revenue. -/
lemma F_bound (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (p x : ℝ)
    (hp : E.IsMonopolyPrice i p) (hx0 : 0 ≤ x) (hx : x ≤ E.vhi) :
    x * Tl E i x ≤ E.prob i * (p * E.D i p) := by
  unfold Tl
  set x' := max x E.vlo
  have hx'V : x' ∈ E.V := ⟨le_max_right _ _, max_le hx hE.vlo_lt_vhi.le⟩
  have hD := D_nonneg E hE h1 i x' hx'V
  have h1' : x * E.D i x' ≤ x' * E.D i x' := mul_le_mul_of_nonneg_right (le_max_left _ _) hD
  have h2' := hp.2 x' hx'V
  have hp0 := (prob_pos E hE i).le
  nlinarith [mul_le_mul_of_nonneg_left (le_trans h1' h2') hp0]

lemma Tl_sub (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (x m : ℝ)
    (hm : m ∈ E.V) : Tl E i x - Tl E i m = ∫ s in (max x E.vlo)..m, w E i s := by
  rw [int_w E h1, Tl, Tl, max_eq_left hm.1]; ring

/-- Key lemma: with `c = m - (m - b) w₁(m)/w₀(m)`,
`b (T₂(b) - T₂(m)) ≤ c (T₁(c) - T₁(m))`. -/
lemma key (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
    (h3 : E.Condition3) (h4 : E.Condition4ii) (b m c : ℝ) (hb0 : 0 ≤ b) (hbm : b ≤ m)
    (hm : m ∈ E.V) (hc : c * w E 0 m = m * w E 0 m - (m - b) * w E 1 m) :
    b * (Tl E 1 b - Tl E 1 m) ≤ c * (Tl E 0 c - Tl E 0 m) := by
  have w0m := w_pos E hE h1 0 m hm
  have w1m := w_pos E hE h1 1 m hm
  have w10 := w1_lt_w0 E h4 m hm
  have hcb : b ≤ c := by
    have : (c - b) * w E 0 m = (m - b) * (w E 0 m - w E 1 m) := by linarith
    have : 0 ≤ (c - b) * w E 0 m := by rw [this]; apply mul_nonneg <;> linarith
    have := (mul_nonneg_iff_of_pos_right w0m).mp this
    linarith
  have hcm : c ≤ m := by
    have : (m - c) * w E 0 m = (m - b) * w E 1 m := by linarith
    have : 0 ≤ (m - c) * w E 0 m := by rw [this]; apply mul_nonneg <;> linarith
    have := (mul_nonneg_iff_of_pos_right w0m).mp this
    linarith
  rcases eq_or_lt_of_le hbm with hbm' | hbm'
  · -- b = m, then c = m
    have hcm' : c = m := by
      rw [← hbm'] at hc; subst hbm'
      have : (c - b) * w E 0 b = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    rw [hcm', ← hbm']; simp
  set b' := max b E.vlo
  set c' := max c E.vlo
  have hb'c' : b' ≤ c' := max_le_max hcb le_rfl
  have hc'm : c' ≤ m := max_le hcm hm.1
  have hb'V : b' ∈ E.V := ⟨le_max_right _ _, le_trans hb'c' (le_trans hc'm hm.2)⟩
  have hc'V : c' ∈ E.V := ⟨le_max_right _ _, le_trans hc'm hm.2⟩
  have hsubV : ∀ s ∈ Icc b' m, s ∈ E.V := fun s hs => ⟨le_trans hb'V.1 hs.1, le_trans hs.2 hm.2⟩
  rw [Tl_sub E hE h1 1 b m hm, Tl_sub E hE h1 0 c m hm]
  set L := ∫ s in b'..m, w E 1 s
  set Jb := ∫ s in b'..m, w E 0 s
  set Jc := ∫ s in c'..m, w E 0 s
  have hint : ∀ i x y, IntervalIntegrable (w E i) volume x y :=
    fun i x y => (w_cont E h1 i).intervalIntegrable x y
  -- (1) w₀(m) L ≤ w₁(m) Jb
  have e1 : w E 0 m * L ≤ w E 1 m * Jb := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (le_trans hb'c' hc'm)
      ((hint 1 _ _).const_mul _) ((hint 0 _ _).const_mul _)
    intro s hs
    have := ratio_mono E hE h1 h2 s m (hsubV s hs) hm hs.2
    linarith
  -- (2) split and bound
  have hsplit : Jb = (∫ s in b'..c', w E 0 s) + Jc :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 _ _) (hint 0 _ _)).symm
  have e2a : (∫ s in b'..c', w E 0 s) ≤ (c' - b') * w E 0 c' := by
    have := intervalIntegral.integral_mono_on hb'c' (hint 0 b' c')
      (intervalIntegrable_const (c := w E 0 c')) (fun s hs =>
        w_mono E hE h1 h3 0 s c' (hsubV s ⟨hs.1, le_trans hs.2 hc'm⟩) hc'V hs.2)
    simpa using this
  have e2b : (m - c') * w E 0 c' ≤ Jc := by
    have := intervalIntegral.integral_mono_on hc'm (intervalIntegrable_const (c := w E 0 c'))
      (hint 0 c' m) (fun s hs =>
        w_mono E hE h1 h3 0 c' s hc'V (hsubV s ⟨le_trans hb'c' hs.1, hs.2⟩) hs.1)
    simpa using this
  have hJb0 : 0 ≤ Jb := intervalIntegral.integral_nonneg (le_trans hb'c' hc'm)
    (fun s hs => (w_pos E hE h1 0 s (hsubV s hs)).le)
  have hJc0 : 0 ≤ Jc := intervalIntegral.integral_nonneg hc'm
    (fun s hs => (w_pos E hE h1 0 s (hsubV s ⟨le_trans hb'c' hs.1, hs.2⟩)).le)
  have hw0c' := w_pos E hE h1 0 c' hc'V
  have e2 : (m - c') * Jb ≤ (m - b') * Jc := by
    rw [hsplit]
    have : (m - c') * (∫ s in b'..c', w E 0 s) ≤ (c' - b') * Jc := by
      have h5 : (m - c') * (∫ s in b'..c', w E 0 s) ≤ (m - c') * ((c' - b') * w E 0 c') :=
        mul_le_mul_of_nonneg_left e2a (by linarith)
      have h6 : (c' - b') * ((m - c') * w E 0 c') ≤ (c' - b') * Jc :=
        mul_le_mul_of_nonneg_left e2b (by linarith)
      nlinarith
    nlinarith
  -- (3) (m - c) Jb ≤ (m - b) Jc
  have e3 : (m - c) * Jb ≤ (m - b) * Jc := by
    by_cases hbv : E.vlo ≤ b
    · have : b' = b := max_eq_left hbv
      have : c' = c := max_eq_left (le_trans hbv hcb)
      simp_all
    · by_cases hcv : E.vlo ≤ c
      · have hb'e : b' = E.vlo := max_eq_right (by linarith)
        have hc'e : c' = c := max_eq_left hcv
        rw [hc'e] at e2
        rw [hb'e] at e2
        have : (m - E.vlo) * Jc ≤ (m - b) * Jc := mul_le_mul_of_nonneg_right (by linarith) hJc0
        linarith
      · have hb'e : b' = E.vlo := max_eq_right (by linarith)
        have hc'e : c' = E.vlo := max_eq_right (by linarith)
        have hJ : Jb = Jc := by simp only [Jb, Jc, hb'e, hc'e]
        rw [hJ]
        exact mul_le_mul_of_nonneg_right (by linarith) hJc0
  -- (4) combine
  have e4 : w E 1 m * Jb ≤ w E 0 m * Jc := by
    have : (m - c) * w E 0 m = (m - b) * w E 1 m := by linarith
    have h7 : ((m - b) * w E 1 m) * Jb ≤ ((m - b) * w E 0 m) * Jc := by
      rw [← this]; nlinarith [mul_le_mul_of_nonneg_left e3 w0m.le]
    have h8 : (m - b) * (w E 1 m * Jb) ≤ (m - b) * (w E 0 m * Jc) := by nlinarith
    exact le_of_mul_le_mul_left h8 (by linarith)
  have e5 : (b * L) * w E 0 m ≤ (c * Jc) * w E 0 m := by
    have h9 : b * (w E 0 m * L) ≤ b * (w E 1 m * Jb) := mul_le_mul_of_nonneg_left e1 hb0
    have h10 : b * (w E 1 m * Jb) ≤ b * (w E 0 m * Jc) := mul_le_mul_of_nonneg_left e4 hb0
    have h11 : b * (w E 0 m * Jc) ≤ c * (w E 0 m * Jc) :=
      mul_le_mul_of_nonneg_right hcb (mul_nonneg w0m.le hJc0)
    nlinarith
  exact le_of_mul_le_mul_right e5 w0m

end Aux_MDU_P1

namespace Aux_MDU_P1
open MonopolyDemandUncertainty.SBSMP

noncomputable def P (E : Economy) (M : Mechanism) (v : ℝ) : ℝ :=
  ∑ i, M.t i v * ind (M.x i v) * E.prob i * E.dens i v

lemma P_eq (E : Economy) (M : Mechanism) (v : ℝ) :
    P E M v = M.t 0 v * ind (M.x 0 v) * w E 0 v + M.t 1 v * ind (M.x 1 v) * w E 1 v := by
  simp only [P, Fin.sum_univ_two, w]; ring

lemma payoff_eq (E : Economy) (M : Mechanism) (v vh : ℝ) :
    E.payoff M v vh = (v - M.t 0 vh) * ind (M.x 0 vh) * w E 0 v +
      (v - M.t 1 vh) * ind (M.x 1 vh) * w E 1 v := by
  simp only [Economy.payoff, Fin.sum_univ_two, w]; ring

lemma profit_eq (E : Economy) (M : Mechanism) : E.profit M = ∫ v in E.V, P E M v := rfl

lemma P_nonneg (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (M : Mechanism)
    (hEIR : E.IsEIR M) (v : ℝ) (hv : v ∈ E.V) : 0 ≤ P E M v := by
  rw [P_eq]
  have h0 := (hEIR 0 v hv).1
  have h1' := (hEIR 1 v hv).1
  have := w_pos E hE h1 0 v hv
  have := w_pos E hE h1 1 v hv
  have i0 : 0 ≤ ind (M.x 0 v) := by unfold ind; split_ifs <;> norm_num
  have i1 : 0 ≤ ind (M.x 1 v) := by unfold ind; split_ifs <;> norm_num
  positivity

/-- generic integral bound. -/
lemma profit_le_of (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (M : Mechanism)
    (hEIR : E.IsEIR M) {n : ℕ} (c : Fin n → ℝ) (I : Fin n → Fin 2) (X : Fin n → ℝ)
    (hX : ∀ k, X k ≤ E.vhi) (hpt : ∀ v ∈ E.V, P E M v ≤ ∑ k, c k * J E (I k) (X k) v) :
    E.profit M ≤ ∑ k, c k * Tl E (I k) (X k) := by
  rw [profit_eq, ← int_sum E hE h1 c I X hX]
  by_cases hint : IntegrableOn (P E M) E.V
  · exact setIntegral_mono_on hint (sum_integrable E h1 c I X) measurableSet_Icc hpt
  · rw [integral_undef hint]
    apply setIntegral_nonneg measurableSet_Icc
    intro v hv
    exact le_trans (P_nonneg E hE h1 M hEIR v hv) (hpt v hv)

/-- classification of the pointwise bound by consumption class. -/
lemma pointwise_of_classes (E : Economy) (M : Mechanism) (g : ℝ → ℝ)
    (h0 : ∀ v ∈ E.V, M.x 0 v = false → M.x 1 v = false → 0 ≤ g v)
    (hA : ∀ v ∈ E.V, M.x 0 v = true → M.x 1 v = false → M.t 0 v * w E 0 v ≤ g v)
    (hB : ∀ v ∈ E.V, M.x 0 v = false → M.x 1 v = true → M.t 1 v * w E 1 v ≤ g v)
    (hC : ∀ v ∈ E.V, M.x 0 v = true → M.x 1 v = true →
      M.t 0 v * w E 0 v + M.t 1 v * w E 1 v ≤ g v) :
    ∀ v ∈ E.V, P E M v ≤ g v := by
  intro v hv
  rw [P_eq]
  cases h0v : M.x 0 v <;> cases h1v : M.x 1 v <;> simp only [ind, Bool.false_eq_true, if_false,
    if_true, mul_zero, mul_one, zero_mul, add_zero, zero_add]
  · exact h0 v hv h0v h1v
  · exact hB v hv h0v h1v
  · exact hA v hv h0v h1v
  · exact hC v hv h0v h1v

lemma mem_only0 (E : Economy) (M : Mechanism) (v : ℝ) (hv : v ∈ E.V) (a : M.x 0 v = true)
    (b : M.x 1 v = false) : v ∈ E.onlySet M 0 := by
  refine ⟨hv, a, fun j hj => ?_⟩
  fin_cases j
  · exact absurd rfl hj
  · exact b

lemma mem_only1 (E : Economy) (M : Mechanism) (v : ℝ) (hv : v ∈ E.V) (a : M.x 0 v = false)
    (b : M.x 1 v = true) : v ∈ E.onlySet M 1 := by
  refine ⟨hv, b, fun j hj => ?_⟩
  fin_cases j
  · exact a
  · exact absurd rfl hj

lemma mem_both (E : Economy) (M : Mechanism) (v : ℝ) (hv : v ∈ E.V) (a : M.x 0 v = true)
    (b : M.x 1 v = true) : v ∈ E.bothSet M := by
  refine ⟨hv, fun j => ?_⟩
  fin_cases j
  · exact a
  · exact b

lemma only0_x (E : Economy) (M : Mechanism) (v : ℝ) (hv : v ∈ E.onlySet M 0) :
    M.x 0 v = true ∧ M.x 1 v = false := ⟨hv.2.1, hv.2.2 1 (by decide)⟩

lemma only1_x (E : Economy) (M : Mechanism) (v : ℝ) (hv : v ∈ E.onlySet M 1) :
    M.x 0 v = false ∧ M.x 1 v = true := ⟨hv.2.2 0 (by decide), hv.2.1⟩

lemma both_x (E : Economy) (M : Mechanism) (v : ℝ) (hv : v ∈ E.bothSet M) :
    M.x 0 v = true ∧ M.x 1 v = true := ⟨hv.2 0, hv.2 1⟩

section mech
variable (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h2 : E.Condition2)
  (M : Mechanism) (hBIC : E.IsBIC M) (hEIR : E.IsEIR M)
include hE h1 h2 hBIC hEIR

/-- (A.4): a type of `V₁₂` pays at most the scheme of any other type of `V₁₂`. -/
lemma M1 (u v : ℝ) (hu : u ∈ E.bothSet M) (hv : v ∈ E.bothSet M) :
    M.t 0 v * w E 0 v + M.t 1 v * w E 1 v ≤ M.t 0 u * w E 0 v + M.t 1 u * w E 1 v := by
  have hh := hBIC v hv.1 u hu.1
  rw [payoff_eq, payoff_eq] at hh
  obtain ⟨a0, a1⟩ := both_x E M u hu
  obtain ⟨b0, b1⟩ := both_x E M v hv
  simp only [ind, a0, a1, b0, b1, if_true, mul_one] at hh
  linarith

/-- bound for `V₁₂` types above `u` when `V₁` is nonempty. -/
lemma M2 (u v q : ℝ) (hu : u ∈ E.bothSet M) (hq : q ∈ E.onlySet M 0) (hv : v ∈ E.V)
    (huv : u ≤ v) :
    M.t 0 u * w E 0 v + M.t 1 u * w E 1 v ≤ M.t 0 q * w E 0 v + u * w E 1 v := by
  have hh := hBIC u hu.1 q hq.1
  rw [payoff_eq, payoff_eq] at hh
  obtain ⟨a0, a1⟩ := both_x E M u hu
  obtain ⟨b0, b1⟩ := only0_x E M q hq
  simp only [ind, a0, a1, b0, b1, if_true, Bool.false_eq_true, if_false, mul_one,
    mul_zero, zero_mul, add_zero] at hh
  have k : (M.t 0 u - M.t 0 q) * w E 0 u ≤ (u - M.t 1 u) * w E 1 u := by linarith
  have := transfer E hE h1 h2 u v _ _ hu.1 hv huv (by linarith [(hEIR 1 u hu.1).2]) k
  linarith

/-- bound for `V₁₂` types above `u` when `V₂` is nonempty. -/
lemma M3 (u v q c : ℝ) (hu : u ∈ E.bothSet M) (hq : q ∈ E.onlySet M 1) (hv : v ∈ E.V)
    (huv : u ≤ v) (hc : c * w E 0 u = u * w E 0 u - (u - M.t 1 q) * w E 1 u) :
    M.t 0 u * w E 0 v + M.t 1 u * w E 1 v ≤ c * w E 0 v + u * w E 1 v := by
  have hh := hBIC u hu.1 q hq.1
  rw [payoff_eq, payoff_eq] at hh
  obtain ⟨a0, a1⟩ := both_x E M u hu
  obtain ⟨b0, b1⟩ := only1_x E M q hq
  simp only [ind, a0, a1, b0, b1, if_true, Bool.false_eq_true, if_false, mul_one,
    mul_zero, zero_mul, zero_add] at hh
  have k : (M.t 0 u - c) * w E 0 u ≤ (u - M.t 1 u) * w E 1 u := by nlinarith
  have := transfer E hE h1 h2 u v _ _ hu.1 hv huv (by linarith [(hEIR 1 u hu.1).2]) k
  linarith

/-- the `V₂` price is at most every `V₁₂` type. -/
lemma M4 (u q : ℝ) (hu : u ∈ E.bothSet M) (hq : q ∈ E.onlySet M 1) : M.t 1 q ≤ u := by
  by_contra hlt
  rw [not_le] at hlt
  have hh := hBIC q hq.1 u hu.1
  rw [payoff_eq, payoff_eq] at hh
  obtain ⟨a0, a1⟩ := both_x E M u hu
  obtain ⟨b0, b1⟩ := only1_x E M q hq
  simp only [ind, a0, a1, b0, b1, if_true, Bool.false_eq_true, if_false, mul_one,
    mul_zero, zero_mul, zero_add] at hh
  have hqb := (hEIR 1 q hq.1).2
  have t0u := (hEIR 0 u hu.1).2
  have t1u := (hEIR 1 u hu.1).2
  have w0 := w_pos E hE h1 0 q hq.1
  have w1 := w_pos E hE h1 1 q hq.1
  have e1 : 0 < (q - M.t 0 u) * w E 0 q := mul_pos (by linarith) w0
  have e2 : (q - M.t 1 q) * w E 1 q ≤ (q - M.t 1 u) * w E 1 q :=
    mul_le_mul_of_nonneg_right (by linarith) w1.le
  linarith

/-- the `V₂` price is at most the `V₁` price (Condition 4(ii)). -/
lemma M5 (h4 : E.Condition4ii) (q r : ℝ) (hq : q ∈ E.onlySet M 1) (hr : r ∈ E.onlySet M 0) :
    M.t 1 q ≤ M.t 0 r := by
  have hh := hBIC q hq.1 r hr.1
  rw [payoff_eq, payoff_eq] at hh
  obtain ⟨a0, a1⟩ := only0_x E M r hr
  obtain ⟨b0, b1⟩ := only1_x E M q hq
  simp only [ind, a0, a1, b0, b1, if_true, Bool.false_eq_true, if_false, mul_one,
    mul_zero, zero_mul, zero_add, add_zero] at hh
  have hqb := (hEIR 1 q hq.1).2
  have w0 := w_pos E hE h1 0 q hq.1
  have w10 := w1_lt_w0 E h4 q hq.1
  have : (q - M.t 1 q) * w E 1 q ≤ (q - M.t 1 q) * w E 0 q :=
    mul_le_mul_of_nonneg_left w10.le (by linarith)
  have : (q - M.t 0 r) * w E 0 q ≤ (q - M.t 1 q) * w E 0 q := by linarith
  have := le_of_mul_le_mul_right this w0
  linarith

/-- BIC of a `V₁` type w.r.t. a `V₂` type. -/
lemma M6 (q r : ℝ) (hq : q ∈ E.onlySet M 1) (hr : r ∈ E.onlySet M 0) :
    M.t 0 r * w E 0 r ≤ r * w E 0 r - (r - M.t 1 q) * w E 1 r := by
  have hh := hBIC r hr.1 q hq.1
  rw [payoff_eq, payoff_eq] at hh
  obtain ⟨a0, a1⟩ := only0_x E M r hr
  obtain ⟨b0, b1⟩ := only1_x E M q hq
  simp only [ind, a0, a1, b0, b1, if_true, Bool.false_eq_true, if_false, mul_one,
    mul_zero, zero_mul, zero_add, add_zero] at hh
  linarith

end mech

end Aux_MDU_P1

namespace Aux_MDU_L1
open MonopolyDemandUncertainty.SBSMP Aux_MDU_P1

lemma J_pos' (E : Economy) (i : Fin 2) (x v : ℝ) (h : x ≤ v) : J E i x v = w E i v := by
  simp [J, h]

lemma J_neg' (E : Economy) (i : Fin 2) (x v : ℝ) (h : v < x) : J E i x v = 0 := by
  simp [J, not_le.mpr h]

lemma J_nonneg' (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (x v : ℝ)
    (hv : v ∈ E.V) : 0 ≤ J E i x v := by
  unfold J; split_ifs
  · exact (w_pos E hE h1 i v hv).le
  · exact le_rfl

lemma Tl_vhi (E : Economy) (hE : E.Valid) (i : Fin 2) : Tl E i E.vhi = 0 := by
  unfold Tl; rw [max_eq_left hE.vlo_lt_vhi.le, hE.D_vhi i]; ring

lemma Tl_pos (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (x : ℝ)
    (hx : x < E.vhi) : 0 < Tl E i x := by
  unfold Tl
  apply mul_pos (prob_pos E hE i)
  have hlt : max x E.vlo < E.vhi := max_lt hx hE.vlo_lt_vhi
  have hmV : max x E.vlo ∈ E.V := ⟨le_max_right _ _, hlt.le⟩
  have hs : StrictAntiOn (E.D i) E.V := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (D_diff E h1 i).continuous.continuousOn
    intro v hv; exact h1.2 i v (interior_subset hv)
  have := hs hmV ⟨hE.vlo_lt_vhi.le, le_rfl⟩ hlt
  rw [hE.D_vhi i] at this; exact this

lemma sbsmp_EIR' (E : Economy) (hE : E.Valid) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    E.IsEIR (sbsmp a b) := by
  intro i v hv
  have hv0 : 0 ≤ v := le_trans hE.vlo_nonneg hv.1
  fin_cases i
  · simp only [sbsmp, Fin.zero_eta, Matrix.cons_val_zero]
    split_ifs with h <;> constructor <;> linarith
  · simp only [sbsmp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    split_ifs with h <;> constructor <;> linarith

lemma term_le (c v vhat w' : ℝ) (hw : 0 ≤ w') :
    (v - (if c ≤ vhat then c else 0)) * ind (decide (c ≤ vhat)) * w' ≤
      (v - (if c ≤ v then c else 0)) * ind (decide (c ≤ v)) * w' := by
  by_cases h1 : c ≤ vhat <;> by_cases h2 : c ≤ v <;> simp [ind, h1, h2]
  · nlinarith
  · nlinarith

lemma sbsmp_BIC' (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (a b : ℝ) :
    E.IsBIC (sbsmp a b) := by
  intro v hv vhat _
  have hw0 : 0 ≤ E.prob 0 * E.dens 0 v :=
    (mul_pos (prob_pos E hE 0) (dens_pos E h1 0 v hv)).le
  have hw1 : 0 ≤ E.prob 1 * E.dens 1 v :=
    (mul_pos (prob_pos E hE 1) (dens_pos E h1 1 v hv)).le
  unfold Economy.payoff
  simp only [Fin.sum_univ_two, sbsmp, Matrix.cons_val_zero, Matrix.cons_val_one]
  have t0 := term_le a v vhat _ hw0
  have t1 := term_le b v vhat _ hw1
  simp only [mul_assoc] at t0 t1 ⊢
  linarith

lemma sbsmp_profit' (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (a b : ℝ)
    (ha : a ≤ E.vhi) (hb : b ≤ E.vhi) :
    E.profit (sbsmp a b) = a * Tl E 0 a + b * Tl E 1 b := by
  have hfun : ∀ v, P E (sbsmp a b) v = ∑ k, ![a, b] k * J E (![0, 1] k) (![a, b] k) v := by
    intro v
    rw [P_eq]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      sbsmp, J, ind]
    by_cases ha' : a ≤ v <;> by_cases hb' : b ≤ v <;> simp [ha', hb']
  rw [profit_eq, show (fun v => P E (sbsmp a b) v) = fun v =>
    ∑ k, ![a, b] k * J E (![0, 1] k) (![a, b] k) v from funext hfun,
    int_sum E hE h1 _ _ _ (by intro k; fin_cases k <;> simp [ha, hb])]
  simp [Fin.sum_univ_two]

end Aux_MDU_L1

open MonopolyDemandUncertainty.SBSMP Aux_MDU_P1 Aux_MDU_L1 in
theorem solution (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (M : Mechanism)
    (hBIC : E.IsBIC M) (hEIR : E.IsEIR M)
    (hV12 : ∀ v ∈ E.V, ¬ (M.x 0 v = true ∧ M.x 1 v = true)) :
    ∃ M' : Mechanism, E.IsBIC M' ∧ E.IsEIR M' ∧ E.profit M < E.profit M' := by
  have hI := hEIR
  have hvhi0 : 0 ≤ E.vhi := le_trans hE.vlo_nonneg hE.vlo_lt_vhi.le
  have Jn : ∀ i x v, v ∈ E.V → 0 ≤ J E i x v := fun i x v hv => J_nonneg' E hE h1 i x v hv
  have price : ∀ i (q : ℝ), q ∈ E.onlySet M i → ∀ v ∈ E.onlySet M i, M.t i v = M.t i q :=
    fun i q hq v hv => MonopolyDemandUncertainty.SBSMP.fact_1 E hE h1 M hBIC i v hv q hq
  have pexist : ∀ i : Fin 2, ∃ a : ℝ, (∀ v ∈ E.onlySet M i, M.t i v = a) ∧ 0 ≤ a ∧
      a ≤ E.vhi := by
    intro i
    by_cases hn : (E.onlySet M i).Nonempty
    · obtain ⟨q, hq⟩ := hn
      exact ⟨M.t i q, price i q hq, (hI i q hq.1).1, le_trans (hI i q hq.1).2 hq.1.2⟩
    · exact ⟨0, fun v hv => absurd ⟨v, hv⟩ hn, le_rfl, hvhi0⟩
  obtain ⟨a, ha, ha0, hav⟩ := pexist 0
  obtain ⟨b, hb, hb0, hbv⟩ := pexist 1
  -- base pointwise bound
  have hpt : ∀ v ∈ E.V, P E M v ≤ a * J E 0 a v + b * J E 1 b v := by
    apply pointwise_of_classes
    · intro v hv _ _; have := mul_nonneg ha0 (Jn 0 a v hv); have := mul_nonneg hb0 (Jn 1 b v hv)
      linarith
    · intro v hv x0 x1
      have e := ha v (mem_only0 E M v hv x0 x1)
      have hle : a ≤ v := by rw [← e]; exact (hI 0 v hv).2
      rw [e, J_pos' E 0 a v hle]; have := mul_nonneg hb0 (Jn 1 b v hv); linarith
    · intro v hv x0 x1
      have e := hb v (mem_only1 E M v hv x0 x1)
      have hle : b ≤ v := by rw [← e]; exact (hI 1 v hv).2
      rw [e, J_pos' E 1 b v hle]; have := mul_nonneg ha0 (Jn 0 a v hv); linarith
    · intro v hv x0 x1; exact absurd ⟨x0, x1⟩ (hV12 v hv)
  have hbase : E.profit M ≤ a * Tl E 0 a + b * Tl E 1 b := by
    have hfin := profit_le_of E hE h1 M hI ![a, b] ![0, 1] ![a, b]
      (by intro k; fin_cases k <;> simp [hav, hbv]) (by
        intro v hv; simpa [Fin.sum_univ_succ] using hpt v hv)
    simpa [Fin.sum_univ_succ] using hfin
  have zero_of : ∀ i (x : ℝ), 0 ≤ x → x ≤ E.vhi → ¬ (0 < x ∧ x < E.vhi) → x * Tl E i x = 0 := by
    intro i x hx0 hx hn
    rcases eq_or_lt_of_le hx0 with h | h
    · rw [← h]; ring
    · have : x = E.vhi := by
        by_contra hne; exact hn ⟨h, lt_of_le_of_ne hx hne⟩
      rw [this, Tl_vhi E hE i]; ring
  by_cases hA : 0 < a ∧ a < E.vhi <;> by_cases hB : 0 < b ∧ b < E.vhi
  · -- strict bound
    refine ⟨sbsmp a b, sbsmp_BIC' E hE h1 a b, sbsmp_EIR' E hE a b ha0 hb0, ?_⟩
    rw [sbsmp_profit' E hE h1 a b hav hbv]
    have hVne : E.V.Nonempty := ⟨E.vlo, le_rfl, hE.vlo_lt_vhi.le⟩
    obtain ⟨v0, hv0V, hv0⟩ := isCompact_Icc.exists_isMinOn hVne (w_cont E h1 0).continuousOn
    obtain ⟨v1, hv1V, hv1⟩ := isCompact_Icc.exists_isMinOn hVne (w_cont E h1 1).continuousOn
    set K := min (a * w E 0 v0) (b * w E 1 v1) with hK
    have hKpos : 0 < K := lt_min (mul_pos hA.1 (w_pos E hE h1 0 v0 hv0V))
      (mul_pos hB.1 (w_pos E hE h1 1 v1 hv1V))
    set c := max a b with hc
    set hf : ℝ → ℝ := (Ici c).indicator (fun _ => K) with hhf
    have hpt2 : ∀ v ∈ E.V, P E M v ≤ (a * J E 0 a v + b * J E 1 b v) - hf v := by
      intro v hv
      rcases lt_or_ge v c with hvc | hvc
      · have : hf v = 0 := by simp [hhf, Set.indicator_apply, not_le.mpr hvc]
        rw [this, sub_zero]; exact hpt v hv
      · have hfv : hf v = K := by simp [hhf, Set.indicator_apply, hvc]
        rw [hfv]
        have hav' : a ≤ v := le_trans (le_max_left _ _) hvc
        have hbv' : b ≤ v := le_trans (le_max_right _ _) hvc
        have k0 : K ≤ a * w E 0 v := le_trans (min_le_left _ _)
          (mul_le_mul_of_nonneg_left (hv0 hv) ha0)
        have k1 : K ≤ b * w E 1 v := le_trans (min_le_right _ _)
          (mul_le_mul_of_nonneg_left (hv1 hv) hb0)
        rw [J_pos' E 0 a v hav', J_pos' E 1 b v hbv']
        rw [P_eq]
        cases h0v : M.x 0 v <;> cases h1v : M.x 1 v <;> simp only [ind, Bool.false_eq_true,
          if_false, if_true, mul_zero, mul_one, zero_mul, add_zero, zero_add]
        · linarith
        · rw [hb v (mem_only1 E M v hv h0v h1v)]; linarith
        · rw [ha v (mem_only0 E M v hv h0v h1v)]; linarith
        · exact absurd ⟨h0v, h1v⟩ (hV12 v hv)
    have hgint : IntegrableOn (fun v => a * J E 0 a v + b * J E 1 b v) E.V :=
      ((J_integrable E h1 0 a).const_mul a).add ((J_integrable E h1 1 b).const_mul b)
    have hfint : IntegrableOn hf E.V :=
      (continuous_const.integrableOn_Icc).indicator measurableSet_Ici
    have hgval : ∫ v in E.V, (a * J E 0 a v + b * J E 1 b v) = a * Tl E 0 a + b * Tl E 1 b := by
      rw [integral_add ((J_integrable E h1 0 a).const_mul a) ((J_integrable E h1 1 b).const_mul b),
        integral_const_mul, integral_const_mul, int_J E hE h1 0 a hav, int_J E hE h1 1 b hbv]
    have hcmax : max c E.vlo < E.vhi := max_lt (max_lt hA.2 hB.2) hE.vlo_lt_vhi
    have hfval : ∫ v in E.V, hf v = (E.vhi - max c E.vlo) * K := by
      rw [hhf, setIntegral_indicator measurableSet_Ici]
      have hset : E.V ∩ Ici c = Icc (max c E.vlo) E.vhi := by
        ext v; simp only [Economy.V, mem_inter_iff, mem_Icc, mem_Ici, max_le_iff]; tauto
      rw [hset, setIntegral_const, Real.volume_real_Icc_of_le hcmax.le, smul_eq_mul]
    have hfpos : 0 < ∫ v in E.V, hf v := by
      rw [hfval]; exact mul_pos (by linarith) hKpos
    by_cases hint : IntegrableOn (P E M) E.V
    · have hsub : IntegrableOn (fun v => (a * J E 0 a v + b * J E 1 b v) - hf v) E.V :=
        hgint.sub hfint
      have := setIntegral_mono_on hint hsub measurableSet_Icc hpt2
      rw [integral_sub hgint hfint, hgval] at this
      rw [profit_eq]; linarith
    · rw [profit_eq, integral_undef hint]
      have := mul_pos hA.1 (Tl_pos E hE h1 0 a hA.2)
      have := mul_pos hB.1 (Tl_pos E hE h1 1 b hB.2)
      linarith
  · refine ⟨sbsmp a a, sbsmp_BIC' E hE h1 a a, sbsmp_EIR' E hE a a ha0 ha0, ?_⟩
    rw [sbsmp_profit' E hE h1 a a hav hav]
    have := zero_of 1 b hb0 hbv hB
    have := mul_pos hA.1 (Tl_pos E hE h1 1 a hA.2)
    linarith
  · refine ⟨sbsmp b b, sbsmp_BIC' E hE h1 b b, sbsmp_EIR' E hE b b hb0 hb0, ?_⟩
    rw [sbsmp_profit' E hE h1 b b hbv hbv]
    have := zero_of 0 a ha0 hav hA
    have := mul_pos hB.1 (Tl_pos E hE h1 0 b hB.2)
    linarith
  · set c := (E.vlo + E.vhi) / 2 with hc
    have hc0 : 0 < c := by linarith [hE.vlo_nonneg, hE.vlo_lt_vhi]
    have hcv : c < E.vhi := by linarith [hE.vlo_lt_vhi]
    refine ⟨sbsmp c c, sbsmp_BIC' E hE h1 c c, sbsmp_EIR' E hE c c hc0.le hc0.le, ?_⟩
    rw [sbsmp_profit' E hE h1 c c hcv.le hcv.le]
    have := zero_of 0 a ha0 hav hA
    have := zero_of 1 b hb0 hbv hB
    have := mul_pos hc0 (Tl_pos E hE h1 0 c hcv)
    have := mul_pos hc0 (Tl_pos E hE h1 1 c hcv)
    linarith
