-- Prove2me | solution 1 for MonopolyDemandUncertainty.SBSMP.proposition_1_condition_4ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:10:33.529416+00:00
-- url     : https://prove2.me/submissions/c086c836-62a0-45a9-a144-3cd124cf6f93

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting
import Theorems.Thm_MonopolyDemandUncertainty_SBSMP_fact_1
import Theorems.Thm_MonopolyDemandUncertainty_SBSMP_lemma_2_i
import Theorems.Thm_MonopolyDemandUncertainty_SBSMP_a57_sbsmp_profit

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

namespace Aux_MDU_P1
open MonopolyDemandUncertainty.SBSMP

lemma J_pos (E : Economy) (i : Fin 2) (x v : ℝ) (h : x ≤ v) : J E i x v = w E i v := by
  simp [J, h]

lemma J_neg (E : Economy) (i : Fin 2) (x v : ℝ) (h : v < x) : J E i x v = 0 := by
  simp [J, not_le.mpr h]

lemma J_nonneg (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (x v : ℝ)
    (hv : v ∈ E.V) : 0 ≤ J E i x v := by
  unfold J; split_ifs
  · exact (w_pos E hE h1 i v hv).le
  · exact le_rfl

/-- the "small set" term `v̄ (w₀ + w₁) 1[m ≤ v < u]`. -/
noncomputable def Ct (E : Economy) (m u v : ℝ) : ℝ :=
  E.vhi * (J E 0 m v + J E 1 m v - J E 0 u v - J E 1 u v)

lemma Ct_nonneg (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (m u v : ℝ) (hmu : m ≤ u)
    (hv : v ∈ E.V) : 0 ≤ Ct E m u v := by
  unfold Ct
  have hvhi : 0 ≤ E.vhi := le_trans hE.vlo_nonneg hE.vlo_lt_vhi.le
  apply mul_nonneg hvhi
  rcases lt_or_ge v m with h | h
  · rw [J_neg E 0 m v h, J_neg E 1 m v h, J_neg E 0 u v (by linarith),
      J_neg E 1 u v (by linarith)]; simp
  · rcases lt_or_ge v u with h' | h'
    · rw [J_pos E 0 m v h, J_pos E 1 m v h, J_neg E 0 u v h', J_neg E 1 u v h']
      have := w_pos E hE h1 0 v hv
      have := w_pos E hE h1 1 v hv
      linarith
    · rw [J_pos E 0 m v h, J_pos E 1 m v h, J_pos E 0 u v h', J_pos E 1 u v h']; simp

lemma Ct_mid (E : Economy) (m u v : ℝ) (h : m ≤ v) (h' : v < u) :
    Ct E m u v = E.vhi * (w E 0 v + w E 1 v) := by
  unfold Ct
  rw [J_pos E 0 m v h, J_pos E 1 m v h, J_neg E 0 u v h', J_neg E 1 u v h']; ring

lemma Ct_hi (E : Economy) (m u v : ℝ) (hmu : m ≤ u) (h' : u ≤ v) : Ct E m u v = 0 := by
  unfold Ct
  rw [J_pos E 0 m v (le_trans hmu h'), J_pos E 1 m v (le_trans hmu h'), J_pos E 0 u v h',
    J_pos E 1 u v h']; ring

lemma small_bound (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (M : Mechanism)
    (hEIR : E.IsEIR M) (v : ℝ) (hv : v ∈ E.V) :
    M.t 0 v * w E 0 v + M.t 1 v * w E 1 v ≤ E.vhi * (w E 0 v + w E 1 v) := by
  have := w_pos E hE h1 0 v hv
  have := w_pos E hE h1 1 v hv
  have e0 : M.t 0 v ≤ E.vhi := le_trans (hEIR 0 v hv).2 hv.2
  have e1 : M.t 1 v ≤ E.vhi := le_trans (hEIR 1 v hv).2 hv.2
  nlinarith

lemma Jdiff_nonneg (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (i : Fin 2) (b u v : ℝ)
    (hbu : b ≤ u) (hv : v ∈ E.V) : 0 ≤ J E i b v - J E i u v := by
  rcases lt_or_ge v b with h | h
  · rw [J_neg E i b v h, J_neg E i u v (by linarith)]; simp
  · rcases lt_or_ge v u with h' | h'
    · rw [J_pos E i b v h, J_neg E i u v h']; have := w_pos E hE h1 i v hv; linarith
    · rw [J_pos E i b v h, J_pos E i u v h']; simp

/-- finishing the ε-argument. -/
lemma approx_finish (S : Set ℝ) (hS : S.Nonempty) (hb : BddBelow S) (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : f (sInf S) = 0) (X K : ℝ) (hK : ∀ u ∈ S, X ≤ K + f u) :
    X ≤ K := by
  by_contra hlt
  rw [not_le] at hlt
  have hc := (Metric.continuousAt_iff.mp (hf.continuousAt (x := sInf S))) (X - K) (by linarith)
  obtain ⟨η, hη, hη'⟩ := hc
  obtain ⟨u, huS, hu⟩ := exists_lt_of_csInf_lt hS (show sInf S < sInf S + η by linarith)
  have hmu : sInf S ≤ u := csInf_le hb huS
  have hd : dist u (sInf S) < η := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
  have := hη' hd
  rw [hf0, Real.dist_eq, abs_lt] at this
  have := hK u huS
  linarith

end Aux_MDU_P1

open MonopolyDemandUncertainty.SBSMP Aux_MDU_P1 in
theorem solution (E : Economy) (hE : E.Valid)
    (h1 : E.Condition1) (h2 : E.Condition2) (h3 : E.Condition3) (h4 : E.Condition4ii)
    (p₁ p₂ : ℝ) (hp₁ : E.IsMonopolyPrice 0 p₁) (hp₂ : E.IsMonopolyPrice 1 p₂) :
    E.IsBIC (sbsmp p₁ p₂) ∧ E.IsEIR (sbsmp p₁ p₂) ∧
      ∀ M : Mechanism, E.IsBIC M → E.IsEIR M → E.profit M ≤ E.profit (sbsmp p₁ p₂) := by
  have A := a57_sbsmp_profit E hE h1 h3 p₁ p₂ hp₁ hp₂
  refine ⟨A.2.2.1, A.2.2.2, fun M hB hI => ?_⟩
  set R := E.prob 0 * (p₁ * E.D 0 p₁) + E.prob 1 * (p₂ * E.D 1 p₂) with hRdef
  have hR : E.profit (sbsmp p₁ p₂) = R := by
    rw [A.1 p₁ hp₁.1 p₂ hp₂.1, hRdef]; simp [Economy.prob]; ring
  rw [hR]
  have hvhi0 : 0 ≤ E.vhi := le_trans hE.vlo_nonneg hE.vlo_lt_vhi.le
  have FB0 : ∀ x, 0 ≤ x → x ≤ E.vhi → x * Tl E 0 x ≤ E.prob 0 * (p₁ * E.D 0 p₁) :=
    fun x hx0 hx => F_bound E hE h1 0 p₁ x hp₁ hx0 hx
  have FB1 : ∀ x, 0 ≤ x → x ≤ E.vhi → x * Tl E 1 x ≤ E.prob 1 * (p₂ * E.D 1 p₂) :=
    fun x hx0 hx => F_bound E hE h1 1 p₂ x hp₂ hx0 hx
  have wp : ∀ i v, v ∈ E.V → 0 < w E i v := fun i v hv => w_pos E hE h1 i v hv
  have Jn : ∀ i x v, v ∈ E.V → 0 ≤ J E i x v := fun i x v hv => J_nonneg E hE h1 i x v hv
  -- prices of the one-state sets
  have price : ∀ i (q : ℝ), q ∈ E.onlySet M i → ∀ v ∈ E.onlySet M i, M.t i v = M.t i q :=
    fun i q hq v hv => MonopolyDemandUncertainty.SBSMP.fact_1 E hE h1 M hB i v hv q hq
  by_cases h12 : (E.bothSet M).Nonempty
  swap
  · -- Case A: nobody consumes in both states
    have pexist : ∀ i : Fin 2, ∃ a : ℝ, (∀ v ∈ E.onlySet M i, M.t i v = a) ∧ 0 ≤ a ∧
        a ≤ E.vhi := by
      intro i
      by_cases hn : (E.onlySet M i).Nonempty
      · obtain ⟨q, hq⟩ := hn
        exact ⟨M.t i q, price i q hq, (hI i q hq.1).1, le_trans (hI i q hq.1).2 hq.1.2⟩
      · exact ⟨0, fun v hv => absurd ⟨v, hv⟩ hn, le_rfl, hvhi0⟩
    obtain ⟨a, ha, ha0, hav⟩ := pexist 0
    obtain ⟨b, hb, hb0, hbv⟩ := pexist 1
    have hpt : ∀ v ∈ E.V, P E M v ≤ a * J E 0 a v + b * J E 1 b v := by
      apply pointwise_of_classes
      · intro v hv _ _; have := mul_nonneg ha0 (Jn 0 a v hv); have := mul_nonneg hb0 (Jn 1 b v hv); linarith
      · intro v hv x0 x1
        have e := ha v (mem_only0 E M v hv x0 x1)
        have hle : a ≤ v := by rw [← e]; exact (hI 0 v hv).2
        rw [e, J_pos E 0 a v hle]; have := mul_nonneg hb0 (Jn 1 b v hv); linarith
      · intro v hv x0 x1
        have e := hb v (mem_only1 E M v hv x0 x1)
        have hle : b ≤ v := by rw [← e]; exact (hI 1 v hv).2
        rw [e, J_pos E 1 b v hle]; have := mul_nonneg ha0 (Jn 0 a v hv); linarith
      · intro v hv x0 x1; exact absurd ⟨v, mem_both E M v hv x0 x1⟩ h12
    have hfin := profit_le_of E hE h1 M hI ![a, b] ![0, 1] ![a, b]
      (by intro k; fin_cases k <;> simp [hav, hbv]) (by
        intro v hv; simpa [Fin.sum_univ_succ] using hpt v hv)
    simp [Fin.sum_univ_succ] at hfin
    linarith [FB0 a ha0 hav, FB1 b hb0 hbv]
  · obtain ⟨u0, hu0⟩ := h12
    have hbdd : BddBelow (E.bothSet M) := ⟨E.vlo, fun v hv => hv.1.1⟩
    set m := sInf (E.bothSet M) with hmdef
    have hmle : ∀ v ∈ E.bothSet M, m ≤ v := fun v hv => csInf_le hbdd hv
    have hmhi : m ≤ E.vhi := le_trans (hmle u0 hu0) hu0.1.2
    set Ef : ℝ → ℝ := fun u => E.vhi * (Tl E 0 m + Tl E 1 m - Tl E 0 u - Tl E 1 u) with hEf
    have hEfc : Continuous Ef := continuous_const.mul
      (((continuous_const.add continuous_const).sub (Tl_cont E h1 0)).sub (Tl_cont E h1 1))
    have hEf0 : Ef m = 0 := by simp [hEf]
    have hsmall : ∀ u ∈ E.bothSet M, ∀ v ∈ E.V, M.x 0 v = true → M.x 1 v = true → v < u →
        M.t 0 v * w E 0 v + M.t 1 v * w E 1 v ≤ Ct E m u v := by
      intro u hu v hv x0 x1 hvu
      rw [Ct_mid E m u v (hmle v (mem_both E M v hv x0 x1)) hvu]
      exact small_bound E hE h1 M hI v hv
    suffices hmain : ∀ u ∈ E.bothSet M, E.profit M ≤ R + Ef u by
      exact approx_finish _ ⟨u0, hu0⟩ hbdd Ef hEfc hEf0 _ _ hmain
    intro u hu
    have huV := hu.1
    have hmu := hmle u hu
    have hCt0 : ∀ v ∈ E.V, 0 ≤ Ct E m u v := fun v hv => Ct_nonneg E hE h1 m u v hmu hv
    have hu0' : 0 ≤ u := le_trans hE.vlo_nonneg huV.1
    have t0u := hI 0 u huV
    have t1u := hI 1 u huV
    by_cases hS1 : (E.onlySet M 0).Nonempty <;> by_cases hS2 : (E.onlySet M 1).Nonempty
    · -- B3: V₁, V₂, V₁₂ all nonempty
      obtain ⟨q, hq⟩ := hS2
      obtain ⟨r, hr⟩ := hS1
      set b := M.t 1 q with hbdef
      set a := M.t 0 r with hadef
      have hb0 : 0 ≤ b := (hI 1 q hq.1).1
      have ha0 : 0 ≤ a := (hI 0 r hr.1).1
      have hba : b ≤ a := M5 E hE h1 h2 M hB hI h4 q r hq hr
      have hbdd1 : BddBelow (E.onlySet M 0) := ⟨E.vlo, fun v hv => hv.1.1⟩
      set m' := sInf (E.onlySet M 0) with hm'def
      have hm'le : ∀ v ∈ E.onlySet M 0, m' ≤ v := fun v hv => csInf_le hbdd1 hv
      set Ef' : ℝ → ℝ := fun v1 => E.vhi * (Tl E 0 m' + Tl E 1 m' - Tl E 0 v1 - Tl E 1 v1)
        with hEf'
      have hEf'c : Continuous Ef' := continuous_const.mul
        (((continuous_const.add continuous_const).sub (Tl_cont E h1 0)).sub (Tl_cont E h1 1))
      have hEf'0 : Ef' m' = 0 := by simp [hEf']
      suffices hm2 : ∀ v1 ∈ E.onlySet M 0, E.profit M ≤ (R + Ef u) + Ef' v1 by
        exact approx_finish _ ⟨r, hr⟩ hbdd1 Ef' hEf'c hEf'0 _ _ hm2
      intro v1 hv1
      have hv1V := hv1.1
      have hta1 : M.t 0 v1 = a := price 0 r hr v1 hv1
      have hav1 : a ≤ v1 := by rw [← hta1]; exact (hI 0 v1 hv1V).2
      have hv1u : v1 < u := MonopolyDemandUncertainty.SBSMP.lemma_2_i E hE h1 h2 M hB hI v1 hv1 u hu
      have hbv1 : b ≤ v1 := le_trans hba hav1
      have hm'v1 := hm'le v1 hv1
      have w0v1 := wp 0 v1 hv1V
      set cc := v1 - (v1 - b) * (w E 1 v1 / w E 0 v1) with hccdef
      have hcc : cc * w E 0 v1 = v1 * w E 0 v1 - (v1 - b) * w E 1 v1 := by
        rw [hccdef]; field_simp
      have hacc : a ≤ cc := by
        have := M6 E hE h1 h2 M hB hI q v1 hq hv1
        rw [hta1, ← hbdef, ← hcc] at this
        exact le_of_mul_le_mul_right this w0v1
      have hccv1 : cc ≤ v1 := by
        have : 0 ≤ (v1 - b) * (w E 1 v1 / w E 0 v1) :=
          mul_nonneg (by linarith) (div_nonneg (wp 1 v1 hv1V).le w0v1.le)
        linarith
      have hCt0' : ∀ v ∈ E.V, 0 ≤ Ct E m' v1 v := fun v hv =>
        Ct_nonneg E hE h1 m' v1 v hm'v1 hv
      have hpt : ∀ v ∈ E.V, P E M v ≤ a * J E 0 v1 v + b * (J E 1 b v - J E 1 v1 v) +
          u * J E 1 u v + Ct E m u v + Ct E m' v1 v := by
        apply pointwise_of_classes
        · intro v hv _ _
          have := mul_nonneg ha0 (Jn 0 v1 v hv); have := mul_nonneg hu0' (Jn 1 u v hv)
          have := mul_nonneg hb0 (Jdiff_nonneg E hE h1 1 b v1 v hbv1 hv)
          have := hCt0 v hv; have := hCt0' v hv
          linarith
        · intro v hv x0 x1
          have e : M.t 0 v = a := price 0 r hr v (mem_only0 E M v hv x0 x1)
          have hle : a ≤ v := by rw [← e]; exact (hI 0 v hv).2
          rw [e]
          have := mul_nonneg hu0' (Jn 1 u v hv)
          have := mul_nonneg hb0 (Jdiff_nonneg E hE h1 1 b v1 v hbv1 hv)
          have := hCt0 v hv; have := hCt0' v hv
          have := mul_nonneg ha0 (Jn 0 v1 v hv)
          rcases le_or_gt v1 v with hvv | hvv
          · rw [J_pos E 0 v1 v hvv] at *; linarith
          · rw [Ct_mid E m' v1 v (hm'le v (mem_only0 E M v hv x0 x1)) hvv]
            have := mul_nonneg hvhi0 (wp 1 v hv).le
            have : a * w E 0 v ≤ E.vhi * w E 0 v :=
              mul_le_mul_of_nonneg_right (le_trans hle hv.2) (wp 0 v hv).le
            linarith
        · intro v hv x0 x1
          have e : M.t 1 v = b := price 1 q hq v (mem_only1 E M v hv x0 x1)
          have hbv : b ≤ v := by rw [← e]; exact (hI 1 v hv).2
          rw [e]
          have := mul_nonneg hu0' (Jn 1 u v hv)
          have := hCt0 v hv; have := hCt0' v hv
          rcases le_or_gt v1 v with hvv | hvv
          · rw [J_pos E 0 v1 v hvv, J_pos E 1 b v hbv, J_pos E 1 v1 v hvv]
            have h10 := w1_lt_w0 E h4 v hv
            have s1 : b * w E 1 v ≤ b * w E 0 v := mul_le_mul_of_nonneg_left h10.le hb0
            have s2 : b * w E 0 v ≤ a * w E 0 v := mul_le_mul_of_nonneg_right hba (wp 0 v hv).le
            linarith
          · rw [J_pos E 1 b v hbv, J_neg E 1 v1 v hvv]
            have := mul_nonneg ha0 (Jn 0 v1 v hv)
            linarith
        · intro v hv x0 x1
          have hv12 := mem_both E M v hv x0 x1
          have := mul_nonneg ha0 (Jn 0 v1 v hv); have := mul_nonneg hu0' (Jn 1 u v hv)
          have := mul_nonneg hb0 (Jdiff_nonneg E hE h1 1 b v1 v hbv1 hv)
          have := hCt0 v hv; have := hCt0' v hv
          rcases le_or_gt u v with huv | huv
          · have k1 := M1 E hE h1 h2 M hB hI u v hu hv12
            have k2 := M2 E hE h1 h2 M hB hI u v r hu hr hv huv
            rw [J_pos E 0 v1 v (by linarith), J_pos E 1 b v (by linarith),
              J_pos E 1 v1 v (by linarith), J_pos E 1 u v huv, Ct_hi E m u v hmu huv,
              Ct_hi E m' v1 v hm'v1 (by linarith)]
            linarith
          · have := hsmall u hu v hv x0 x1 huv
            linarith
      have hfin := profit_le_of E hE h1 M hI
        ![a, b, -b, u, E.vhi, E.vhi, -E.vhi, -E.vhi, E.vhi, E.vhi, -E.vhi, -E.vhi]
        ![0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] ![v1, b, v1, u, m, m, u, u, m', m', v1, v1]
        (by
          have hm'hi : m' ≤ E.vhi := le_trans hm'v1 hv1V.2
          intro k; fin_cases k <;> simp <;> linarith [hv1V.2, huV.2])
        (by
          intro v hv
          have := hpt v hv
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Ct] at this ⊢
          simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
            Fin.succ_zero_eq_one, Matrix.head_cons] at ⊢
          linarith)
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, Fin.succ_zero_eq_one,
        Matrix.head_cons] at hfin
      have kl := key E hE h1 h2 h3 h4 b v1 cc hb0 hbv1 hv1V hcc
      have hT0 : a * Tl E 0 v1 ≤ cc * Tl E 0 v1 :=
        mul_le_mul_of_nonneg_right hacc (Tl_nonneg E hE h1 0 v1 hv1V.2)
      have f0 := FB0 cc (by linarith) (by linarith [hv1V.2])
      have f1 := FB1 u hu0' huV.2
      simp only [hEf, hEf']
      linarith
    · -- B1: V₁ and V₁₂ nonempty, V₂ empty
      obtain ⟨r, hr⟩ := hS1
      set a := M.t 0 r with hadef
      have ha0 : 0 ≤ a := (hI 0 r hr.1).1
      have hau : a ≤ u := le_trans (hI 0 r hr.1).2
        (MonopolyDemandUncertainty.SBSMP.lemma_2_i E hE h1 h2 M hB hI r hr u hu).le
      have hpt : ∀ v ∈ E.V, P E M v ≤ a * J E 0 a v + u * J E 1 u v + Ct E m u v := by
        apply pointwise_of_classes
        · intro v hv _ _
          have := mul_nonneg ha0 (Jn 0 a v hv); have := mul_nonneg hu0' (Jn 1 u v hv)
          have := hCt0 v hv
          linarith
        · intro v hv x0 x1
          have e : M.t 0 v = a := price 0 r hr v (mem_only0 E M v hv x0 x1)
          have hle : a ≤ v := by rw [← e]; exact (hI 0 v hv).2
          rw [e, J_pos E 0 a v hle]
          have := mul_nonneg hu0' (Jn 1 u v hv); have := hCt0 v hv
          linarith
        · intro v hv x0 x1; exact absurd ⟨v, mem_only1 E M v hv x0 x1⟩ hS2
        · intro v hv x0 x1
          have hv12 := mem_both E M v hv x0 x1
          have := mul_nonneg ha0 (Jn 0 a v hv); have := mul_nonneg hu0' (Jn 1 u v hv)
          have := hCt0 v hv
          rcases le_or_gt u v with huv | huv
          · have k1 := M1 E hE h1 h2 M hB hI u v hu hv12
            have k2 := M2 E hE h1 h2 M hB hI u v r hu hr hv huv
            rw [J_pos E 0 a v (by linarith), J_pos E 1 u v huv, Ct_hi E m u v hmu huv]
            linarith
          · have := hsmall u hu v hv x0 x1 huv
            linarith
      have hfin := profit_le_of E hE h1 M hI ![a, u, E.vhi, E.vhi, -E.vhi, -E.vhi]
        ![0, 1, 0, 1, 0, 1] ![a, u, m, m, u, u]
        (by intro k; fin_cases k <;> simp <;> linarith [huV.2])
        (by
          intro v hv
          have := hpt v hv
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Ct] at this ⊢
          simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
            Fin.succ_zero_eq_one, Matrix.head_cons] at ⊢
          linarith)
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, Fin.succ_zero_eq_one,
        Matrix.head_cons] at hfin
      have f0 := FB0 a ha0 (by linarith [huV.2])
      have f1 := FB1 u hu0' huV.2
      simp only [hEf]
      linarith
    · -- B2: V₂ and V₁₂ nonempty, V₁ empty
      obtain ⟨q, hq⟩ := hS2
      set b := M.t 1 q with hbdef
      have hb0 : 0 ≤ b := (hI 1 q hq.1).1
      have hbu : b ≤ u := M4 E hE h1 h2 M hB hI u q hu hq
      have w0u := wp 0 u huV
      set cc := u - (u - b) * (w E 1 u / w E 0 u) with hccdef
      have hcc : cc * w E 0 u = u * w E 0 u - (u - b) * w E 1 u := by
        rw [hccdef]; field_simp
      have hccu : cc ≤ u := by
        have : 0 ≤ (u - b) * (w E 1 u / w E 0 u) :=
          mul_nonneg (by linarith) (div_nonneg (wp 1 u huV).le w0u.le)
        linarith
      have hbcc : b ≤ cc := by
        have h10 := w1_lt_w0 E h4 u huV
        have : (cc - b) * w E 0 u = (u - b) * (w E 0 u - w E 1 u) := by linarith
        have : 0 ≤ (cc - b) * w E 0 u := by rw [this]; apply mul_nonneg <;> linarith
        have := (mul_nonneg_iff_of_pos_right w0u).mp this
        linarith
      have hcc0 : 0 ≤ cc := by linarith
      have hpt : ∀ v ∈ E.V, P E M v ≤ cc * J E 0 u v + u * J E 1 u v +
          b * (J E 1 b v - J E 1 u v) + Ct E m u v := by
        apply pointwise_of_classes
        · intro v hv _ _
          have := mul_nonneg hcc0 (Jn 0 u v hv); have := mul_nonneg hu0' (Jn 1 u v hv)
          have := hCt0 v hv
          have := mul_nonneg hb0 (Jdiff_nonneg E hE h1 1 b u v hbu hv)
          linarith
        · intro v hv x0 x1; exact absurd ⟨v, mem_only0 E M v hv x0 x1⟩ hS1
        · intro v hv x0 x1
          have e : M.t 1 v = b := price 1 q hq v (mem_only1 E M v hv x0 x1)
          have hbv : b ≤ v := by rw [← e]; exact (hI 1 v hv).2
          rw [e]
          have := hCt0 v hv
          rcases le_or_gt u v with huv | huv
          · rw [J_pos E 0 u v huv, J_pos E 1 u v huv, J_pos E 1 b v hbv]
            have := mul_nonneg hcc0 (wp 0 v hv).le
            have := mul_le_mul_of_nonneg_right hbu (wp 1 v hv).le
            linarith
          · rw [J_neg E 0 u v huv, J_neg E 1 u v huv, J_pos E 1 b v hbv]
            linarith
        · intro v hv x0 x1
          have hv12 := mem_both E M v hv x0 x1
          have := mul_nonneg hcc0 (Jn 0 u v hv); have := mul_nonneg hu0' (Jn 1 u v hv)
          have := hCt0 v hv
          have := mul_nonneg hb0 (Jdiff_nonneg E hE h1 1 b u v hbu hv)
          rcases le_or_gt u v with huv | huv
          · have k1 := M1 E hE h1 h2 M hB hI u v hu hv12
            have k3 := M3 E hE h1 h2 M hB hI u v q cc hu hq hv huv hcc
            rw [J_pos E 0 u v huv, J_pos E 1 u v huv, J_pos E 1 b v (by linarith),
              Ct_hi E m u v hmu huv]
            linarith
          · have := hsmall u hu v hv x0 x1 huv
            linarith
      have hfin := profit_le_of E hE h1 M hI ![cc, u, b, -b, E.vhi, E.vhi, -E.vhi, -E.vhi]
        ![0, 1, 1, 1, 0, 1, 0, 1] ![u, u, b, u, m, m, u, u]
        (by intro k; fin_cases k <;> simp <;> linarith [huV.2])
        (by
          intro v hv
          have := hpt v hv
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Ct] at this ⊢
          simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
            Fin.succ_zero_eq_one, Matrix.head_cons] at ⊢
          linarith)
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, Fin.succ_zero_eq_one,
        Matrix.head_cons] at hfin
      have kl := key E hE h1 h2 h3 h4 b u cc hb0 hbu huV hcc
      have f0 := FB0 cc (by linarith) (by linarith [huV.2])
      have f1 := FB1 u hu0' huV.2
      simp only [hEf]
      linarith
    · -- B0: only V₁₂ nonempty
      have hpt : ∀ v ∈ E.V, P E M v ≤ u * J E 0 u v + u * J E 1 u v + Ct E m u v := by
        apply pointwise_of_classes
        · intro v hv _ _
          have := mul_nonneg hu0' (Jn 0 u v hv); have := mul_nonneg hu0' (Jn 1 u v hv)
          have := hCt0 v hv
          linarith
        · intro v hv x0 x1; exact absurd ⟨v, mem_only0 E M v hv x0 x1⟩ hS1
        · intro v hv x0 x1; exact absurd ⟨v, mem_only1 E M v hv x0 x1⟩ hS2
        · intro v hv x0 x1
          have hv12 := mem_both E M v hv x0 x1
          have := Jn 0 u v hv; have := Jn 1 u v hv; have := hCt0 v hv
          rcases le_or_gt u v with huv | huv
          · have k1 := M1 E hE h1 h2 M hB hI u v hu hv12
            rw [J_pos E 0 u v huv, J_pos E 1 u v huv, Ct_hi E m u v hmu huv]
            have := wp 0 v hv; have := wp 1 v hv
            have : M.t 0 u * w E 0 v ≤ u * w E 0 v :=
              mul_le_mul_of_nonneg_right t0u.2 (wp 0 v hv).le
            have : M.t 1 u * w E 1 v ≤ u * w E 1 v :=
              mul_le_mul_of_nonneg_right t1u.2 (wp 1 v hv).le
            linarith
          · have := hsmall u hu v hv x0 x1 huv
            have := mul_nonneg hu0' (Jn 0 u v hv); have := mul_nonneg hu0' (Jn 1 u v hv)
            linarith
      have hfin := profit_le_of E hE h1 M hI ![u, u, E.vhi, E.vhi, -E.vhi, -E.vhi]
        ![0, 1, 0, 1, 0, 1] ![u, u, m, m, u, u]
        (by intro k; fin_cases k <;> simp <;> linarith [huV.2])
        (by
          intro v hv
          have := hpt v hv
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Ct] at this ⊢
          simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
            Fin.succ_zero_eq_one, Matrix.head_cons] at ⊢
          linarith)
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_one, Fin.succ_zero_eq_one,
        Matrix.head_cons] at hfin
      have f0 := FB0 u hu0' huV.2
      have f1 := FB1 u hu0' huV.2
      simp only [hEf]
      linarith
