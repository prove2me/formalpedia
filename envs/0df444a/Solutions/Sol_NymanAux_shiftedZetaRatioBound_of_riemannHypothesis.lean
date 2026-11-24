-- Prove2me | solution 1 for NymanAux.shiftedZetaRatioBound_of_riemannHypothesis
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T01:51:19.226463+00:00
-- url     : https://prove2.me/submissions/ea8a51eb-8ed9-4618-8d89-33df2453c9c7

import Mathlib
import Theorems.Thm_Zeta23_StirlingVert_re_digamma_stirling
import Theorems.Thm_XiPairingPublished_concrete_upper_paired_product
import Theorems.Thm_XiHadamardPortPublished_concrete_xi_no_real_zeros
import Definitions.Def_NymanBeurling_DampedMellinFrontiers
namespace NymanAux
open Complex

lemma gamma_hasDerivAt_line (y u : ℝ) (hu : 0 < 1/4 + u) :
    HasDerivAt (fun v : ℝ => Complex.Gamma (((1/4 + v : ℝ) : ℂ) + I * y))
      (deriv Complex.Gamma (((1/4 + u : ℝ) : ℂ) + I * y)) u := by
  have hz : ∀ m : ℕ, (((1/4 + u : ℝ) : ℂ) + I * y) ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := m.cast_nonneg
    linarith
  have hG := (Complex.differentiableAt_Gamma _ hz).hasDerivAt
  have hl : HasDerivAt (fun w : ℂ => ((1/4 : ℂ) + w + I * y)) 1 (u : ℂ) := by
    simpa using ((hasDerivAt_id (u : ℂ)).const_add (1/4 : ℂ)).add_const (I * y)
  have hc : ((1/4 : ℂ) + (u : ℂ) + I * y) = (((1/4 + u : ℝ) : ℂ) + I * y) := by push_cast; ring
  rw [← hc] at hG
  have h2 := (hG.comp (u : ℂ) hl).comp_ofReal
  rw [mul_one, hc] at h2
  convert h2 using 1
  funext v; simp only [Function.comp]; push_cast; ring_nf

lemma gamma_line_ne (y u : ℝ) (hu : 0 < 1/4 + u) :
    Complex.Gamma (((1/4 + u : ℝ) : ℂ) + I * y) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := m.cast_nonneg
  linarith

/-- derivative of `log ‖Γ‖²` along a horizontal line is `2 Re ψ`. -/
lemma log_normSq_gamma_hasDerivAt (y u : ℝ) (hu : 0 < 1/4 + u) :
    HasDerivAt (fun v : ℝ => Real.log (‖Complex.Gamma (((1/4 + v : ℝ) : ℂ) + I * y)‖ ^ 2))
      (2 * (Complex.digamma (((1/4 + u : ℝ) : ℂ) + I * y)).re) u := by
  set z := (((1/4 + u : ℝ) : ℂ) + I * y)
  have hne := gamma_line_ne y u hu
  have h1 := (gamma_hasDerivAt_line y u hu).norm_sq
  have hpos : (‖Complex.Gamma z‖ ^ 2) ≠ 0 := by positivity
  have h2 := h1.log hpos
  convert h2 using 1
  rw [Complex.inner, Complex.digamma_def, logDeriv_apply]
  set G := Complex.Gamma z
  set D := deriv Complex.Gamma z
  have hG : G ≠ 0 := hne
  have hc : (starRingEnd ℂ) G ≠ 0 := by simpa using hG
  have : D / G = D * (starRingEnd ℂ) G / ((Complex.normSq G : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    field_simp
  rw [this, Complex.div_ofReal_re, Complex.normSq_eq_norm_sq]; ring

lemma gamma_ratio_large (y d : ℝ) (hy : 1/2 ≤ |y|) (hd0 : 0 ≤ d) (hd1 : d ≤ 1/4) :
    ‖Complex.Gamma (((1/4 + d : ℝ) : ℂ) + I * y)‖ ≤
      Real.exp 4 * (1 + |y|) ^ d * ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y)‖ := by
  rcases hd0.eq_or_lt with h | h
  · subst h
    rw [Real.rpow_zero, mul_one]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by norm_num))
  set g := fun v : ℝ => Real.log (‖Complex.Gamma (((1/4 + v : ℝ) : ℂ) + I * y)‖ ^ 2)
  have hcont : ContinuousOn g (Set.Icc 0 d) := by
    intro v hv
    exact (log_normSq_gamma_hasDerivAt y v (by linarith [hv.1])).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g
    (fun u => 2 * (Complex.digamma (((1/4 + u : ℝ) : ℂ) + I * y)).re) h hcont
    (fun v hv => log_normSq_gamma_hasDerivAt y v (by linarith [hv.1]))
  have hst := Zeta23.StirlingVert.re_digamma_stirling (a := 1/4 + c) (by linarith [hc.1])
    (by linarith [hc.2]) hy
  have hy2 : (4:ℝ) / y ^ 2 ≤ 16 := by
    have : (1/4 : ℝ) ≤ y ^ 2 := by
      have := sq_abs y; nlinarith [abs_nonneg y]
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hlog : (1/2) * Real.log ((1/4 + c) ^ 2 + y ^ 2) ≤ Real.log (1 + |y|) := by
    have hp : 0 < (1/4 + c) ^ 2 + y ^ 2 := by nlinarith [hc.1]
    have : (1/4 + c) ^ 2 + y ^ 2 ≤ (1 + |y|) ^ 2 := by
      have := sq_abs y; nlinarith [abs_nonneg y, hc.1, hc.2]
    have := Real.log_le_log hp this
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hre : (Complex.digamma (((1/4 + c : ℝ) : ℂ) + I * y)).re ≤ Real.log (1 + |y|) + 16 := by
    have := (abs_le.mp hst).2; linarith
  have hgd : g d - g 0 ≤ 2 * d * (Real.log (1 + |y|) + 16) := by
    have : g d - g 0 = 2 * (Complex.digamma (((1/4 + c : ℝ) : ℂ) + I * y)).re * d := by
      rw [hcd]; field_simp; ring
    rw [this]; nlinarith
  set A := ‖Complex.Gamma (((1/4 + d : ℝ) : ℂ) + I * y)‖
  set B := ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y)‖
  have hA : 0 < A := norm_pos_iff.mpr (gamma_line_ne y d (by linarith))
  have hB : 0 < B := norm_pos_iff.mpr (gamma_line_ne y 0 (by norm_num))
  have key : Real.log A ≤ Real.log B + d * (Real.log (1 + |y|) + 16) := by
    have e1 : g d = 2 * Real.log A := by
      change Real.log (A^2) = _; rw [Real.log_pow]; norm_num
    have e2 : g 0 = 2 * Real.log B := by
      change Real.log (B^2) = _; rw [Real.log_pow]; norm_num
    rw [e1, e2] at hgd; linarith
  have hy0 : 0 < 1 + |y| := by positivity
  have : A ≤ B * Real.exp (d * (Real.log (1 + |y|) + 16)) := by
    rw [← Real.log_le_log_iff hA (by positivity), Real.log_mul hB.ne' (by positivity),
      Real.log_exp]
    exact key
  calc A ≤ B * Real.exp (d * (Real.log (1 + |y|) + 16)) := this
    _ = Real.exp (16 * d) * (1 + |y|) ^ d * B := by
      rw [Real.rpow_def_of_pos hy0, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp 4 * (1 + |y|) ^ d * B := by
      gcongr; linarith

lemma gamma_ratio_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y d : ℝ, 0 ≤ d → d ≤ 1/4 →
    ‖Complex.Gamma (((1/4 + d : ℝ) : ℂ) + I * y)‖ ≤
      C * (1 + |y|) ^ d * ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y)‖ := by
  -- compactness for small |y|
  have hK : IsCompact (Set.Icc (0:ℝ) (1/4) ×ˢ Set.Icc (-1/2 : ℝ) (1/2)) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖Complex.Gamma (((1/4 + p.1 : ℝ) : ℂ) + I * p.2)‖)
      (Set.Icc (0:ℝ) (1/4) ×ˢ Set.Icc (-1/2 : ℝ) (1/2)) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.norm
    have hz : ∀ m : ℕ, (((1/4 + p.1 : ℝ) : ℂ) + I * p.2) ≠ -m := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ m := m.cast_nonneg
      linarith [hp.1.1]
    exact ContinuousAt.comp (g := Complex.Gamma)
      (Complex.differentiableAt_Gamma _ hz).continuousAt (by fun_prop)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  have hK2 : IsCompact (Set.Icc (-1/2 : ℝ) (1/2)) := isCompact_Icc
  have hcont2 : ContinuousOn (fun y : ℝ => ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y)‖)
      (Set.Icc (-1/2 : ℝ) (1/2)) := by
    intro y _
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.norm
    have hz : ∀ m : ℕ, (((1/4 + 0 : ℝ) : ℂ) + I * y) ≠ -m := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ m := m.cast_nonneg
      linarith
    exact ContinuousAt.comp (g := Complex.Gamma)
      (Complex.differentiableAt_Gamma _ hz).continuousAt (by fun_prop)
  obtain ⟨y0, hy0, hmin⟩ := hK2.exists_isMinOn ⟨0, by norm_num, by norm_num⟩ hcont2
  set m := ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y0)‖
  have hm : 0 < m := norm_pos_iff.mpr (gamma_line_ne y0 0 (by norm_num))
  refine ⟨max (Real.exp 4) (|M| / m), by positivity, ?_⟩
  intro y d hd0 hd1
  have hB0 : 0 ≤ ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y)‖ := norm_nonneg _
  have hpow : 1 ≤ (1 + |y|) ^ d := Real.one_le_rpow (by linarith [abs_nonneg y]) hd0
  by_cases hy : 1/2 ≤ |y|
  · calc _ ≤ Real.exp 4 * (1 + |y|) ^ d * ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y)‖ :=
          gamma_ratio_large y d hy hd0 hd1
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push Not at hy
    have hyI : y ∈ Set.Icc (-1/2 : ℝ) (1/2) := by
      constructor <;> linarith [abs_lt.mp hy]
    have h1 := hM (d, y) ⟨⟨hd0, hd1⟩, hyI⟩
    simp only [norm_norm] at h1
    have h2 : m ≤ ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y)‖ := hmin hyI
    calc ‖Complex.Gamma (((1/4 + d : ℝ) : ℂ) + I * y)‖ ≤ |M| := h1.trans (le_abs_self M)
      _ = (|M| / m) * m := by field_simp
      _ ≤ max (Real.exp 4) (|M| / m) * 1 * ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + I * y)‖ := by
          rw [mul_one]; gcongr; exact le_max_right _ _
      _ ≤ _ := by gcongr


section XiPart
open Filter Topology

/-- `Λ(s) ≠ 0` for `Re s ≥ 1`, `s ≠ 1`. -/
lemma completed_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

noncomputable def xiM (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

/-- Under RH, zeros of `xiM` lie on the critical line. -/
lemma xiM_zero_re (hRH : RiemannHypothesis) {s : ℂ} (hx' : xiM s = 0) : s.re = 1/2 := by
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    unfold xiM at hx'; linear_combination 2 * hx'
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    linear_combination (-1 : ℂ) * hx
  rcases le_or_gt 1 s.re with h | h
  · exact absurd hΛ (completed_ne_zero_of_one_le_re h hs1)
  rcases le_or_gt s.re 0 with h' | h'
  · have : 1 ≤ (1 - s).re := by simp; linarith
    refine absurd ?_ (completed_ne_zero_of_one_le_re this ?_)
    · rw [completedRiemannZeta_one_sub]; exact hΛ
    · intro h2; apply hs0; linear_combination -h2
  have hζ : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  apply hRH s hζ
  · rintro ⟨n, hn⟩
    rw [hn] at h'
    simp at h'
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hs1

noncomputable def FP (z : ℂ) : ℂ :=
  ((z + 1/2) * ((z + 1/2) - 1) * completedRiemannZeta₀ (z + 1/2) + 1) / 2

lemma FP_eq (z : ℂ) : FP z = xiM (z + 1/2) := by
  unfold FP xiM; ring

lemma FP_ne_zero (hRH : RiemannHypothesis) {w : ℂ} (hw : w.re ≠ 0) : FP w ≠ 0 := by
  rw [FP_eq]
  intro h
  have := xiM_zero_re hRH h
  simp at this
  exact hw this

lemma FP_zero_ne : FP 0 ≠ 0 := by
  have := XiHadamardPortPublished.concrete_xi_no_real_zeros (1/2 : ℝ)
  rw [FP_eq, xiM]
  simpa using this

lemma xiM_two : xiM 2 = (Real.pi : ℂ) / 6 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    rw [Complex.Gammaℝ_def]
    norm_num [Complex.cpow_neg_one]
  have h2 : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
    have := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
    rw [riemannZeta_two, hG, div_inv_eq_mul] at this
    have h3 : completedRiemannZeta 2 * Real.pi = (Real.pi : ℂ) / 6 * Real.pi := by
      rw [← this]; ring
    exact mul_right_cancel₀ hpi h3
  have h0 := completedRiemannZeta_eq 2
  rw [h2] at h0
  unfold xiM
  have : completedRiemannZeta₀ 2 = (Real.pi : ℂ) / 6 + 1/2 + 1/(1-2) := by
    linear_combination -h0
  rw [this]; norm_num; ring

lemma factor_lt {a wa wb : ℂ} (hre : a.re = 0) (hpos : 0 < a.im)
    (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖1 + wa ^ 2 / (-a ^ 2)‖ < ‖1 + wb ^ 2 / (-a ^ 2)‖ := by
  have ha : -a ^ 2 = ((a.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two, hre]
  have hc : (0:ℝ) < a.im ^ 2 := by positivity
  have hc' : ((a.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrw : ∀ w : ℂ, 1 + w ^ 2 / (-a ^ 2) = (((a.im ^ 2 : ℝ) : ℂ) + w ^ 2) / ((a.im ^ 2 : ℝ) : ℂ) := by
    intro w; rw [ha]; field_simp
  rw [hrw, hrw, norm_div, norm_div]
  apply div_lt_div_of_pos_right _ (by simpa using hc)
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_re, Complex.mul_im, zero_add]
  rw [him] at *
  have hX' : wa.re * wa.re < wb.re * wb.re := by nlinarith
  have hpos2 : 0 < 2 * (a.im * a.im) + 2 * (wb.im * wb.im) + wa.re * wa.re + wb.re * wb.re := by
    nlinarith [mul_self_nonneg wb.im, mul_self_nonneg wa.re, mul_self_nonneg wb.re]
  nlinarith [mul_pos (sub_pos.mpr hX') hpos2]

lemma zero_re_of_order (hRH : RiemannHypothesis) {a : ℂ} (h : analyticOrderNatAt FP a ≠ 0) : a.re = 0 := by
  have h1 : analyticOrderAt FP a ≠ 0 := by
    intro h0; apply h; simp [analyticOrderNatAt, h0]
  have h2 := (analyticOrderAt_ne_zero.mp h1).2
  rw [FP_eq] at h2
  have := xiM_zero_re hRH h2
  simpa using this

lemma main_lt (hRH : RiemannHypothesis) {wa wb : ℂ} (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖FP wa‖ < ‖FP wb‖ := by
  let U : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt FP z.val)
  have key : ∀ w : ℂ, Multipliable (fun p : U => 1+w^2/(-p.1.val^2)) ∧
      FP w / FP 0 = ∏' p : U, (1+w^2/(-p.1.val^2)) :=
    XiPairingPublished.concrete_upper_paired_product
  have h0 := FP_zero_ne
  have hwb : wb.re ≠ 0 := by
    intro h; rw [h] at hX; nlinarith [sq_nonneg wa.re]
  have hFb := FP_ne_zero hRH hwb
  have hP : ∀ w, FP w = FP 0 * ∏' p : U, (1+w^2/(-p.1.val^2)) := by
    intro w; rw [← (key w).2]; field_simp
  -- nonempty
  have hne : Nonempty U := by
    by_contra hU
    rw [not_nonempty_iff] at hU
    have hc : ∀ w, FP w = FP 0 := by intro w; rw [hP w, tprod_empty, mul_one]
    have e1 : FP (-1/2) = 1/2 := by unfold FP; ring_nf
    have e2 : FP (3/2) = (Real.pi : ℂ) / 6 := by
      rw [FP_eq]; norm_num; exact xiM_two
    have := (hc (3/2)).trans (hc (-1/2)).symm
    rw [e1, e2] at this
    have h3 : (Real.pi : ℂ) = 3 := by linear_combination 6 * this
    have : Real.pi = 3 := by exact_mod_cast h3
    linarith [Real.pi_gt_three]
  obtain ⟨p0⟩ := hne
  set g : U → ℂ → ℂ := fun p w => 1+w^2/(-p.1.val^2) with hg
  have hgle : ∀ p : U, ‖g p wa‖ < ‖g p wb‖ := by
    intro p
    have hord : analyticOrderNatAt FP p.1.val ≠ 0 := by
      intro h; have := p.2.isLt; omega
    exact factor_lt (zero_re_of_order hRH hord) p.1.2 him hX
  set Pa := ‖∏' p : U, g p wa‖
  set Pb := ‖∏' p : U, g p wb‖
  have hTa := (key wa).1.hasProd.norm
  have hTb := (key wb).1.hasProd.norm
  have hlim : ‖g p0 wb‖ * Pa ≤ ‖g p0 wa‖ * Pb := by
    apply le_of_tendsto_of_tendsto (hTa.const_mul _) (hTb.const_mul _)
    filter_upwards [Filter.eventually_ge_atTop {p0}] with S hS
    have hp0 : p0 ∈ S := Finset.singleton_subset_iff.mp hS
    rw [← Finset.mul_prod_erase S _ hp0, ← Finset.mul_prod_erase S (fun p => ‖g p wb‖) hp0]
    have : ∏ x ∈ S.erase p0, ‖g x wa‖ ≤ ∏ x ∈ S.erase p0, ‖g x wb‖ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (hgle i).le)
    have hn : 0 ≤ ‖g p0 wb‖ * ‖g p0 wa‖ := by positivity
    calc ‖g p0 wb‖ * (‖g p0 wa‖ * ∏ x ∈ S.erase p0, ‖g x wa‖)
        = (‖g p0 wb‖ * ‖g p0 wa‖) * ∏ x ∈ S.erase p0, ‖g x wa‖ := by ring
      _ ≤ (‖g p0 wb‖ * ‖g p0 wa‖) * ∏ x ∈ S.erase p0, ‖g x wb‖ :=
          mul_le_mul_of_nonneg_left this hn
      _ = ‖g p0 wa‖ * (‖g p0 wb‖ * ∏ x ∈ S.erase p0, ‖g x wb‖) := by ring
  have hna : ‖FP wa‖ = ‖FP 0‖ * Pa := by rw [hP wa, norm_mul]
  have hnb : ‖FP wb‖ = ‖FP 0‖ * Pb := by rw [hP wb, norm_mul]
  have hF0 : 0 < ‖FP 0‖ := norm_pos_iff.mpr h0
  rw [hna, hnb]
  apply mul_lt_mul_of_pos_left _ hF0
  have hPb : 0 < Pb := by
    have : 0 < ‖FP wb‖ := norm_pos_iff.mpr hFb
    rw [hnb] at this
    exact pos_of_mul_pos_right this hF0.le
  rcases (norm_nonneg (∏' p : U, g p wa)).eq_or_lt with hPa | hPa
  · change 0 = Pa at hPa
    rw [← hPa]; exact hPb
  change 0 < Pa at hPa
  have hA := norm_nonneg (g p0 wa)
  have hAB := hgle p0
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon hA, mul_lt_mul_of_pos_right hAB hPa]


end XiPart

lemma zeta_eq_xi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannZeta s = 2 * xiM s / (s * (s - 1) * Complex.Gammaℝ s) := by
  rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  unfold xiM
  have hs1' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  by_cases hG : Complex.Gammaℝ s = 0
  · simp [hG]
  field_simp
  ring

lemma norm_Gammaℝ (s : ℂ) :
    ‖Complex.Gammaℝ s‖ = Real.pi ^ (-s.re / 2) * ‖Complex.Gamma (s / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp [Complex.neg_re]

end NymanAux

open NymanAux in
theorem NymanAux.shiftedZetaRatioBound_of_RH (hRH : RiemannHypothesis) :
    NymanBeurling.ShiftedZetaRatioBound := by
  obtain ⟨C, hC0, hC⟩ := gamma_ratio_bound
  refine ⟨4 * C, by positivity, ?_⟩
  intro ε hε hε2 t
  set s : ℂ := (1/2 : ℂ) - (t : ℂ) * Complex.I with hs
  set s' : ℂ := s + (ε : ℂ) with hs'
  have hsre : s.re = 1/2 := by simp [s]
  have hsim : s.im = -t := by simp [s]
  have hs're : s'.re = 1/2 + ε := by simp [s', s]
  have hs'im : s'.im = -t := by simp [s', s]
  by_cases hz : riemannZeta s' = 0
  · rw [hz, div_zero, norm_zero]; positivity
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre; norm_num at hsre
  have hs'0 : s' ≠ 0 := fun h => by rw [h] at hs're; simp at hs're; linarith
  have hs'1 : s' ≠ 1 := fun h => by rw [h] at hs're; simp at hs're; linarith
  have hxi : ‖xiM s‖ ≤ ‖xiM s'‖ := by
    have h := main_lt hRH (wa := s - 1/2) (wb := s' - 1/2) (by simp [hsim, hs'im])
      (by simp [hsre, hs're]; nlinarith)
    rw [FP_eq, FP_eq] at h
    simp only [sub_add_cancel] at h
    exact h.le
  have hz' := hz
  rw [zeta_eq_xi s' hs'0 hs'1] at hz'
  have hX' : 0 < ‖xiM s'‖ := by
    apply norm_pos_iff.mpr; intro h; apply hz'; rw [h]; simp
  have hG : ∀ w : ℂ, 0 < w.re → 0 < ‖Complex.Gammaℝ w‖ := fun w hw =>
    norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos hw)
  have hgs : 0 < ‖Complex.Gammaℝ s‖ := hG s (by rw [hsre]; norm_num)
  have hgs' : 0 < ‖Complex.Gammaℝ s'‖ := hG s' (by rw [hs're]; linarith)
  -- gamma comparison
  have hgam : ‖Complex.Gammaℝ s'‖ ≤ C * (1 + |t|) ^ (ε / 2) * ‖Complex.Gammaℝ s‖ := by
    rw [norm_Gammaℝ, norm_Gammaℝ, hsre, hs're]
    have e1 : s / 2 = (((1/4 + 0 : ℝ) : ℂ) + Complex.I * ((-t/2 : ℝ) : ℂ)) := by
      simp only [s]; push_cast; ring
    have e2 : s' / 2 = (((1/4 + ε/2 : ℝ) : ℂ) + Complex.I * ((-t/2 : ℝ) : ℂ)) := by
      simp only [s', s]; push_cast; ring
    rw [e1, e2]
    have h1 := hC (-t/2) (ε/2) (by linarith) (by linarith)
    have h2 : (1 + |(-t/2)|) ^ (ε/2) ≤ (1 + |t|) ^ (ε/2) := by
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      rw [abs_div, abs_neg]; norm_num; try linarith [abs_nonneg t]
    have h3 : Real.pi ^ (-(1/2 + ε) / 2) ≤ Real.pi ^ (-(1/2 : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]); linarith
    set A := ‖Complex.Gamma (((1/4 + ε/2 : ℝ) : ℂ) + Complex.I * ((-t/2 : ℝ) : ℂ))‖
    set B := ‖Complex.Gamma (((1/4 + 0 : ℝ) : ℂ) + Complex.I * ((-t/2 : ℝ) : ℂ))‖
    have hA : 0 ≤ A := norm_nonneg _
    have hB : 0 ≤ B := norm_nonneg _
    have hp : 0 ≤ Real.pi ^ (-(1/2 + ε) / 2) := by positivity
    have hp' : 0 ≤ Real.pi ^ (-(1/2 : ℝ) / 2) := by positivity
    have hq : 0 ≤ (1 + |t|) ^ (ε/2) := by positivity
    calc Real.pi ^ (-(1/2 + ε) / 2) * A ≤ Real.pi ^ (-(1/2 : ℝ) / 2) * (C * (1 + |t|) ^ (ε / 2) * B) := by
          apply mul_le_mul h3 _ hA hp'
          calc A ≤ C * (1 + |(-t/2)|) ^ (ε/2) * B := h1
            _ ≤ C * (1 + |t|) ^ (ε / 2) * B := by gcongr
      _ = _ := by ring
  have hsa : ‖s'‖ ≤ 2 * ‖s‖ := by
    have h1 : ‖s'‖ ≤ ‖s‖ + ε := by
      calc ‖s'‖ ≤ ‖s‖ + ‖(ε : ℂ)‖ := norm_add_le _ _
        _ = ‖s‖ + ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    have h2 : (1/2 : ℝ) ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s; rw [hsre] at this; norm_num at this; linarith
    linarith
  have hsb : ‖s' - 1‖ ≤ 2 * ‖s - 1‖ := by
    have h1 : ‖s' - 1‖ ≤ ‖s - 1‖ + ε := by
      calc ‖s' - 1‖ = ‖(s - 1) + (ε : ℂ)‖ := by congr 1; simp only [s']; ring
        _ ≤ ‖s - 1‖ + ‖(ε : ℂ)‖ := norm_add_le _ _
        _ = ‖s - 1‖ + ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    have h2 : (1/2 : ℝ) ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1); rw [Complex.sub_re, hsre] at this
      norm_num at this; linarith
    linarith
  have hna : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hnb : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hna' : 0 < ‖s'‖ := norm_pos_iff.mpr hs'0
  have hnb' : 0 < ‖s' - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs'1)
  rw [zeta_eq_xi s hs0 hs1, zeta_eq_xi s' hs'0 hs'1, norm_div, norm_div, norm_div,
    norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_two]  
  rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
  set X := ‖xiM s‖
  set X' := ‖xiM s'‖
  set P := (1 + |t|) ^ (ε / 2)
  have hP : 0 ≤ P := by positivity
  have hX : 0 ≤ X := norm_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have key : X * (‖s'‖ * ‖s' - 1‖ * ‖Complex.Gammaℝ s'‖) ≤
      X' * ((2 * ‖s‖) * (2 * ‖s - 1‖) * (C * P * ‖Complex.Gammaℝ s‖)) := by
    apply mul_le_mul hxi _ (by positivity) hX'.le
    apply mul_le_mul (mul_le_mul hsa hsb (by positivity) (by positivity)) hgam (by positivity)
      (by positivity)
  rw [norm_mul s'] 
  nlinarith [key]

theorem solution (hRH : RiemannHypothesis) : NymanBeurling.ShiftedZetaRatioBound :=
  NymanAux.shiftedZetaRatioBound_of_RH hRH
