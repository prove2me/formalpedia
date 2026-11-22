-- Prove2me | solution 1 for NymanBeurling.shifted_zeta_critical_line_ratio_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T18:10:31.702762+00:00
-- url     : https://prove2.me/submissions/c763e450-0a13-472f-b3d5-820a41c84ca9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_NymanBeurling_DampedMellinFrontiers
import Theorems.Thm_EtaQBridgePublished_concrete_xi_bridge
import Theorems.Thm_XiPairingPublished_concrete_upper_paired_product
import Theorems.Thm_XiPairingPublished_concrete_xi_no_real_zeros
import Theorems.Thm_Zeta23_StirlingVert_digamma_stirling
import Theorems.Thm_ZeroFreeBridge_logDeriv_gammaR
import Theorems.Thm_rh_zeta_zero_free_right_half
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Complex Set
open scoped Topology

private noncomputable def xi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

private theorem xi_factor {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    xi s = s * (s - 1) * Gammaℝ s * riemannZeta s / 2 := by
  simpa [xi, add_comm] using EtaQBridgePublished.concrete_xi_bridge.2.2 s hs h1

private theorem xi_ne_zero_right (s : ℂ) (hs : 1 / 2 < s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    norm_num [xi]
  have h0 : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by contrapose! h0; simp [h0]
  have hz : riemannZeta s ≠ 0 := by
    by_cases hr : s.re < 1
    · exact rh_zeta_zero_free_right_half s hs hr
    · exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hr)
  rw [xi_factor h0 h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr h1))
    (Gammaℝ_ne_zero_of_re_pos h0)) hz) (by norm_num)

private theorem norm_le_of_re_sq_le {z w : ℂ}
    (hre : z.re * z.re ≤ w.re * w.re) (him : z.im = w.im) : ‖z‖ ≤ ‖w‖ := by
  simp only [Complex.norm_def, Complex.normSq_apply, him]
  exact Real.sqrt_le_sqrt (add_le_add hre le_rfl)

private theorem xi_norm_increases {s : ℂ} (hs : s.re = 1 / 2) (ε : ℝ) :
    ‖xi s‖ ≤ ‖xi (s + (ε : ℂ))‖ := by
  let F : ℂ → ℂ := fun w => xi (w + 1 / 2)
  let U : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt F z.val)
  let w := s - (1 / 2 : ℂ)
  let factor (z : ℂ) (p : U) : ℂ := 1 + z ^ 2 / (-p.1.val ^ 2)
  have hcenter : F 0 ≠ 0 := by
    simpa [F, xi] using XiPairingPublished.concrete_xi_no_real_zeros (1 / 2)
  have hzero (p : U) : p.1.val.re = 0 := by
    have hp : F p.1.val = 0 := by
      apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
      exact Nat.ne_of_gt (Nat.zero_lt_of_lt p.2.isLt)
    have heven : F (-p.1.val) = F p.1.val := by
      simpa [F, xi, sub_eq_add_neg, add_comm] using
        EtaQBridgePublished.concrete_xi_bridge.2.1 p.1.val
    rcases lt_trichotomy p.1.val.re 0 with h | h | h
    · have hr : 1 / 2 < (-p.1.val + (1 / 2 : ℂ)).re := by
        simp only [add_re, neg_re, div_ofNat_re, one_re]
        linarith
      exact False.elim (xi_ne_zero_right _ hr (heven.trans hp))
    · exact h
    · have hr : 1 / 2 < (p.1.val + (1 / 2 : ℂ)).re := by
        simp only [add_re, div_ofNat_re, one_re]
        linarith
      exact False.elim (xi_ne_zero_right _ hr hp)
  have hw : w.re = 0 := by simp [w, hs]
  have hfactor (p : U) : ‖factor w p‖ ≤ ‖factor (w + (ε : ℂ)) p‖ := by
    let a := p.1.val
    have ha : a ≠ 0 := by
      intro h
      have hi := p.1.property
      change 0 < a.im at hi
      simp [h] at hi
    have ha' : a.re = 0 := hzero p
    have hfac (z : ℂ) : factor z p = (z - a) * (z + a) / (-a ^ 2) := by
      change 1 + z ^ 2 / (-a ^ 2) = _
      field_simp [ha]; ring
    have hminus : ‖w - a‖ ≤ ‖w + (ε : ℂ) - a‖ := by
      apply norm_le_of_re_sq_le
      · simpa [hw, ha'] using mul_self_nonneg ε
      · simp
    have hplus : ‖w + a‖ ≤ ‖w + (ε : ℂ) + a‖ := by
      apply norm_le_of_re_sq_le
      · simpa [hw, ha'] using mul_self_nonneg ε
      · simp
    rw [hfac, hfac, norm_div, norm_div, norm_mul, norm_mul]
    exact div_le_div_of_nonneg_right
      (mul_le_mul hminus hplus (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hprod (z : ℂ) : Multipliable (factor z) ∧ F z / F 0 = ∏' p, factor z p :=
    XiPairingPublished.concrete_upper_paired_product z
  obtain ⟨hm, hp⟩ := hprod w
  obtain ⟨hm', hp'⟩ := hprod (w + (ε : ℂ))
  have hle : ‖∏' p, factor w p‖ ≤ ‖∏' p, factor (w + (ε : ℂ)) p‖ := by
    apply le_of_tendsto_of_tendsto' hm.hasProd.norm hm'.hasProd.norm
    intro b
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => hfactor p)
  rw [← hp, ← hp', norm_div, norm_div] at hle
  have hnorm := (div_le_div_iff_of_pos_right (norm_pos_iff.mpr hcenter)).mp hle
  have hw₁ : w + 1 / 2 = s := sub_add_cancel _ _
  have hw₂ : w + (ε : ℂ) + 1 / 2 = s + (ε : ℂ) := by rw [add_right_comm, hw₁]
  simpa only [F, hw₁, hw₂] using hnorm

private theorem digamma_re_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, 1 / 4 ≤ w.re → w.re ≤ 1 / 2 →
      (digamma w).re ≤ Real.log (1 + |w.im|) + A := by
  let K := Set.Icc (1 / 4 : ℝ) (1 / 2) ×ˢ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
  let toComplex : ℝ × ℝ → ℂ := fun p => ⟨p.1, p.2⟩
  have hc : Continuous toComplex := by
    change Continuous Complex.equivRealProdCLM.symm
    exact Complex.equivRealProdCLM.symm.continuous
  have hΓ : DifferentiableOn ℂ Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    change 0 < w.re at hw
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_Gamma
    intro n h
    rw [h, neg_re, natCast_re] at hw
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hw
  have hd : ContinuousOn (fun p => (digamma (toComplex p)).re) K := by
    intro p hp
    have hpos : 0 < (toComplex p).re := lt_of_lt_of_le (by norm_num) hp.1.1
    have ha : AnalyticAt ℂ Gamma (toComplex p) :=
      (hΓ.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)) _ hpos
    have hd' : ContinuousAt digamma (toComplex p) := by
      change ContinuousAt (fun w => deriv Gamma w / Gamma w) (toComplex p)
      exact ha.deriv.continuousAt.div ha.continuousAt (Gamma_ne_zero_of_re_pos hpos)
    exact (Complex.continuous_re.continuousAt.comp (hd'.comp hc.continuousAt)).continuousWithinAt
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.prod isCompact_Icc : IsCompact K).bddAbove_image hd
  refine ⟨max 13 B, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro w hlo hhi
  by_cases ht : 1 / 2 ≤ |w.im|
  · have hp : 0 < w.re := by linarith
    have hnorm : ‖w‖ ≤ 1 + |w.im| := by
      refine (norm_le_abs_re_add_abs_im w).trans ?_
      rw [abs_of_pos hp]
      linarith
    have hlog : Real.log ‖w‖ ≤ Real.log (1 + |w.im|) :=
      Real.log_le_log (lt_of_lt_of_le (by linarith) (abs_im_le_norm w)) hnorm
    have herr := Zeta23.StirlingVert.digamma_stirling hp ht
    have hsquare : (1 / 4 : ℝ) ≤ w.im ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg w.im]
    have hdiv : 3 / w.im ^ 2 ≤ 12 := by
      apply (div_le_iff₀ (by linarith : 0 < w.im ^ 2)).2
      linarith
    have hterm : ‖(1 / 2 : ℂ) / w‖ ≤ 1 := by
      rw [norm_div, norm_div, norm_one, show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact (div_le_one (lt_of_lt_of_le (by linarith) (abs_im_le_norm w))).2
        (ht.trans (abs_im_le_norm w))
    have hreal := (re_le_norm _).trans (herr.trans hdiv)
    have ha := (abs_re_le_norm ((1 / 2 : ℂ) / w)).trans hterm
    simp only [add_re, sub_re, Complex.log_re] at hreal
    linarith [neg_abs_le ((1 / 2 : ℂ) / w).re, le_max_left (13 : ℝ) B]
  · have hsmall := abs_lt.mp (lt_of_not_ge ht)
    have hmem : (w.re, w.im) ∈ K := ⟨⟨hlo, hhi⟩, hsmall.1.le, hsmall.2.le⟩
    have hBw : (digamma w).re ≤ B :=
      hB ⟨(w.re, w.im), hmem, rfl⟩
    linarith [le_max_right (13 : ℝ) B, Real.log_nonneg (le_add_of_nonneg_right (abs_nonneg w.im))]

-- Normalize by the value at the base point to keep the complex logarithm local.
private theorem hasDerivAt_log_norm {f : ℂ → ℂ} {x : ℝ}
    (hf : DifferentiableAt ℂ f (x : ℂ)) (hn : f (x : ℂ) ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log ‖f (u : ℂ)‖)
      (logDeriv f (x : ℂ)).re x := by
  have hunit : f (x : ℂ) / f (x : ℂ) ∈ Complex.slitPlane := by simp [hn]
  have hlog := ((hf.hasDerivAt.div_const (f (x : ℂ))).clog hunit).real_of_complex
  rw [div_self hn, div_one] at hlog
  have hh := hlog.add_const (Real.log ‖f (x : ℂ)‖)
  apply hh.congr_of_eventuallyEq
  have hz : ∀ᶠ u : ℝ in 𝓝 x, f (u : ℂ) ≠ 0 :=
    (hf.continuousAt.comp Complex.continuous_ofReal.continuousAt).eventually_ne hn
  filter_upwards [hz] with u hu
  simp only [Complex.log_re, norm_div]
  rw [Real.log_div (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr hn), sub_add_cancel]

private theorem gammaR_shift_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ε : ℝ, 0 < ε → ε < 1 / 2 →
      ‖Gammaℝ ((1 / 2 : ℂ) - (t : ℂ) * I + (ε : ℂ))‖ ≤
        C * (1 + |t|) ^ (ε / 2) * ‖Gammaℝ ((1 / 2 : ℂ) - (t : ℂ) * I)‖ := by
  obtain ⟨A, hA, hbound⟩ := digamma_re_bound
  refine ⟨Real.exp (A / 4), (Real.exp_pos _).le, ?_⟩
  intro t ε hε hε'
  let z (u : ℂ) := u - (t : ℂ) * I
  let f : ℂ → ℂ := Gammaℝ ∘ z
  let g (x : ℝ) := Real.log ‖f (x : ℂ)‖
  have hzre (x : ℝ) : (z x).re = x := by simp [z]
  have hzim (x : ℝ) : (z x).im = -t := by simp [z]
  have hn (x : ℝ) (hx : x ∈ Icc (1 / 2 : ℝ) 1) : f x ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by change 0 < (z x).re; rw [hzre]; linarith [hx.1])
  have hg (x : ℝ) (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
      HasDerivAt g (logDeriv Gammaℝ (z x)).re x := by
    have hG : DifferentiableAt ℂ Gammaℝ (z x) := by
      have hG0 : Gammaℝ (z x) ≠ 0 := hn x hx
      have hi := (differentiable_Gammaℝ_inv (z x)).inv (inv_ne_zero hG0)
      have heq : ((fun s : ℂ => (Gammaℝ s)⁻¹)⁻¹) = Gammaℝ := by
        funext s
        exact inv_inv _
      rwa [heq] at hi
    have hz : HasDerivAt z 1 (x : ℂ) := (hasDerivAt_id (x : ℂ)).sub_const _
    have hf := hG.hasDerivAt.comp (x : ℂ) hz
    have hd := hasDerivAt_log_norm hf.differentiableAt (hn x hx)
    convert hd using 1
    simp [logDeriv_apply, hf.deriv]
  let D := (Real.log (1 + |t|) + A) / 2
  have hderiv (x : ℝ) (hx : x ∈ Icc (1 / 2 : ℝ) 1) : deriv g x ≤ D := by
    have hre : ((z x) / 2).re = x / 2 := by rw [div_ofNat_re, hzre]
    have him : ((z x) / 2).im = -t / 2 := by rw [div_ofNat_im, hzim]
    have hψ := hbound (z x / 2) (by rw [hre]; linarith [hx.1])
      (by rw [hre]; linarith [hx.2])
    have hlog : Real.log (1 + |(z x / 2).im|) ≤ Real.log (1 + |t|) := by
      apply Real.log_le_log (by positivity)
      rw [him, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg t]
    have hπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [(hg x hx).deriv, ZeroFreeBridge.logDeriv_gammaR _ (by rw [hre]; linarith [hx.1])]
    simp only [add_re, div_ofNat_re, neg_re, ofReal_re, mul_re, one_re, one_im, div_ofNat_im,
      zero_div, zero_mul, sub_zero]
    dsimp only [D]
    linarith
  have ha : (1 / 2 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 := by norm_num
  have hb : (1 / 2 : ℝ) + ε ∈ Icc (1 / 2 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hgcont := HasDerivAt.continuousOn hg
  have hdiff : DifferentiableOn ℝ g (interior (Icc (1 / 2 : ℝ) 1)) :=
    fun x hx => (hg x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hmv := (convex_Icc (1 / 2 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    hgcont hdiff (fun x hx => hderiv x (interior_subset hx))
    _ ha _ hb (by linarith)
  have hlogineq : g (1 / 2 + ε) - g (1 / 2) ≤
      A / 4 + Real.log (1 + |t|) * (ε / 2) := by
    dsimp [D] at hmv
    nlinarith [mul_nonneg hA (show 0 ≤ 1 / 2 - ε by linarith)]
  have h := Real.exp_le_exp.mpr hlogineq
  rw [Real.exp_add, ← Real.rpow_def_of_pos (by positivity : 0 < 1 + |t|)] at h
  have hn₁ : 0 < ‖f ((1 / 2 : ℝ) : ℂ)‖ := norm_pos_iff.mpr (hn _ ha)
  have hn₂ : 0 < ‖f (((1 / 2 : ℝ) + ε : ℝ) : ℂ)‖ := norm_pos_iff.mpr (hn _ hb)
  dsimp only [g] at h
  rw [Real.exp_sub, Real.exp_log hn₁, Real.exp_log hn₂, div_le_iff₀ hn₁] at h
  push_cast at h
  simpa [f, z, sub_eq_add_neg, add_right_comm] using h

theorem solution : NymanBeurling.ShiftedZetaRatioBound := by
  obtain ⟨C, hC, hgamma⟩ := gammaR_shift_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro ε hε hε' t
  let s : ℂ := (1 / 2 : ℂ) - (t : ℂ) * I
  let u : ℂ := s + (ε : ℂ)
  have hs : s.re = 1 / 2 := by norm_num [s, mul_re]
  have hu : u.re = 1 / 2 + ε := by simp [u, hs]
  have hs0 : 0 < s.re := by linarith
  have hu0 : 0 < u.re := by linarith
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hu1 : u ≠ 1 := by intro h; simp [h] at hu; linarith
  have hsz : s ≠ 0 := by intro h; simp [h] at hs
  have hn : riemannZeta u ≠ 0 :=
    rh_zeta_zero_free_right_half u (by linarith) (by linarith)
  have hxi := xi_norm_increases hs ε
  change ‖xi s‖ ≤ ‖xi u‖ at hxi
  rw [xi_factor hs0 hs1, xi_factor hu0 hu1, norm_div, norm_div] at hxi
  have hmain := (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < ‖(2 : ℂ)‖)).mp hxi
  simp only [norm_mul] at hmain
  have hsmin : (1 / 2 : ℝ) ≤ ‖s‖ := hs ▸ re_le_norm s
  have hlen : ‖u‖ ≤ 2 * ‖s‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    linarith
  have hlen' : ‖u - 1‖ ≤ ‖s - 1‖ := by
    apply norm_le_of_re_sq_le
    · simp only [sub_re, hs, hu, one_re]
      nlinarith [mul_nonneg hε.le (show 0 ≤ 1 - ε by linarith)]
    · simp [u]
  have hγ := hgamma t ε hε hε'
  change ‖Gammaℝ u‖ ≤ C * (1 + |t|) ^ (ε / 2) * ‖Gammaℝ s‖ at hγ
  let P := ‖s‖ * ‖s - 1‖ * ‖Gammaℝ s‖
  have hP : 0 < P := mul_pos (mul_pos (norm_pos_iff.mpr hsz)
    (norm_pos_iff.mpr (sub_ne_zero.mpr hs1)))
    (norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos hs0))
  have hscale : ‖u‖ * ‖u - 1‖ * ‖Gammaℝ u‖ ≤ (2 * C * (1 + |t|) ^ (ε / 2)) * P := by
    calc
      _ ≤ (2 * ‖s‖) * ‖s - 1‖ * (C * (1 + |t|) ^ (ε / 2) * ‖Gammaℝ s‖) := by
        gcongr
      _ = _ := by dsimp [P]; ring
  change P * ‖riemannZeta s‖ ≤ _ at hmain
  have hz : ‖riemannZeta s‖ ≤ (2 * C * (1 + |t|) ^ (ε / 2)) * ‖riemannZeta u‖ := by
    apply (le_of_mul_le_mul_left _ hP)
    calc
      _ ≤ (‖u‖ * ‖u - 1‖ * ‖Gammaℝ u‖) * ‖riemannZeta u‖ := hmain
      _ ≤ ((2 * C * (1 + |t|) ^ (ε / 2)) * P) * ‖riemannZeta u‖ :=
        mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
      _ = _ := by ring
  change ‖riemannZeta s / riemannZeta u‖ ≤ _
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hn)).2 hz
