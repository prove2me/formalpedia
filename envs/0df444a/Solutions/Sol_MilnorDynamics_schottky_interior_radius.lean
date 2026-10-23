-- Prove2me | solution 1 for MilnorDynamics.schottky_interior_radius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:29:41.851979+00:00
-- url     : https://prove2.me/submissions/34528bbb-b1fa-420a-840a-5c9f66fcaff0

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set Metric Topology

namespace MilnorSchottkyAux


/-- **Bloch's theorem** (quantitative form, constant `1/128`): a holomorphic function on a disc
of radius `s` covers some disc of radius `s ‖f' z‖ / 128`. -/
theorem bloch (f : ℂ → ℂ) (z : ℂ) (s : ℝ) (hs : 0 < s)
    (hf : DifferentiableOn ℂ f (ball z s)) :
    ∃ b, ball b (s * ‖deriv f z‖ / 128) ⊆ f '' ball z s := by
  rcases eq_or_ne (deriv f z) 0 with h0 | h0
  · exact ⟨0, by simp [h0]⟩
  have hfa : AnalyticOnNhd ℂ f (ball z s) := hf.analyticOnNhd isOpen_ball
  have hdc : ContinuousOn (deriv f) (ball z s) := hfa.deriv.continuousOn
  set K := closedBall z (s / 2) with hK
  have hKsub : K ⊆ ball z s := closedBall_subset_ball (by linarith)
  have hKc : IsCompact K := isCompact_closedBall _ _
  let u : ℂ → ℝ := fun w => (s / 2 - dist w z) * ‖deriv f w‖
  have hu : ContinuousOn u K :=
    ((continuousOn_const.sub (continuous_id.dist continuous_const).continuousOn)).mul
      ((hdc.mono hKsub).norm)
  have hzK : z ∈ K := mem_closedBall_self (by linarith)
  obtain ⟨a, haK, hamax⟩ := hKc.exists_isMaxOn ⟨z, hzK⟩ hu
  have hua : u z ≤ u a := hamax hzK
  have huz : u z = s / 2 * ‖deriv f z‖ := by simp [u]
  have huz_pos : 0 < u z := by rw [huz]; positivity
  have hdpos : 0 < s / 2 - dist a z := by
    by_contra hcon
    push Not at hcon
    have : u a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon (norm_nonneg _)
    linarith
  set d := s / 2 - dist a z with hd
  set A := ‖deriv f a‖ with hA
  have hApos : 0 < A := by
    by_contra hcon
    push Not at hcon
    have : u a ≤ 0 := by
      show d * A ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos hdpos.le hcon
    linarith
  set ρ := d / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  -- derivative bound on the closed ball of radius ρ about a
  have hball_sub : closedBall a ρ ⊆ K := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    have := dist_triangle w a z
    linarith
  have hderiv_bd : ∀ w ∈ closedBall a ρ, ‖deriv f w‖ ≤ 2 * A := by
    intro w hw
    have hwK := hball_sub hw
    have h1 : u w ≤ u a := hamax hwK
    have hw' : dist w z ≤ dist a z + ρ := by
      have := dist_triangle w a z
      rw [mem_closedBall] at hw
      linarith
    have h2 : ρ ≤ s / 2 - dist w z := by linarith
    have h3 : ρ * ‖deriv f w‖ ≤ u w := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h4 : u a = 2 * ρ * A := by simp only [u, hA]; rw [← hd]; ring
    nlinarith
  -- Schwarz lemma applied to f' - f'(a)
  have hsub_ball : ball a ρ ⊆ ball z s := ball_subset_closedBall.trans (hball_sub.trans hKsub)
  have hschw : ∀ w ∈ ball a ρ, ‖deriv f w - deriv f a‖ ≤ 3 * A / ρ * ‖w - a‖ := by
    intro w hw
    have hd' : DifferentiableOn ℂ (deriv f) (ball a ρ) :=
      (hfa.deriv.differentiableOn).mono hsub_ball
    have hmaps : MapsTo (deriv f) (ball a ρ) (closedBall (deriv f a) (3 * A)) := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm]
      have := hderiv_bd x (ball_subset_closedBall hx)
      calc ‖deriv f x - deriv f a‖ ≤ ‖deriv f x‖ + ‖deriv f a‖ := norm_sub_le _ _
        _ ≤ 3 * A := by rw [← hA]; linarith
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd' hmaps hw
    simpa [dist_eq_norm] using this
  set t := ρ / 8 with ht
  have htpos : 0 < t := by positivity
  have htρ : t < ρ := by linarith
  have hcl_sub : closedBall a t ⊆ ball a ρ := closedBall_subset_ball htρ
  -- k(w) = f w - f a - f'(a) (w - a) is (A/2)-Lipschitz on closedBall a t
  have hk : ∀ w ∈ closedBall a t,
      ‖(f w - deriv f a * w) - (f a - deriv f a * a)‖ ≤ A / 2 * ‖w - a‖ := by
    intro w hw
    have hdiff : ∀ x ∈ closedBall a t, DifferentiableAt ℂ (fun x => f x - deriv f a * x) x := by
      intro x hx
      have : DifferentiableAt ℂ f x :=
        hf.differentiableAt (isOpen_ball.mem_nhds (hsub_ball (hcl_sub hx)))
      exact this.sub ((differentiableAt_id).const_mul _)
    have hbound : ∀ x ∈ closedBall a t, ‖deriv (fun x => f x - deriv f a * x) x‖ ≤ A / 2 := by
      intro x hx
      have hfx : DifferentiableAt ℂ f x :=
        hf.differentiableAt (isOpen_ball.mem_nhds (hsub_ball (hcl_sub hx)))
      have : deriv (fun x => f x - deriv f a * x) x = deriv f x - deriv f a := by
        have := ((hfx.hasDerivAt).sub ((hasDerivAt_id x).const_mul (deriv f a))).deriv
        rw [mul_one] at this
        exact this
      rw [this]
      have h1 := hschw x (hcl_sub hx)
      have h2 : ‖x - a‖ ≤ t := by rw [← dist_eq_norm]; exact hx
      calc ‖deriv f x - deriv f a‖ ≤ 3 * A / ρ * ‖x - a‖ := h1
        _ ≤ 3 * A / ρ * t := by gcongr
        _ ≤ A / 2 := by rw [ht]; field_simp; nlinarith
    exact (convex_closedBall a t).norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (mem_closedBall_self htpos.le) hw
  -- lower bound on the sphere
  have hsphere : ∀ w ∈ sphere a t, A * t / 2 ≤ ‖f w - f a‖ := by
    intro w hw
    have hw' : w ∈ closedBall a t := sphere_subset_closedBall hw
    have h1 := hk w hw'
    have h2 : ‖w - a‖ = t := by rw [← dist_eq_norm]; exact hw
    have h3 : ‖deriv f a * (w - a)‖ = A * t := by rw [norm_mul, h2]
    have : f w - f a = deriv f a * (w - a) +
        ((f w - deriv f a * w) - (f a - deriv f a * a)) := by ring
    rw [this]
    have := norm_sub_norm_le (deriv f a * (w - a))
      (-((f w - deriv f a * w) - (f a - deriv f a * a)))
    rw [norm_neg, sub_neg_eq_add] at this
    rw [h2] at h1
    linarith
  have hdcl : DiffContOnCl ℂ f (ball a t) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball a htpos.ne']
    exact hf.mono (hcl_sub.trans hsub_ball)
  have hfreq : ∃ᶠ w in 𝓝 a, f w ≠ f a := by
    intro hev
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hεf⟩ := hev
    set r := min ε t / 2 with hr
    have hrpos : 0 < r := by positivity
    have hrε : r < ε := by have := min_le_left ε t; linarith
    have hrt : r ≤ t := by have := min_le_right ε t; linarith
    have hw : dist (a + r) a = r := by simp [abs_of_pos hrpos]
    have hfeq : f (a + r) = f a := not_not.mp (hεf (by rw [hw]; exact hrε))
    have h1 := hk (a + r) (by rw [mem_closedBall, hw]; exact hrt)
    have h2 : ‖(a + r) - a‖ = r := by rw [← dist_eq_norm]; exact hw
    rw [h2, hfeq] at h1
    have : (f a - deriv f a * (a + ↑r)) - (f a - deriv f a * a) = -(deriv f a * r) := by ring
    rw [this, norm_neg, norm_mul] at h1
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos] at h1
    rw [← hA] at h1
    nlinarith
  have himg := hdcl.ball_subset_image_closedBall htpos hsphere hfreq
  refine ⟨f a, ?_⟩
  intro v hv
  have hv' : v ∈ ball (f a) (A * t / 2 / 2) := by
    refine mem_of_mem_of_subset hv (ball_subset_ball ?_)
    have h4 : u a = 2 * ρ * A := by simp only [u, hA]; rw [← hd]; ring
    rw [huz] at hua
    rw [ht]
    nlinarith
  obtain ⟨w, hw, rfl⟩ := himg hv'
  exact ⟨w, hsub_ball (hcl_sub hw), rfl⟩


/-- Holomorphic logarithm of a nonvanishing holomorphic function on a disc. -/
theorem exists_log (c : ℂ) (r : ℝ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball c r))
    (hne : ∀ z ∈ ball c r, g z ≠ 0) (hr : 0 < r) (w0 : ℂ) (hw0 : Complex.exp w0 = g c) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c r) ∧ L c = w0 ∧
      ∀ z ∈ ball c r, Complex.exp (L z) = g z := by
  have hga : AnalyticOnNhd ℂ g (ball c r) := hg.analyticOnNhd isOpen_ball
  have hq : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c r) :=
    hga.deriv.differentiableOn.div hg hne
  obtain ⟨P, hPc, hP⟩ := hq.isExactOn_ball.with_val_at c w0
  have hPd : DifferentiableOn ℂ P (ball c r) := fun z hz => (hP z hz).differentiableAt.differentiableWithinAt
  have hcmem : c ∈ ball c r := mem_ball_self hr
  let k : ℂ → ℂ := fun z => g z * Complex.exp (-P z)
  have hkd : ∀ z ∈ ball c r, HasDerivAt k 0 z := by
    intro z hz
    have hgz : HasDerivAt g (deriv g z) z :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have h1 : HasDerivAt k (deriv g z * Complex.exp (-P z) +
        g z * (Complex.exp (-P z) * -(deriv g z / g z))) z := hgz.mul ((hP z hz).neg.cexp)
    convert h1 using 1
    have := hne z hz
    field_simp
    ring
  have hkdiff : DifferentiableOn ℂ k (ball c r) := fun z hz => (hkd z hz).differentiableAt.differentiableWithinAt
  have hconst : ∀ z ∈ ball c r, k z = k c := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected hkdiff
      (fun x hx => (hkd x hx).deriv) hz hcmem
  have hkc : k c = 1 := by
    simp only [k, hPc, ← hw0, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  refine ⟨P, hPd, hPc, fun z hz => ?_⟩
  have := hconst z hz
  rw [hkc] at this
  simp only [k] at this
  have h2 : Complex.exp (-P z) * Complex.exp (P z) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc Complex.exp (P z) = g z * Complex.exp (-P z) * Complex.exp (P z) := by rw [this, one_mul]
    _ = g z := by rw [mul_assoc, h2, mul_one]

/-- The values `v k = log (√(k+1) + √k)`. -/
noncomputable def vv (k : ℕ) : ℝ := Real.log (Real.sqrt (k + 1) + Real.sqrt k)

lemma vv_pos_arg (k : ℕ) : 0 < Real.sqrt (k + 1) + Real.sqrt k := by
  have : 0 < Real.sqrt (k + 1) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma vv_zero : vv 0 = 0 := by simp [vv]

lemma vv_gap (k : ℕ) : vv (k + 1) < vv k + 1 := by
  unfold vv
  have h0 := vv_pos_arg k
  have hk1 : 0 < Real.sqrt ((k:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (((k + 1 : ℕ) : ℝ) + 1) ≤ 3 / 2 * Real.sqrt ((k:ℝ) + 1) := by
    rw [show (3 / 2 : ℝ) = Real.sqrt (9 / 4) by
      rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    push_cast
    linarith
  have he : (5 / 2 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hl : Real.log (Real.sqrt (k + 1) + Real.sqrt k) + 1 =
      Real.log (Real.exp 1 * (Real.sqrt (k + 1) + Real.sqrt k)) := by
    rw [Real.log_mul (by positivity) h0.ne', Real.log_exp]; ring
  rw [hl]
  apply Real.log_lt_log (vv_pos_arg (k + 1))
  have hsk : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  push_cast at hs ⊢
  nlinarith [mul_lt_mul_of_pos_right he h0]

lemma vv_large (t : ℝ) : ∃ k : ℕ, t < vv (k + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp t)
  refine ⟨n ^ 2, ?_⟩
  unfold vv
  rw [← Real.exp_lt_exp, Real.exp_log (vv_pos_arg _)]
  have h1 : Real.sqrt (((n ^ 2 : ℕ) : ℝ)) = n := by push_cast; exact Real.sqrt_sq (by positivity)
  have h2 : 0 ≤ Real.sqrt ((((n ^ 2 + 1 : ℕ)) : ℝ) + 1) := Real.sqrt_nonneg _
  have h3 : Real.sqrt (((n ^ 2 + 1 : ℕ) : ℝ)) ≥ Real.sqrt (((n ^ 2 : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt (by push_cast; linarith)
  rw [h1] at h3
  linarith

lemma exists_vv_near (t : ℝ) (ht : 0 ≤ t) : ∃ k : ℕ, |t - vv k| < 1 := by
  classical
  have hex := vv_large t
  let m := Nat.find hex
  have hm : t < vv (m + 1) := Nat.find_spec hex
  have hle : vv m ≤ t := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, vv_zero]; exact ht
    · have := Nat.find_min hex (show m - 1 < m by omega)
      push Not at this
      rwa [show m - 1 + 1 = m by omega] at this
  refine ⟨m, ?_⟩
  have := vv_gap m
  rw [abs_lt]; constructor <;> linarith

lemma cosh_sq_vv (k : ℕ) (j : ℤ) :
    ((Complex.exp ((vv k : ℂ) + 2 * Real.pi * Complex.I * j) +
      Complex.exp (-((vv k : ℂ) + 2 * Real.pi * Complex.I * j))) / 2) ^ 2 = ((k + 1 : ℕ) : ℂ) := by
  have hj1 : Complex.exp (2 * Real.pi * Complex.I * j) = 1 := by
    rw [show (2 * Real.pi * Complex.I * j : ℂ) = j * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I j
  have hj2 : Complex.exp (-(2 * Real.pi * Complex.I * j)) = 1 := by
    rw [Complex.exp_neg, hj1, inv_one]
  rw [neg_add, Complex.exp_add, Complex.exp_add, hj1, hj2, mul_one, mul_one]
  have hpos := vv_pos_arg k
  have e1 : Complex.exp (vv k : ℂ) = ((Real.sqrt (k + 1) + Real.sqrt k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, vv, Real.exp_log hpos]
  have e2 : Complex.exp (-(vv k : ℂ)) = ((Real.sqrt (k + 1) - Real.sqrt k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, vv, Real.exp_neg, Real.exp_log hpos]
    congr 1
    have h1 : Real.sqrt ((k:ℝ) + 1) ^ 2 = k + 1 := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt (k:ℝ) ^ 2 = k := Real.sq_sqrt (by positivity)
    field_simp
    nlinarith
  rw [e1, e2]
  have h1 : Real.sqrt ((k:ℝ) + 1) ^ 2 = k + 1 := Real.sq_sqrt (by positivity)
  push_cast
  have : ((Real.sqrt ((k:ℝ) + 1) : ℂ)) ^ 2 = (k : ℂ) + 1 := by
    rw [← Complex.ofReal_pow, h1]; push_cast; ring
  linear_combination this

/-- The set `{ω | cosh ω ^ 2 ∈ ℕ}` is `5`-dense in `ℂ`. -/
lemma omitted_dense (b : ℂ) : ∃ ω ∈ ball b 5,
    ∃ n : ℕ, ((Complex.exp ω + Complex.exp (-ω)) / 2) ^ 2 = (n : ℂ) := by
  -- reduce to `0 ≤ b.re`
  wlog hb : 0 ≤ b.re generalizing b
  · obtain ⟨ω, hω, n, hn⟩ := this (-b) (by simp; linarith)
    refine ⟨-ω, ?_, n, ?_⟩
    · rw [mem_ball, dist_eq_norm] at hω ⊢
      rw [show -ω - b = -(ω - -b) by ring, norm_neg]; exact hω
    · rw [neg_neg, add_comm]; exact hn
  obtain ⟨k, hk⟩ := exists_vv_near b.re hb
  set j : ℤ := round (b.im / (2 * Real.pi)) with hj
  refine ⟨(vv k : ℂ) + 2 * Real.pi * Complex.I * j, ?_, k + 1, cosh_sq_vv k j⟩
  rw [mem_ball, dist_eq_norm]
  have hpi := Real.pi_pos
  have hround : |b.im / (2 * Real.pi) - j| ≤ 1 / 2 := by
    rw [hj]; exact abs_sub_round _
  have him : |b.im - 2 * Real.pi * j| ≤ Real.pi := by
    have : b.im - 2 * Real.pi * j = 2 * Real.pi * (b.im / (2 * Real.pi) - j) := by
      field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  calc ‖(vv k : ℂ) + 2 * Real.pi * Complex.I * j - b‖
      ≤ |((vv k : ℂ) + 2 * Real.pi * Complex.I * j - b).re| +
        |((vv k : ℂ) + 2 * Real.pi * Complex.I * j - b).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |b.re - vv k| + |b.im - 2 * Real.pi * j| := by
        congr 1
        · simp [abs_sub_comm]
        · simp [abs_sub_comm]
    _ < 1 + Real.pi := by linarith
    _ < 5 := by have := Real.pi_lt_four; linarith


lemma norm_log_le (x : ℂ) (hx : x ≠ 0) : ‖Complex.log x‖ ≤ ‖x‖ + ‖x‖⁻¹ + Real.pi := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  have h1 : |Real.log ‖x‖| ≤ ‖x‖ + ‖x‖⁻¹ := by
    rw [abs_le]; constructor
    · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
      rw [Real.log_inv] at this
      linarith
    · have := Real.log_le_sub_one_of_pos hpos
      have : 0 < ‖x‖⁻¹ := inv_pos.mpr hpos
      linarith
  have h2 : |Complex.arg x| ≤ Real.pi := Complex.abs_arg_le_pi x
  linarith

lemma le_one_add_of_sq_le {x B : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ B) : x ≤ 1 + B := by
  nlinarith

/-- Core of Schottky's theorem: `1/2 ≤ |g 0| ≤ M`. -/
theorem schottky_core (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) →
      MapsTo g (ball 0 1) ({0, 1}ᶜ : Set ℂ) → 1 / 2 ≤ ‖g 0‖ → ‖g 0‖ ≤ M →
      ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ C := by
  set B0 := M + 1 + Real.pi with hB0
  set B1 := 3 + 2 * B0 with hB1
  set B2 := 2 * B1 + Real.pi with hB2
  set B3 := B2 + 640 / (1 - r) with hB3
  refine ⟨Real.exp (2 * Real.pi * Real.exp (2 * B3)), ?_⟩
  intro g hg hmaps hg0l hg0u z hz
  have hpi := Real.pi_pos
  have h1r : 0 < 1 - r := by linarith
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hgne0 : ∀ z ∈ ball (0:ℂ) 1, g z ≠ 0 := fun z hz h => by
    have := hmaps hz; simp [h] at this
  have hgne1 : ∀ z ∈ ball (0:ℂ) 1, g z ≠ 1 := fun z hz h => by
    have := hmaps hz; simp [h] at this
  -- logarithm of g
  obtain ⟨L, hLd, hL0, hLexp⟩ := exists_log 0 1 g hg hgne0 one_pos (Complex.log (g 0))
    (Complex.exp_log (hgne0 0 h0mem))
  have hL0b : ‖L 0‖ ≤ B0 := by
    rw [hL0]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    have hpos : 0 < ‖g 0‖ := by linarith
    have h1 : |Real.log ‖g 0‖| ≤ M + 1 := by
      rw [abs_le]; constructor
      · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
        rw [Real.log_inv] at this
        have : ‖g 0‖⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]; linarith
        linarith
      · have := Real.log_le_sub_one_of_pos hpos
        linarith
    have h2 : |Complex.arg (g 0)| ≤ Real.pi := Complex.abs_arg_le_pi _
    linarith
  -- F = L / (2πi)
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hn2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpi]; norm_num
  set F : ℂ → ℂ := fun z => L z / (2 * Real.pi * Complex.I) with hF
  have hLF : ∀ z, L z = 2 * Real.pi * Complex.I * F z := fun z => by
    simp only [hF]; field_simp
  have hFint : ∀ z ∈ ball (0:ℂ) 1, ∀ n : ℤ, F z ≠ n := by
    intro z hz n hn
    apply hgne1 z hz
    rw [← hLexp z hz, hLF z, hn, show (2 * Real.pi * Complex.I * n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hLd.div_const _
  have hF0b : ‖F 0‖ ≤ B0 := by
    simp only [hF]
    rw [norm_div, hn2pi]
    have : ‖L 0‖ / (2 * Real.pi) ≤ ‖L 0‖ := by
      apply div_le_self (norm_nonneg _); linarith [Real.pi_gt_three]
    linarith
  -- square roots
  have hFne : ∀ z ∈ ball (0:ℂ) 1, F z ≠ 0 := fun z hz h => hFint z hz 0 (by simp [h])
  have hF1ne : ∀ z ∈ ball (0:ℂ) 1, F z - 1 ≠ 0 := fun z hz h =>
    hFint z hz 1 (by simpa [sub_eq_zero] using h)
  obtain ⟨P1, hP1d, -, hP1⟩ := exists_log 0 1 F hFd hFne one_pos (Complex.log (F 0))
    (Complex.exp_log (hFne 0 h0mem))
  obtain ⟨P2, hP2d, -, hP2⟩ := exists_log 0 1 (fun z => F z - 1) (hFd.sub_const 1) hF1ne one_pos
    (Complex.log (F 0 - 1)) (Complex.exp_log (hF1ne 0 h0mem))
  set S1 : ℂ → ℂ := fun z => Complex.exp (P1 z / 2) with hS1
  set S2 : ℂ → ℂ := fun z => Complex.exp (P2 z / 2) with hS2
  have hS1sq : ∀ z ∈ ball (0:ℂ) 1, S1 z ^ 2 = F z := fun z hz => by
    simp only [hS1]; rw [← Complex.exp_nat_mul]; push_cast
    rw [show (2 : ℂ) * (P1 z / 2) = P1 z by ring]; exact hP1 z hz
  have hS2sq : ∀ z ∈ ball (0:ℂ) 1, S2 z ^ 2 = F z - 1 := fun z hz => by
    simp only [hS2]; rw [← Complex.exp_nat_mul]; push_cast
    rw [show (2 : ℂ) * (P2 z / 2) = P2 z by ring]; exact hP2 z hz
  set H : ℂ → ℂ := fun z => S1 z - S2 z with hH
  set Hi : ℂ → ℂ := fun z => S1 z + S2 z with hHi
  have hHHi : ∀ z ∈ ball (0:ℂ) 1, H z * Hi z = 1 := fun z hz => by
    simp only [hH, hHi]
    have := hS1sq z hz; have := hS2sq z hz
    linear_combination (hS1sq z hz) - (hS2sq z hz)
  have hHne : ∀ z ∈ ball (0:ℂ) 1, H z ≠ 0 := fun z hz h => by
    have := hHHi z hz; rw [h, zero_mul] at this; exact zero_ne_one this
  have hHd : DifferentiableOn ℂ H (ball 0 1) :=
    ((hP1d.div_const 2).cexp).sub ((hP2d.div_const 2).cexp)
  obtain ⟨G, hGd, hG0, hGexp⟩ := exists_log 0 1 H hHd hHne one_pos (Complex.log (H 0))
    (Complex.exp_log (hHne 0 h0mem))
  have hGneg : ∀ z ∈ ball (0:ℂ) 1, Complex.exp (-G z) = Hi z := fun z hz => by
    rw [Complex.exp_neg, hGexp z hz]
    exact inv_eq_of_mul_eq_one_right (hHHi z hz)
  have hS1G : ∀ z ∈ ball (0:ℂ) 1, (Complex.exp (G z) + Complex.exp (-G z)) / 2 = S1 z :=
    fun z hz => by rw [hGexp z hz, hGneg z hz]; simp only [hH, hHi]; ring
  -- G omits the dense set
  have homit : ∀ ζ ∈ ball (0:ℂ) 1, ∀ n : ℕ,
      ((Complex.exp (G ζ) + Complex.exp (-G ζ)) / 2) ^ 2 ≠ (n : ℂ) := by
    intro ζ hζ n hn
    rw [hS1G ζ hζ, hS1sq ζ hζ] at hn
    exact hFint ζ hζ n (by simpa using hn)
  -- derivative bound via Bloch
  have hderiv : ∀ w : ℂ, ‖w‖ ≤ r → ‖deriv G w‖ ≤ 640 / (1 - r) := by
    intro w hw
    by_contra hcon
    push Not at hcon
    have hsub : ball w (1 - r) ⊆ ball 0 1 := by
      intro x hx
      rw [mem_ball, dist_zero_right]
      rw [mem_ball, dist_eq_norm] at hx
      calc ‖x‖ ≤ ‖x - w‖ + ‖w‖ := by
            have := norm_add_le (x - w) w; simpa using this
        _ < 1 := by linarith
    obtain ⟨b, hb⟩ := bloch G w (1 - r) h1r (hGd.mono hsub)
    obtain ⟨ω, hω, n, hn⟩ := omitted_dense b
    have hrad : 5 ≤ (1 - r) * ‖deriv G w‖ / 128 := by
      rw [div_lt_iff₀ h1r] at hcon
      linarith
    obtain ⟨ζ, hζ, rfl⟩ := hb (ball_subset_ball hrad hω)
    exact homit ζ (hsub hζ) n hn
  -- bound on G
  have hcl : closedBall (0:ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
  have hzmem : z ∈ closedBall (0:ℂ) r := by rw [mem_closedBall, dist_zero_right]; exact hz
  have hGdiff : ∀ x ∈ closedBall (0:ℂ) r, DifferentiableAt ℂ G x := fun x hx =>
    hGd.differentiableAt (isOpen_ball.mem_nhds (hcl hx))
  have hmv := (convex_closedBall (0:ℂ) r).norm_image_sub_le_of_norm_deriv_le hGdiff
    (fun x hx => hderiv x (by rw [mem_closedBall, dist_zero_right] at hx; exact hx))
    (mem_closedBall_self hr) hzmem
  rw [sub_zero] at hmv
  have hS10 : ‖S1 0‖ ≤ 1 + B0 := by
    apply le_one_add_of_sq_le (norm_nonneg _)
    rw [← norm_pow, hS1sq 0 h0mem]; exact hF0b
  have hS20 : ‖S2 0‖ ≤ 2 + B0 := by
    have := le_one_add_of_sq_le (norm_nonneg (S2 0)) (B := ‖F 0 - 1‖)
      (by rw [← norm_pow, hS2sq 0 h0mem])
    have h2 : ‖F 0 - 1‖ ≤ ‖F 0‖ + 1 := by
      have := norm_sub_le (F 0) 1; simpa using this
    linarith
  have hH0 : ‖H 0‖ ≤ B1 := by
    simp only [hH]; have := norm_sub_le (S1 0) (S2 0); linarith
  have hHi0 : ‖H 0‖⁻¹ ≤ B1 := by
    have : ‖H 0‖⁻¹ = ‖Hi 0‖ := by
      rw [← norm_inv, inv_eq_of_mul_eq_one_right (hHHi 0 h0mem)]
    rw [this]; simp only [hHi]; have := norm_add_le (S1 0) (S2 0); linarith
  have hG0b : ‖G 0‖ ≤ B2 := by
    rw [hG0]
    have := norm_log_le (H 0) (hHne 0 h0mem)
    linarith
  have hGz : ‖G z‖ ≤ B3 := by
    have h1 : ‖G z‖ ≤ ‖G z - G 0‖ + ‖G 0‖ := by
      have := norm_add_le (G z - G 0) (G 0); simpa using this
    have h2 : 640 / (1 - r) * ‖z‖ ≤ 640 / (1 - r) := by
      have : ‖z‖ ≤ 1 := by linarith
      have : 0 ≤ 640 / (1 - r) := by positivity
      nlinarith
    linarith
  have hzball : z ∈ ball (0:ℂ) 1 := hcl hzmem
  have hS1z : ‖S1 z‖ ≤ Real.exp B3 := by
    rw [← hS1G z hzball]
    have e1 := Complex.norm_exp_le_exp_norm (G z)
    have e2 := Complex.norm_exp_le_exp_norm (-G z)
    rw [norm_neg] at e2
    have e3 : Real.exp ‖G z‖ ≤ Real.exp B3 := Real.exp_le_exp.mpr hGz
    rw [norm_div]
    have := norm_add_le (Complex.exp (G z)) (Complex.exp (-G z))
    simp only [Complex.norm_ofNat]
    linarith
  have hFz : ‖F z‖ ≤ Real.exp (2 * B3) := by
    rw [← hS1sq z hzball, norm_pow, show 2 * B3 = B3 + B3 by ring, Real.exp_add]
    nlinarith [norm_nonneg (S1 z), Real.exp_pos B3]
  rw [← hLexp z hzball, hLF z]
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
  rw [norm_mul, hn2pi]
  exact mul_le_mul_of_nonneg_left hFz (by positivity)


/-- **Schottky's theorem.** -/
theorem schottky (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 1) →
      MapsTo g (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) → ‖g 0‖ ≤ M →
      ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ C := by
  obtain ⟨C1, hC1⟩ := schottky_core r hr hr1 M hM
  obtain ⟨C2, hC2⟩ := schottky_core r hr hr1 (3 / 2) (by norm_num)
  refine ⟨max (max C1 (1 + C2)) 0, le_max_right _ _, ?_⟩
  intro g hg hmaps hg0 z hz
  rcases le_or_gt (1 / 2) ‖g 0‖ with h | h
  · exact (hC1 g hg hmaps h hg0 z hz).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have hg' : DifferentiableOn ℂ (fun z => 1 - g z) (ball 0 1) := hg.const_sub 1
    have hmaps' : MapsTo (fun z => 1 - g z) (ball 0 1) ({0, 1}ᶜ : Set ℂ) := by
      intro x hx
      have := hmaps hx
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at this ⊢
      constructor
      · intro h; exact this.2 (by linear_combination -h)
      · intro h; exact this.1 (by linear_combination -h)
    have hl : 1 / 2 ≤ ‖1 - g 0‖ := by
      have := norm_sub_norm_le (1 : ℂ) (g 0); simp at this; linarith
    have hu : ‖1 - g 0‖ ≤ 3 / 2 := by
      have := norm_sub_le (1 : ℂ) (g 0); simp at this; linarith
    have := hC2 _ hg' hmaps' hl hu z hz
    have h2 : ‖g z‖ ≤ 1 + ‖1 - g z‖ := by
      have := norm_sub_le (1 : ℂ) (1 - g z); simp at this; linarith
    exact (h2.trans (by linarith)).trans ((le_max_right _ _).trans (le_max_left _ _))

end MilnorSchottkyAux

theorem solution (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℂ → ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 1) →
      MapsTo g (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) →
      ‖g 0‖ ≤ M → ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ C :=
  MilnorSchottkyAux.schottky r hr hr1 M hM
