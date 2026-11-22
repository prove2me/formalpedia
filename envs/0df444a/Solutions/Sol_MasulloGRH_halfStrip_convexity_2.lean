-- Prove2me | solution 2 for MasulloGRH.halfStrip_convexity
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T19:31:59.066222+00:00
-- url     : https://prove2.me/submissions/f695236d-8a19-4e14-a91a-3ed14683d648

import Mathlib

set_option autoImplicit false

/-!
# Phragmén–Lindelöf convexity on half-strips

Proof of `MasulloGRH.halfStrip_convexity`.

The weight is the affine-logarithmic weight `exp (-(p + q s) log (-i s))`, whose modulus on the
upper half-strip is comparable to `(Im s) ^ (-(p + q Re s))`.  The same weight (in the form
`exp ((p + q s) log (s - z₀) - ε q π/2 · i s)`) and the same estimate `|t · arg| ≤ |σ|` are used in
`RiemannMasullo/AppB_AnalyticNT/Sec1.lean` of https://github.com/mccorvie/riemann-masullo
(`norm_affineLogWeight`, `im_mul_halfArg_bounds`, `isBigO_rpow_of_verticalStrip_of_le`,
Apache-2.0), where full strips are treated.  Here the function is only assumed holomorphic on the
two half-strips, so instead of Mathlib's strip Phragmén–Lindelöf theorem the proof uses the
maximum modulus principle on rectangles `[a, b] × [T, Y]` after multiplying by `exp (i ε s)`.
-/

open Complex Filter Topology Set

namespace HalfStripAux

/-- For `z` with positive real part, `|re z · arg z| ≤ |im z|`. -/
lemma abs_re_mul_arg_le {z : ℂ} (hz : 0 < z.re) : |z.re * z.arg| ≤ |z.im| := by
  have h1 : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have htan : Real.tan z.arg = z.im / z.re := Complex.tan_arg z
  have h2 : |z.arg| ≤ |Real.tan z.arg| := by
    rcases le_total 0 z.arg with h | h
    · rw [abs_of_nonneg h] at h1 ⊢
      exact (Real.le_tan h h1).trans (le_abs_self _)
    · rw [abs_of_nonpos h] at h1 ⊢
      have h3 := Real.le_tan (by linarith : (0 : ℝ) ≤ -z.arg) h1
      rw [Real.tan_neg] at h3
      exact h3.trans (neg_le_abs _)
  rw [abs_mul, abs_of_pos hz]
  calc z.re * |z.arg| ≤ z.re * |Real.tan z.arg| := by gcongr
    _ = z.re * (|z.im| / z.re) := by rw [htan, abs_div, abs_of_pos hz]
    _ = |z.im| := by field_simp

lemma rpow_le_of_ratio {u c x L : ℝ} (hu : 1 ≤ u) (huc : u ≤ c) (hx : |x| ≤ L) :
    u ^ x ≤ c ^ L := by
  have hc : 1 ≤ c := hu.trans huc
  calc u ^ x ≤ u ^ |x| := Real.rpow_le_rpow_of_exponent_le hu (le_abs_self x)
    _ ≤ c ^ |x| := Real.rpow_le_rpow (by linarith) huc (abs_nonneg x)
    _ ≤ c ^ L := Real.rpow_le_rpow_of_exponent_le hc hx

lemma rpow_comparison {t r c x L : ℝ} (ht : 0 < t) (htr : t ≤ r) (hrc : r ≤ c * t)
    (hx : |x| ≤ L) : r ^ x ≤ c ^ L * t ^ x ∧ t ^ x ≤ c ^ L * r ^ x := by
  have hr : 0 < r := ht.trans_le htr
  have hu : 1 ≤ r / t := by rw [le_div_iff₀ ht]; linarith
  have huc : r / t ≤ c := by rw [div_le_iff₀ ht]; exact hrc
  have hrt : 0 < r / t := div_pos hr ht
  constructor
  · have h1 := rpow_le_of_ratio hu huc hx
    have h2 : r ^ x = (r / t) ^ x * t ^ x := by
      rw [← Real.mul_rpow hrt.le ht.le]
      congr 1
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht.le _)
  · have h1 := rpow_le_of_ratio (x := -x) (L := L) hu huc (by rwa [abs_neg])
    have h2 : t ^ x = (r / t) ^ (-x) * r ^ x := by
      rw [Real.rpow_neg hrt.le, ← Real.inv_rpow hrt.le, inv_div,
        ← Real.mul_rpow (div_pos ht hr).le hr.le]
      congr 1
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hr.le _)

/-- The affine-logarithmic weight on the upper half-plane. -/
noncomputable def W (p q : ℝ) (s : ℂ) : ℂ :=
  cexp (-((p : ℂ) + q * s) * Complex.log (-I * s))

lemma norm_W (p q : ℝ) (s : ℂ) (hs : s ≠ 0) :
    ‖W p q s‖ = ‖s‖ ^ (-(p + q * s.re)) * Real.exp (q * (s.im * (-I * s).arg)) := by
  have hn : ‖-I * s‖ = ‖s‖ := by simp
  have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  rw [W, Complex.norm_exp]
  have hre : (-((p : ℂ) + q * s) * Complex.log (-I * s)).re
      = Real.log ‖s‖ * (-(p + q * s.re)) + q * (s.im * (-I * s).arg) := by
    rw [Complex.mul_re, Complex.log_re, Complex.log_im, hn]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.neg_im, Complex.add_im, Complex.mul_im]
    ring
  rw [hre, Real.exp_add, Real.rpow_def_of_pos hpos]

lemma differentiableAt_W (p q : ℝ) {s : ℂ} (hs : 0 < s.im) : DifferentiableAt ℂ (W p q) s := by
  unfold W
  have hslit : -I * s ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => Complex.log (-I * s)) s :=
    DifferentiableAt.clog (by fun_prop) hslit
  exact DifferentiableAt.cexp (DifferentiableAt.mul (by fun_prop) h1)

lemma W_bounds (p q a b L T : ℝ) (hab : a ≤ b) (hT : 1 ≤ T)
    (hL : ∀ σ : ℝ, a ≤ σ → σ ≤ b → |p + q * σ| ≤ L) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im →
      ‖W p q s‖ ≤ E * s.im ^ (-(p + q * s.re)) ∧
        s.im ^ (-(p + q * s.re)) ≤ E * ‖W p q s‖ := by
  set D : ℝ := max |a| |b| with hD
  have hD0 : 0 ≤ D := le_max_of_le_left (abs_nonneg a)
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL a le_rfl hab)
  have hc1 : (1 : ℝ) ≤ 1 + D := by linarith
  have hcL : (1 : ℝ) ≤ (1 + D) ^ L := Real.one_le_rpow hc1 hL0
  have hqD : 0 ≤ |q| * D := mul_nonneg (abs_nonneg q) hD0
  refine ⟨Real.exp (|q| * D) * (1 + D) ^ L, ?_, ?_⟩
  · calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.exp (|q| * D) * (1 + D) ^ L :=
        mul_le_mul (Real.one_le_exp hqD) hcL zero_le_one (Real.exp_pos _).le
  intro s h1 h2 h3
  have ht1 : 1 ≤ s.im := hT.trans h3
  have ht0 : 0 < s.im := by linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at ht0
    simp at ht0
  have hσ : |s.re| ≤ D := abs_le_max_abs_abs h1 h2
  have hzre : (-I * s).re = s.im := by simp
  have hzim : (-I * s).im = -s.re := by simp
  have harg : |s.im * (-I * s).arg| ≤ D := by
    have h := abs_re_mul_arg_le (z := -I * s) (by rw [hzre]; exact ht0)
    rw [hzre, hzim, abs_neg] at h
    exact h.trans hσ
  have hqarg : |q * (s.im * (-I * s).arg)| ≤ |q| * D := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left harg (abs_nonneg q)
  have hexp_up : Real.exp (q * (s.im * (-I * s).arg)) ≤ Real.exp (|q| * D) :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans hqarg)
  have hexp_lo : Real.exp (-(|q| * D)) ≤ Real.exp (q * (s.im * (-I * s).arg)) :=
    Real.exp_le_exp.mpr (by linarith [neg_abs_le (q * (s.im * (-I * s).arg))])
  have hts : s.im ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_im_le_norm s)
  have hsc : ‖s‖ ≤ (1 + D) * s.im := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos ht0] at h
    nlinarith
  obtain ⟨hc_up, hc_lo⟩ := rpow_comparison (x := -(p + q * s.re)) (L := L) ht0 hts hsc
    (by rw [abs_neg]; exact hL _ h1 h2)
  have hrpow_t : 0 ≤ s.im ^ (-(p + q * s.re)) := Real.rpow_nonneg ht0.le _
  have hrpow_s : 0 ≤ ‖s‖ ^ (-(p + q * s.re)) := Real.rpow_nonneg (norm_nonneg _) _
  rw [norm_W p q s hs0]
  constructor
  · calc ‖s‖ ^ (-(p + q * s.re)) * Real.exp (q * (s.im * (-I * s).arg))
        ≤ ((1 + D) ^ L * s.im ^ (-(p + q * s.re))) * Real.exp (|q| * D) :=
          mul_le_mul hc_up hexp_up (Real.exp_pos _).le (by positivity)
      _ = Real.exp (|q| * D) * (1 + D) ^ L * s.im ^ (-(p + q * s.re)) := by ring
  · have hone : 1 ≤ Real.exp (|q| * D) * Real.exp (q * (s.im * (-I * s).arg)) := by
      calc (1 : ℝ) = Real.exp (|q| * D) * Real.exp (-(|q| * D)) := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ ≤ Real.exp (|q| * D) * Real.exp (q * (s.im * (-I * s).arg)) :=
          mul_le_mul_of_nonneg_left hexp_lo (Real.exp_pos _).le
    calc s.im ^ (-(p + q * s.re)) ≤ (1 + D) ^ L * ‖s‖ ^ (-(p + q * s.re)) := hc_lo
      _ = (1 + D) ^ L * ‖s‖ ^ (-(p + q * s.re)) * 1 := by ring
      _ ≤ (1 + D) ^ L * ‖s‖ ^ (-(p + q * s.re)) *
            (Real.exp (|q| * D) * Real.exp (q * (s.im * (-I * s).arg))) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ = Real.exp (|q| * D) * (1 + D) ^ L *
            (‖s‖ ^ (-(p + q * s.re)) * Real.exp (q * (s.im * (-I * s).arg))) := by ring

/-- Phragmén–Lindelöf convexity on the upper half-strip `a ≤ Re s ≤ b`, `Im s ≥ T`. -/
theorem upper (f : ℂ → ℂ) (a b α β M A T : ℝ) (hab : a < b) (hT : 1 ≤ T) (hA : 0 ≤ A)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im → DifferentiableAt ℂ f s)
    (hgrowth : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im → ‖f s‖ ≤ A * s.im ^ M)
    (ha : ∀ s : ℂ, s.re = a → T ≤ s.im → ‖f s‖ ≤ A * s.im ^ α)
    (hb : ∀ s : ℂ, s.re = b → T ≤ s.im → ‖f s‖ ≤ A * s.im ^ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im →
      ‖f s‖ ≤ C * s.im ^ (α * (b - s.re) / (b - a) + β * (s.re - a) / (b - a)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hba' : b - a ≠ 0 := hba.ne'
  set q : ℝ := (β - α) / (b - a) with hq
  set p : ℝ := (α * b - β * a) / (b - a) with hp
  have hℓ : ∀ σ : ℝ, p + q * σ = α * (b - σ) / (b - a) + β * (σ - a) / (b - a) := by
    intro σ
    rw [hp, hq]
    field_simp
    ring
  have hℓa : p + q * a = α := by
    rw [hℓ]
    field_simp
    ring
  have hℓb : p + q * b = β := by
    rw [hℓ]
    field_simp
    ring
  set L : ℝ := max |α| |β| with hLdef
  have hL : ∀ σ : ℝ, a ≤ σ → σ ≤ b → |p + q * σ| ≤ L := by
    intro σ h1 h2
    rw [hℓ]
    have hu : 0 ≤ (b - σ) / (b - a) := div_nonneg (by linarith) hba.le
    have hv : 0 ≤ (σ - a) / (b - a) := div_nonneg (by linarith) hba.le
    have huv : (b - σ) / (b - a) + (σ - a) / (b - a) = 1 := by
      field_simp
      ring
    have e : α * (b - σ) / (b - a) + β * (σ - a) / (b - a)
        = α * ((b - σ) / (b - a)) + β * ((σ - a) / (b - a)) := by ring
    rw [e]
    calc |α * ((b - σ) / (b - a)) + β * ((σ - a) / (b - a))|
        ≤ |α * ((b - σ) / (b - a))| + |β * ((σ - a) / (b - a))| := abs_add_le _ _
      _ = |α| * ((b - σ) / (b - a)) + |β| * ((σ - a) / (b - a)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hv]
      _ ≤ L * ((b - σ) / (b - a)) + L * ((σ - a) / (b - a)) :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hv)
      _ = L := by rw [← mul_add, huv, mul_one]
  obtain ⟨E, hE1, hE⟩ := W_bounds p q a b L T hab.le hT hL
  have hL0 : 0 ≤ L := le_max_of_le_left (abs_nonneg α)
  set M' : ℝ := |M| + L with hM'
  have hM'0 : 0 ≤ M' := add_nonneg (abs_nonneg M) hL0
  have hE0 : 0 ≤ E := by linarith
  have hT0 : 0 < T := by linarith
  have hTM : 1 ≤ T ^ M' := Real.one_le_rpow hT hM'0
  set K : ℝ := A * E * T ^ M' with hK
  have hAE0 : 0 ≤ A * E := mul_nonneg hA hE0
  have hK0 : 0 ≤ K := mul_nonneg hAE0 (by linarith)
  have hAEK : A * E ≤ K := le_mul_of_one_le_right hAE0 hTM
  let g : ℂ → ℂ := fun s => f s * W p q s
  have hg_norm : ∀ s : ℂ, ‖g s‖ = ‖f s‖ * ‖W p q s‖ := fun s => norm_mul _ _
  have hg_growth : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im → ‖g s‖ ≤ A * E * s.im ^ M' := by
    intro s h1 h2 h3
    have ht : 1 ≤ s.im := hT.trans h3
    have ht0 : 0 < s.im := by linarith
    have hW := (hE s h1 h2 h3).1
    have hf := hgrowth s h1 h2 h3
    have e1 : s.im ^ M ≤ s.im ^ |M| := Real.rpow_le_rpow_of_exponent_le ht (le_abs_self M)
    have e2 : s.im ^ (-(p + q * s.re)) ≤ s.im ^ L :=
      Real.rpow_le_rpow_of_exponent_le ht ((neg_le_abs _).trans (hL _ h1 h2))
    have n1 : 0 ≤ s.im ^ M := Real.rpow_nonneg ht0.le _
    have n2 : 0 ≤ s.im ^ (-(p + q * s.re)) := Real.rpow_nonneg ht0.le _
    have n3 : 0 ≤ s.im ^ |M| := Real.rpow_nonneg ht0.le _
    calc ‖g s‖ = ‖f s‖ * ‖W p q s‖ := hg_norm s
      _ ≤ (A * s.im ^ M) * (E * s.im ^ (-(p + q * s.re))) :=
          mul_le_mul hf hW (norm_nonneg _) (mul_nonneg hA n1)
      _ ≤ (A * s.im ^ |M|) * (E * s.im ^ L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left e1 hA) (mul_le_mul_of_nonneg_left e2 hE0)
            (mul_nonneg hE0 n2) (mul_nonneg hA n3)
      _ = A * E * s.im ^ M' := by
          rw [hM', Real.rpow_add ht0]
          ring
  have hg_edge : ∀ (γ : ℝ) (s : ℂ), a ≤ s.re → s.re ≤ b → T ≤ s.im → p + q * s.re = γ →
      ‖f s‖ ≤ A * s.im ^ γ → ‖g s‖ ≤ K := by
    intro γ s h1 h2 h3 hγ hf
    have ht0 : 0 < s.im := by linarith
    have hW := (hE s h1 h2 h3).1
    rw [hγ] at hW
    have n1 : 0 ≤ s.im ^ γ := Real.rpow_nonneg ht0.le _
    calc ‖g s‖ = ‖f s‖ * ‖W p q s‖ := hg_norm s
      _ ≤ (A * s.im ^ γ) * (E * s.im ^ (-γ)) :=
          mul_le_mul hf hW (norm_nonneg _) (mul_nonneg hA n1)
      _ = A * E * (s.im ^ γ * s.im ^ (-γ)) := by ring
      _ = A * E := by rw [← Real.rpow_add ht0, add_neg_cancel, Real.rpow_zero, mul_one]
      _ ≤ K := hAEK
  have hg_bottom : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s.im = T → ‖g s‖ ≤ K := by
    intro s h1 h2 h3
    have h := hg_growth s h1 h2 h3.ge
    rwa [h3] at h
  have hg_diff : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im → DifferentiableAt ℂ g s :=
    fun s h1 h2 h3 => (hd s h1 h2 h3).mul (differentiableAt_W p q (by linarith))
  -- the maximum principle on rectangles, with the damping factor `exp (i ε s)`
  have key : ∀ ε : ℝ, 0 < ε → ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im →
      ‖g s‖ ≤ K * Real.exp (ε * s.im) := by
    intro ε hε s h1 h2 h3
    have htend := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero M' ε hε
    obtain ⟨Y0, hY0⟩ := eventually_atTop.mp (htend.eventually (eventually_le_nhds one_pos))
    set Y : ℝ := max (max Y0 s.im) (T + 1) with hYdef
    have hY0' : Y0 ≤ Y := (le_max_left _ _).trans (le_max_left _ _)
    have hsY : s.im ≤ Y := (le_max_right _ _).trans (le_max_left _ _)
    have hTY : T < Y := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    let U : Set ℂ := Ioo a b ×ℂ Ioo T Y
    have hUcl : closure U = Icc a b ×ℂ Icc T Y := by
      rw [Complex.closure_reProdIm, closure_Ioo hab.ne, closure_Ioo hTY.ne]
    have hUopen : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
    have hUbdd : Bornology.IsBounded U :=
      (Metric.isBounded_Ioo a b).reProdIm (Metric.isBounded_Ioo T Y)
    let h : ℂ → ℂ := fun z => g z * cexp (I * ε * z)
    have hnorm_h : ∀ z : ℂ, ‖h z‖ = ‖g z‖ * Real.exp (-(ε * z.im)) := by
      intro z
      have hre : (I * ε * z).re = -(ε * z.im) := by simp
      simp only [h, norm_mul, Complex.norm_exp, hre]
    have hdiff : DiffContOnCl ℂ h U := by
      apply DifferentiableOn.diffContOnCl
      rw [hUcl]
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      exact ((hg_diff z hz1.1 hz1.2 hz2.1).mul (by fun_prop)).differentiableWithinAt
    have hfront : ∀ z ∈ frontier U, ‖h z‖ ≤ K := by
      intro z hz
      rw [frontier, hUopen.interior_eq, hUcl] at hz
      obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
      have hzim : 0 < z.im := lt_of_lt_of_le hT0 hz2.1
      have hexp_le : Real.exp (-(ε * z.im)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε.le hzim.le))
      rw [hnorm_h]
      by_cases hre_a : z.re = a
      · exact (mul_le_of_le_one_right (norm_nonneg _) hexp_le).trans
          (hg_edge α z hz1.1 hz1.2 hz2.1 (by rw [hre_a, hℓa]) (ha z hre_a hz2.1))
      by_cases hre_b : z.re = b
      · exact (mul_le_of_le_one_right (norm_nonneg _) hexp_le).trans
          (hg_edge β z hz1.1 hz1.2 hz2.1 (by rw [hre_b, hℓb]) (hb z hre_b hz2.1))
      by_cases him_T : z.im = T
      · exact (mul_le_of_le_one_right (norm_nonneg _) hexp_le).trans
          (hg_bottom z hz1.1 hz1.2 him_T)
      have him_Y : z.im = Y := by
        by_contra hne
        exact hz3 ⟨⟨lt_of_le_of_ne hz1.1 (Ne.symm hre_a), lt_of_le_of_ne hz1.2 hre_b⟩,
          ⟨lt_of_le_of_ne hz2.1 (Ne.symm him_T), lt_of_le_of_ne hz2.2 hne⟩⟩
      have hgz := hg_growth z hz1.1 hz1.2 hz2.1
      have hYb : Y ^ M' * Real.exp (-ε * Y) ≤ 1 := hY0 Y hY0'
      calc ‖g z‖ * Real.exp (-(ε * z.im))
          ≤ (A * E * z.im ^ M') * Real.exp (-(ε * z.im)) :=
            mul_le_mul_of_nonneg_right hgz (Real.exp_pos _).le
        _ = A * E * (Y ^ M' * Real.exp (-ε * Y)) := by
            rw [him_Y, neg_mul]
            ring
        _ ≤ A * E * 1 := mul_le_mul_of_nonneg_left hYb hAE0
        _ ≤ K := by
            rw [mul_one]
            exact hAEK
    have hs_mem : s ∈ closure U := by
      rw [hUcl]
      exact ⟨⟨h1, h2⟩, ⟨h3, hsY⟩⟩
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hUbdd hdiff hfront hs_mem
    rw [hnorm_h] at hmax
    calc ‖g s‖ = ‖g s‖ * Real.exp (-(ε * s.im)) * Real.exp (ε * s.im) := by
          rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ K * Real.exp (ε * s.im) := mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le
  have hgK : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im → ‖g s‖ ≤ K := by
    intro s h1 h2 h3
    have hcont : Continuous fun ε : ℝ => K * Real.exp (ε * s.im) := by fun_prop
    have ht : Tendsto (fun ε : ℝ => K * Real.exp (ε * s.im)) (𝓝[>] 0) (𝓝 K) := by
      have h0 := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using h0
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => key ε hε s h1 h2 h3)
  refine ⟨E * K, mul_nonneg hE0 hK0, fun s h1 h2 h3 => ?_⟩
  have ht0 : 0 < s.im := by linarith
  have hW := (hE s h1 h2 h3).2
  have hgs := hgK s h1 h2 h3
  rw [← hℓ]
  have hmain : ‖f s‖ * s.im ^ (-(p + q * s.re)) ≤ E * K := by
    calc ‖f s‖ * s.im ^ (-(p + q * s.re)) ≤ ‖f s‖ * (E * ‖W p q s‖) :=
          mul_le_mul_of_nonneg_left hW (norm_nonneg _)
      _ = E * ‖g s‖ := by
          rw [hg_norm]
          ring
      _ ≤ E * K := mul_le_mul_of_nonneg_left hgs hE0
  calc ‖f s‖ = ‖f s‖ * s.im ^ (-(p + q * s.re)) * s.im ^ (p + q * s.re) := by
        rw [mul_assoc, ← Real.rpow_add ht0, neg_add_cancel, Real.rpow_zero, mul_one]
    _ ≤ E * K * s.im ^ (p + q * s.re) :=
        mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg ht0.le _)

end HalfStripAux

open HalfStripAux in
theorem solution (f : ℂ → ℂ) (a b α β M A T : ℝ) (hab : a < b) (hT : 1 ≤ T)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → DifferentiableAt ℂ f s)
    (hgrowth : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖f s‖ ≤ A * |s.im| ^ M)
    (ha : ∀ t : ℝ, T ≤ |t| → ‖f ((a : ℂ) + t * Complex.I)‖ ≤ A * |t| ^ α)
    (hb : ∀ t : ℝ, T ≤ |t| → ‖f ((b : ℂ) + t * Complex.I)‖ ≤ A * |t| ^ β) :
    ∃ C T' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T' ≤ |s.im| →
      ‖f s‖ ≤ C * |s.im| ^ (α * (b - s.re) / (b - a) + β * (s.re - a) / (b - a)) := by
  have hT0 : 0 < T := by linarith
  -- the constant `A` is nonnegative, since it bounds a norm at a point of the half-strip
  have hA : 0 ≤ A := by
    have h := hgrowth ((a : ℂ) + T * Complex.I) (by simp) (by simpa using hab.le)
      (by simp [abs_of_pos hT0])
    have h0 : 0 ≤ A * |((a : ℂ) + T * Complex.I).im| ^ M := (norm_nonneg _).trans h
    have him : ((a : ℂ) + T * Complex.I).im = T := by simp
    have hpos : 0 < |((a : ℂ) + T * Complex.I).im| ^ M := by
      apply Real.rpow_pos_of_pos
      rw [him]
      exact abs_pos.mpr hT0.ne'
    exact nonneg_of_mul_nonneg_left h0 hpos
  have hedge : ∀ (c : ℝ) (s : ℂ), s.re = c → s = (c : ℂ) + s.im * Complex.I := by
    intro c s hs
    apply Complex.ext <;> simp [hs]
  -- upper half-strip
  obtain ⟨C₁, hC₁0, hC₁⟩ := upper f a b α β M A T hab hT hA
    (fun s h1 h2 h3 => hd s h1 h2 (h3.trans (le_abs_self _)))
    (fun s h1 h2 h3 => by
      have h := hgrowth s h1 h2 (h3.trans (le_abs_self _))
      rwa [abs_of_pos (lt_of_lt_of_le hT0 h3)] at h)
    (fun s h1 h3 => by
      have h := ha s.im (h3.trans (le_abs_self _))
      rwa [← hedge a s h1, abs_of_pos (lt_of_lt_of_le hT0 h3)] at h)
    (fun s h1 h3 => by
      have h := hb s.im (h3.trans (le_abs_self _))
      rwa [← hedge b s h1, abs_of_pos (lt_of_lt_of_le hT0 h3)] at h)
  -- lower half-strip, via `s ↦ -s`
  obtain ⟨C₂, hC₂0, hC₂⟩ := upper (fun s => f (-s)) (-b) (-a) β α M A T (by linarith) hT hA
    (fun s h1 h2 h3 => by
      have h3' : T ≤ |(-s).im| := by
        rw [Complex.neg_im, abs_neg]
        exact h3.trans (le_abs_self _)
      have hd' := hd (-s) (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith) h3'
      exact hd'.comp s differentiable_neg.differentiableAt)
    (fun s h1 h2 h3 => by
      have h3' : T ≤ |(-s).im| := by
        rw [Complex.neg_im, abs_neg]
        exact h3.trans (le_abs_self _)
      have h := hgrowth (-s) (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith)
        h3'
      rwa [Complex.neg_im, abs_neg, abs_of_pos (lt_of_lt_of_le hT0 h3)] at h)
    (fun s h1 h3 => by
      have h := hb (-s.im) (by rw [abs_neg]; exact h3.trans (le_abs_self _))
      have e : -s = (b : ℂ) + ((-s.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [h1]
      rwa [← e, abs_neg, abs_of_pos (lt_of_lt_of_le hT0 h3)] at h)
    (fun s h1 h3 => by
      have h := ha (-s.im) (by rw [abs_neg]; exact h3.trans (le_abs_self _))
      have e : -s = (a : ℂ) + ((-s.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [h1]
      rwa [← e, abs_neg, abs_of_pos (lt_of_lt_of_le hT0 h3)] at h)
  refine ⟨max C₁ C₂, T, fun s h1 h2 h3 => ?_⟩
  have hrpow : 0 ≤ |s.im| ^ (α * (b - s.re) / (b - a) + β * (s.re - a) / (b - a)) :=
    Real.rpow_nonneg (abs_nonneg _) _
  rcases le_total 0 s.im with him | him
  · rw [abs_of_nonneg him] at h3 ⊢
    exact (hC₁ s h1 h2 h3).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by rwa [abs_of_nonneg him] at hrpow))
  · rw [abs_of_nonpos him] at h3
    have h := hC₂ (-s) (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith)
      (by rw [Complex.neg_im]; exact h3)
    simp only [neg_neg, Complex.neg_re, Complex.neg_im] at h
    have hexp : β * (-a - -s.re) / (-a - -b) + α * (-s.re - -b) / (-a - -b)
        = α * (b - s.re) / (b - a) + β * (s.re - a) / (b - a) := by
      have e1 : -a - -b = b - a := by ring
      have e2 : -a - -s.re = s.re - a := by ring
      have e3 : -s.re - -b = b - s.re := by ring
      rw [e1, e2, e3]
      ring
    rw [hexp] at h
    rw [abs_of_nonpos him]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (by rwa [abs_of_nonpos him] at hrpow))
