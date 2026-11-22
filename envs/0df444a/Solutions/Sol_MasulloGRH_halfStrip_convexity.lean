-- Prove2me | solution 1 for MasulloGRH.halfStrip_convexity
-- status  : ACCEPTED   (prove)
-- author  : @flashonfire
-- created : 2026-11-21T19:30:22.684295+00:00
-- url     : https://prove2.me/submissions/6acf6fac-6270-47ba-9e7a-aadfaae17dcf

import Mathlib

set_option autoImplicit false

open Complex Set Filter Topology

namespace HalfStripPL

/-- Bounded Phragmén–Lindelöf on an upper half-strip, for functions of polynomial growth. -/
theorem bounded_upper (G : ℂ → ℂ) (a b T B K M : ℝ) (hab : a ≤ b) (hT : 0 < T)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ z.im → DifferentiableAt ℂ G z)
    (hg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ z.im → ‖G z‖ ≤ K * z.im ^ M)
    (hbd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ z.im → (z.re = a ∨ z.re = b ∨ z.im = T) →
      ‖G z‖ ≤ B) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T ≤ z.im → ‖G z‖ ≤ B := by
  intro z hza hzb hzT
  have hB : 0 ≤ B := by
    have := hbd ⟨a, T⟩ le_rfl hab le_rfl (Or.inl rfl)
    exact (norm_nonneg _).trans this
  by_cases hbdry : z.re = a ∨ z.re = b ∨ z.im = T
  · exact hbd z hza hzb hzT hbdry
  push Not at hbdry
  obtain ⟨hza', hzb', hzT'⟩ := hbdry
  have hza2 : a < z.re := lt_of_le_of_ne hza (Ne.symm hza')
  have hzb2 : z.re < b := lt_of_le_of_ne hzb hzb'
  have hzT2 : T < z.im := lt_of_le_of_ne hzT (Ne.symm hzT')
  have hab2 : a < b := hza2.trans hzb2
  have hy : 0 < z.im := hT.trans hzT2
  have key : ∀ ε : ℝ, 0 < ε → ‖G z‖ ≤ (B + ε) * Real.exp ε := by
    intro ε hε
    set η : ℝ := ε / z.im with hη
    have hηpos : 0 < η := div_pos hε hy
    have hnexp : ∀ w : ℂ, ‖Complex.exp (I * η * w)‖ = Real.exp (-η * w.im) := by
      intro w; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
    obtain ⟨R, hR1, hR2⟩ : ∃ R : ℝ, z.im < R ∧ K * (R ^ M * Real.exp (-η * R)) < B + ε := by
      have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero M η hηpos).const_mul K
      rw [mul_zero] at ht
      exact ((eventually_gt_atTop z.im).and (ht.eventually (gt_mem_nhds (by linarith)))).exists
    set U : Set ℂ := Ioo a b ×ℂ Ioo T R
    have hTR : T < R := hzT2.trans hR1
    have hcl : closure U = Icc a b ×ℂ Icc T R := by
      simp only [U, closure_reProdIm, closure_Ioo hab2.ne, closure_Ioo hTR.ne]
    have hGη : DiffContOnCl ℂ (fun w => G w * Complex.exp (I * η * w)) U := by
      apply DifferentiableOn.diffContOnCl
      rw [hcl]
      intro w hw
      rw [Complex.mem_reProdIm] at hw
      exact ((hd w hw.1.1 hw.1.2 hw.2.1).mul
        ((differentiableAt_id.const_mul (I * η)).cexp)).differentiableWithinAt
    have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le
      ((Metric.isBounded_Ioo a b).reProdIm (Metric.isBounded_Ioo T R)) hGη
      (C := B + ε) ?_ (subset_closure (show z ∈ U from
        (Complex.mem_reProdIm).2 ⟨⟨hza2, hzb2⟩, ⟨hzT2, hR1⟩⟩))
    · rw [norm_mul, hnexp] at hbound
      have hexp : Real.exp (-η * z.im) * Real.exp ε = 1 := by
        rw [← Real.exp_add, hη]
        have : -(ε / z.im) * z.im + ε = 0 := by field_simp; ring
        rw [this, Real.exp_zero]
      calc ‖G z‖ = ‖G z‖ * Real.exp (-η * z.im) * Real.exp ε := by
            rw [mul_assoc, hexp, mul_one]
        _ ≤ (B + ε) * Real.exp ε :=
            mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le
    · intro w hw
      rw [frontier_reProdIm, closure_Ioo hab2.ne, closure_Ioo hTR.ne, frontier_Ioo hab2,
        frontier_Ioo hTR] at hw
      rw [norm_mul, hnexp]
      have hle1 : ∀ y : ℝ, T ≤ y → Real.exp (-η * y) ≤ 1 := fun y hy' =>
        Real.exp_le_one_iff.2 (by nlinarith)
      rcases hw with hw | hw
      · rw [Complex.mem_reProdIm] at hw
        obtain ⟨⟨hwa, hwb⟩, hwim⟩ := hw
        rcases hwim with hwT | hwR
        · have hwT' : w.im = T := hwT
          calc ‖G w‖ * Real.exp (-η * w.im) ≤ B * 1 :=
                mul_le_mul (hbd w hwa hwb hwT'.ge (Or.inr (Or.inr hwT')))
                  (hle1 _ hwT'.ge) (Real.exp_pos _).le hB
            _ ≤ B + ε := by linarith
        · have hwR' : w.im = R := hwR
          have hg' := hg w hwa hwb (by rw [hwR']; exact hTR.le)
          rw [hwR'] at hg' ⊢
          calc ‖G w‖ * Real.exp (-η * R) ≤ K * R ^ M * Real.exp (-η * R) :=
                mul_le_mul_of_nonneg_right hg' (Real.exp_pos _).le
            _ ≤ B + ε := by rw [mul_assoc]; exact hR2.le
      · rw [Complex.mem_reProdIm] at hw
        obtain ⟨hwre, ⟨hwT, hwR⟩⟩ := hw
        have hwa : a ≤ w.re := by rcases hwre with h | h <;> simp_all [Set.mem_singleton_iff]
        have hwb : w.re ≤ b := by
          rcases hwre with h | h
          · rw [Set.mem_singleton_iff.1 h]; exact hab
          · rw [Set.mem_singleton_iff.1 h]
        have hor : w.re = a ∨ w.re = b ∨ w.im = T := by
          rcases hwre with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        calc ‖G w‖ * Real.exp (-η * w.im) ≤ B * 1 :=
              mul_le_mul (hbd w hwa hwb hwT hor) (hle1 _ hwT) (Real.exp_pos _).le hB
          _ ≤ B + ε := by linarith
  have ht : Tendsto (fun ε : ℝ => (B + ε) * Real.exp ε) (𝓝[>] 0) (𝓝 B) := by
    have : Tendsto (fun ε : ℝ => (B + ε) * Real.exp ε) (𝓝 0) (𝓝 ((B + 0) * Real.exp 0)) :=
      ((continuous_const.add continuous_id).mul Real.continuous_exp).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

/-- The interpolation multiplier `H(z) = (-i z)^{-(p + q z)}`. -/
noncomputable def mult (p q : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-((p : ℂ) + (q : ℂ) * z) * Complex.log (-I * z))

theorem mult_differentiableAt (p q : ℝ) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (mult p q) z := by
  unfold mult
  have hslit : -I * z ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simpa using hz
  exact (((differentiableAt_const _).add (differentiableAt_id.const_mul _)).neg.mul
    ((differentiableAt_id.const_mul (-I)).clog hslit)).cexp

theorem norm_mult (p q : ℝ) (z : ℂ) :
    ‖mult p q z‖ = Real.exp (-(p + q * z.re) * Real.log ‖z‖ + q * z.im * arg (-I * z)) := by
  unfold mult
  rw [Complex.norm_exp]
  congr 1
  have h1 : ‖-I * z‖ = ‖z‖ := by simp
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.log_re, Complex.log_im, h1]
  ring

/-- `|arg(-i z)| ≤ (π/2) |Re z| / ‖z‖` in the upper half-plane (Jordan's inequality). -/
theorem abs_arg_le (z : ℂ) (hz : 0 < z.im) :
    |arg (-I * z)| ≤ Real.pi / 2 * (|z.re| / ‖z‖) := by
  set w := -I * z
  have hwre : 0 ≤ w.re := by simp [w]; exact hz.le
  have hpi := Complex.abs_arg_le_pi_div_two_iff.2 hwre
  have hsin : Real.sin (arg w) = -z.re / ‖z‖ := by
    rw [Complex.sin_arg]; simp [w]
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by simp [h] at hz)
  have hjordan : 2 / Real.pi * |arg w| ≤ |Real.sin (arg w)| := by
    rcases le_total 0 (arg w) with h | h
    · rw [abs_of_nonneg h]
      have := Real.mul_le_sin h (by rw [abs_of_nonneg h] at hpi; exact hpi)
      exact this.trans (le_abs_self _)
    · rw [abs_of_nonpos h]
      have := Real.mul_le_sin (neg_nonneg.2 h) (by rw [abs_of_nonpos h] at hpi; exact hpi)
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  rw [hsin, abs_div, abs_neg, abs_of_pos hzn] at hjordan
  have hpi0 : 0 < Real.pi := Real.pi_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ hpi0] at hjordan
  nlinarith [abs_nonneg (arg w), div_nonneg (abs_nonneg z.re) hzn.le]

/-- Two-sided bounds `‖H z‖ ≍ (Im z)^{-(p + q Re z)}` on a half-strip. -/
theorem mult_bounds (p q a b : ℝ) : ∃ D : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
    |a| + |b| + 1 ≤ z.im →
    Real.exp (-D) * z.im ^ (-(p + q * z.re)) ≤ ‖mult p q z‖ ∧
      ‖mult p q z‖ ≤ Real.exp D * z.im ^ (-(p + q * z.re)) := by
  set R0 := |a| + |b|
  set Lm := |p| + |q| * R0
  refine ⟨Lm * Real.log 2 + |q| * (Real.pi / 2 * R0), fun z hza hzb hzT => ?_⟩
  set x := z.re
  set y := z.im
  have hR0 : 0 ≤ R0 := by positivity
  have hy1 : 1 ≤ y := by linarith
  have hy : 0 < y := by linarith
  have hx : |x| ≤ R0 := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self b, abs_nonneg a]
    · rw [abs_of_nonpos h]; linarith [neg_abs_le a, abs_nonneg b]
  have hzn : y ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)
  have hzn2 : ‖z‖ ≤ 2 * y := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hy] at this
    linarith
  have hzpos : 0 < ‖z‖ := hy.trans_le hzn
  -- the logarithmic error
  set Δ := Real.log ‖z‖ - Real.log y
  have hΔ0 : 0 ≤ Δ := sub_nonneg.2 (Real.log_le_log hy hzn)
  have hΔ1 : Δ ≤ Real.log 2 := by
    have := Real.log_le_log hzpos hzn2
    rw [Real.log_mul (by norm_num) hy.ne'] at this
    simp only [Δ]; linarith
  have hℓ : |p + q * x| ≤ Lm := by
    calc |p + q * x| ≤ |p| + |q| * |x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Lm := by simp only [Lm]; gcongr
  have herr1 : |(p + q * x) * Δ| ≤ Lm * Real.log 2 := by
    rw [abs_mul, abs_of_nonneg hΔ0]
    exact mul_le_mul hℓ hΔ1 hΔ0 ((abs_nonneg _).trans hℓ)
  have harg := abs_arg_le z hy
  have herr2 : |q * y * arg (-I * z)| ≤ |q| * (Real.pi / 2 * R0) := by
    rw [abs_mul, abs_mul, abs_of_pos hy, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg q)
    calc y * |arg (-I * z)| ≤ y * (Real.pi / 2 * (|x| / ‖z‖)) :=
          mul_le_mul_of_nonneg_left harg hy.le
      _ = Real.pi / 2 * (|x| * (y / ‖z‖)) := by ring
      _ ≤ Real.pi / 2 * (R0 * 1) := by
          gcongr
          · exact (div_le_one hzpos).2 hzn
      _ = Real.pi / 2 * R0 := by ring
  have hrpow : y ^ (-(p + q * x)) = Real.exp (-(p + q * x) * Real.log y) := by
    rw [Real.rpow_def_of_pos hy]; ring_nf
  have hE : -(p + q * x) * Real.log ‖z‖ + q * y * arg (-I * z) =
      -(p + q * x) * Real.log y - (p + q * x) * Δ + q * y * arg (-I * z) := by
    simp only [Δ]; ring
  rw [norm_mult, hrpow, hE, ← Real.exp_add, ← Real.exp_add]
  have h1 := abs_le.1 herr1
  have h2 := abs_le.1 herr2
  constructor
  · apply Real.exp_le_exp.2; linarith
  · apply Real.exp_le_exp.2; linarith

/-- Phragmén–Lindelöf convexity on the upper half-strip. -/
theorem upper (f : ℂ → ℂ) (a b α β M A T : ℝ) (hab : a < b) (hT : 1 ≤ T)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im → DifferentiableAt ℂ f s)
    (hg : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ s.im → ‖f s‖ ≤ A * s.im ^ M)
    (ha : ∀ t : ℝ, T ≤ t → ‖f ((a : ℂ) + t * I)‖ ≤ A * t ^ α)
    (hb : ∀ t : ℝ, T ≤ t → ‖f ((b : ℂ) + t * I)‖ ≤ A * t ^ β) :
    ∃ C T' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T' ≤ s.im →
      ‖f s‖ ≤ C * s.im ^ (α * (b - s.re) / (b - a) + β * (s.re - a) / (b - a)) := by
  have hba : 0 < b - a := sub_pos.2 hab
  set p : ℝ := (α * b - β * a) / (b - a)
  set q : ℝ := (β - α) / (b - a)
  have hℓ : ∀ x : ℝ, p + q * x = α * (b - x) / (b - a) + β * (x - a) / (b - a) := by
    intro x; simp only [p, q]; field_simp; ring
  have hℓa : p + q * a = α := by rw [hℓ]; field_simp; ring
  have hℓb : p + q * b = β := by rw [hℓ]; field_simp; ring
  obtain ⟨D, hD⟩ := mult_bounds p q a b
  set T0 : ℝ := max T (|a| + |b| + 1)
  have hT0T : T ≤ T0 := le_max_left _ _
  have hT0R : |a| + |b| + 1 ≤ T0 := le_max_right _ _
  have hT01 : 1 ≤ T0 := hT.trans hT0T
  set G : ℂ → ℂ := fun z => f z * mult p q z
  set Lm : ℝ := |p| + |q| * (|a| + |b|)
  have hℓbound : ∀ x : ℝ, a ≤ x → x ≤ b → |p + q * x| ≤ Lm := by
    intro x hxa hxb
    have hx : |x| ≤ |a| + |b| := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self b, abs_nonneg a]
      · rw [abs_of_nonpos h]; linarith [neg_abs_le a, abs_nonneg b]
    calc |p + q * x| ≤ |p| + |q| * |x| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Lm := by simp only [Lm]; gcongr
  have hdG : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T0 ≤ z.im → DifferentiableAt ℂ G z :=
    fun z h1 h2 h3 => (hd z h1 h2 (hT0T.trans h3)).mul
      (mult_differentiableAt p q (by linarith))
  -- polynomial growth of `G`
  have hgG : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T0 ≤ z.im →
      ‖G z‖ ≤ (|A| * Real.exp D) * z.im ^ (M + Lm) := by
    intro z h1 h2 h3
    have hy : 0 < z.im := by linarith
    have hy1 : 1 ≤ z.im := hT01.trans h3
    have hf := (hg z h1 h2 (hT0T.trans h3)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.rpow_nonneg hy.le _))
    have hH := (hD z h1 h2 (hT0R.trans h3)).2
    have hpow : z.im ^ (-(p + q * z.re)) ≤ z.im ^ Lm :=
      Real.rpow_le_rpow_of_exponent_le hy1
        ((neg_le_abs _).trans (hℓbound z.re h1 h2))
    calc ‖G z‖ = ‖f z‖ * ‖mult p q z‖ := norm_mul _ _
      _ ≤ (|A| * z.im ^ M) * (Real.exp D * z.im ^ Lm) :=
          mul_le_mul hf (hH.trans (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le))
            (norm_nonneg _) (by positivity)
      _ = (|A| * Real.exp D) * z.im ^ (M + Lm) := by
          rw [Real.rpow_add hy M Lm]; ring
  -- boundary values of `G`
  have hedge : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → T0 ≤ z.im → (z.re = a ∨ z.re = b) →
      ‖G z‖ ≤ |A| * Real.exp D := by
    intro z h1 h2 h3 hre
    have hy : 0 < z.im := by linarith
    have hH := (hD z h1 h2 (hT0R.trans h3)).2
    have key : ∀ (c γ : ℝ), z.re = c → p + q * c = γ → ‖f z‖ ≤ A * z.im ^ γ →
        ‖G z‖ ≤ |A| * Real.exp D := by
      intro c γ hc hγ hfz
      rw [hc, hγ] at hH
      have hfz' := hfz.trans
        (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.rpow_nonneg hy.le _))
      calc ‖G z‖ = ‖f z‖ * ‖mult p q z‖ := norm_mul _ _
        _ ≤ (|A| * z.im ^ γ) * (Real.exp D * z.im ^ (-γ)) :=
            mul_le_mul hfz' hH (norm_nonneg _) (by positivity)
        _ = |A| * Real.exp D * (z.im ^ γ * z.im ^ (-γ)) := by ring
        _ = |A| * Real.exp D := by
            rw [← Real.rpow_add hy, add_neg_cancel, Real.rpow_zero, mul_one]
    have hzeq : ∀ c : ℝ, z.re = c → z = (c : ℂ) + (z.im : ℂ) * I := by
      intro c hc; apply Complex.ext <;> simp [hc]
    rcases hre with hre | hre
    · refine key a α hre hℓa ?_
      rw [hzeq a hre]; simpa using ha z.im (hT0T.trans h3)
    · refine key b β hre hℓb ?_
      rw [hzeq b hre]; simpa using hb z.im (hT0T.trans h3)
  obtain ⟨Bs, hBs⟩ := (isCompact_Icc.reProdIm (isCompact_singleton (x := T0))).exists_bound_of_continuousOn
    (f := G) (fun z hz => by
      rw [Complex.mem_reProdIm] at hz
      exact (hdG z hz.1.1 hz.1.2 (le_of_eq (Set.mem_singleton_iff.1 hz.2).symm)).continuousAt.continuousWithinAt)
  set B : ℝ := max (|A| * Real.exp D) Bs
  have hbound := bounded_upper G a b T0 B (|A| * Real.exp D) (M + Lm) hab.le (by linarith)
    hdG hgG (by
      intro z h1 h2 h3 hor
      rcases hor with h | h | h
      · exact (hedge z h1 h2 h3 (Or.inl h)).trans (le_max_left _ _)
      · exact (hedge z h1 h2 h3 (Or.inr h)).trans (le_max_left _ _)
      · exact (hBs z ((Complex.mem_reProdIm).2 ⟨⟨h1, h2⟩, Set.mem_singleton_iff.2 h⟩)).trans
          (le_max_right _ _))
  refine ⟨B * Real.exp D, T0, fun s h1 h2 h3 => ?_⟩
  have hy : 0 < s.im := by linarith
  have hGs := hbound s h1 h2 h3
  have hH := (hD s h1 h2 (hT0R.trans h3)).1
  rw [← hℓ s.re]
  set ℓ := p + q * s.re
  have hpos : 0 < Real.exp (-D) * s.im ^ (-ℓ) := by positivity
  have h4 : ‖f s‖ * (Real.exp (-D) * s.im ^ (-ℓ)) ≤ B := by
    calc ‖f s‖ * (Real.exp (-D) * s.im ^ (-ℓ)) ≤ ‖f s‖ * ‖mult p q s‖ :=
          mul_le_mul_of_nonneg_left hH (norm_nonneg _)
      _ = ‖G s‖ := (norm_mul _ _).symm
      _ ≤ B := hGs
  have h5 := (le_div_iff₀ hpos).2 h4
  have h6 : B / (Real.exp (-D) * s.im ^ (-ℓ)) = B * Real.exp D * s.im ^ ℓ := by
    rw [Real.rpow_neg hy.le, Real.exp_neg]
    have : 0 < s.im ^ ℓ := Real.rpow_pos_of_pos hy _
    field_simp
  rw [h6] at h5
  exact h5

end HalfStripPL

open HalfStripPL ComplexConjugate in
theorem solution (f : ℂ → ℂ) (a b α β M A T : ℝ) (hab : a < b) (hT : 1 ≤ T)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → DifferentiableAt ℂ f s)
    (hgrowth : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖f s‖ ≤ A * |s.im| ^ M)
    (ha : ∀ t : ℝ, T ≤ |t| → ‖f ((a : ℂ) + t * Complex.I)‖ ≤ A * |t| ^ α)
    (hb : ∀ t : ℝ, T ≤ |t| → ‖f ((b : ℂ) + t * Complex.I)‖ ≤ A * |t| ^ β) :
    ∃ C T' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T' ≤ |s.im| →
      ‖f s‖ ≤ C * |s.im| ^ (α * (b - s.re) / (b - a) + β * (s.re - a) / (b - a)) := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  -- upper half-strip
  obtain ⟨C1, T1, h1⟩ := upper f a b α β M A T hab hT
    (fun s h1 h2 h3 => hd s h1 h2 (h3.trans (le_abs_self _)))
    (fun s h1 h2 h3 => by
      have := hgrowth s h1 h2 (h3.trans (le_abs_self _))
      rwa [abs_of_nonneg (hT0.trans h3)] at this)
    (fun t ht => by
      have := ha t (ht.trans (le_abs_self _)); rwa [abs_of_nonneg (hT0.trans ht)] at this)
    (fun t ht => by
      have := hb t (ht.trans (le_abs_self _)); rwa [abs_of_nonneg (hT0.trans ht)] at this)
  -- lower half-strip, via `conj ∘ f ∘ conj`
  set g : ℂ → ℂ := conj ∘ f ∘ conj with hg_def
  have hgval : ∀ z, g z = conj (f (conj z)) := fun z => rfl
  have hconj_edge : ∀ (c t : ℝ), conj ((c : ℂ) + t * Complex.I) = (c : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by
    intro c t; apply Complex.ext <;> simp
  obtain ⟨C2, T2, h2⟩ := upper g a b α β M A T hab hT
    (fun s h1 h2 h3 => by
      have hdc := (hd (conj s) (by simpa using h1) (by simpa using h2)
        (by simpa [abs_of_nonneg (hT0.trans h3)] using h3)).conj_conj
      rw [Complex.conj_conj] at hdc; exact hdc)
    (fun s h1 h2 h3 => by
      have := hgrowth (conj s) (by simpa using h1) (by simpa using h2)
        (by simpa [abs_of_nonneg (hT0.trans h3)] using h3)
      rw [hgval, RCLike.norm_conj]
      simpa [abs_of_nonneg (hT0.trans h3)] using this)
    (fun t ht => by
      rw [hgval, RCLike.norm_conj, hconj_edge]
      have := ha (-t) (by rw [abs_neg]; exact ht.trans (le_abs_self _))
      rwa [abs_neg, abs_of_nonneg (hT0.trans ht)] at this)
    (fun t ht => by
      rw [hgval, RCLike.norm_conj, hconj_edge]
      have := hb (-t) (by rw [abs_neg]; exact ht.trans (le_abs_self _))
      rwa [abs_neg, abs_of_nonneg (hT0.trans ht)] at this)
  refine ⟨max C1 C2, max T1 T2, fun s hs1 hs2 hs3 => ?_⟩
  have hnn : 0 ≤ |s.im| ^ (α * (b - s.re) / (b - a) + β * (s.re - a) / (b - a)) :=
    Real.rpow_nonneg (abs_nonneg _) _
  rcases le_total 0 s.im with him | him
  · rw [abs_of_nonneg him] at hs3 hnn ⊢
    exact (h1 s hs1 hs2 (le_trans (le_max_left _ _) hs3)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn)
  · have hc := h2 (conj s) (by simpa using hs1) (by simpa using hs2)
      (by simp only [Complex.conj_im]; rw [abs_of_nonpos him] at hs3;
          exact le_trans (le_max_right _ _) hs3)
    rw [hgval, RCLike.norm_conj, Complex.conj_conj] at hc
    simp only [Complex.conj_re, Complex.conj_im] at hc
    rw [abs_of_nonpos him]
    rw [abs_of_nonpos him] at hnn
    exact hc.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnn)
