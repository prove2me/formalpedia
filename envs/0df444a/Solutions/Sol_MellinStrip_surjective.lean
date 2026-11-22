-- Prove2me | solution 1 for MellinStrip.surjective
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T08:17:59.591407+00:00
-- url     : https://prove2.me/submissions/2a432f0d-d3dd-4d3c-9403-06a2337ce130

import Mathlib
import Theorems.Thm_OAI_VerticalContourShift_integral_eq_of_strip_decay

set_option autoImplicit false

open MeasureTheory FourierTransform

namespace B4Aux

def D (I : Set ℝ) : Set ℂ := {s : ℂ | s.re ∈ I}

lemma isOpen_D {I : Set ℝ} (hI : IsOpen I) : IsOpen (D I) := hI.preimage Complex.continuous_re

def Q (I : Set ℝ) (G : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ G (D I) ∧ ∀ α β : ℝ, Set.Icc α β ⊆ I → ∀ N : ℕ, ∃ C : ℝ,
    ∀ s : ℂ, α ≤ s.re → s.re ≤ β → ‖s ^ N * G s‖ ≤ C

lemma add_pow_le_two (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    (u + v) ^ n ≤ 2 ^ n * (u ^ n + v ^ n) := by
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rcases le_total u v with h | h
  · calc (u + v) ^ n ≤ (2 * v) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * v ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (u ^ n + v ^ n) := by have := pow_nonneg hu n; nlinarith
  · calc (u + v) ^ n ≤ (2 * u) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2 ^ n * u ^ n := mul_pow _ _ _
      _ ≤ 2 ^ n * (u ^ n + v ^ n) := by have := pow_nonneg hv n; nlinarith

lemma re_close {z s : ℂ} {r : ℝ} (h : dist z s ≤ r) : |z.re - s.re| ≤ r := by
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm (z - s)).trans (by rwa [← dist_eq_norm])

lemma Q_deriv {I : Set ℝ} (hI : IsOpen I) (hI' : I.OrdConnected) {G : ℂ → ℂ} (hG : Q I G) :
    Q I (deriv G) := by
  refine ⟨hG.1.deriv (isOpen_D hI), fun α β hab N => ?_⟩
  by_cases h : α ≤ β
  swap
  · exact ⟨0, fun s h1 h2 => absurd (h1.trans h2) h⟩
  have hα : α ∈ I := hab ⟨le_refl _, h⟩
  have hβ : β ∈ I := hab ⟨h, le_refl _⟩
  obtain ⟨ε1, hε1, hb1⟩ := Metric.isOpen_iff.1 hI α hα
  obtain ⟨ε2, hε2, hb2⟩ := Metric.isOpen_iff.1 hI β hβ
  set r := min ε1 ε2 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < ε1 := by have := min_le_left ε1 ε2; linarith
  have hr2 : r < ε2 := by have := min_le_right ε1 ε2; linarith
  have hlo : α - r ∈ I := hb1 (by
    rw [Metric.mem_ball, Real.dist_eq, show α - r - α = -r by ring, abs_neg, abs_of_pos hr0]
    exact hr1)
  have hhi : β + r ∈ I := hb2 (by
    rw [Metric.mem_ball, Real.dist_eq, show β + r - β = r by ring, abs_of_pos hr0]
    exact hr2)
  have hsub : Set.Icc (α - r) (β + r) ⊆ I := hI'.out hlo hhi
  obtain ⟨CN, hCN⟩ := hG.2 _ _ hsub N
  obtain ⟨C0, hC0⟩ := hG.2 _ _ hsub 0
  refine ⟨2 ^ N * (CN + r ^ N * C0) / r, fun s h1 h2 => ?_⟩
  have hball : ∀ z ∈ Metric.closedBall s r, z ∈ D I := by
    intro z hz
    have := abs_le.1 (re_close (Metric.mem_closedBall.1 hz))
    exact hsub ⟨by linarith, by linarith⟩
  have hdiff : DifferentiableOn ℂ (fun z => s ^ N * G z) (Metric.closedBall s r) :=
    ((differentiableOn_const _).mul hG.1).mono hball
  have hsD : s ∈ D I := hball s (Metric.mem_closedBall_self hr0.le)
  have hd : deriv (fun z => s ^ N * G z) s = s ^ N * deriv G s :=
    deriv_const_mul _ (hG.1.differentiableAt ((isOpen_D hI).mem_nhds hsD))
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0
    (DifferentiableOn.diffContOnCl (by rwa [closure_ball s hr0.ne']))
    (C := 2 ^ N * (CN + r ^ N * C0)) (fun z hz => by
      have hzs : dist z s = r := Metric.mem_sphere.1 hz
      have hre := abs_le.1 (re_close hzs.le)
      have e1 := hCN z (by linarith) (by linarith)
      have e0 := hC0 z (by linarith) (by linarith)
      rw [pow_zero, one_mul] at e0
      rw [norm_mul, norm_pow] at e1 ⊢
      have hs : ‖s‖ ≤ ‖z‖ + r := by
        have := norm_le_norm_add_norm_sub' s z
        rw [← dist_eq_norm, dist_comm, hzs] at this
        linarith [norm_sub_rev s z]
      have hp := (pow_le_pow_left₀ (norm_nonneg _) hs N).trans
        (add_pow_le_two ‖z‖ r (norm_nonneg _) hr0.le N)
      have hGz := norm_nonneg (G z)
      have h2N : (0 : ℝ) ≤ 2 ^ N := by positivity
      calc ‖s‖ ^ N * ‖G z‖ ≤ 2 ^ N * (‖z‖ ^ N + r ^ N) * ‖G z‖ :=
            mul_le_mul_of_nonneg_right hp hGz
        _ = 2 ^ N * (‖z‖ ^ N * ‖G z‖ + r ^ N * ‖G z‖) := by ring
        _ ≤ 2 ^ N * (CN + r ^ N * C0) := by
            gcongr)
  rw [hd] at hC
  exact hC

lemma Q_iter {I : Set ℝ} (hI : IsOpen I) (hI' : I.OrdConnected) {F : ℂ → ℂ} (hF : Q I F)
    (n : ℕ) : Q I (deriv^[n] F) := by
  induction n with
  | zero => exact hF
  | succ n ih => rw [Function.iterate_succ_apply']; exact Q_deriv hI hI' ih

noncomputable def cc : ℂ := -(2 * (Real.pi : ℂ)) * Complex.I

lemma norm_cc : ‖cc‖ = 2 * Real.pi := by
  unfold cc
  rw [norm_mul, norm_neg, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

lemma h_re (a w : ℝ) : ((a : ℂ) + cc * w).re = a := by simp [cc]

lemma h_im (a w : ℝ) : ((a : ℂ) + cc * w).im = -(2 * Real.pi) * w := by simp [cc]

lemma Phi_exists {I : Set ℝ} (hI : IsOpen I) (hI' : I.OrdConnected) {F : ℂ → ℂ} (hF : Q I F)
    {a : ℝ} (ha : a ∈ I) : ∃ Φ : SchwartzMap ℝ ℂ, ∀ w : ℝ, Φ w = F ((a : ℂ) + cc * w) := by
  have hmem : ∀ w : ℝ, ((a : ℂ) + cc * w) ∈ D I := fun w => by
    show ((a : ℂ) + cc * w).re ∈ I; rw [h_re]; exact ha
  have hderiv : ∀ (n : ℕ) (w : ℝ), HasDerivAt (fun w : ℝ => (deriv^[n] F) ((a : ℂ) + cc * w))
      ((deriv^[n + 1] F) ((a : ℂ) + cc * w) * cc) w := by
    intro n w
    have hG : HasDerivAt (deriv^[n] F) (deriv (deriv^[n] F) ((a : ℂ) + cc * w))
        ((a : ℂ) + cc * w) :=
      ((Q_iter hI hI' hF n).1.differentiableAt ((isOpen_D hI).mem_nhds (hmem w))).hasDerivAt
    have hh : HasDerivAt (fun z : ℂ => (a : ℂ) + cc * z) cc (w : ℂ) := by
      have := ((hasDerivAt_id (w : ℂ)).const_mul cc).const_add (a : ℂ)
      simpa using this
    have := (hG.comp (w : ℂ) hh).comp_ofReal
    rw [Function.iterate_succ_apply']
    exact this
  have hiter : ∀ (n : ℕ) (w : ℝ), iteratedDeriv n (fun w : ℝ => F ((a : ℂ) + cc * w)) w =
      cc ^ n * (deriv^[n] F) ((a : ℂ) + cc * w) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [iteratedDeriv_succ, show iteratedDeriv n (fun w : ℝ => F ((a : ℂ) + cc * w)) =
        fun w : ℝ => cc ^ n * (deriv^[n] F) ((a : ℂ) + cc * w) from funext ih,
        ((hderiv n w).const_mul (cc ^ n)).deriv]
      ring
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℝ => F ((a : ℂ) + cc * w)) := by
    refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
    rw [show iteratedDeriv m (fun w : ℝ => F ((a : ℂ) + cc * w)) =
      fun w : ℝ => cc ^ m * (deriv^[m] F) ((a : ℂ) + cc * w) from funext (hiter m)]
    exact fun w => ((hderiv m w).differentiableAt).const_mul _
  have hdecay : ∀ k n : ℕ, ∃ C : ℝ, ∀ w : ℝ,
      ‖w‖ ^ k * ‖iteratedFDeriv ℝ n (fun w : ℝ => F ((a : ℂ) + cc * w)) w‖ ≤ C := by
    intro k n
    have hIcc : Set.Icc a a ⊆ I := by rw [Set.Icc_self]; exact Set.singleton_subset_iff.2 ha
    obtain ⟨C, hC⟩ := (Q_iter hI hI' hF n).2 a a hIcc k
    have hpi : 0 < 2 * Real.pi := by positivity
    refine ⟨(2 * Real.pi) ^ n * ((2 * Real.pi) ^ k)⁻¹ * C, fun w => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter, norm_mul, norm_pow, norm_cc]
    have e := hC ((a : ℂ) + cc * w) (by rw [h_re]) (by rw [h_re])
    rw [norm_mul, norm_pow] at e
    have hw : (2 * Real.pi) ^ k * ‖w‖ ^ k ≤ ‖(a : ℂ) + cc * w‖ ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have := Complex.abs_im_le_norm ((a : ℂ) + cc * w)
      rw [h_im, abs_mul, abs_neg, abs_of_pos hpi] at this
      rw [Real.norm_eq_abs]
      exact this
    have hG := norm_nonneg ((deriv^[n] F) ((a : ℂ) + cc * w))
    have hk : 0 < (2 * Real.pi) ^ k := by positivity
    have hn : 0 ≤ (2 * Real.pi) ^ n := by positivity
    have : ‖w‖ ^ k ≤ ((2 * Real.pi) ^ k)⁻¹ * ‖(a : ℂ) + cc * w‖ ^ k := by
      rw [inv_mul_eq_div, le_div_iff₀ hk]; linarith
    calc ‖w‖ ^ k * ((2 * Real.pi) ^ n * ‖(deriv^[n] F) ((a : ℂ) + cc * w)‖) ≤
        ((2 * Real.pi) ^ k)⁻¹ * ‖(a : ℂ) + cc * w‖ ^ k *
          ((2 * Real.pi) ^ n * ‖(deriv^[n] F) ((a : ℂ) + cc * w)‖) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (2 * Real.pi) ^ n * ((2 * Real.pi) ^ k)⁻¹ *
          (‖(a : ℂ) + cc * w‖ ^ k * ‖(deriv^[n] F) ((a : ℂ) + cc * w)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e (by positivity)
  exact ⟨⟨fun w : ℝ => F ((a : ℂ) + cc * w), hsmooth, hdecay⟩, fun w => rfl⟩

/-- The integrand used for the contour shift. -/
noncomputable def fx (F : ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ := F z * Complex.exp (-(z * x))

lemma J_eq {F : ℂ → ℂ} {a : ℝ} {Φ : SchwartzMap ℝ ℂ} (hΦ : ∀ w : ℝ, Φ w = F ((a : ℂ) + cc * w))
    (x : ℝ) :
    (Real.exp (-(a * x)) : ℂ) * (𝓕⁻ Φ) x =
      (2 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ, fx F x ((a : ℂ) + t * Complex.I) := by
  have hinv : (𝓕⁻ Φ) x = ∫ v : ℝ, Complex.exp (((2 * Real.pi * (v * x) : ℝ) : ℂ) * Complex.I) *
      Φ v := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    simp_rw [Real.inner_apply, smul_eq_mul]
  rw [hinv, ← integral_const_mul]
  have hpt : ∀ v : ℝ, (Real.exp (-(a * x)) : ℂ) *
      (Complex.exp (((2 * Real.pi * (v * x) : ℝ) : ℂ) * Complex.I) * Φ v) =
      fx F x ((a : ℂ) + ((-(2 * Real.pi) * v : ℝ) : ℂ) * Complex.I) := by
    intro v
    unfold fx
    have harg : ((a : ℂ) + ((-(2 * Real.pi) * v : ℝ) : ℂ) * Complex.I) = (a : ℂ) + cc * v := by
      unfold cc; push_cast; ring
    rw [harg, hΦ, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 2
    unfold cc
    push_cast
    ring
  simp_rw [hpt]
  have := Measure.integral_comp_mul_left
    (fun t : ℝ => fx F x ((a : ℂ) + (t : ℂ) * Complex.I)) (-(2 * Real.pi))
  rw [this, Complex.real_smul, inv_neg, abs_neg, abs_of_pos (by positivity)]
  push_cast
  ring

lemma contour {I : Set ℝ} (hI : IsOpen I) (hI' : I.OrdConnected) {F : ℂ → ℂ} (hF : Q I F)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) (x : ℝ) :
    ∫ t : ℝ, fx F x ((a : ℂ) + t * Complex.I) = ∫ t : ℝ, fx F x ((b : ℂ) + t * Complex.I) := by
  have hsub : Set.Icc a b ⊆ I := hI'.out ha hb
  obtain ⟨C0, hC0⟩ := hF.2 a b hsub 0
  obtain ⟨C2, hC2⟩ := hF.2 a b hsub 2
  set Ex := Real.exp (-(a * x)) + Real.exp (-(b * x))
  have hbound : ∀ σ ∈ Set.Icc a b, ∀ t : ℝ,
      ‖fx F x ((σ : ℂ) + t * Complex.I)‖ ≤ ((C0 + C2) * Ex) / (1 + t ^ 2) := by
    intro σ hσ t
    have hre : ((σ : ℂ) + t * Complex.I).re = σ := by simp
    have e0 := hC0 ((σ : ℂ) + t * Complex.I) (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2)
    have e2 := hC2 ((σ : ℂ) + t * Complex.I) (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2)
    rw [pow_zero, one_mul] at e0
    rw [norm_mul, norm_pow] at e2
    have hn : ‖(σ : ℂ) + t * Complex.I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
      rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    rw [hn] at e2
    have hFt : ‖F ((σ : ℂ) + t * Complex.I)‖ * (1 + t ^ 2) ≤ C0 + C2 := by
      nlinarith [sq_nonneg σ, norm_nonneg (F ((σ : ℂ) + t * Complex.I))]
    have hexp : ‖Complex.exp (-(((σ : ℂ) + t * Complex.I) * x))‖ ≤ Ex := by
      rw [Complex.norm_exp]
      have : (-(((σ : ℂ) + t * Complex.I) * x)).re = -(σ * x) := by simp
      rw [this]
      rcases le_total 0 x with hx | hx
      · have : Real.exp (-(σ * x)) ≤ Real.exp (-(a * x)) :=
          Real.exp_le_exp.2 (by nlinarith [hσ.1])
        linarith [Real.exp_pos (-(b * x))]
      · have : Real.exp (-(σ * x)) ≤ Real.exp (-(b * x)) :=
          Real.exp_le_exp.2 (by nlinarith [hσ.2])
        linarith [Real.exp_pos (-(a * x))]
    unfold fx
    rw [norm_mul, le_div_iff₀ (by positivity)]
    have hE : 0 ≤ Ex := by positivity
    calc ‖F ((σ : ℂ) + t * Complex.I)‖ * ‖Complex.exp (-(((σ : ℂ) + t * Complex.I) * x))‖ *
          (1 + t ^ 2) = (‖F ((σ : ℂ) + t * Complex.I)‖ * (1 + t ^ 2)) *
            ‖Complex.exp (-(((σ : ℂ) + t * Complex.I) * x))‖ := by ring
      _ ≤ (C0 + C2) * Ex := mul_le_mul hFt hexp (norm_nonneg _)
          (le_trans (by positivity) hFt)
  have hcont : ∀ σ ∈ I, Continuous (fun t : ℝ => fx F x ((σ : ℂ) + t * Complex.I)) := by
    intro σ hσ
    unfold fx
    have hl : Continuous (fun t : ℝ => (σ : ℂ) + t * Complex.I) := by fun_prop
    refine Continuous.mul ?_ (by fun_prop)
    exact hF.1.continuousOn.comp_continuous hl (fun t => by
      show ((σ : ℂ) + t * Complex.I).re ∈ I; simpa using hσ)
  have hint : ∀ σ, σ ∈ Set.Icc a b →
      Integrable (fun t : ℝ => fx F x ((σ : ℂ) + t * Complex.I)) := by
    intro σ hσ
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul ((C0 + C2) * Ex))
      (hcont σ (hsub hσ)).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [← div_eq_mul_inv]
    exact hbound σ hσ t
  refine OAI.VerticalContourShift.integral_eq_of_strip_decay (fx F x) a b ((C0 + C2) * Ex) hab
    (fun z h1 h2 => ?_) (hint a ⟨le_refl _, hab⟩) (hint b ⟨hab, le_refl _⟩) hbound
  unfold fx
  have hz : z ∈ D I := hsub ⟨h1, h2⟩
  exact ((hF.1.differentiableAt ((isOpen_D hI).mem_nhds hz))).mul (by fun_prop)

end B4Aux

open B4Aux in
theorem solution (I : Set ℝ) (hI : IsOpen I) (hI' : I.OrdConnected) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | s.re ∈ I})
    (hbd : ∀ a b : ℝ, Set.Icc a b ⊆ I → ∀ N : ℕ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖s ^ N * F s‖ ≤ C) :
    ∃ ψ : ℝ → ℂ, (∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
        g x = (Real.exp (a * x) : ℂ) * ψ x) ∧
      ∀ s : ℂ, s.re ∈ I → ∫ x : ℝ, ψ x * Complex.exp (s * x) = F s := by
  have hQ : Q I F := ⟨hF, hbd⟩
  by_cases hne : I.Nonempty
  swap
  · refine ⟨0, fun a ha => absurd ⟨a, ha⟩ hne, fun s hs => absurd ⟨_, hs⟩ hne⟩
  obtain ⟨a0, ha0⟩ := hne
  choose Φ hΦ using fun (a : ℝ) (ha : a ∈ I) => Phi_exists hI hI' hQ ha
  let ψ : ℝ → ℂ := fun x => (Real.exp (-(a0 * x)) : ℂ) * (𝓕⁻ (Φ a0 ha0)) x
  have key : ∀ (b : ℝ) (hb : b ∈ I) (x : ℝ),
      (Real.exp (-(b * x)) : ℂ) * (𝓕⁻ (Φ b hb)) x = ψ x := by
    intro b hb x
    show _ = (Real.exp (-(a0 * x)) : ℂ) * (𝓕⁻ (Φ a0 ha0)) x
    rw [J_eq (hΦ b hb), J_eq (hΦ a0 ha0)]
    congr 1
    rcases le_total b a0 with h | h
    · exact contour hI hI' hQ hb ha0 h x
    · exact (contour hI hI' hQ ha0 hb h x).symm
  have hg : ∀ (b : ℝ) (hb : b ∈ I) (x : ℝ),
      (𝓕⁻ (Φ b hb)) x = (Real.exp (b * x) : ℂ) * ψ x := by
    intro b hb x
    rw [← key b hb x, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]
  refine ⟨ψ, fun a ha => ⟨𝓕⁻ (Φ a ha), hg a ha⟩, fun s hs => ?_⟩
  set b := s.re with hbdef
  set t := s.im with htdef
  have hs' : s = (b : ℂ) + t * Complex.I := (Complex.re_add_im s).symm
  have hpt : ∀ x : ℝ, ψ x * Complex.exp (s * x) =
      Complex.exp (((-2 * Real.pi * x * (-(t / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I) •
        (𝓕⁻ (Φ b hs)) x := by
    intro x
    have h1 : ψ x = (Real.exp (-(b * x)) : ℂ) * (𝓕⁻ (Φ b hs)) x := (key b hs x).symm
    rw [h1, smul_eq_mul, Complex.ofReal_exp, hs']
    rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
    congr 2
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
    push_cast
    field_simp
    ring
  simp_rw [hpt]
  rw [← Real.fourier_real_eq_integral_exp_smul, ← SchwartzMap.fourier_coe,
    fourier_fourierInv_eq, hΦ, hs']
  congr 1
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  unfold cc
  push_cast
  field_simp
