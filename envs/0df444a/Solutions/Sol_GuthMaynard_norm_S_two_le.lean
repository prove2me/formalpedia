-- Prove2me | solution 1 for GuthMaynard.norm_S_two_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:49:39.794647+00:00
-- url     : https://prove2.me/submissions/228f1e0b-f8ea-4760-8222-15676b39b248

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_sum_norm_tsum_hHat_sq_le
section
namespace GuthMaynardS56

open MeasureTheory Complex Set

/-- amplitude: smooth, supported in `[1,2]` -/
def Amp (G : ℝ → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) G ∧ tsupport G ⊆ Icc (1:ℝ) 2

theorem Amp.zero_of_lt {G : ℝ → ℂ} (h : Amp G) {u : ℝ} (hu : u < 1) : G u = 0 := by
  by_contra hne
  have : u ∈ tsupport G := subset_tsupport _ (Function.mem_support.2 hne)
  have := h.2 this
  simp only [mem_Icc] at this
  linarith [this.1]

theorem Amp.zero_of_notMem {G : ℝ → ℂ} (h : Amp G) {u : ℝ} (hu : u ∉ Icc (1:ℝ) 2) : G u = 0 := by
  by_contra hne
  exact hu (h.2 (subset_tsupport _ (Function.mem_support.2 hne)))

theorem Amp.deriv {G : ℝ → ℂ} (h : Amp G) : Amp (deriv G) := by
  refine ⟨?_, ?_⟩
  · exact (contDiff_infty_iff_deriv.1 h.1).2
  · have h1 : tsupport (_root_.deriv G) ⊆ tsupport G := tsupport_deriv_subset
    exact h1.trans h.2

theorem Amp.mul_smooth {G H : ℝ → ℂ} (h : Amp G) (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    Amp (fun u => G u * H u) := by
  refine ⟨h.1.mul hH, ?_⟩
  exact (tsupport_mul_subset_left).trans h.2

theorem Amp.mul_inv {G : ℝ → ℂ} (h : Amp G) : Amp (fun u => G u * ((u⁻¹ : ℝ) : ℂ)) := by
  refine ⟨?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < 1
    · have : (fun u => G u * ((u⁻¹ : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hx] with u hu
        simp [h.zero_of_lt hu]
      exact (contDiffAt_const).congr_of_eventuallyEq this
    · have hx0 : x ≠ 0 := by intro h0; apply hx; rw [h0]; norm_num
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) G x := h.1.contDiffAt
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_inv ℝ hx0)
      exact h1.mul h2
  · refine (tsupport_mul_subset_left).trans h.2

end GuthMaynardS56
end

section
namespace GuthMaynardS56

open MeasureTheory Complex Set

/-- Whole-line integration by parts for a compactly supported amplitude. -/
theorem ibp_amp {A A' F F' : ℝ → ℂ} (hAs : tsupport A ⊆ Icc (1:ℝ) 2)
    (hA : ∀ x, HasDerivAt A (A' x) x) (hF : ∀ x ∈ Icc (1:ℝ) 2, HasDerivAt F (F' x) x)
    (hA'z : ∀ x, x ∉ Icc (1:ℝ) 2 → A' x = 0)
    (hA'c : ContinuousOn A' (Icc 1 2)) (hF'c : ContinuousOn F' (Icc 1 2))
    (hFc : ContinuousOn F (Icc 1 2)) :
    ∫ x, A x * F' x = -∫ x, A' x * F x := by
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun x => (hA x).continuousAt
  have hAz : ∀ x, x ∉ Icc (1:ℝ) 2 → A x = 0 := fun x hx => by
    by_contra hne
    exact hx (hAs (subset_tsupport _ (Function.mem_support.2 hne)))
  have hI1 : Integrable (A * F') := by
    have : IntegrableOn (A * F') (Icc 1 2) :=
      (hAc.continuousOn.mul hF'c).integrableOn_Icc
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 this
    intro x hx
    by_contra hx'
    exact hx (by simp [Pi.mul_apply, hAz x hx'])
  have hI2 : Integrable (A' * F) := by
    have : IntegrableOn (A' * F) (Icc 1 2) := (hA'c.mul hFc).integrableOn_Icc
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 this
    intro x hx
    by_contra hx'
    exact hx (by simp [Pi.mul_apply, hA'z x hx'])
  have key := integral_mul_deriv_eq_deriv_mul (u := A) (v := F) (u' := A') (v' := F')
    (a' := 0) (b' := 0) (fun x _ => hA x) ?_ hI1 hI2 ?_ ?_
  · simpa using key
  · intro x hx
    exact hF x (hAs hx)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot (1:ℝ)] with x hx
    simp [hAz x (fun h => by linarith [h.1])]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (2:ℝ)] with x hx
    simp [hAz x (fun h => by linarith [h.2])]

end GuthMaynardS56
end

section
namespace GuthMaynardS56

open MeasureTheory Complex Set

theorem norm_cpow_it {u : ℝ} (hu : 0 < u) (t : ℝ) : ‖(u:ℂ)^((t:ℂ)*I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]; simp

theorem contAt_cpow (c : ℂ) {u : ℝ} (hu : 0 < u) : ContinuousAt (fun u : ℝ => (u:ℂ)^c) u :=
  ContinuousAt.cpow (Complex.continuous_ofReal.continuousAt) continuousAt_const (Complex.ofReal_mem_slitPlane.2 hu)

theorem contOn_cpow (c : ℂ) : ContinuousOn (fun u : ℝ => (u:ℂ)^c) (Icc 1 2) := fun u hu =>
  (contAt_cpow c (by linarith [hu.1])).continuousWithinAt

theorem Amp.continuous {G : ℝ → ℂ} (h : Amp G) : Continuous G := h.1.continuous

theorem Amp.integrable_norm {G : ℝ → ℂ} (h : Amp G) : Integrable (fun u => ‖G u‖) := by
  have hc : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) h.2
  exact (h.continuous.integrable_of_hasCompactSupport hc).norm

theorem Amp.integrable_mul {G : ℝ → ℂ} (h : Amp G) {H : ℝ → ℂ} (hH : ContinuousOn H (Icc 1 2)) :
    Integrable (fun u => G u * H u) := by
  have : IntegrableOn (fun u => G u * H u) (Icc 1 2) :=
    (h.continuous.continuousOn.mul hH).integrableOn_Icc
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 this
  intro x hx
  by_contra hx'
  exact hx (by simp [h.zero_of_notMem hx'])

theorem decay_zero_freq : ∀ k : ℕ, ∀ G : ℝ → ℂ, Amp G → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
    ‖∫ u, G u * (u:ℂ)^((t:ℂ)*I)‖ * |t|^k ≤ C := by
  intro k
  induction k with
  | zero =>
    intro G hG
    refine ⟨∫ u, ‖G u‖, fun t ht => ?_⟩
    simp only [pow_zero, mul_one]
    refine norm_integral_le_of_norm_le hG.integrable_norm (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : 0 < u
    · simp [norm_mul, norm_cpow_it hu]
    · have : G u = 0 := hG.zero_of_notMem (fun hh => hu (by linarith [hh.1]))
      simp [this]
  | succ k ih =>
    intro G hG
    obtain ⟨C, hC⟩ := ih (fun u => deriv G u * (u:ℂ)) (by
      have := (hG.deriv.mul_smooth (H := fun u : ℝ => (u:ℂ)) (Complex.ofRealCLM.contDiff))
      exact this)
    refine ⟨C, fun t ht => ?_⟩
    have ht0 : 0 < |t| := lt_of_lt_of_le one_pos ht
    have hr : (t:ℂ)*I ≠ -1 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hne : (t:ℂ)*I + 1 ≠ 0 := by
      intro h; apply hr; linear_combination h
    set F : ℝ → ℂ := fun y => (y:ℂ)^((t:ℂ)*I+1) / ((t:ℂ)*I+1) with hFdef
    have key : ∫ x, G x * (x:ℂ)^((t:ℂ)*I) = -∫ x, deriv G x * F x := by
      refine ibp_amp (A := G) (A' := deriv G) (F := F) (F' := fun x => (x:ℂ)^((t:ℂ)*I)) hG.2
        (fun x => (hG.1.differentiable (by simp)).differentiableAt.hasDerivAt)
        (fun x hx => hasDerivAt_ofReal_cpow_const' (by linarith [hx.1] : x ≠ 0) hr |>.congr_deriv rfl)
        (fun x hx => hG.deriv.zero_of_notMem hx)
        hG.deriv.continuous.continuousOn (contOn_cpow _) ?_
      intro x hx
      exact (hasDerivAt_ofReal_cpow_const' (by linarith [hx.1] : x ≠ 0) hr).continuousAt.continuousWithinAt
    have h2 : ∫ x, deriv G x * F x = (1 / ((t:ℂ)*I+1)) * ∫ x, (deriv G x * (x:ℂ)) * (x:ℂ)^((t:ℂ)*I) := by
      rw [← integral_const_mul]
      congr 1; funext x
      by_cases hx : x ∈ Icc (1:ℝ) 2
      · have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast (by linarith [hx.1] : x ≠ 0)
        simp only [hFdef]
        rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
        ring
      · simp [hG.deriv.zero_of_notMem hx]
    rw [key, h2, norm_neg, norm_mul]
    have hn : ‖(1 / ((t:ℂ)*I+1))‖ ≤ 1 / |t| := by
      rw [norm_div, norm_one]
      apply one_div_le_one_div_of_le ht0
      calc |t| = |((t:ℂ)*I+1).im| := by simp
        _ ≤ ‖(t:ℂ)*I+1‖ := Complex.abs_im_le_norm _
    have hC' := hC t ht
    calc ‖(1 / ((t:ℂ)*I+1))‖ * ‖∫ x, (deriv G x * (x:ℂ)) * (x:ℂ)^((t:ℂ)*I)‖ * |t|^(k+1)
        ≤ (1/|t|) * ‖∫ x, (deriv G x * (x:ℂ)) * (x:ℂ)^((t:ℂ)*I)‖ * |t|^(k+1) := by
          gcongr
      _ = ‖∫ x, (deriv G x * (x:ℂ)) * (x:ℂ)^((t:ℂ)*I)‖ * |t|^k := by
          field_simp
          ring
      _ ≤ C := hC'

end GuthMaynardS56
end

section
namespace GuthMaynardS56

open MeasureTheory Complex Set
open scoped Real

/-- the character `u ↦ e(-ξu)` as `exp(c u)` -/
noncomputable def Ec (ξ : ℝ) (u : ℝ) : ℂ := Complex.exp ((((-2 * π * ξ : ℝ) : ℂ) * I) * (u:ℂ))

theorem norm_Ec (ξ u : ℝ) : ‖Ec ξ u‖ = 1 := by
  unfold Ec
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_Ec (ξ u : ℝ) :
    HasDerivAt (Ec ξ) ((((-2 * π * ξ : ℝ) : ℂ) * I) * Ec ξ u) u := by
  unfold Ec
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp ((((-2 * π * ξ : ℝ) : ℂ) * I) * z))
      (Complex.exp ((((-2 * π * ξ : ℝ) : ℂ) * I) * (u:ℂ)) * (((-2 * π * ξ : ℝ) : ℂ) * I)) (u:ℂ) := by
    have := ((hasDerivAt_id (u:ℂ)).const_mul ((((-2 * π * ξ : ℝ) : ℂ) * I))).cexp
    simpa using this
  have := h1.comp_ofReal
  convert this using 1
  ring

theorem continuous_Ec (ξ : ℝ) : Continuous (Ec ξ) := by
  unfold Ec
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem hasDerivAt_cpow_it (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y:ℂ)^((t:ℂ)*I)) ((t:ℂ)*I * ((x⁻¹ : ℝ) : ℂ) * (x:ℂ)^((t:ℂ)*I)) x := by
  by_cases ht : t = 0
  · subst ht; simpa using hasDerivAt_const x (1:ℂ)
  · have hr : (t:ℂ)*I ≠ 0 := by simp [ht]
    have h := hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hr
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
    convert h using 1
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    push_cast
    ring

theorem decay_freq : ∀ k : ℕ, ∀ G : ℝ → ℂ, Amp G → ∃ C : ℝ, ∀ t ξ : ℝ, ξ ≠ 0 →
    ‖∫ u, G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ * |ξ|^k ≤ C * (1 + |t|)^k := by
  intro k
  induction k with
  | zero =>
    intro G hG
    refine ⟨∫ u, ‖G u‖, fun t ξ hξ => ?_⟩
    simp only [pow_zero, mul_one]
    refine norm_integral_le_of_norm_le hG.integrable_norm (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : 0 < u
    · simp [norm_mul, norm_cpow_it hu, norm_Ec]
    · have : G u = 0 := hG.zero_of_notMem (fun hh => hu (by linarith [hh.1]))
      simp [this]
  | succ k ih =>
    intro G hG
    obtain ⟨C1, hC1⟩ := ih (deriv G) hG.deriv
    obtain ⟨C3, hC3⟩ := ih (fun u => G u * ((u⁻¹ : ℝ) : ℂ)) hG.mul_inv
    refine ⟨|C1| + |C3|, fun t ξ hξ => ?_⟩
    set c : ℂ := (((-2 * π * ξ : ℝ) : ℂ) * I) with hc
    have hc0 : c ≠ 0 := by
      simp only [hc]
      have : (-2 * π * ξ : ℝ) ≠ 0 := by
        have := Real.pi_pos
        intro h
        have : ξ = 0 := by
          have h2 : (-2 * π) * ξ = 0 := h
          rcases mul_eq_zero.1 h2 with h3 | h3
          · linarith
          · exact h3
        exact hξ this
      exact mul_ne_zero (by exact_mod_cast this) Complex.I_ne_zero
    have hcn : ‖c‖ = 2 * π * |ξ| := by
      simp only [hc]; rw [norm_mul]; simp [abs_mul, abs_of_pos Real.pi_pos]
    set A : ℝ → ℂ := fun u => G u * (u:ℂ)^((t:ℂ)*I) with hAdef
    set A' : ℝ → ℂ := fun u => (deriv G u + (t:ℂ)*I * (G u * ((u⁻¹ : ℝ) : ℂ))) * (u:ℂ)^((t:ℂ)*I)
      with hA'def
    have hAd : ∀ x, HasDerivAt A (A' x) x := by
      intro x
      by_cases hx : 0 < x
      · have h1 : HasDerivAt G (deriv G x) x :=
          (hG.1.differentiable (by simp)).differentiableAt.hasDerivAt
        have h2 := h1.mul (hasDerivAt_cpow_it t hx)
        refine h2.congr_deriv ?_
        simp only [hA'def]; ring
      · have hev : A =ᶠ[nhds x] fun _ => 0 := by
          have hx1 : x < 1 := by linarith
          filter_upwards [Iio_mem_nhds hx1] with u hu
          simp [hAdef, hG.zero_of_lt hu]
        have h0 : HasDerivAt (fun _ : ℝ => (0:ℂ)) 0 x := hasDerivAt_const x 0
        have := h0.congr_of_eventuallyEq hev
        have hxn : x ∉ Icc (1:ℝ) 2 := fun hh => hx (by linarith [hh.1])
        refine this.congr_deriv ?_
        simp [hA'def, hG.deriv.zero_of_notMem hxn, hG.zero_of_notMem hxn]
    set F : ℝ → ℂ := fun u => Ec ξ u / c with hFdef
    have hFd : ∀ x, HasDerivAt F (Ec ξ x) x := by
      intro x
      have := (hasDerivAt_Ec ξ x).div_const c
      refine this.congr_deriv ?_
      exact mul_div_cancel_left₀ _ hc0
    have hcontcpow : ContinuousOn (fun u : ℝ => (u:ℂ)^((t:ℂ)*I)) (Icc 1 2) := contOn_cpow _
    have hA'c : ContinuousOn A' (Icc 1 2) := by
      have h1 : ContinuousOn (fun u : ℝ => deriv G u) (Icc 1 2) := hG.deriv.continuous.continuousOn
      have h2 : ContinuousOn (fun u : ℝ => G u * ((u⁻¹ : ℝ) : ℂ)) (Icc 1 2) :=
        hG.mul_inv.continuous.continuousOn
      exact (h1.add (continuousOn_const.mul h2)).mul hcontcpow
    have key : ∫ x, A x * Ec ξ x = -∫ x, A' x * F x := by
      refine ibp_amp (A := A) (A' := A') (F := F) (F' := Ec ξ) ?_ hAd (fun x _ => hFd x) ?_ hA'c
        (continuous_Ec ξ).continuousOn ((continuous_Ec ξ).div_const c).continuousOn
      · exact (tsupport_mul_subset_left).trans hG.2
      · intro x hx
        simp [hA'def, hG.deriv.zero_of_notMem hx, hG.zero_of_notMem hx]
    have hI1 : Integrable (fun u => deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) :=
      hG.deriv.integrable_mul (hcontcpow.mul (continuous_Ec ξ).continuousOn)
    have hI3 : Integrable (fun u => (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) :=
      hG.mul_inv.integrable_mul (hcontcpow.mul (continuous_Ec ξ).continuousOn)
    have hsplit : ∫ x, A' x * F x = (1 / c) * ((∫ u, deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) +
        (t:ℂ)*I * ∫ u, (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) := by
      have hpt : (fun x => A' x * F x) = fun x => (1 / c) * (deriv G x * ((x:ℂ)^((t:ℂ)*I) * Ec ξ x) +
          (t:ℂ)*I * ((G x * ((x⁻¹ : ℝ) : ℂ)) * ((x:ℂ)^((t:ℂ)*I) * Ec ξ x))) := by
        funext x
        simp only [hA'def, hFdef]
        field_simp
      rw [hpt, integral_const_mul, integral_add hI1 (hI3.const_mul _), integral_const_mul]
    have hmain : ∫ u, G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u) = -∫ x, A' x * F x := by
      rw [← key]; congr 1; funext x; simp only [hAdef]; ring
    rw [hmain, hsplit, norm_neg, norm_mul, norm_div, norm_one, hcn]
    have h1 := hC1 t ξ hξ
    have h3 := hC3 t ξ hξ
    have hξp : 0 < |ξ| := abs_pos.2 hξ
    have hpi : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    have hsum : ‖(∫ u, deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) +
        (t:ℂ)*I * ∫ u, (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ * |ξ|^k ≤
        (|C1| + |C3|) * (1 + |t|)^(k+1) := by
      calc _ ≤ (‖∫ u, deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ +
            |t| * ‖∫ u, (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖) * |ξ|^k := by
              gcongr
              refine (norm_add_le _ _).trans ?_
              gcongr
              simp [norm_mul]
        _ = ‖∫ u, deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ * |ξ|^k +
            |t| * (‖∫ u, (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ * |ξ|^k) := by ring
        _ ≤ |C1| * (1 + |t|)^k + |t| * (|C3| * (1 + |t|)^k) := by
              exact add_le_add
                (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
                (mul_le_mul_of_nonneg_left
                  (h3.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
                  (abs_nonneg t))
        _ ≤ (|C1| + |C3|) * (1 + |t|)^(k+1) := by
              have hp : 0 ≤ (1 + |t|)^k := by positivity
              have : (1 + |t|)^(k+1) = (1+|t|)^k * (1 + |t|) := pow_succ _ _
              rw [this]
              nlinarith [abs_nonneg C1, abs_nonneg C3, abs_nonneg t, mul_nonneg (abs_nonneg C1) hp,
                mul_nonneg (abs_nonneg C3) hp, mul_nonneg (mul_nonneg (abs_nonneg C3) hp) (abs_nonneg t),
                mul_nonneg (mul_nonneg (abs_nonneg C1) hp) (abs_nonneg t)]
    have hfac : 1 / (2 * π * |ξ|) ≤ 1 / |ξ| := by
      apply one_div_le_one_div_of_le hξp
      nlinarith
    have hg : ∀ X : ℝ, 1 / |ξ| * X * |ξ|^(k+1) = X * |ξ|^k := by
      intro X; rw [pow_succ]; field_simp
    calc 1 / (2 * π * |ξ|) * ‖_‖ * |ξ|^(k+1) ≤ 1 / |ξ| * ‖_‖ * |ξ|^(k+1) := by gcongr
      _ = _ := hg _
      _ ≤ _ := hsum

end GuthMaynardS56
end

section
namespace GuthMaynardS56

open MeasureTheory Complex Set
open scoped Real

theorem ampW {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) :
    Amp (fun u => ((w u ^ 2 : ℝ) : ℂ)) := by
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((hw.smooth).pow 2)
  · have h1 : tsupport (fun u => ((w u ^ 2 : ℝ) : ℂ)) ⊆ tsupport w := by
      apply closure_mono
      intro u hu
      simp only [Function.mem_support] at hu ⊢
      intro h; apply hu; simp [h]
    refine h1.trans ?_
    exact closure_minimal hw.support_subset isClosed_Icc

theorem hHat_eq {w : ℝ → ℝ} (t ξ : ℝ) :
    GuthMaynard.hHat w t ξ =
      ∫ u, ((w u ^ 2 : ℝ) : ℂ) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u) := by
  unfold GuthMaynard.hHat
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext u
  simp only [smul_eq_mul, Ec]
  have : (((-2 * π * u * ξ : ℝ) : ℂ) * I) = (((-2 * π * ξ : ℝ) : ℂ) * I) * (u:ℂ) := by
    push_cast; ring
  rw [this]; ring

theorem hHat_zero {w : ℝ → ℝ} (t : ℝ) :
    GuthMaynard.hHat w t 0 = ∫ u, ((w u ^ 2 : ℝ) : ℂ) * (u:ℂ)^((t:ℂ)*I) := by
  rw [hHat_eq]; congr 1; funext u; simp [Ec]

theorem hHat_bdd {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) :
    ∃ C : ℝ, ∀ t ξ : ℝ, ‖GuthMaynard.hHat w t ξ‖ ≤ C := by
  have hG := ampW hw
  refine ⟨∫ u, ‖((w u ^ 2 : ℝ) : ℂ)‖, fun t ξ => ?_⟩
  rw [hHat_eq]
  refine norm_integral_le_of_norm_le hG.integrable_norm (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : 0 < u
  · simp [norm_cpow_it hu, norm_Ec]
  · have : ((w u ^ 2 : ℝ) : ℂ) = 0 := hG.zero_of_notMem (fun hh => hu (by linarith [hh.1]))
    simp [this]

theorem hHat_decay_freq {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) (k : ℕ) :
    ∃ C : ℝ, ∀ t ξ : ℝ, ξ ≠ 0 → ‖GuthMaynard.hHat w t ξ‖ * |ξ|^k ≤ C * (1 + |t|)^k := by
  obtain ⟨C, hC⟩ := decay_freq k _ (ampW hw)
  exact ⟨C, fun t ξ hξ => by rw [hHat_eq]; exact hC t ξ hξ⟩

theorem hHat_decay_zero {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) (k : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| → ‖GuthMaynard.hHat w t 0‖ * |t|^k ≤ C := by
  obtain ⟨C, hC⟩ := decay_zero_freq k _ (ampW hw)
  exact ⟨C, fun t ht => by rw [hHat_zero]; exact hC t ht⟩

end GuthMaynardS56
end

section
namespace GuthMaynardS56

/-- card of a separated set in an interval -/
theorem card_le_of_sep {W : Finset ℝ} {a T δ : ℝ} (hδ : 1 ≤ δ) (hT : 0 ≤ T)
    (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → δ ≤ |t - t'|) (hW : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) :
    (W.card : ℝ) ≤ T + 1 := by
  have hc : W.card ≤ (Finset.Icc (0:ℤ) ⌊T⌋).card := by
    refine Finset.card_le_card_of_injOn (fun t => ⌊t - a⌋) ?_ ?_
    · intro t ht
      have := hW t ht
      simp only [Finset.coe_Icc, Set.mem_Icc]
      constructor
      · exact Int.floor_nonneg.2 (by linarith [this.1])
      · exact Int.floor_mono (by linarith [this.2])
    · intro t ht t' ht' h
      by_contra hne
      have h1 := hsep t ht t' ht' hne
      have h2 := Int.abs_sub_lt_one_of_floor_eq_floor h
      have : |(t - a) - (t' - a)| = |t - t'| := by ring_nf
      linarith
  have h2 : ((Finset.Icc (0:ℤ) ⌊T⌋).card : ℝ) = (⌊T⌋ : ℝ) + 1 := by
    rw [Int.card_Icc]
    have : (0:ℤ) ≤ ⌊T⌋ := Int.floor_nonneg.2 hT
    have : ((⌊T⌋ + 1 - 0).toNat : ℤ) = ⌊T⌋ + 1 := by omega
    exact_mod_cast this
  calc (W.card : ℝ) ≤ ((Finset.Icc (0:ℤ) ⌊T⌋).card : ℝ) := by exact_mod_cast hc
    _ = (⌊T⌋ : ℝ) + 1 := h2
    _ ≤ T + 1 := by linarith [Int.floor_le T]

end GuthMaynardS56
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-!
# Blueprint: Guth–Maynard Proposition 6.1 (the `S₂` bound)

Route (pp. 17–20 of arXiv v2, with the Mellin inversion replaced by Fourier inversion in the
variable `x = log u`, and van der Corput replaced by one explicit integration by parts):

* `S₂ = 3N³ ∑_{t₁,t₂,t₃} ĥ_{t₃-t₁}(0) A(t₁-t₂) A(t₂-t₃)` with `A(t) = ∑_{m ≠ 0} ĥ_t(mN)`.
* `A(t)` = (positive `m ≤ M`) + (negative `m ≤ M`, a conjugate of the positive sum at `-t`) + tail.
* Positive part: `w(u)² = u⁻¹ G(log u)`, `G(x) = eˣ w(eˣ)²`, and Fourier inversion of `G` give
  `∑_{m=1}^M ĥ_t(mN) = ∫ Ĝ(ρ) (∑_m (mN)^{-iτ}) I(τ) dρ`, `τ = t + 2πρ`,
  `I(τ) = ∫_N^{2NM} v^{-1+iτ} e(-v) dv`, and `|I(τ)| ≪ |τ|^{-1/2}`.
* Hölder + divisor bound + Heath-Brown (Theorem 1.6) bound the Dirichlet polynomial sums.
-/
/-- `A(t) = ∑_{m ≠ 0} ĥ_t(mN)`. -/
noncomputable def Asum (w : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑' z : {z : ℤ // z ≠ 0}, hHat w t ((z : ℤ) * N)

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartA
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartA
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part A: the oscillatory integral -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartA
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartA
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartB
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartB
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part B: Fourier inversion in `log u` -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartB
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartB
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartD
open Complex MeasureTheory FourierTransform
/-- nonzero integers -/
abbrev Z' := {z : ℤ // z ≠ 0}

/-- the index set of `S 2` -/
abbrev Sub2 := {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 2}

theorem decay {w : ℝ → ℝ} (hw : IsWeight w) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ z : ℤ, z ≠ 0 →
      ‖hHat w t ((z:ℝ) * N)‖ ≤ C * (1 + |t|) ^ J / ((N:ℝ) ^ J * |(z:ℝ)| ^ J) := by
  obtain ⟨C, hC⟩ := GuthMaynardS56.hHat_decay_freq hw J
  refine ⟨|C|, abs_nonneg _, fun t N hN z hz => ?_⟩
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hz0 : (0:ℝ) < |(z:ℝ)| := abs_pos.2 (by exact_mod_cast hz)
  have hξ : (z:ℝ) * N ≠ 0 := mul_ne_zero (by exact_mod_cast hz) hN0.ne'
  have h := hC t _ hξ
  rw [abs_mul, abs_of_pos hN0, mul_pow] at h
  rw [le_div_iff₀ (by positivity)]
  calc ‖hHat w t ((z:ℝ) * N)‖ * ((N:ℝ) ^ J * |(z:ℝ)| ^ J)
      = ‖hHat w t ((z:ℝ) * N)‖ * (|(z:ℝ)| ^ J * (N:ℝ) ^ J) := by ring
    _ ≤ C * (1 + |t|)^J := h
    _ ≤ |C| * (1 + |t|)^J := by gcongr; exact le_abs_self _

theorem summable_Z {w : ℝ → ℝ} (hw : IsWeight w) (t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun z : Z' => ‖hHat w t (((z:ℤ):ℝ) * N)‖) := by
  obtain ⟨C, hC0, hC⟩ := decay hw 2
  have h1 : Summable (fun n : ℤ => 1 / ((n:ℝ))^2) := by
    exact_mod_cast (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have h2 := (h1.subtype {z : ℤ | z ≠ 0}).mul_left (C * (1 + |t|)^2)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) h2
  refine (hC t N hN z.1 z.2).trans ?_
  have hN1 : (1:ℝ) ≤ (N:ℝ)^2 := one_le_pow₀ (by exact_mod_cast hN)
  have hz : ((z.1:ℤ):ℝ) ≠ 0 := by exact_mod_cast z.2
  simp only [Function.comp_apply, sq_abs]
  rw [show C * (1 + |t|) ^ 2 / ((N:ℝ) ^ 2 * ((z.1:ℤ):ℝ) ^ 2)
      = (C * (1 + |t|) ^ 2 * (1 / ((z.1:ℤ):ℝ) ^ 2)) / (N:ℝ)^2 by field_simp]
  exact div_le_self (by positivity) hN1

theorem hasSum_pair {w : ℝ → ℝ} (hw : IsWeight w) {N : ℕ} (hN : 1 ≤ N) (W : Finset ℝ)
    (F G : ℝ → ℝ → ℝ → ℝ) (c : ℝ → ℝ → ℝ → ℂ) :
    HasSum (fun p : Z' × Z' => (N:ℂ)^3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      hHat w (F t₁ t₂ t₃) (((p.1:ℤ):ℝ) * N) * hHat w (G t₁ t₂ t₃) (((p.2:ℤ):ℝ) * N) * c t₁ t₂ t₃)
    ((N:ℂ)^3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      Asum w N (F t₁ t₂ t₃) * Asum w N (G t₁ t₂ t₃) * c t₁ t₂ t₃) := by
  refine HasSum.mul_left _ ?_
  refine hasSum_sum (fun t₁ _ => ?_)
  refine hasSum_sum (fun t₂ _ => ?_)
  refine hasSum_sum (fun t₃ _ => ?_)
  refine HasSum.mul_right _ ?_
  have h1 := summable_Z hw (F t₁ t₂ t₃) N hN
  have h2 := summable_Z hw (G t₁ t₂ t₃) N hN
  have := (summable_mul_of_summable_norm h1 h2).hasSum
  rw [← tsum_mul_tsum_of_summable_norm h1 h2] at this
  exact this

theorem card_three (m : Fin 3 → ℤ) : (Finset.univ.filter fun i => m i ≠ 0).card =
    (if m 0 ≠ 0 then 1 else 0) + (if m 1 ≠ 0 then 1 else 0) + (if m 2 ≠ 0 then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_three]

theorem norm_triple (N : ℕ) (W : Finset ℝ) (X : ℝ → ℝ → ℝ → ℂ) :
    ‖(N:ℂ)^3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, X t₁ t₂ t₃‖ ≤
      (N:ℝ)^3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖X t₁ t₂ t₃‖ := by
  rw [norm_mul]
  have : ‖(N:ℂ)^3‖ = (N:ℝ)^3 := by simp
  rw [this]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₁ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₂ _ => ?_)
  exact norm_sum_le _ _

theorem cyc (W : Finset ℝ) (H : ℝ → ℝ → ℝ → ℝ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, H t₃ t₁ t₂ = ∑ s₁ ∈ W, ∑ s₂ ∈ W, ∑ s₃ ∈ W, H s₁ s₂ s₃ := by
  calc _ = ∑ t₁ ∈ W, ∑ t₃ ∈ W, ∑ t₂ ∈ W, H t₃ t₁ t₂ :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem norm_S_two_le_sum {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) :
    ‖S 2 w N W‖ ≤ 3 * (N : ℝ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ‖hHat w (t₃ - t₁) 0‖ * ‖Asum w N (t₁ - t₂)‖ * ‖Asum w N (t₂ - t₃)‖ := by
  classical
  let f : Sub2 → ℂ := fun m => Iterm w N W m.1
  let e2 : Z' × Z' → Sub2 := fun p => ⟨![p.1.1, p.2.1, 0], by rw [card_three]; simp [p.1.2, p.2.2]⟩
  let e1 : Z' × Z' → Sub2 := fun p => ⟨![p.1.1, 0, p.2.1], by rw [card_three]; simp [p.1.2, p.2.2]⟩
  let e0 : Z' × Z' → Sub2 := fun p => ⟨![0, p.1.1, p.2.1], by rw [card_three]; simp [p.1.2, p.2.2]⟩
  let g : Fin 3 → Sub2 → ℂ := fun i m => if m.1 i = 0 then f m else 0
  have hsplit : f = fun m => g 0 m + g 1 m + g 2 m := by
    funext m
    have h := m.2
    rw [card_three] at h
    simp only [g]
    by_cases h0 : m.1 0 = 0 <;> by_cases h1 : m.1 1 = 0 <;> by_cases h2 : m.1 2 = 0 <;>
      simp [h0, h1, h2] at h ⊢
  have H2 := hasSum_pair hw hN W (fun t₁ t₂ _ => t₁ - t₂) (fun _ t₂ t₃ => t₂ - t₃)
    (fun t₁ _ t₃ => hHat w (t₃ - t₁) 0)
  have H1 := hasSum_pair hw hN W (fun t₁ t₂ _ => t₁ - t₂) (fun t₁ _ t₃ => t₃ - t₁)
    (fun _ t₂ t₃ => hHat w (t₂ - t₃) 0)
  have H0 := hasSum_pair hw hN W (fun _ t₂ t₃ => t₂ - t₃) (fun t₁ _ t₃ => t₃ - t₁)
    (fun t₁ t₂ _ => hHat w (t₁ - t₂) 0)
  have H2' : HasSum (g 2 ∘ e2) ((N:ℂ)^3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      Asum w N (t₁ - t₂) * Asum w N (t₂ - t₃) * hHat w (t₃ - t₁) 0) := by
    convert H2 using 1
    funext p
    simp [g, e2, f, Iterm]
  have H1' : HasSum (g 1 ∘ e1) ((N:ℂ)^3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      Asum w N (t₁ - t₂) * Asum w N (t₃ - t₁) * hHat w (t₂ - t₃) 0) := by
    convert H1 using 1
    funext p
    simp only [g, e1, f, Iterm, Function.comp_apply]
    simp
    left
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have H0' : HasSum (g 0 ∘ e0) ((N:ℂ)^3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      Asum w N (t₂ - t₃) * Asum w N (t₃ - t₁) * hHat w (t₁ - t₂) 0) := by
    convert H0 using 1
    funext p
    simp only [g, e0, f, Iterm, Function.comp_apply]
    simp
    left
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have inj2 : Function.Injective e2 := by
    intro p q h
    have h0 := congrArg (fun m : Sub2 => m.1 0) h
    have h1 := congrArg (fun m : Sub2 => m.1 1) h
    simp [e2] at h0 h1
    exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)
  have inj1 : Function.Injective e1 := by
    intro p q h
    have h0 := congrArg (fun m : Sub2 => m.1 0) h
    have h1 := congrArg (fun m : Sub2 => m.1 2) h
    simp [e1] at h0 h1
    exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)
  have inj0 : Function.Injective e0 := by
    intro p q h
    have h0 := congrArg (fun m : Sub2 => m.1 1) h
    have h1 := congrArg (fun m : Sub2 => m.1 2) h
    simp [e0] at h0 h1
    exact Prod.ext (Subtype.ext h0) (Subtype.ext h1)
  have rng2 : ∀ m ∉ Set.range e2, g 2 m = 0 := by
    intro m hm
    by_contra hne
    have h2 : m.1 2 = 0 := by by_contra h; exact hne (by simp [g, h])
    have h := m.2
    rw [card_three] at h
    have a0 : m.1 0 ≠ 0 := by intro h0; simp [h0, h2] at h; split_ifs at h; omega
    have a1 : m.1 1 ≠ 0 := by intro h1; simp [h1, h2] at h; split_ifs at h; omega
    exact hm ⟨(⟨m.1 0, a0⟩, ⟨m.1 1, a1⟩), Subtype.ext (funext fun i => by
      fin_cases i <;> simp [e2, h2])⟩
  have rng1 : ∀ m ∉ Set.range e1, g 1 m = 0 := by
    intro m hm
    by_contra hne
    have h2 : m.1 1 = 0 := by by_contra h; exact hne (by simp [g, h])
    have h := m.2
    rw [card_three] at h
    have a0 : m.1 0 ≠ 0 := by intro h0; simp [h0, h2] at h; split_ifs at h; omega
    have a1 : m.1 2 ≠ 0 := by intro h1; simp [h1, h2] at h; split_ifs at h; omega
    exact hm ⟨(⟨m.1 0, a0⟩, ⟨m.1 2, a1⟩), Subtype.ext (funext fun i => by
      fin_cases i <;> simp [e1, h2])⟩
  have rng0 : ∀ m ∉ Set.range e0, g 0 m = 0 := by
    intro m hm
    by_contra hne
    have h2 : m.1 0 = 0 := by by_contra h; exact hne (by simp [g, h])
    have h := m.2
    rw [card_three] at h
    have a0 : m.1 1 ≠ 0 := by intro h0; simp [h0, h2] at h; split_ifs at h; omega
    have a1 : m.1 2 ≠ 0 := by intro h1; simp [h1, h2] at h; split_ifs at h; omega
    exact hm ⟨(⟨m.1 1, a0⟩, ⟨m.1 2, a1⟩), Subtype.ext (funext fun i => by
      fin_cases i <;> simp [e0, h2])⟩
  have G2 := (inj2.hasSum_iff rng2).1 H2'
  have G1 := (inj1.hasSum_iff rng1).1 H1'
  have G0 := (inj0.hasSum_iff rng0).1 H0'
  have HS := (G0.add G1).add G2
  rw [← hsplit] at HS
  have hS : S 2 w N W = ∑' m : Sub2, f m := rfl
  rw [hS, HS.tsum_eq]
  set H : ℝ → ℝ → ℝ → ℝ := fun s₁ s₂ s₃ =>
    ‖hHat w (s₃ - s₁) 0‖ * ‖Asum w N (s₁ - s₂)‖ * ‖Asum w N (s₂ - s₃)‖ with hH
  have b2 := norm_triple N W (fun t₁ t₂ t₃ =>
    Asum w N (t₁ - t₂) * Asum w N (t₂ - t₃) * hHat w (t₃ - t₁) 0)
  have b1 := norm_triple N W (fun t₁ t₂ t₃ =>
    Asum w N (t₁ - t₂) * Asum w N (t₃ - t₁) * hHat w (t₂ - t₃) 0)
  have b0 := norm_triple N W (fun t₁ t₂ t₃ =>
    Asum w N (t₂ - t₃) * Asum w N (t₃ - t₁) * hHat w (t₁ - t₂) 0)
  have e2' : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ‖Asum w N (t₁ - t₂) * Asum w N (t₂ - t₃) * hHat w (t₃ - t₁) 0‖ =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, H t₁ t₂ t₃ :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by simp only [hH, norm_mul]; ring
  have e1' : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ‖Asum w N (t₁ - t₂) * Asum w N (t₃ - t₁) * hHat w (t₂ - t₃) 0‖ =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, H t₁ t₂ t₃ := by
    rw [← cyc W H]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by simp only [hH, norm_mul]; ring
  have e0' : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ‖Asum w N (t₂ - t₃) * Asum w N (t₃ - t₁) * hHat w (t₁ - t₂) 0‖ =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, H t₁ t₂ t₃ := by
    rw [← cyc W H, ← cyc W (fun x y z => H z x y)]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by simp only [hH, norm_mul]; ring
  rw [e2'] at b2
  rw [e1'] at b1
  rw [e0'] at b0
  calc _ ≤ _ := norm_add₃_le
    _ ≤ _ := add_le_add (add_le_add b0 b1) b2
    _ = _ := by ring

end GuthMaynard.S2.PartD
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part D: reduction of `S₂` and the splitting of `A(t)` -/
alias norm_S_two_le_sum := GuthMaynard.S2.PartD.norm_S_two_le_sum

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartD
open Complex MeasureTheory FourierTransform
theorem tel (K : ℕ) (hK : 1 ≤ K) (L : ℕ) :
    ∑ n ∈ Finset.range L, 1 / ((n:ℝ) + K)^2 ≤ 2 / (K:ℝ) - 2 / ((L:ℝ) + K) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hx : (1:ℝ) ≤ (L:ℝ) + K := by
      have : (1:ℝ) ≤ K := by exact_mod_cast hK
      linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)]
    have key : 1 / ((L:ℝ) + K)^2 ≤ 2 / ((L:ℝ) + K) - 2 / (((L:ℝ) + K) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    have : ((L:ℝ) + 1 + K) = ((L:ℝ) + K) + 1 := by ring
    rw [this]
    linarith

/-- a family with `‖h n‖ ≤ D/(n+1)^J` is summable with explicit tails. -/
theorem tail_generic (h : ℕ → ℂ) {D : ℝ} (hD : 0 ≤ D) {J : ℕ} (hJ : 2 ≤ J)
    (hh : ∀ n : ℕ, ‖h n‖ ≤ D / ((n:ℝ) + 1)^J) :
    Summable h ∧ ∀ M : ℕ, ‖∑' n, h n - ∑ i ∈ Finset.range M, h i‖ ≤
      2 * D / ((M:ℝ) + 1)^(J-1) := by
  have part : ∀ M L : ℕ, ∑ n ∈ Finset.range L, ‖h (n + M)‖ ≤ 2 * D / ((M:ℝ) + 1)^(J-1) := by
    intro M L
    have hM1 : (1:ℝ) ≤ (M:ℝ) + 1 := by linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]
    have hb : ∀ n : ℕ, ‖h (n + M)‖ ≤
        D / ((M:ℝ) + 1)^(J-2) * (1 / ((n:ℝ) + ((M + 1 : ℕ) : ℝ))^2) := by
      intro n
      refine (hh (n + M)).trans ?_
      have hx : (M:ℝ) + 1 ≤ (n:ℝ) + ((M+1:ℕ):ℝ) := by
        push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have e : (((n + M : ℕ) : ℝ) + 1) = (n:ℝ) + ((M+1:ℕ):ℝ) := by push_cast; ring
      rw [e]
      set x := (n:ℝ) + ((M+1:ℕ):ℝ)
      have hx0 : 0 < x := by linarith
      rw [show x^J = x^(J-2) * x^2 by rw [← pow_add]; congr 1; omega]
      rw [div_mul_div_comm, mul_one]
      gcongr
    calc ∑ n ∈ Finset.range L, ‖h (n + M)‖
        ≤ ∑ n ∈ Finset.range L, D / ((M:ℝ) + 1)^(J-2) * (1 / ((n:ℝ) + ((M + 1 : ℕ) : ℝ))^2) :=
          Finset.sum_le_sum fun n _ => hb n
      _ = D / ((M:ℝ) + 1)^(J-2) * ∑ n ∈ Finset.range L, 1 / ((n:ℝ) + ((M + 1 : ℕ) : ℝ))^2 := by
          rw [Finset.mul_sum]
      _ ≤ D / ((M:ℝ) + 1)^(J-2) * (2 / ((M + 1 : ℕ) : ℝ)) := by
          gcongr
          refine (tel (M+1) (by omega) L).trans ?_
          have : 0 ≤ 2 / ((L:ℝ) + ((M+1:ℕ):ℝ)) := by positivity
          linarith
      _ = 2 * D / ((M:ℝ) + 1)^(J-1) := by
          have hJ' : J - 1 = (J - 2) + 1 := by omega
          rw [hJ', pow_succ]
          push_cast
          field_simp
  have hs0 : Summable (fun n => ‖h n‖) :=
    summable_of_sum_range_le (fun _ => norm_nonneg _) (fun L => by simpa using part 0 L)
  refine ⟨hs0.of_norm, fun M => ?_⟩
  have hsM : Summable (fun n => ‖h (n + M)‖) := (summable_nat_add_iff M).2 hs0
  rw [← hs0.of_norm.sum_add_tsum_nat_add M, add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm hsM).trans ?_
  exact Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) (part M)

theorem hHat_neg {w : ℝ → ℝ} (hw : IsWeight w) (t ξ : ℝ) :
    hHat w t (-ξ) = (starRingEnd ℂ) (hHat w (-t) ξ) := by
  rw [GuthMaynardS56.hHat_eq, GuthMaynardS56.hHat_eq, ← integral_conj]
  congr 1; funext u
  by_cases hu : 0 < u
  · simp only [map_mul, Complex.conj_ofReal]
    congr 2
    · have := Complex.conj_cpow (u:ℂ) (((-t:ℝ):ℂ) * I)
        (by rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_ne_zero.symm)
      rw [Complex.conj_ofReal] at this
      rw [this]; simp [map_mul]
    · unfold GuthMaynardS56.Ec; rw [← Complex.exp_conj]; congr 1; simp [map_mul]
      left; left; exact (map_ofNat _ 2).symm
  · have : w u = 0 := by
      by_contra h
      have := hw.support_subset h
      exact hu (by linarith [this.1])
    simp [this]

theorem norm_Asum_le {w : ℝ → ℝ} (hw : IsWeight w) (J : ℕ) (hJ : 2 ≤ J) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ (M : ℕ) (t : ℝ),
      ‖Asum w N t‖ ≤ ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ +
        ‖∑ m ∈ Finset.Icc 1 M, hHat w (-t) ((m : ℝ) * N)‖ +
        C * (1 + |t|) ^ J / ((N : ℝ) ^ J * ((M : ℝ) + 1) ^ (J - 1)) := by
  obtain ⟨C, hC0, hC⟩ := decay hw J
  refine ⟨4 * C, fun N hN M t => ?_⟩
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  set D := C * (1 + |t|)^J / (N:ℝ)^J with hDdef
  have hD : 0 ≤ D := by positivity
  let hp : ℕ → ℂ := fun n => hHat w t (((n:ℝ) + 1) * N)
  let hm : ℕ → ℂ := fun n => hHat w t (-(((n:ℝ) + 1) * N))
  have bp : ∀ n : ℕ, ‖hp n‖ ≤ D / ((n:ℝ)+1)^J := by
    intro n
    have := hC t N hN ((n:ℤ)+1) (by omega)
    rw [show (((n:ℤ)+1 : ℤ) : ℝ) = (n:ℝ)+1 by push_cast; ring,
      abs_of_pos (show (0:ℝ) < (n:ℝ)+1 by positivity)] at this
    rw [hDdef, div_div]; exact this
  have bm : ∀ n : ℕ, ‖hm n‖ ≤ D / ((n:ℝ)+1)^J := by
    intro n
    have := hC t N hN (-((n:ℤ)+1)) (by omega)
    rw [show ((-((n:ℤ)+1) : ℤ) : ℝ) = -((n:ℝ)+1) by push_cast; ring, abs_neg,
      abs_of_pos (show (0:ℝ) < (n:ℝ)+1 by positivity), neg_mul] at this
    rw [hDdef, div_div]; exact this
  obtain ⟨sp, tp⟩ := tail_generic hp hD hJ bp
  obtain ⟨sm, tm⟩ := tail_generic hm hD hJ bm
  have hA : Asum w N t = ∑' n, hp n + ∑' n, hm n := by
    have e : Asum w N t = ∑' z : ({z : ℤ | z ≠ 0} : Set ℤ), hHat w t (((z:ℤ):ℝ) * N) := rfl
    rw [e, tsum_subtype ({z : ℤ | z ≠ 0} : Set ℤ) (fun z : ℤ => hHat w t ((z:ℝ) * N))]
    set F := ({z : ℤ | z ≠ 0} : Set ℤ).indicator (fun z : ℤ => hHat w t ((z:ℝ) * N)) with hF
    have fp : (fun n : ℕ => F (n + 1)) = hp := by
      funext n
      rw [hF, Set.indicator_of_mem (by simp; omega)]
      simp [hp]
    have fm : (fun n : ℕ => F (-(n + 1))) = hm := by
      funext n
      rw [hF, Set.indicator_of_mem (by simp; omega)]
      simp [hm]
      congr 1; ring
    rw [tsum_of_add_one_of_neg_add_one (by rw [fp]; exact sp) (by rw [fm]; exact sm), fp, fm]
    simp [F]
  have pp : ∀ M : ℕ, ∑ i ∈ Finset.range M, hp i = ∑ m ∈ Finset.Icc 1 M, hHat w t ((m:ℝ) * N) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
      simp [hp]
  have pm : ∀ M : ℕ, ∑ i ∈ Finset.range M, hm i =
      starRingEnd ℂ (∑ m ∈ Finset.Icc 1 M, hHat w (-t) ((m:ℝ) * N)) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), map_add]
      simp only [hm]
      rw [hHat_neg hw]
      simp
  have split : Asum w N t = ∑ i ∈ Finset.range M, hp i + ∑ i ∈ Finset.range M, hm i +
      ((∑' n, hp n - ∑ i ∈ Finset.range M, hp i) + (∑' n, hm n - ∑ i ∈ Finset.range M, hm i)) := by
    rw [hA]; ring
  rw [split]
  refine (norm_add₃_le).trans ?_
  have := tp M
  have := tm M
  have h4 : ‖(∑' n, hp n - ∑ i ∈ Finset.range M, hp i) + (∑' n, hm n - ∑ i ∈ Finset.range M, hm i)‖
      ≤ 4 * C * (1 + |t|) ^ J / ((N : ℝ) ^ J * ((M : ℝ) + 1) ^ (J - 1)) := by
    refine (norm_add_le _ _).trans ?_
    have e : 4 * C * (1 + |t|) ^ J / ((N : ℝ) ^ J * ((M : ℝ) + 1) ^ (J - 1)) =
        2 * D / ((M:ℝ) + 1)^(J-1) + 2 * D / ((M:ℝ) + 1)^(J-1) := by
      rw [hDdef]; field_simp; ring
    rw [e]; linarith
  rw [pp, pm] at h4 ⊢
  rw [Complex.norm_conj]
  linarith

end GuthMaynard.S2.PartD
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
alias norm_Asum_le := GuthMaynard.S2.PartD.norm_Asum_le

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartE1
open Complex MeasureTheory FourierTransform
/-! Helpers on `Gw` (same proofs as in Part B, restated here so this file only needs the
Blueprint). -/

/-! Dirichlet polynomial facts. -/

/-! Cauchy–Schwarz for a nonnegative integrable weight. -/

/-! The three factors of the integrand in `norm_sum_hHat_le`. -/

end GuthMaynard.S2.PartE1
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part E: the approximate functional equation, squared; the sum over pairs -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartC
open Complex MeasureTheory FourierTransform

/-!
# Part C of the `S₂` Blueprint: the divisor bound, and Hölder + Heath-Brown

Helpers live in `S2PartC0.lean` (same namespace).
-/

end GuthMaynard.S2.PartC
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part C: the divisor bound, and Hölder + Heath-Brown -/

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartC
open Complex MeasureTheory FourierTransform
/-! ### Combinatorics of `(dpoly c M t)^k` -/

/-! ### Analytic helpers -/

/-! ### Exponent bookkeeping -/

end GuthMaynard.S2.PartC
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartE2
open Complex MeasureTheory FourierTransform
/-! Helpers for Part E2 (`sum_Asum_sq_le`). -/
/-! ### `Gw` and its Fourier transform (same proofs as Part B / E1) -/

/-! ### Dirichlet polynomials -/

/-! ### Integrals against a nonnegative integrable weight -/

/-! ### Counting shells -/

/-! ### Arithmetic -/

/-! ### Shells: the cut-off `M_j`, the per-pair bound -/

/-! ### The core estimate, with all constants given -/

/-! Part E2: `sum_Asum_sq_le`, from `norm_Asum_le`, `norm_sum_hHat_sq_le`, `lv_holder`
(Blueprint stubs) and the helpers of `S2PartE2a`. -/

end GuthMaynard.S2.PartE2
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
theorem sum_Asum_sq_le {w : ℝ → ℝ} (hw : IsWeight w) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ,
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      (N : ℝ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖Asum w N (t₁ - t₂)‖ ^ 2 ≤
        C * T ^ δ * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
          T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
            (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) := by
  exact GuthMaynard.sum_norm_tsum_hHat_sq_le w hw ε hε k hk

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartM
open Complex MeasureTheory FourierTransform
theorem norm_S_two_le_main (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 2 w N W‖ ≤ C * T ^ δ * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
        T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
        (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) := by
  intro δ hδ
  obtain ⟨CE, TE, hE⟩ := GuthMaynard.S2.sum_Asum_sq_le hw hε k hk δ hδ
  obtain ⟨CA, hCA⟩ := GuthMaynard.S2.norm_Asum_le hw 2 le_rfl
  obtain ⟨C0, hC0⟩ := GuthMaynardS56.hHat_bdd hw
  obtain ⟨Ck, hCk⟩ := GuthMaynardS56.hHat_decay_zero hw ⌈6 / ε⌉₊
  refine ⟨3 * (|C0| * |CE| + 32 * |Ck| * CA ^ 2), max TE 1, ?_⟩
  intro T hT N hN W a hsep hWi
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTE : TE ≤ T := le_trans (le_max_left _ _) hT
  have hT0 : 0 < T := by linarith
  have hN1R : (1:ℝ) ≤ N := le_trans (Real.one_le_rpow hT1 (by norm_num)) hN.1
  have hN1 : 1 ≤ N := by exact_mod_cast hN1R
  have hNT : (N:ℝ) ≤ T := hN.2
  set X := (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
        T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
        (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))
    with hX
  have hX0 : (N:ℝ) ^ 2 * (W.card : ℝ) ^ 2 ≤ X := by
    have h1 : 0 ≤ T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := by positivity
    have h2 : 0 ≤ (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
        (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ)) := by positivity
    linarith
  have hXnn : 0 ≤ X := le_trans (by positivity) hX0
  have hTd : 1 ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hτ : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hcard : (W.card : ℝ) ≤ T + 1 := GuthMaynardS56.card_le_of_sep hτ hT0.le hsep hWi
  have hE' := hE T hTE N hN W a hsep hWi
  have hS := GuthMaynard.S2.norm_S_two_le_sum hw N hN1 W
  have hdist : ∀ t₁ ∈ W, ∀ t₂ ∈ W, |t₁ - t₂| ≤ T := by
    intro t₁ h₁ t₂ h₂
    have a1 := hWi t₁ h₁
    have a2 := hWi t₂ h₂
    rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  -- crude bound on `A`
  have hAb : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ‖Asum w N (t₁ - t₂)‖ ≤ |CA| * (1 + T) ^ 2 := by
    intro t₁ h₁ t₂ h₂
    have h := hCA N hN1 0 (t₁ - t₂)
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at h
    have hI : Finset.Icc 1 0 = (∅ : Finset ℕ) := rfl
    rw [hI] at h
    simp only [Finset.sum_empty, norm_zero, zero_add] at h
    refine h.trans ?_
    have hN2 : (1:ℝ) ≤ (N:ℝ) ^ 2 := one_le_pow₀ hN1R
    have hd := hdist t₁ h₁ t₂ h₂
    calc CA * (1 + |t₁ - t₂|) ^ 2 / (N:ℝ) ^ 2 ≤ |CA| * (1 + |t₁ - t₂|) ^ 2 / (N:ℝ) ^ 2 := by
          gcongr; exact le_abs_self _
      _ ≤ |CA| * (1 + |t₁ - t₂|) ^ 2 := div_le_self (by positivity) hN2
      _ ≤ |CA| * (1 + T) ^ 2 := by gcongr
  -- decay of `ĥ_t(0)` off the diagonal
  have hz : ∀ t₁ ∈ W, ∀ t₃ ∈ W, t₃ ≠ t₁ → ‖hHat w (t₃ - t₁) 0‖ ≤ |Ck| / T ^ 6 := by
    intro t₁ h₁ t₃ h₃ hne
    have hs : T ^ ε ≤ |t₃ - t₁| := hsep t₃ h₃ t₁ h₁ hne
    have hs1 : 1 ≤ |t₃ - t₁| := hτ.trans hs
    have h := hCk (t₃ - t₁) hs1
    have hpow : T ^ 6 ≤ |t₃ - t₁| ^ ⌈6 / ε⌉₊ := by
      calc T ^ 6 = T ^ (6:ℝ) := by norm_cast
        _ ≤ T ^ (ε * ⌈6 / ε⌉₊) := by
          apply Real.rpow_le_rpow_of_exponent_le hT1
          have := Nat.le_ceil (6 / ε)
          calc (6:ℝ) = ε * (6 / ε) := by field_simp
            _ ≤ ε * ⌈6 / ε⌉₊ := by gcongr
        _ = (T ^ ε) ^ ⌈6 / ε⌉₊ := by rw [Real.rpow_mul hT0.le]; norm_cast
        _ ≤ |t₃ - t₁| ^ ⌈6 / ε⌉₊ := by gcongr
    have hT6 : 0 < T ^ 6 := by positivity
    rw [le_div_iff₀ hT6]
    calc ‖hHat w (t₃ - t₁) 0‖ * T ^ 6 ≤ ‖hHat w (t₃ - t₁) 0‖ * |t₃ - t₁| ^ ⌈6 / ε⌉₊ := by
          gcongr
      _ ≤ Ck := h
      _ ≤ |Ck| := le_abs_self _
  set B := |Ck| / T ^ 6 * (|CA| * (1 + T) ^ 2) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set Af := fun t₁ t₂ : ℝ => ‖Asum w N (t₁ - t₂)‖ with hAf
  have hterm : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W,
      ‖hHat w (t₃ - t₁) 0‖ * ‖Asum w N (t₁ - t₂)‖ * ‖Asum w N (t₂ - t₃)‖ ≤
        (if t₁ = t₃ then |C0| * ((Af t₁ t₂) ^ 2 + (Af t₂ t₁) ^ 2) / 2 else 0) + B := by
    intro t₁ h₁ t₂ h₂ t₃ h₃
    by_cases he : t₁ = t₃
    · subst he
      rw [if_pos rfl]
      have hc : ‖hHat w (t₁ - t₁) 0‖ ≤ |C0| := (hC0 _ _).trans (le_abs_self _)
      have p1 : 0 ≤ Af t₁ t₂ := norm_nonneg _
      have p2 : 0 ≤ Af t₂ t₁ := norm_nonneg _
      have : ‖hHat w (t₁ - t₁) 0‖ * Af t₁ t₂ * Af t₂ t₁ ≤ |C0| * (Af t₁ t₂ * Af t₂ t₁) := by
        rw [mul_assoc]; gcongr
      have hab : Af t₁ t₂ * Af t₂ t₁ ≤ ((Af t₁ t₂) ^ 2 + (Af t₂ t₁) ^ 2) / 2 := by
        nlinarith [sq_nonneg (Af t₁ t₂ - Af t₂ t₁)]
      have : |C0| * (Af t₁ t₂ * Af t₂ t₁) ≤ |C0| * (((Af t₁ t₂) ^ 2 + (Af t₂ t₁) ^ 2) / 2) := by
        gcongr
      simp only [hAf] at *
      linarith
    · rw [if_neg he, zero_add]
      have h1 := hz t₁ h₁ t₃ h₃ (Ne.symm he)
      have h2 := hAb t₁ h₁ t₂ h₂
      have h3 := hAb t₂ h₂ t₃ h₃
      rw [hB, sq]
      calc ‖hHat w (t₃ - t₁) 0‖ * ‖Asum w N (t₁ - t₂)‖ * ‖Asum w N (t₂ - t₃)‖
          ≤ |Ck| / T ^ 6 * (|CA| * (1 + T) ^ 2) * (|CA| * (1 + T) ^ 2) := by gcongr
        _ = _ := by ring
  set Ssq := ∑ t₁ ∈ W, ∑ t₂ ∈ W, (Af t₁ t₂) ^ 2 with hSsq
  have hsum : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ‖hHat w (t₃ - t₁) 0‖ * ‖Asum w N (t₁ - t₂)‖ * ‖Asum w N (t₂ - t₃)‖ ≤
        |C0| * Ssq + (W.card : ℝ) ^ 3 * B := by
    calc _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ((if t₁ = t₃ then |C0| * ((Af t₁ t₂) ^ 2 + (Af t₂ t₁) ^ 2) / 2 else 0) + B) :=
          Finset.sum_le_sum fun t₁ h₁ => Finset.sum_le_sum fun t₂ h₂ =>
            Finset.sum_le_sum fun t₃ h₃ => hterm t₁ h₁ t₂ h₂ t₃ h₃
      _ = ∑ t₁ ∈ W, ∑ t₂ ∈ W, (|C0| / 2 * (Af t₁ t₂) ^ 2 + |C0| / 2 * (Af t₂ t₁) ^ 2 +
            (W.card : ℝ) * B) :=
          Finset.sum_congr rfl fun t₁ h₁ => Finset.sum_congr rfl fun t₂ _ => by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos h₁, Finset.sum_const,
              nsmul_eq_mul]
            ring
      _ = |C0| / 2 * Ssq + |C0| / 2 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, (Af t₂ t₁) ^ 2 +
            (W.card : ℝ) ^ 3 * B := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hSsq]
          ring
      _ = |C0| * Ssq + (W.card : ℝ) ^ 3 * B := by
          rw [show ∑ t₁ ∈ W, ∑ t₂ ∈ W, (Af t₂ t₁) ^ 2 = Ssq from Finset.sum_comm]
          ring
  have hR : (N:ℝ) * W.card * (1 + T) ^ 4 ≤ 32 * T ^ 6 := by
    have a1 : (W.card:ℝ) ≤ 2 * T := by linarith
    have a2 : (1 + T) ^ 4 ≤ (2 * T) ^ 4 := by gcongr; linarith
    calc (N:ℝ) * W.card * (1 + T) ^ 4 ≤ T * (2 * T) * (2 * T) ^ 4 := by gcongr
      _ = 32 * T ^ 6 := by ring
  have hBb : (N:ℝ) ^ 3 * (W.card : ℝ) ^ 3 * B ≤
      32 * |Ck| * CA ^ 2 * ((N:ℝ) ^ 2 * (W.card : ℝ) ^ 2) := by
    have e : (N:ℝ) ^ 3 * (W.card : ℝ) ^ 3 * B = |Ck| * CA ^ 2 * ((N:ℝ) ^ 2 * (W.card : ℝ) ^ 2) *
        (((N:ℝ) * W.card * (1 + T) ^ 4) / T ^ 6) := by
      rw [hB, mul_pow, sq_abs]; ring
    rw [e]
    have : ((N:ℝ) * W.card * (1 + T) ^ 4) / T ^ 6 ≤ 32 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    calc _ ≤ |Ck| * CA ^ 2 * ((N:ℝ) ^ 2 * (W.card : ℝ) ^ 2) * 32 := by gcongr
      _ = _ := by ring
  have hE2 : (N:ℝ) ^ 3 * Ssq ≤ |CE| * T ^ δ * X := by
    refine hE'.trans ?_
    gcongr
    exact le_abs_self _
  have hX1 : (N:ℝ) ^ 2 * (W.card : ℝ) ^ 2 ≤ T ^ δ * X :=
    hX0.trans (le_mul_of_one_le_left hXnn hTd)
  calc ‖S 2 w N W‖ ≤ 3 * (N:ℝ) ^ 3 * (|C0| * Ssq + (W.card : ℝ) ^ 3 * B) := by
        refine hS.trans ?_
        gcongr
    _ = 3 * |C0| * ((N:ℝ) ^ 3 * Ssq) + 3 * ((N:ℝ) ^ 3 * (W.card : ℝ) ^ 3 * B) := by ring
    _ ≤ 3 * |C0| * (|CE| * T ^ δ * X) +
          3 * (32 * |Ck| * CA ^ 2 * ((N:ℝ) ^ 2 * (W.card : ℝ) ^ 2)) := by gcongr
    _ ≤ 3 * |C0| * (|CE| * T ^ δ * X) + 3 * (32 * |Ck| * CA ^ 2 * (T ^ δ * X)) := by gcongr
    _ = _ := by ring

end GuthMaynard.S2.PartM
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Main -/
alias norm_S_two_le_main := GuthMaynard.S2.PartM.norm_S_two_le_main

end GuthMaynard.S2
end

section
namespace GuthMaynard
theorem norm_S_two_le_dev (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 2 w N W‖ ≤ C * T ^ δ * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
        T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
        (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) :=
  S2.norm_S_two_le_main w hw ε hε k hk

end GuthMaynard
end

section
open GuthMaynard
theorem solution (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 2 w N W‖ ≤ C * T ^ δ * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
        T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
        (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 * (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) := by
  exact GuthMaynard.norm_S_two_le_dev w hw ε hε k hk
end
