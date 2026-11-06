-- Prove2me | solution 1 for GuthMaynard.sum_norm_tsum_hHat_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:49:40.385543+00:00
-- url     : https://prove2.me/submissions/bc7ba2d6-9ac2-4046-9852-98f7edf667d0

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_norm_sum_hHat_sq_le
import Theorems.Thm_GuthMaynard_sum_norm_dirichlet_poly_sq_le
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

theorem hHat_decay_freq {w : ℝ → ℝ} (hw : GuthMaynard.IsWeight w) (k : ℕ) :
    ∃ C : ℝ, ∀ t ξ : ℝ, ξ ≠ 0 → ‖GuthMaynard.hHat w t ξ‖ * |ξ|^k ≤ C * (1 + |t|)^k := by
  obtain ⟨C, hC⟩ := decay_freq k _ (ampW hw)
  exact ⟨C, fun t ξ hξ => by rw [hHat_eq]; exact hC t ξ hξ⟩

end GuthMaynardS56
end

section
namespace GuthMaynardS56

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

/-- The Dirichlet polynomial `∑_{1 ≤ m ≤ M} c_m m^{it}`. -/
noncomputable def dpoly (c : ℕ → ℂ) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, c m * (m : ℂ) ^ ((t : ℂ) * I)

/-- `G(x) = eˣ w(eˣ)²`, so that `w(u)² = u⁻¹ G(log u)` for `u > 0`. -/
noncomputable def Gw (w : ℝ → ℝ) (x : ℝ) : ℂ :=
  ((Real.exp x * w (Real.exp x) ^ 2 : ℝ) : ℂ)

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

end GuthMaynard.S2.PartD
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part D: reduction of `S₂` and the splitting of `A(t)` -/

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
theorem norm_sum_hHat_sq_le {w : ℝ → ℝ} (hw : IsWeight w) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N M : ℕ, 1 ≤ N → 1 ≤ M → (M : ℝ) ≤ T ^ 2 →
      ∀ t : ℝ, T ^ ε ≤ |t| →
        ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ^ 2 ≤
          C / |t| * (∫ ρ, ‖𝓕 (Gw w) ρ‖ * ‖dpoly (fun _ => 1) M (-(t + 2 * Real.pi * ρ))‖ ^ 2) +
            T ^ (-100 : ℝ) := by
  obtain ⟨C, T₀, h⟩ := GuthMaynard.norm_sum_hHat_sq_le w hw ε hε
  refine ⟨C, T₀, fun T hT N M hN hM hMT t ht => ?_⟩
  have := h T hT N M hN hM hMT t ht
  simpa only [dpoly, one_mul, show Gw w = (fun x : ℝ => ((Real.exp x * w (Real.exp x) ^ 2 : ℝ) : ℂ)) from rfl] using this

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
theorem lv_holder (k : ℕ) (hk : 1 ≤ k) : ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
    ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ m, ‖c m‖ ≤ 1) →
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖dpoly c M (t₁ - t₂)‖ ^ 2 ≤
        C * T ^ δ * ((W.card : ℝ) ^ 2 * M + (M : ℝ) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) * M) := by
  exact GuthMaynard.sum_norm_dirichlet_poly_sq_le k hk

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartE2
open Complex MeasureTheory FourierTransform
/-! Helpers for Part E2 (`sum_Asum_sq_le`). -/
/-! ### `Gw` and its Fourier transform (same proofs as Part B / E1) -/
theorem Gw_contDiff {w : ℝ → ℝ} (hw : IsWeight w) : ContDiff ℝ (⊤ : ℕ∞) (Gw w) := by
  unfold Gw
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.mul ((hw.smooth.comp Real.contDiff_exp).pow 2))

theorem Gw_zero {w : ℝ → ℝ} (hw : IsWeight w) {x : ℝ} (hx : x ∉ Set.Icc 0 (Real.log 2)) :
    Gw w x = 0 := by
  unfold Gw
  have : w (Real.exp x) = 0 := by
    by_contra h
    have h2 := hw.support_subset (Function.mem_support.2 h)
    apply hx
    refine ⟨?_, ?_⟩
    · have := h2.1; by_contra hlt
      have := Real.exp_lt_exp.mpr (not_le.mp hlt); rw [Real.exp_zero] at this; linarith
    · rw [Real.le_log_iff_exp_le (by norm_num)]; exact h2.2
  simp [this]

theorem Gw_hasCompactSupport {w : ℝ → ℝ} (hw : IsWeight w) : HasCompactSupport (Gw w) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => Gw_zero hw hx)

noncomputable def GwS {w : ℝ → ℝ} (hw : IsWeight w) : SchwartzMap ℝ ℂ :=
  (Gw_hasCompactSupport hw).toSchwartzMap (Gw_contDiff hw)

theorem fourier_GwS {w : ℝ → ℝ} (hw : IsWeight w) :
    ((𝓕 (GwS hw) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 (Gw w) := by
  rw [SchwartzMap.fourier_coe]; rfl

theorem fourier_Gw_integrable {w : ℝ → ℝ} (hw : IsWeight w) : Integrable (𝓕 (Gw w)) := by
  rw [← fourier_GwS hw]; exact (𝓕 (GwS hw)).integrable

/-! ### Dirichlet polynomials -/
theorem norm_dpoly_le (M : ℕ) (s : ℝ) : ‖dpoly (fun _ => 1) M s‖ ≤ M := by
  unfold dpoly
  refine (norm_sum_le _ _).trans ?_
  have : ∀ m ∈ Finset.Icc 1 M, ‖(1 : ℂ) * (m : ℂ) ^ ((s : ℂ) * I)‖ = 1 := fun m hm => by
    rw [one_mul, Complex.norm_natCast_cpow_of_pos (Finset.mem_Icc.1 hm).1]
    simp
  rw [Finset.sum_congr rfl this]
  simp

theorem continuous_dpoly (M : ℕ) : Continuous (fun s : ℝ => dpoly (fun _ => 1) M s) := by
  unfold dpoly
  refine continuous_finsetSum _ fun m hm => continuous_const.mul ?_
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  have := (Finset.mem_Icc.1 hm).1
  exact_mod_cast (show m ≠ 0 by omega)

theorem dpoly_shift (M : ℕ) (x y : ℝ) :
    dpoly (fun _ => 1) M (x + y) = dpoly (fun m => (m : ℂ) ^ ((y : ℂ) * I)) M x := by
  unfold dpoly
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (m : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.1 hm).1
    exact_mod_cast (show m ≠ 0 by omega)
  push_cast
  rw [add_mul, Complex.cpow_add _ _ hm0]; ring

theorem norm_c_le (y : ℝ) (m : ℕ) : ‖(m : ℂ) ^ ((y : ℂ) * I)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · by_cases h : (y : ℂ) * I = 0
    · simp [h]
    · simp [Complex.zero_cpow h]
  · rw [Complex.norm_natCast_cpow_of_pos hm]; simp

theorem dpoly_zero (c : ℕ → ℂ) (t : ℝ) : dpoly c 0 t = 0 := by
  simp [dpoly]

/-! ### Integrals against a nonnegative integrable weight -/
theorem sum_int_le {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ ρ, 0 ≤ f ρ) (W : Finset ℝ)
    (g : ℝ → ℝ → ℝ → ℝ) (hg : ∀ t₁ t₂, Continuous (g t₁ t₂)) (K : ℝ)
    (hgK : ∀ t₁ t₂ ρ, ‖g t₁ t₂ ρ‖ ≤ K) (B : ℝ)
    (hB : ∀ ρ, ∑ t₁ ∈ W, ∑ t₂ ∈ W, g t₁ t₂ ρ ≤ B) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, (∫ ρ, f ρ * g t₁ t₂ ρ) ≤ (∫ ρ, f ρ) * B := by
  have hint : ∀ t₁ t₂, Integrable (fun ρ => f ρ * g t₁ t₂ ρ) := fun t₁ t₂ => by
    refine (hf.const_mul K).mono'
      (hf.aestronglyMeasurable.mul (hg t₁ t₂).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun ρ => ?_
    rw [norm_mul, Real.norm_of_nonneg (hf0 ρ), mul_comm K]
    exact mul_le_mul_of_nonneg_left (hgK t₁ t₂ ρ) (hf0 ρ)
  have h1 : ∑ t₁ ∈ W, ∑ t₂ ∈ W, (∫ ρ, f ρ * g t₁ t₂ ρ) =
      ∫ ρ, ∑ t₁ ∈ W, ∑ t₂ ∈ W, f ρ * g t₁ t₂ ρ := by
    rw [integral_finsetSum _ (fun t₁ _ => integrable_finsetSum _ fun t₂ _ => hint t₁ t₂)]
    refine Finset.sum_congr rfl fun t₁ _ => ?_
    rw [integral_finsetSum _ (fun t₂ _ => hint t₁ t₂)]
  rw [h1, ← integral_mul_const]
  refine integral_mono (integrable_finsetSum _ fun t₁ _ =>
    integrable_finsetSum _ fun t₂ _ => hint t₁ t₂) (hf.mul_const B) fun ρ => ?_
  simp only [← Finset.mul_sum]
  rw [mul_comm (f ρ) B, mul_comm B]
  exact mul_le_mul_of_nonneg_left (hB ρ) (hf0 ρ)

/-- The integral of `E1`. -/
noncomputable def Ip (w : ℝ → ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  ∫ ρ, ‖𝓕 (Gw w) ρ‖ * ‖dpoly (fun _ => 1) M (-(t + 2 * Real.pi * ρ))‖ ^ 2

theorem Ip_nonneg (w : ℝ → ℝ) (M : ℕ) (t : ℝ) : 0 ≤ Ip w M t :=
  integral_nonneg fun ρ => by positivity

/-- The `ρ`-uniform large-values bound, summed against `‖Ĝ‖`. -/
theorem sum_Ip_le {w : ℝ → ℝ} (hw : IsWeight w) (W : Finset ℝ) (M : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hLV : 1 ≤ M → ∀ c : ℕ → ℂ, (∀ m, ‖c m‖ ≤ 1) →
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖dpoly c M (t₁ - t₂)‖ ^ 2 ≤ B) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, Ip w M (t₁ - t₂) ≤ (∫ ρ, ‖𝓕 (Gw w) ρ‖) * B ∧
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, Ip w M (-(t₁ - t₂)) ≤ (∫ ρ, ‖𝓕 (Gw w) ρ‖) * B := by
  have hLV' : ∀ c : ℕ → ℂ, (∀ m, ‖c m‖ ≤ 1) →
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖dpoly c M (t₁ - t₂)‖ ^ 2 ≤ B := by
    intro c hc
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp [dpoly_zero, hB0]
    · exact hLV hM c hc
  have hf := (fourier_Gw_integrable hw).norm
  have hf0 : ∀ ρ, 0 ≤ ‖𝓕 (Gw w) ρ‖ := fun ρ => norm_nonneg _
  have hK : ∀ s : ℝ, ‖‖dpoly (fun _ => 1) M s‖ ^ 2‖ ≤ (M : ℝ) ^ 2 := fun s => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_dpoly_le M s) 2
  constructor
  · refine sum_int_le hf hf0 W
      (fun t₁ t₂ ρ => ‖dpoly (fun _ => 1) M (-((t₁ - t₂) + 2 * Real.pi * ρ))‖ ^ 2)
      (fun t₁ t₂ => ((continuous_dpoly M).comp (by fun_prop)).norm.pow 2) _
      (fun _ _ _ => hK _) B fun ρ => ?_
    have e : ∀ t₁ t₂ : ℝ, ‖dpoly (fun _ => 1) M (-((t₁ - t₂) + 2 * Real.pi * ρ))‖ ^ 2 =
        ‖dpoly (fun m => (m : ℂ) ^ (((-(2 * Real.pi * ρ) : ℝ) : ℂ) * I)) M (t₂ - t₁)‖ ^ 2 := by
      intro t₁ t₂
      rw [← dpoly_shift]; congr 3; ring
    simp only [e]
    rw [Finset.sum_comm]
    exact hLV' _ fun m => norm_c_le _ m
  · refine sum_int_le hf hf0 W
      (fun t₁ t₂ ρ => ‖dpoly (fun _ => 1) M (-(-(t₁ - t₂) + 2 * Real.pi * ρ))‖ ^ 2)
      (fun t₁ t₂ => ((continuous_dpoly M).comp (by fun_prop)).norm.pow 2) _
      (fun _ _ _ => hK _) B fun ρ => ?_
    have e : ∀ t₁ t₂ : ℝ, ‖dpoly (fun _ => 1) M (-(-(t₁ - t₂) + 2 * Real.pi * ρ))‖ ^ 2 =
        ‖dpoly (fun m => (m : ℂ) ^ (((-(2 * Real.pi * ρ) : ℝ) : ℂ) * I)) M (t₁ - t₂)‖ ^ 2 := by
      intro t₁ t₂
      rw [← dpoly_shift]; congr 3; ring
    simp only [e]
    exact hLV' _ fun m => norm_c_le _ m

/-! ### Counting shells -/
theorem log_count {η : ℝ} (hη : 0 < η) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) + 1 ≤ C * T ^ η := by
  have hb : 1 < (2 : ℝ) ^ η := Real.one_lt_rpow (by norm_num) hη
  refine ⟨1 / ((2 : ℝ) ^ η - 1) + 1, by
    have : 0 < (2 : ℝ) ^ η - 1 := by linarith
    positivity, fun T hT => ?_⟩
  have hfl : ⌊T⌋₊ ≠ 0 := (Nat.floor_pos.2 hT).ne'
  have h2m : ((2 : ℝ) ^ (Nat.log 2 ⌊T⌋₊)) ≤ T := by
    have := Nat.pow_log_le_self 2 hfl
    calc ((2 : ℝ) ^ (Nat.log 2 ⌊T⌋₊)) = ((2 ^ (Nat.log 2 ⌊T⌋₊) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ⌊T⌋₊ := by exact_mod_cast this
      _ ≤ T := Nat.floor_le (by linarith)
  have hbern : 1 + ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) * ((2 : ℝ) ^ η - 1) ≤
      ((2 : ℝ) ^ η) ^ (Nat.log 2 ⌊T⌋₊) := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ (2 : ℝ) ^ η - 1 by linarith) (Nat.log 2 ⌊T⌋₊)
    simpa using this
  have hbm : ((2 : ℝ) ^ η) ^ (Nat.log 2 ⌊T⌋₊) ≤ T ^ η := by
    calc ((2 : ℝ) ^ η) ^ (Nat.log 2 ⌊T⌋₊) = ((2 : ℝ) ^ (Nat.log 2 ⌊T⌋₊)) ^ η := by
          rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
      _ ≤ T ^ η := Real.rpow_le_rpow (by positivity) h2m hη.le
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hm : ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) ≤ T ^ η / ((2 : ℝ) ^ η - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  calc ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) + 1 ≤ T ^ η / ((2 : ℝ) ^ η - 1) + T ^ η := by linarith
    _ = (1 / ((2 : ℝ) ^ η - 1) + 1) * T ^ η := by ring

theorem shell {t : ℝ} (ht : 1 ≤ |t|) :
    (2 : ℝ) ^ (Nat.log 2 ⌊|t|⌋₊) ≤ |t| ∧ |t| < (2 : ℝ) ^ (Nat.log 2 ⌊|t|⌋₊ + 1) := by
  have hfl : ⌊|t|⌋₊ ≠ 0 := (Nat.floor_pos.2 ht).ne'
  constructor
  · calc (2 : ℝ) ^ (Nat.log 2 ⌊|t|⌋₊) = ((2 ^ Nat.log 2 ⌊|t|⌋₊ : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ⌊|t|⌋₊ := by exact_mod_cast Nat.pow_log_le_self 2 hfl
      _ ≤ |t| := Nat.floor_le (abs_nonneg t)
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊|t|⌋₊
    have h' : ⌊|t|⌋₊ + 1 ≤ 2 ^ (Nat.log 2 ⌊|t|⌋₊ + 1) := h
    calc |t| < ⌊|t|⌋₊ + 1 := Nat.lt_floor_add_one _
      _ ≤ ((2 ^ (Nat.log 2 ⌊|t|⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h'
      _ = _ := by push_cast; rfl

/-! ### Arithmetic -/
theorem shell_arith {N x y T M n A B : ℝ} (hN : 0 < N) (hx : 0 < x) (hy : 1 ≤ y) (hxT : x ≤ T)
    (hM0 : 0 ≤ M) (hM : M ≤ 4 * x * y / N) (hn : 0 ≤ n) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    N ^ 3 * (1 / x) * (n ^ 2 * M + M ^ 2 * A + B * M) ≤
      16 * y ^ 2 * (N ^ 2 * n ^ 2 + T * N * A + N ^ 2 * B) := by
  have hMN : M * N ≤ 4 * x * y := by rwa [le_div_iff₀ hN] at hM
  have hP : N ^ 3 * (1 / x) * M ≤ 4 * y * N ^ 2 := by
    rw [show N ^ 3 * (1 / x) * M = N ^ 2 * (M * N) / x by field_simp, div_le_iff₀ hx]
    have : N ^ 2 * (M * N) ≤ N ^ 2 * (4 * x * y) := mul_le_mul_of_nonneg_left hMN (by positivity)
    linarith
  have hP0 : 0 ≤ N ^ 3 * (1 / x) * M := by positivity
  have hy2 : 4 * y ≤ 16 * y ^ 2 := by nlinarith
  have e1 : N ^ 3 * (1 / x) * M * n ^ 2 ≤ 16 * y ^ 2 * (N ^ 2 * n ^ 2) := by
    calc N ^ 3 * (1 / x) * M * n ^ 2 ≤ 4 * y * N ^ 2 * n ^ 2 :=
          mul_le_mul_of_nonneg_right hP (by positivity)
      _ ≤ 16 * y ^ 2 * (N ^ 2 * n ^ 2) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hy2 (by positivity)) (by positivity)
  have e3 : N ^ 3 * (1 / x) * M * B ≤ 16 * y ^ 2 * (N ^ 2 * B) := by
    calc N ^ 3 * (1 / x) * M * B ≤ 4 * y * N ^ 2 * B :=
          mul_le_mul_of_nonneg_right hP hB
      _ ≤ 16 * y ^ 2 * (N ^ 2 * B) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hy2 (by positivity)) hB
  have e2 : N ^ 3 * (1 / x) * M * (M * A) ≤ 16 * y ^ 2 * (T * N * A) := by
    calc N ^ 3 * (1 / x) * M * (M * A) ≤ 4 * y * N ^ 2 * (M * A) :=
          mul_le_mul_of_nonneg_right hP (by positivity)
      _ = 4 * y * N * (M * N) * A := by ring
      _ ≤ 4 * y * N * (4 * x * y) * A := by gcongr
      _ ≤ 4 * y * N * (4 * T * y) * A := by gcongr
      _ = 16 * y ^ 2 * (T * N * A) := by ring
  have : N ^ 3 * (1 / x) * (n ^ 2 * M + M ^ 2 * A + B * M) =
      N ^ 3 * (1 / x) * M * n ^ 2 + N ^ 3 * (1 / x) * M * (M * A) +
        N ^ 3 * (1 / x) * M * B := by ring
  rw [this]; nlinarith

theorem four_mul_le {T η : ℝ} (hT : 16 ≤ T) (hη : η ≤ 1 / 2) :
    4 * T * T ^ η ≤ T ^ 2 := by
  have h1 : T ^ η ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hη
  rw [← Real.sqrt_eq_rpow] at h1
  have h4 : 4 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by linarith)
  have hs : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (by linarith)
  have hT0 : 0 ≤ T := by linarith
  calc 4 * T * T ^ η ≤ 4 * T * Real.sqrt T := by gcongr
    _ ≤ Real.sqrt T * T * Real.sqrt T := by gcongr
    _ = T ^ 2 := by rw [mul_comm (Real.sqrt T) T, mul_assoc, hs]; ring

theorem rpow_bracket {n T : ℝ} (hn : 0 < n) (hT : 0 ≤ T) (k : ℕ) (hk : 1 ≤ k) :
    n ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) =
      n ^ 2 * (T ^ (1 / 2 : ℝ) / n ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hT, ← Real.rpow_mul hn.le,
    Real.rpow_sub hn, Real.rpow_two]
  have e1 : (1 / 2 : ℝ) * (1 / k) = 1 / (2 * k) := by field_simp
  have e2 : (3 / 4 : ℝ) * (1 / k) = 3 / (4 * k) := by field_simp
  rw [e1, e2]; ring

/-! ### Shells: the cut-off `M_j`, the per-pair bound -/
noncomputable def Mj (T η : ℝ) (N j : ℕ) : ℕ := ⌊(2 : ℝ) ^ (j + 2) * T ^ η / N⌋₊

theorem Mj_le {T η : ℝ} {N j : ℕ} (hT : 16 ≤ T) (hη : η ≤ 1 / 2) (hN : (1 : ℝ) ≤ N)
    (hj : (2 : ℝ) ^ j ≤ T) :
    (Mj T η N j : ℝ) ≤ T ^ 2 ∧ (Mj T η N j : ℝ) ≤ 4 * 2 ^ j * T ^ η / N := by
  have hT0 : 0 < T := by linarith
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 2) * T ^ η / N := by positivity
  have h1 : (Mj T η N j : ℝ) ≤ (2 : ℝ) ^ (j + 2) * T ^ η / N := Nat.floor_le h0
  have e : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
  refine ⟨?_, by rw [e] at h1; exact h1⟩
  calc _ ≤ (2 : ℝ) ^ (j + 2) * T ^ η / N := h1
    _ ≤ (2 : ℝ) ^ (j + 2) * T ^ η := div_le_self (by positivity) hN
    _ = 4 * 2 ^ j * T ^ η := by ring
    _ ≤ 4 * T * T ^ η := by gcongr
    _ ≤ T ^ 2 := four_mul_le hT hη

theorem two_pow_le {T : ℝ} (hT : 1 ≤ T) {j : ℕ} (hj : j ≤ Nat.log 2 ⌊T⌋₊) : (2 : ℝ) ^ j ≤ T := by
  have hfl : ⌊T⌋₊ ≠ 0 := (Nat.floor_pos.2 hT).ne'
  calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (Nat.log 2 ⌊T⌋₊) := pow_le_pow_right₀ (by norm_num) hj
    _ = ((2 ^ (Nat.log 2 ⌊T⌋₊) : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ⌊T⌋₊ := by exact_mod_cast Nat.pow_log_le_self 2 hfl
    _ ≤ T := Nat.floor_le (by linarith)

theorem pair_bound {w : ℝ → ℝ} {N K : ℕ} {T η ε C_A C_E : ℝ} (hN : (1 : ℝ) ≤ N) (hT : 16 ≤ T)
    (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hCA : 0 ≤ C_A) (hCE : 0 ≤ C_E)
    (hA : ∀ (M : ℕ) (t : ℝ), ‖Asum w N t‖ ≤ ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ +
        ‖∑ m ∈ Finset.Icc 1 M, hHat w (-t) ((m : ℝ) * N)‖ +
        C_A * (1 + |t|) ^ (K + 1) / ((N : ℝ) ^ (K + 1) * ((M : ℝ) + 1) ^ (K + 1 - 1)))
    (hE : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ t : ℝ, T ^ ε ≤ |t| →
        ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ^ 2 ≤
          C_E / |t| * Ip w M t + T ^ (-100 : ℝ))
    {t : ℝ} (htε : T ^ ε ≤ |t|) (ht1 : 1 ≤ |t|) (htT : |t| ≤ T) :
    ‖Asum w N t‖ ^ 2 ≤
      3 * C_E * (1 / 2 ^ (Nat.log 2 ⌊|t|⌋₊)) *
          (Ip w (Mj T η N (Nat.log 2 ⌊|t|⌋₊)) t + Ip w (Mj T η N (Nat.log 2 ⌊|t|⌋₊)) (-t)) +
        (6 * T ^ (-100 : ℝ) + 3 * (C_A * (1 + T) * (T ^ (-η)) ^ K) ^ 2) := by
  obtain ⟨hj1, hj2⟩ := shell ht1
  set j := Nat.log 2 ⌊|t|⌋₊ with hj
  have hT0 : 0 < T := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hTη : 0 < T ^ η := Real.rpow_pos_of_pos hT0 η
  have h2j : (2 : ℝ) ^ j ≤ T := hj1.trans htT
  have hMT : (Mj T η N j : ℝ) ≤ T ^ 2 := (Mj_le hT hη2 hN h2j).1
  have hMlt : (2 : ℝ) ^ (j + 2) * T ^ η / N < (Mj T η N j : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hN0] at hMlt
  set M := Mj T η N j with hMdef
  set τ₀ := C_A * (1 + T) * (T ^ (-η)) ^ K with hτ₀
  have hτ0 : 0 ≤ τ₀ := by positivity
  have htail : C_A * (1 + |t|) ^ (K + 1) / ((N : ℝ) ^ (K + 1) * ((M : ℝ) + 1) ^ (K + 1 - 1)) ≤
      τ₀ := by
    rw [show K + 1 - 1 = K by omega]
    have hr : (1 + |t|) / (((M : ℝ) + 1) * N) ≤ T ^ (-η) := by
      have h1 : 1 + |t| ≤ (2 : ℝ) ^ (j + 2) := by
        have : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
        rw [this]; linarith
      rw [Real.rpow_neg hT0.le, ← one_div, div_le_div_iff₀ (by positivity) hTη]
      nlinarith [mul_le_mul_of_nonneg_right h1 hTη.le]
    have hfirst : (1 + |t|) / N ≤ 1 + T := by
      rw [div_le_iff₀ hN0]; nlinarith
    have e : (1 + |t|) ^ (K + 1) / ((N : ℝ) ^ (K + 1) * ((M : ℝ) + 1) ^ K) =
        (1 + |t|) / N * ((1 + |t|) / (((M : ℝ) + 1) * N)) ^ K := by
      rw [div_pow, mul_pow, pow_succ, pow_succ]; field_simp; try ring
    rw [mul_div_assoc, e, hτ₀, mul_assoc]
    gcongr
  have hS : ∀ s : ℝ, |s| = |t| → ‖∑ m ∈ Finset.Icc 1 M, hHat w s ((m : ℝ) * N)‖ ^ 2 ≤
      C_E / |t| * Ip w M s + T ^ (-100 : ℝ) := by
    intro s hs
    rcases Nat.eq_zero_or_pos M with hM | hM
    · have h0 : Finset.Icc 1 M = ∅ := by rw [hM]; rfl
      rw [h0, Finset.sum_empty, norm_zero, zero_pow two_ne_zero]
      exact add_nonneg (mul_nonneg (div_nonneg hCE (abs_nonneg _)) (Ip_nonneg _ _ _))
        (Real.rpow_nonneg hT0.le _)
    · rw [← hs]; exact hE M hM hMT s (hs ▸ htε)
  have hp := hS t rfl
  have hm := hS (-t) (abs_neg t)
  set a := ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖
  set b := ‖∑ m ∈ Finset.Icc 1 M, hHat w (-t) ((m : ℝ) * N)‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hAt : ‖Asum w N t‖ ≤ a + b + τ₀ := (hA M t).trans (by linarith [htail])
  have hsq : ‖Asum w N t‖ ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + τ₀ ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hAt 2
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - τ₀), sq_nonneg (b - τ₀)]
  have hdiv : C_E / |t| ≤ C_E * (1 / 2 ^ j) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_left hCE (by positivity) hj1
  have hI1 := mul_le_mul_of_nonneg_right hdiv (Ip_nonneg w M t)
  have hI2 := mul_le_mul_of_nonneg_right hdiv (Ip_nonneg w M (-t))
  nlinarith

theorem diag_bound {w : ℝ → ℝ} {N K : ℕ} {C_A : ℝ} (hN : (1 : ℝ) ≤ N) (hCA : 0 ≤ C_A)
    (hA : ∀ (M : ℕ) (t : ℝ), ‖Asum w N t‖ ≤ ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ +
        ‖∑ m ∈ Finset.Icc 1 M, hHat w (-t) ((m : ℝ) * N)‖ +
        C_A * (1 + |t|) ^ (K + 1) / ((N : ℝ) ^ (K + 1) * ((M : ℝ) + 1) ^ (K + 1 - 1))) :
    ‖Asum w N 0‖ ^ 2 ≤ C_A ^ 2 / N := by
  have h := hA 0 0
  have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := rfl
  rw [h0, Finset.sum_empty, Finset.sum_empty, norm_zero] at h
  simp only [abs_zero, add_zero, Nat.cast_zero, zero_add, one_pow, mul_one] at h
  have hN0 : (0 : ℝ) < N := by linarith
  have hpow : (N : ℝ) ≤ (N : ℝ) ^ (K + 1) := le_self_pow₀ hN (by omega)
  have h1 : ‖Asum w N 0‖ ≤ C_A / N := h.trans (div_le_div_of_nonneg_left hCA hN0 hpow)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ‖Asum w N 0‖ ^ 2 ≤ (C_A / N) ^ 2 := h2
    _ = C_A ^ 2 / N / N := by ring
    _ ≤ C_A ^ 2 / N := div_le_self (by positivity) hN

theorem err_small {T η C N : ℝ} {K : ℕ} (hT : 1 ≤ T) (hηK : 2 ≤ η * K) (hN1 : 1 ≤ N)
    (hNT : N ≤ T) (hC : 0 ≤ C) :
    N * (6 * T ^ (-100 : ℝ) + 3 * (C * (1 + T) * (T ^ (-η)) ^ K) ^ 2) ≤ 6 + 12 * C ^ 2 := by
  have hT0 : 0 < T := by linarith
  have e : (T ^ (-η)) ^ K = T ^ (-(η * K)) := by
    rw [← Real.rpow_mul_natCast hT0.le]; ring_nf
  rw [e]
  set u := T ^ (-(η * K)) with hu
  have hu0 : 0 ≤ u := by positivity
  have huT : u * T ^ 2 ≤ 1 := by
    have h1 : u ≤ T ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
    have h2 : T ^ (-2 : ℝ) * T ^ 2 = 1 := by
      rw [Real.rpow_neg hT0.le, Real.rpow_two]; field_simp
    calc u * T ^ 2 ≤ T ^ (-2 : ℝ) * T ^ 2 := by gcongr
      _ = 1 := h2
  have h1 : N * T ^ (-100 : ℝ) ≤ 1 := by
    calc N * T ^ (-100 : ℝ) ≤ T * T ^ (-100 : ℝ) := by gcongr
      _ = T ^ (-99 : ℝ) := by
          rw [show (-99 : ℝ) = 1 + (-100) by norm_num, Real.rpow_add hT0, Real.rpow_one]
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num)
  have huT1 : u * T ≤ 1 := by nlinarith
  have h2 : N * (1 + T) ^ 2 * u ^ 2 ≤ 4 := by
    calc N * (1 + T) ^ 2 * u ^ 2 ≤ T * (2 * T) ^ 2 * u ^ 2 := by gcongr; linarith
      _ = 4 * (u * T ^ 2) * (u * T) := by ring
      _ ≤ 4 * 1 * 1 := by gcongr
      _ = 4 := by norm_num
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg C)
  nlinarith

/-! ### The core estimate, with all constants given -/
set_option maxHeartbeats 1000000 in
theorem core {w : ℝ → ℝ} (hw : IsWeight w) {N K : ℕ} {T η ε δL C_A C_E C_L C_c A' B' : ℝ}
    (W : Finset ℝ) (a : ℝ)
    (hT : 16 ≤ T) (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hηK : 2 ≤ η * K)
    (hN1 : (1 : ℝ) ≤ N) (hNT : (N : ℝ) ≤ T)
    (hCA : 0 ≤ C_A) (hCE : 0 ≤ C_E) (hCL : 0 ≤ C_L) (hCc : 0 ≤ C_c) (hA' : 0 ≤ A')
    (hB' : 0 ≤ B')
    (hA : ∀ (M : ℕ) (t : ℝ), ‖Asum w N t‖ ≤ ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ +
        ‖∑ m ∈ Finset.Icc 1 M, hHat w (-t) ((m : ℝ) * N)‖ +
        C_A * (1 + |t|) ^ (K + 1) / ((N : ℝ) ^ (K + 1) * ((M : ℝ) + 1) ^ (K + 1 - 1)))
    (hE : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ t : ℝ, T ^ ε ≤ |t| →
        ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ^ 2 ≤
          C_E / |t| * Ip w M t + T ^ (-100 : ℝ))
    (hLV : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ m, ‖c m‖ ≤ 1) →
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖dpoly c M (t₁ - t₂)‖ ^ 2 ≤
        C_L * T ^ δL * ((W.card : ℝ) ^ 2 * M + (M : ℝ) ^ 2 * A' + B' * M))
    (hTε : 1 ≤ T ^ ε)
    (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → T ^ ε ≤ |t - t'|)
    (hW : ∀ t ∈ W, t ∈ Set.Icc a (a + T))
    (hcnt : ((Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) + 1 ≤ C_c * T ^ η) :
    (N : ℝ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖Asum w N (t₁ - t₂)‖ ^ 2 ≤
      96 * C_E * (∫ ρ, ‖𝓕 (Gw w) ρ‖) * C_L * C_c * (T ^ δL * (T ^ η) ^ 3) *
          ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 + T * N * A' + (N : ℝ) ^ 2 * B') +
        (6 + 13 * C_A ^ 2) * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) := by
  set C_F := ∫ ρ, ‖𝓕 (Gw w) ρ‖ with hCF
  have hCF0 : 0 ≤ C_F := integral_nonneg fun ρ => norm_nonneg _
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  set L := Nat.log 2 ⌊T⌋₊ + 1 with hL
  set E := 6 * T ^ (-100 : ℝ) + 3 * (C_A * (1 + T) * (T ^ (-η)) ^ K) ^ 2 with hEdef
  have hE0 : 0 ≤ E := by positivity
  set D := C_A ^ 2 / N with hD
  have hD0 : 0 ≤ D := by positivity
  set R' := (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 + T * N * A' + (N : ℝ) ^ 2 * B' with hR'
  have hR'0 : 0 ≤ R' := by positivity
  set X : ℕ → ℝ → ℝ := fun j t =>
    3 * C_E * (1 / 2 ^ j) * (Ip w (Mj T η N j) t + Ip w (Mj T η N j) (-t)) with hX
  have hX0 : ∀ j t, 0 ≤ X j t := fun j t =>
    mul_nonneg (by positivity) (add_nonneg (Ip_nonneg _ _ _) (Ip_nonneg _ _ _))
  -- per pair
  have hpair : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ‖Asum w N (t₁ - t₂)‖ ^ 2 ≤
      (∑ j ∈ Finset.range L, X j (t₁ - t₂)) + (E + D) := by
    intro t₁ h₁ t₂ h₂
    have hF0 : 0 ≤ ∑ j ∈ Finset.range L, X j (t₁ - t₂) :=
      Finset.sum_nonneg fun j _ => hX0 j _
    by_cases h : t₁ = t₂
    · subst h; rw [sub_self] at hF0 ⊢
      have := diag_bound hN1 hCA hA; rw [← hD] at this; linarith
    · have hs := hsep t₁ h₁ t₂ h₂ h
      obtain ⟨a1, b1⟩ := hW t₁ h₁
      obtain ⟨a2, b2⟩ := hW t₂ h₂
      have htT : |t₁ - t₂| ≤ T := by
        rw [abs_le]; constructor <;> linarith
      have hpb := pair_bound (η := η) hN1 hT hη hη2 hCA hCE hA hE hs (hTε.trans hs) htT
      have hmem : Nat.log 2 ⌊|t₁ - t₂|⌋₊ ∈ Finset.range L := by
        rw [Finset.mem_range, hL]
        exact Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_mono htT))
      have hsingle := Finset.single_le_sum (f := fun j => X j (t₁ - t₂))
        (fun j _ => hX0 j _) hmem
      simp only [hX] at hsingle hpb ⊢
      linarith
  -- sum over pairs
  have hsum : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖Asum w N (t₁ - t₂)‖ ^ 2 ≤
      ∑ j ∈ Finset.range L, ∑ t₁ ∈ W, ∑ t₂ ∈ W, X j (t₁ - t₂) +
        (W.card : ℝ) ^ 2 * (E + D) := by
    calc _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ((∑ j ∈ Finset.range L, X j (t₁ - t₂)) + (E + D)) :=
          Finset.sum_le_sum fun t₁ h₁ => Finset.sum_le_sum fun t₂ h₂ => hpair t₁ h₁ t₂ h₂
      _ = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ j ∈ Finset.range L, X j (t₁ - t₂) +
            (W.card : ℝ) ^ 2 * (E + D) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
      _ = _ := by
          congr 1
          calc ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ j ∈ Finset.range L, X j (t₁ - t₂)
              = ∑ t₁ ∈ W, ∑ j ∈ Finset.range L, ∑ t₂ ∈ W, X j (t₁ - t₂) :=
                Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
  -- per shell
  set K0 := 96 * C_E * C_F * C_L * (T ^ δL * (T ^ η) ^ 2) * R' with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hshell : ∀ j ∈ Finset.range L,
      (N : ℝ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, X j (t₁ - t₂) ≤ K0 := by
    intro j hjL
    have hjle : j ≤ Nat.log 2 ⌊T⌋₊ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hjL)
    have h2j := two_pow_le hT1 hjle
    obtain ⟨hMT, hMle⟩ := Mj_le (η := η) hT hη2 hN1 h2j
    set M := Mj T η N j with hM
    set LV := C_L * T ^ δL * ((W.card : ℝ) ^ 2 * M + (M : ℝ) ^ 2 * A' + B' * M) with hLVdef
    have hLV0 : 0 ≤ LV := by positivity
    obtain ⟨h1, h2⟩ := sum_Ip_le hw W M LV hLV0 (fun hM1 c hc => hLV M hM1 hMT c hc)
    have e : ∑ t₁ ∈ W, ∑ t₂ ∈ W, X j (t₁ - t₂) = 3 * C_E * (1 / 2 ^ j) *
        (∑ t₁ ∈ W, ∑ t₂ ∈ W, Ip w M (t₁ - t₂) + ∑ t₁ ∈ W, ∑ t₂ ∈ W, Ip w M (-(t₁ - t₂))) := by
      simp only [hX, mul_add, Finset.mul_sum, Finset.sum_add_distrib]; rfl
    rw [e]
    have hsa := shell_arith (N := (N : ℝ)) (T := T) (n := (W.card : ℝ)) hN0
      (by positivity : (0 : ℝ) < 2 ^ j) (Real.one_le_rpow hT1 hη.le) h2j (Nat.cast_nonneg M)
      hMle (Nat.cast_nonneg _) hA' hB'
    calc (N : ℝ) ^ 3 * (3 * C_E * (1 / 2 ^ j) * (∑ t₁ ∈ W, ∑ t₂ ∈ W, Ip w M (t₁ - t₂) +
          ∑ t₁ ∈ W, ∑ t₂ ∈ W, Ip w M (-(t₁ - t₂))))
        ≤ (N : ℝ) ^ 3 * (3 * C_E * (1 / 2 ^ j) * (C_F * LV + C_F * LV)) := by gcongr
      _ = 6 * C_E * C_F * C_L * T ^ δL * ((N : ℝ) ^ 3 * (1 / 2 ^ j) *
            ((W.card : ℝ) ^ 2 * M + (M : ℝ) ^ 2 * A' + B' * M)) := by rw [hLVdef]; ring
      _ ≤ 6 * C_E * C_F * C_L * T ^ δL * (16 * (T ^ η) ^ 2 * R') := by gcongr
      _ = K0 := by rw [hK0]; ring
  have hjsum : (N : ℝ) ^ 3 * ∑ j ∈ Finset.range L, ∑ t₁ ∈ W, ∑ t₂ ∈ W, X j (t₁ - t₂) ≤
      96 * C_E * C_F * C_L * C_c * (T ^ δL * (T ^ η) ^ 3) * R' := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ j ∈ Finset.range L, K0 := Finset.sum_le_sum hshell
      _ = (L : ℝ) * K0 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (C_c * T ^ η) * K0 := by
          gcongr; rw [hL]; push_cast; exact hcnt
      _ = _ := by rw [hK0]; ring
  have herr : (N : ℝ) ^ 3 * (E + D) ≤ (6 + 13 * C_A ^ 2) * (N : ℝ) ^ 2 := by
    have h1 := err_small (K := K) (η := η) (C := C_A) hT1 hηK hN1 hNT hCA
    have h2 : (N : ℝ) ^ 3 * D = C_A ^ 2 * (N : ℝ) ^ 2 := by rw [hD]; field_simp
    have h3 : (N : ℝ) ^ 3 * E = (N : ℝ) ^ 2 * (N * E) := by ring
    rw [mul_add, h2, h3]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
    nlinarith
  calc (N : ℝ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖Asum w N (t₁ - t₂)‖ ^ 2
      ≤ (N : ℝ) ^ 3 * (∑ j ∈ Finset.range L, ∑ t₁ ∈ W, ∑ t₂ ∈ W, X j (t₁ - t₂) +
        (W.card : ℝ) ^ 2 * (E + D)) := by gcongr
    _ = (N : ℝ) ^ 3 * ∑ j ∈ Finset.range L, ∑ t₁ ∈ W, ∑ t₂ ∈ W, X j (t₁ - t₂) +
        (W.card : ℝ) ^ 2 * ((N : ℝ) ^ 3 * (E + D)) := by ring
    _ ≤ 96 * C_E * C_F * C_L * C_c * (T ^ δL * (T ^ η) ^ 3) * R' +
        (W.card : ℝ) ^ 2 * ((6 + 13 * C_A ^ 2) * (N : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

/-! Part E2: `sum_Asum_sq_le`, from `norm_Asum_le`, `norm_sum_hHat_sq_le`, `lv_holder`
(Blueprint stubs) and the helpers of `S2PartE2a`. -/
set_option maxHeartbeats 1000000 in
theorem sum_Asum_sq_le {w : ℝ → ℝ} (hw : IsWeight w) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ,
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      (N : ℝ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖Asum w N (t₁ - t₂)‖ ^ 2 ≤
        C * T ^ δ * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
          T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
            (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) := by
  intro δ hδ
  set η := min δ 1 / 8 with hηdef
  have hη : 0 < η := by positivity
  have hη2 : η ≤ 1 / 2 := by have := min_le_right δ 1; rw [hηdef]; linarith
  have hηδ : η ≤ δ / 8 := by have := min_le_left δ 1; rw [hηdef]; linarith
  set K : ℕ := ⌈2 / η⌉₊ + 1 with hK
  have hηK : 2 ≤ η * K := by
    have h1 := Nat.le_ceil (2 / η)
    rw [div_le_iff₀ hη] at h1
    have h2 : (K : ℝ) = ⌈2 / η⌉₊ + 1 := by rw [hK]; push_cast; ring
    rw [h2]; nlinarith
  obtain ⟨CA, hCA⟩ := GuthMaynard.S2.norm_Asum_le hw (K + 1) (by omega)
  obtain ⟨CE, TE, hCE⟩ := GuthMaynard.S2.norm_sum_hHat_sq_le hw hε
  obtain ⟨CL, TL, hCL⟩ := GuthMaynard.S2.lv_holder k hk (δ / 4) (by positivity)
  obtain ⟨Cc, hCc0, hCc⟩ := log_count hη
  have hCF0 : 0 ≤ ∫ ρ, ‖𝓕 (Gw w) ρ‖ := integral_nonneg fun ρ => norm_nonneg _
  have hK10 : 0 ≤ 96 * max CE 0 * (∫ ρ, ‖𝓕 (Gw w) ρ‖) * max CL 0 * Cc := by
    have := le_max_right CE 0; have := le_max_right CL 0; positivity
  have hK20 : 0 ≤ 6 + 13 * max CA 0 ^ 2 := by positivity
  refine ⟨96 * max CE 0 * (∫ ρ, ‖𝓕 (Gw w) ρ‖) * max CL 0 * Cc + (6 + 13 * max CA 0 ^ 2),
    max (max TE TL) 16, ?_⟩
  intro T hT N hN W a hsep hW
  have hT16 : 16 ≤ T := le_trans (le_max_right _ _) hT
  have hTE : TE ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTL : TL ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT1 : 1 ≤ T := by linarith
  have hN1 : (1 : ℝ) ≤ N := le_trans (Real.one_le_rpow hT1 (by norm_num)) hN.1
  have hNT : (N : ℝ) ≤ T := hN.2
  have hN1' : 1 ≤ N := by exact_mod_cast hN1
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hsep1 : IsSeparated 1 W := fun t ht t' ht' hne => hTε.trans (hsep t ht t' ht' hne)
  have hA : ∀ (M : ℕ) (t : ℝ), ‖Asum w N t‖ ≤
      ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ +
        ‖∑ m ∈ Finset.Icc 1 M, hHat w (-t) ((m : ℝ) * N)‖ +
        max CA 0 * (1 + |t|) ^ (K + 1) / ((N : ℝ) ^ (K + 1) * ((M : ℝ) + 1) ^ (K + 1 - 1)) :=
    fun M t => by
      refine (hCA N hN1' M t).trans ?_
      gcongr
      exact le_max_left _ _
  have hE : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ t : ℝ, T ^ ε ≤ |t| →
      ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ^ 2 ≤
        max CE 0 / |t| * Ip w M t + T ^ (-100 : ℝ) :=
    fun M hM hMT t ht => (hCE T hTE N M hN1' hM hMT t ht).trans (add_le_add_left
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
        (Ip_nonneg w M t)) _)
  have hLV : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ m, ‖c m‖ ≤ 1) →
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖dpoly c M (t₁ - t₂)‖ ^ 2 ≤
        max CL 0 * T ^ (δ / 4) * ((W.card : ℝ) ^ 2 * M +
          (M : ℝ) ^ 2 * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) * M) :=
    fun M hM hMT c hc => (hCL T hTL W a hsep1 hW M hM hMT c hc).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (by positivity))
  have key := core hw (K := K) (η := η) (ε := ε) (C_A := max CA 0) (C_E := max CE 0)
    (C_L := max CL 0) W a hT16 hη hη2 hηK hN1 hNT
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) hCc0 (by positivity)
    (by positivity) hA hE hLV hTε hsep hW (hCc T hT1)
  -- the target bracket
  set R := (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 + T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
    (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
      (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hTδ : 1 ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  rcases Nat.eq_zero_or_pos W.card with hW0 | hWpos
  · rw [Finset.card_eq_zero.1 hW0]
    simp only [Finset.sum_empty, mul_zero]
    exact mul_nonneg (mul_nonneg (add_nonneg hK10 hK20) (by positivity)) hR0
  have hn : (0 : ℝ) < W.card := by exact_mod_cast hWpos
  have hbr := rpow_bracket hn (by linarith : (0 : ℝ) ≤ T) k hk
  have hRR : (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 + T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
      (N : ℝ) ^ 2 * ((W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))) = R := by
    rw [hbr, hR]; ring
  rw [hRR] at key
  have hpow : T ^ (δ / 4) * (T ^ η) ^ 3 ≤ T ^ δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
  have hNn : (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 ≤ T ^ δ * R := by
    have h1 : (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 ≤ R := by
      rw [hR]
      have : 0 ≤ T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) := by positivity
      have : 0 ≤ (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
          (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ)) := by positivity
      linarith
    nlinarith
  calc _ ≤ _ := key
    _ ≤ 96 * max CE 0 * (∫ ρ, ‖𝓕 (Gw w) ρ‖) * max CL 0 * Cc * T ^ δ * R +
        (6 + 13 * max CA 0 ^ 2) * (T ^ δ * R) := by
        gcongr
    _ = _ := by ring

end GuthMaynard.S2.PartE2
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
alias sum_Asum_sq_le := GuthMaynard.S2.PartE2.sum_Asum_sq_le

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartM
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2.PartM
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Main -/

end GuthMaynard.S2
end


section
open GuthMaynard
theorem solution (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (hk : 1 ≤ k) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ,
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      (N : ℝ) ^ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W,
          ‖∑' z : {z : ℤ // z ≠ 0}, hHat w (t₁ - t₂) ((z : ℤ) * N)‖ ^ 2 ≤
        C * T ^ δ * ((N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 +
          T * N * (W.card : ℝ) ^ (2 - 1 / (k : ℝ)) +
          (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
            (T ^ (1 / 2 : ℝ) / (W.card : ℝ) ^ (3 / 4 : ℝ)) ^ (1 / (k : ℝ))) := GuthMaynard.S2.sum_Asum_sq_le hw hε k hk
end
