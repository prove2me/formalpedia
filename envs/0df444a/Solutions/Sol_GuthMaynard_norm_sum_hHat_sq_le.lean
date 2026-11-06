-- Prove2me | solution 1 for GuthMaynard.norm_sum_hHat_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:29:25.9552+00:00
-- url     : https://prove2.me/submissions/97b652bd-4ede-431e-a78b-9531e89fc74c

import Mathlib
import Definitions.Def_GuthMaynard
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

/-- The Dirichlet polynomial `∑_{1 ≤ m ≤ M} c_m m^{it}`. -/
noncomputable def dpoly (c : ℕ → ℂ) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, c m * (m : ℂ) ^ ((t : ℂ) * I)

/-- The oscillatory integral `I(τ) = ∫_a^b v^{-1+iτ} e(-v) dv`. -/
noncomputable def Iosc (a b τ : ℝ) : ℂ :=
  ∫ v in a..b, (v : ℂ) ^ ((-1 : ℂ) + (τ : ℂ) * I) * Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * I)

/-- `G(x) = eˣ w(eˣ)²`, so that `w(u)² = u⁻¹ G(log u)` for `u > 0`. -/
noncomputable def Gw (w : ℝ → ℝ) (x : ℝ) : ℂ :=
  ((Real.exp x * w (Real.exp x) ^ 2 : ℝ) : ℂ)

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartA
open Complex MeasureTheory FourierTransform
/-- The phase factor `e^{i(τ log v - 2π v)}`. -/
noncomputable def Eph (τ v : ℝ) : ℂ :=
  Complex.exp (((τ * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)

theorem integrand_eq (τ : ℝ) {v : ℝ} (hv : 0 < v) :
    (v : ℂ) ^ ((-1 : ℂ) + (τ : ℂ) * I) * Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * I) =
      (v : ℂ)⁻¹ * Eph τ v := by
  have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Complex.cpow_def_of_ne_zero hv0, Eph]
  have hlog : Complex.log (v : ℂ) = ((Real.log v : ℝ) : ℂ) := (Complex.ofReal_log hv.le).symm
  have hinv : (v : ℂ)⁻¹ = Complex.exp (-((Real.log v : ℝ) : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hv]
  rw [hinv, hlog, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_integrand_le (τ : ℝ) {v : ℝ} (hv : 0 < v) :
    ‖(v : ℂ) ^ ((-1 : ℂ) + (τ : ℂ) * I) * Complex.exp (((-2 * Real.pi * v : ℝ) : ℂ) * I)‖ = v⁻¹ := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_exp_ofReal_mul_I]
  simp [Real.rpow_neg_one]

theorem norm_Iosc_le_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (τ : ℝ) :
    ‖Iosc a b τ‖ ≤ Real.log (b / a) := by
  rw [← integral_inv_of_pos ha (ha.trans_le hab)]
  unfold Iosc
  refine intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun v hv => ?_) ?_
  · rw [norm_integrand_le τ (ha.trans hv.1)]
  · exact intervalIntegral.intervalIntegrable_inv (fun x hx => by
      rw [Set.uIcc_of_le hab] at hx; exact (ha.trans_le hx.1).ne') continuousOn_id

end GuthMaynard.S2.PartA
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part A: the oscillatory integral -/
alias norm_Iosc_le_log := GuthMaynard.S2.PartA.norm_Iosc_le_log

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartA
open Complex MeasureTheory FourierTransform
theorem hasDerivAt_Eph (τ : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (Eph τ) (Eph τ v * ((((τ * v⁻¹ - 2 * Real.pi) : ℝ) : ℂ) * I)) v := by
  have h1 : HasDerivAt (fun x : ℝ => τ * Real.log x - 2 * Real.pi * x)
      (τ * v⁻¹ - 2 * Real.pi) v := by
    have := ((Real.hasDerivAt_log hv.ne').const_mul τ).sub ((hasDerivAt_id v).const_mul (2 * Real.pi))
    exact this.congr_deriv (by ring)
  exact (h1.ofReal_comp.mul_const I).cexp

/-- `G(v) = (τ - 2πv)⁻¹`. -/
noncomputable def Gi (τ v : ℝ) : ℝ := (τ - 2 * Real.pi * v)⁻¹

theorem hasDerivAt_Gi (τ : ℝ) {v : ℝ} (hv : τ - 2 * Real.pi * v ≠ 0) :
    HasDerivAt (Gi τ) (2 * Real.pi * (Gi τ v) ^ 2) v := by
  have h : HasDerivAt (fun x => (τ - 2 * Real.pi * x)⁻¹)
      (-(-(2 * Real.pi * 1)) / (τ - 2 * Real.pi * v) ^ 2) v :=
    (((hasDerivAt_id v).const_mul (2 * Real.pi)).const_sub τ).inv hv
  exact h.congr_deriv (by simp only [Gi]; field_simp)

theorem ibp_bound (τ : ℝ) {c d K : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hK : 0 < K)
    (hsep : ∀ v ∈ Set.Icc c d, K ≤ |τ - 2 * Real.pi * v|) :
    ‖∫ v in c..d, (v : ℂ)⁻¹ * Eph τ v‖ ≤ 4 / K := by
  have hne : ∀ v ∈ Set.Icc c d, τ - 2 * Real.pi * v ≠ 0 := fun v hv h => by
    have := hsep v hv; rw [h, abs_zero] at this; linarith
  have hGle : ∀ v ∈ Set.Icc c d, |Gi τ v| ≤ 1 / K := fun v hv => by
    rw [Gi, abs_inv, ← one_div]
    exact one_div_le_one_div_of_le hK (hsep v hv)
  have hpos : ∀ v ∈ Set.Icc c d, 0 < v := fun v hv => hc.trans_le hv.1
  rw [← Set.uIcc_of_le hcd] at hne hGle hpos
  -- F = E * (-I * G)
  set F : ℝ → ℂ := fun v => Eph τ v * (-I * (Gi τ v : ℂ)) with hF
  set g : ℝ → ℂ := fun v => I * Eph τ v * ((2 * Real.pi * (Gi τ v) ^ 2 : ℝ) : ℂ) with hg
  have hderF : ∀ v ∈ Set.uIcc c d, HasDerivAt F ((v : ℂ)⁻¹ * Eph τ v - g v) v := by
    intro v hv
    have hE := hasDerivAt_Eph τ (hpos v hv)
    have hG := (hasDerivAt_Gi τ (hne v hv)).ofReal_comp
    have := hE.mul (hG.const_mul (-I))
    refine this.congr_deriv ?_
    have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast (hpos v hv).ne'
    have hτ : ((τ : ℂ) - 2 * Real.pi * v) ≠ 0 := by exact_mod_cast hne v hv
    have key : (((τ * v⁻¹ - 2 * Real.pi) : ℝ) : ℂ) * (Gi τ v : ℂ) = (v : ℂ)⁻¹ := by
      have : (τ * v⁻¹ - 2 * Real.pi) * Gi τ v = v⁻¹ := by
        have := hne v hv; have := (hpos v hv).ne'
        have h1 : τ - 2 * Real.pi * v ≠ 0 := hne v hv
        have h2 : v ≠ 0 := (hpos v hv).ne'
        simp only [Gi]
        rw [show τ * v⁻¹ - 2 * Real.pi = (τ - 2 * Real.pi * v) * v⁻¹ by field_simp,
          mul_comm _ v⁻¹, mul_assoc, mul_inv_cancel₀ h1, mul_one]
      exact_mod_cast this
    simp only [hg]
    linear_combination (Eph τ v) * key -
      (Eph τ v * (((τ * v⁻¹ - 2 * Real.pi) : ℝ) : ℂ) * (Gi τ v : ℂ)) * Complex.I_sq
  have hEc : ContinuousOn (Eph τ) (Set.uIcc c d) := fun v hv =>
    (hasDerivAt_Eph τ (hpos v hv)).continuousAt.continuousWithinAt
  have hGc : ContinuousOn (Gi τ) (Set.uIcc c d) := fun v hv =>
    (hasDerivAt_Gi τ (hne v hv)).continuousAt.continuousWithinAt
  have hinvc : ContinuousOn (fun v : ℝ => (v : ℂ)⁻¹) (Set.uIcc c d) :=
    (continuous_ofReal.continuousOn).inv₀ (fun v hv => by exact_mod_cast (hpos v hv).ne')
  have hgc : ContinuousOn g (Set.uIcc c d) := by
    simp only [hg]
    exact (continuousOn_const.mul hEc).mul
      (continuous_ofReal.comp_continuousOn (continuousOn_const.mul (hGc.pow 2)))
  have hfc : ContinuousOn (fun v : ℝ => (v : ℂ)⁻¹ * Eph τ v) (Set.uIcc c d) := hinvc.mul hEc
  have hint1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderF
    ((hfc.sub hgc).intervalIntegrable)
  rw [intervalIntegral.integral_sub hfc.intervalIntegrable hgc.intervalIntegrable] at hint1
  have heq : ∫ v in c..d, (v : ℂ)⁻¹ * Eph τ v = (F d - F c) + ∫ v in c..d, g v := by
    rw [← hint1]; ring
  rw [heq]
  have hG'c : ContinuousOn (fun v => 2 * Real.pi * (Gi τ v) ^ 2) (Set.uIcc c d) :=
    continuousOn_const.mul (hGc.pow 2)
  have hint2 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => hasDerivAt_Gi τ (hne v hv)) hG'c.intervalIntegrable
  have hgn : ‖∫ v in c..d, g v‖ ≤ Gi τ d - Gi τ c := by
    rw [← hint2]
    refine intervalIntegral.norm_integral_le_of_norm_le hcd
      (Filter.Eventually.of_forall fun v _ => ?_) hG'c.intervalIntegrable
    simp only [hg, norm_mul, Complex.norm_I, one_mul, Eph, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos Real.pi_pos, abs_of_nonneg (sq_nonneg (Gi τ v))]
    norm_num
  have hFn : ∀ v ∈ Set.uIcc c d, ‖F v‖ ≤ 1 / K := fun v hv => by
    simp only [hF, Eph, norm_mul, Complex.norm_exp_ofReal_mul_I, norm_neg, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact hGle v hv
  have hd : d ∈ Set.uIcc c d := Set.right_mem_uIcc
  have hc' : c ∈ Set.uIcc c d := Set.left_mem_uIcc
  have h1 := hFn d hd
  have h2 := hFn c hc'
  have h3 := (abs_le.1 (hGle d hd)).2
  have h4 := (abs_le.1 (hGle c hc')).1
  calc ‖F d - F c + ∫ v in c..d, g v‖ ≤ ‖F d‖ + ‖F c‖ + ‖∫ v in c..d, g v‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 4 / K := by
        have : 4 / K = 1 / K + 1 / K + (1 / K + 1 / K) := by ring
        rw [this]; linarith

theorem Iosc_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (τ : ℝ) :
    Iosc a b τ = ∫ v in a..b, (v : ℂ)⁻¹ * Eph τ v := by
  unfold Iosc
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [Set.uIcc_of_le hab] at hv
  exact integrand_eq τ (ha.trans_le hv.1)

theorem f1_intervalIntegrable (τ : ℝ) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    IntervalIntegrable (fun v : ℝ => (v : ℂ)⁻¹ * Eph τ v) volume c d := by
  have hpos : ∀ v ∈ Set.uIcc c d, 0 < v := fun v hv => by
    rw [Set.uIcc_of_le hcd] at hv; exact hc.trans_le hv.1
  refine ContinuousOn.intervalIntegrable ?_
  refine ((continuous_ofReal.continuousOn).inv₀ (fun v hv => by exact_mod_cast (hpos v hv).ne')).mul ?_
  exact fun v hv => (hasDerivAt_Eph τ (hpos v hv)).continuousAt.continuousWithinAt

theorem norm_f1 (τ : ℝ) {v : ℝ} (hv : 0 < v) : ‖(v : ℂ)⁻¹ * Eph τ v‖ = v⁻¹ := by
  rw [norm_mul, Eph, Complex.norm_exp_ofReal_mul_I, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hv, mul_one]

theorem norm_Iosc_le : ∃ C : ℝ, ∀ a b τ : ℝ, 0 < a → a ≤ b → 200 ≤ |τ| →
    ‖Iosc a b τ‖ ≤ C * |τ| ^ (-(1 / 2 : ℝ)) := by
  refine ⟨40, fun a b τ ha hab hτ => ?_⟩
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  set s := Real.sqrt |τ| with hs_def
  have hs2 : s * s = |τ| := Real.mul_self_sqrt (abs_nonneg τ)
  have hs4 : 4 * Real.pi ≤ s := by
    rw [hs_def]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hspos : 0 < s := by linarith
  have hrpow : |τ| ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg τ), hs_def, Real.sqrt_eq_rpow]
  rw [hrpow, Iosc_eq ha hab]
  rcases le_or_gt τ 0 with hneg | hposτ
  · -- τ ≤ -200: no stationary point
    rw [abs_of_nonpos hneg] at hs2 hτ
    have hb := ibp_bound τ ha hab (K := -τ) (by linarith) (fun v hv => by
      have : 0 < v := ha.trans_le hv.1
      rw [abs_of_neg (by nlinarith [Real.pi_pos])]; nlinarith [Real.pi_pos])
    refine hb.trans ?_
    rw [← hs2, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  · rw [abs_of_pos hposτ] at hs2
    set v₀ := τ / (2 * Real.pi) with hv₀
    have hτv : τ = 2 * Real.pi * v₀ := by rw [hv₀]; field_simp
    have hDv : s ≤ v₀ / 2 := by
      rw [hv₀, le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity), ← hs2]; nlinarith
    set p := max a (min b (v₀ - s)) with hp
    set q := max a (min b (v₀ + s)) with hq
    have hap : a ≤ p := le_max_left _ _
    have hpq : p ≤ q := max_le_max le_rfl (min_le_min le_rfl (by linarith))
    have hqb : q ≤ b := max_le hab (min_le_left _ _)
    have hp0 : 0 < p := ha.trans_le hap
    have hq0 : 0 < q := hp0.trans_le hpq
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := p)
        (f1_intervalIntegrable τ ha hap) ((f1_intervalIntegrable τ hp0 hpq).trans
          (f1_intervalIntegrable τ hq0 hqb)),
      ← intervalIntegral.integral_add_adjacent_intervals (a := p) (b := q)
        (f1_intervalIntegrable τ hp0 hpq) (f1_intervalIntegrable τ hq0 hqb)]
    have hK : 0 < 2 * Real.pi * s := by positivity
    -- left piece
    have hL : ‖∫ v in a..p, (v : ℂ)⁻¹ * Eph τ v‖ ≤ 4 / (2 * Real.pi * s) := by
      by_cases h : a ≤ v₀ - s
      · refine ibp_bound τ ha hap hK fun v hv => ?_
        have : v ≤ v₀ - s := hv.2.trans (max_le h (min_le_right _ _))
        rw [abs_of_pos (by nlinarith)]; nlinarith
      · have : p = a := by
          rw [hp]; exact max_eq_left ((min_le_right _ _).trans (le_of_lt (not_le.mp h)))
        rw [this, intervalIntegral.integral_same, norm_zero]; positivity
    have hR : ‖∫ v in q..b, (v : ℂ)⁻¹ * Eph τ v‖ ≤ 4 / (2 * Real.pi * s) := by
      by_cases h : v₀ + s ≤ b
      · refine ibp_bound τ hq0 hqb hK fun v hv => ?_
        have : v₀ + s ≤ v := (le_trans (le_min h le_rfl) (le_max_right _ _)).trans hv.1
        rw [abs_of_neg (by nlinarith)]; nlinarith
      · have : q = b := by
          rw [hq, min_eq_left (le_of_lt (not_le.mp h))]; exact max_eq_right hab
        rw [this, intervalIntegral.integral_same, norm_zero]; positivity
    have hM : ‖∫ v in p..q, (v : ℂ)⁻¹ * Eph τ v‖ ≤ (2 / v₀) * (2 * s) := by
      have hlen : |q - p| ≤ 2 * s := by
        rw [abs_of_nonneg (by linarith), hp, hq]
        simp only [max_def, min_def]
        split_ifs <;> linarith
      have hv0pos : 0 < v₀ := by positivity
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun v hv => ?_).trans
        (mul_le_mul_of_nonneg_left hlen (by positivity))
      rw [Set.uIoc_of_le hpq] at hv
      have hv1 : v₀ - s ≤ v := by
        by_contra hc
        push Not at hc
        have h1 : min b (v₀ - s) ≤ p := le_max_right _ _
        have h2 : p < v₀ - s := hv.1.trans hc
        have h3 : min b (v₀ - s) = b := by
          rcases min_choice b (v₀ - s) with h | h <;> [exact h; (rw [h] at h1; linarith)]
        rw [h3] at h1
        linarith [hv.1, hv.2]
      rw [norm_f1 τ (by linarith), inv_le_comm₀ (by linarith) (by positivity)]
      rw [inv_div]; linarith
    calc ‖(∫ v in a..p, (v : ℂ)⁻¹ * Eph τ v) +
          ((∫ v in p..q, (v : ℂ)⁻¹ * Eph τ v) + ∫ v in q..b, (v : ℂ)⁻¹ * Eph τ v)‖
        ≤ ‖∫ v in a..p, (v : ℂ)⁻¹ * Eph τ v‖ +
          (‖∫ v in p..q, (v : ℂ)⁻¹ * Eph τ v‖ + ‖∫ v in q..b, (v : ℂ)⁻¹ * Eph τ v‖) :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 4 / (2 * Real.pi * s) + ((2 / v₀) * (2 * s) + 4 / (2 * Real.pi * s)) := by
          gcongr
      _ ≤ 40 * s⁻¹ := by
          have e1 : 4 / (2 * Real.pi * s) ≤ 1 * s⁻¹ := by
            rw [div_le_iff₀ hK]; field_simp; nlinarith
          have e2 : (2 / v₀) * (2 * s) = 8 * Real.pi * s⁻¹ := by
            have : v₀ = s * s / (2 * Real.pi) := by rw [hs2]
            rw [this]; field_simp; norm_num
          rw [e2]; nlinarith [inv_pos.2 hspos]

end GuthMaynard.S2.PartA
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
alias norm_Iosc_le := GuthMaynard.S2.PartA.norm_Iosc_le

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartB
open Complex MeasureTheory FourierTransform
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

theorem GwS_coe {w : ℝ → ℝ} (hw : IsWeight w) : ((GwS hw : SchwartzMap ℝ ℂ) : ℝ → ℂ) = Gw w := rfl

theorem fourier_GwS {w : ℝ → ℝ} (hw : IsWeight w) :
    ((𝓕 (GwS hw) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 (Gw w) := by
  rw [SchwartzMap.fourier_coe]; rfl

theorem Gw_decay {w : ℝ → ℝ} (hw : IsWeight w) (j : ℕ) :
    ∃ C : ℝ, ∀ ρ : ℝ, ‖𝓕 (Gw w) ρ‖ * (1 + |ρ|) ^ j ≤ C := by
  refine ⟨2 ^ j * (Finset.Iic (j, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)
    (𝓕 (GwS hw)), fun ρ => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (j, 0)) (k := j) (n := 0)
    le_rfl le_rfl (𝓕 (GwS hw)) ρ
  rw [norm_iteratedFDeriv_zero, fourier_GwS, Real.norm_eq_abs] at h
  linarith

end GuthMaynard.S2.PartB
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part B: Fourier inversion in `log u` -/
alias Gw_decay := GuthMaynard.S2.PartB.Gw_decay

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartB
open Complex MeasureTheory FourierTransform
theorem Gw_integrable {w : ℝ → ℝ} (hw : IsWeight w) : Integrable (Gw w) := by
  rw [← GwS_coe hw]; exact (GwS hw).integrable

theorem fourier_Gw_integrable {w : ℝ → ℝ} (hw : IsWeight w) : Integrable (𝓕 (Gw w)) := by
  rw [← fourier_GwS hw]; exact (𝓕 (GwS hw)).integrable

theorem fourier_Gw_continuous {w : ℝ → ℝ} (hw : IsWeight w) : Continuous (𝓕 (Gw w)) := by
  rw [← fourier_GwS hw]; exact (𝓕 (GwS hw)).continuous

open GuthMaynardS56 in
theorem w_sq_eq {w : ℝ → ℝ} (hw : IsWeight w) {u : ℝ} (hu : 0 < u) :
    ((w u ^ 2 : ℝ) : ℂ) =
      ∫ ρ, 𝓕 (Gw w) ρ * (u:ℂ) ^ ((-1:ℂ) + ((2 * Real.pi * ρ : ℝ) : ℂ) * I) := by
  have hinv := congrFun ((Gw_contDiff hw).continuous.fourierInv_fourier_eq (Gw_integrable hw)
    (fourier_Gw_integrable hw)) (Real.log u)
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  have hG : Gw w (Real.log u) = (u:ℂ) * ((w u ^ 2 : ℝ) : ℂ) := by
    simp [Gw, Real.exp_log hu]
  rw [hG] at hinv
  have hu0 : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have h2 : ((w u ^ 2 : ℝ) : ℂ) = (u:ℂ)⁻¹ * ∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * -Real.log u) * I) • 𝓕 (Gw w) v := by
    rw [hinv]; field_simp
  rw [h2, ← integral_const_mul]
  congr 1; funext ρ
  rw [Complex.cpow_add _ _ hu0, Complex.cpow_neg_one, Complex.cpow_def_of_ne_zero hu0,
    ← Complex.ofReal_log hu.le, smul_eq_mul]
  have : (↑(-2 * Real.pi * ρ * -Real.log u) * I : ℂ) = ↑(Real.log u) * (↑(2 * Real.pi * ρ) * I) := by
    push_cast; ring
  rw [this]; ring

open GuthMaynardS56 in
theorem inner_eq {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (τ : ℝ) :
    ∫ u in a..b, (u:ℂ) ^ ((-1:ℂ) + (τ:ℂ) * I) * Ec c u =
      (c:ℂ) ^ ((((-τ) : ℝ) : ℂ) * I) * Iosc (c * a) (c * b) τ := by
  unfold Iosc
  rw [← intervalIntegral.smul_integral_comp_mul_left]
  have hc0 : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcongr : ∫ x in a..b, ((c * x : ℝ) : ℂ) ^ ((-1:ℂ) + (τ:ℂ) * I) *
      Complex.exp (((-2 * Real.pi * (c * x) : ℝ) : ℂ) * I) =
      ∫ x in a..b, (c:ℂ) ^ ((-1:ℂ) + (τ:ℂ) * I) * ((x:ℂ) ^ ((-1:ℂ) + (τ:ℂ) * I) * Ec c x) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hx0 : 0 < x := by
      rcases Set.mem_uIcc.1 hx with h | h <;> linarith [h.1]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hx0.le]
    unfold Ec
    have : (((-2 * Real.pi * (c * x) : ℝ) : ℂ) * I) = (((-2 * Real.pi * c : ℝ) : ℂ) * I) * (x:ℂ) := by
      push_cast; ring
    rw [this]; ring
  rw [hcongr, intervalIntegral.integral_const_mul, real_smul, ← mul_assoc, ← mul_assoc]
  have hcp : (c:ℂ) ^ ((((-τ) : ℝ) : ℂ) * I) * (c:ℂ) * (c:ℂ) ^ ((-1:ℂ) + (τ:ℂ) * I) = 1 := by
    conv_lhs => rw [mul_assoc]; arg 2; arg 1; rw [← Complex.cpow_one (c:ℂ)]
    rw [← Complex.cpow_add _ _ hc0, ← Complex.cpow_add _ _ hc0]
    have : (((-τ) : ℝ) : ℂ) * I + (1 + ((-1:ℂ) + (τ:ℂ) * I)) = 0 := by push_cast; ring
    rw [this, Complex.cpow_zero]
  rw [hcp, one_mul]

/-- the `m`-th summand of the inverted sum -/
noncomputable def H (w : ℝ → ℝ) (t : ℝ) (N M m : ℕ) (ρ : ℝ) : ℂ :=
  𝓕 (Gw w) ρ * (((((m:ℝ) * N : ℝ)) : ℂ) ^ ((((-(t + 2 * Real.pi * ρ)) : ℝ) : ℂ) * I) *
    Iosc N (2 * N * M) (t + 2 * Real.pi * ρ))

open GuthMaynardS56 in
theorem hHat_m_eq {w : ℝ → ℝ} (hw : IsWeight w) (t : ℝ) {N M m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (hmM : m ≤ M) :
    hHat w t ((m:ℝ) * N) = ∫ ρ, H w t N M m ρ ∧ Integrable (H w t N M m) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmM' : (m:ℝ) ≤ M := by exact_mod_cast hmM
  set a : ℝ := 1 / (m:ℝ) with ha
  set b : ℝ := 2 * M / (m:ℝ) with hb
  set c : ℝ := (m:ℝ) * N with hc
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hm0]; exact hm1
  have hb2 : 2 ≤ b := by rw [hb, le_div_iff₀ hm0]; linarith
  have hc0 : 0 < c := by positivity
  set F : ℝ → ℝ → ℂ := fun u ρ => 𝓕 (Gw w) ρ *
    ((u:ℂ) ^ ((-1:ℂ) + ((t + 2 * Real.pi * ρ : ℝ) : ℂ) * I) * Ec c u) with hF
  -- integrability on the product
  have hmeas : Measurable (Function.uncurry F) := by
    have h1 : Measurable (𝓕 (Gw w)) := (fourier_Gw_continuous hw).measurable
    have h2 : Measurable (fun p : ℝ × ℝ => Ec c p.1) := (continuous_Ec c).measurable.comp measurable_fst
    have h3 : Measurable (fun p : ℝ × ℝ =>
        (p.1:ℂ) ^ ((-1:ℂ) + ((t + 2 * Real.pi * p.2 : ℝ) : ℂ) * I)) := by
      fun_prop
    exact (h1.comp measurable_snd).mul (h3.mul h2)
  have hint : Integrable (Function.uncurry F) ((volume.restrict (Set.Icc a b)).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℝ => (a⁻¹ : ℝ) * ‖𝓕 (Gw w) p.2‖)
        ((volume.restrict (Set.Icc a b)).prod volume) :=
      (integrable_const (a⁻¹ : ℝ)).mul_prod (fourier_Gw_integrable hw).norm
    refine hg.mono' hmeas.aestronglyMeasurable ?_
    rw [← Measure.restrict_univ (μ := volume), Measure.prod_restrict, Measure.restrict_univ]
    rw [ae_restrict_iff' (measurableSet_Icc.prod MeasurableSet.univ)]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    obtain ⟨u, ρ⟩ := p
    have hu : 0 < u := lt_of_lt_of_le ha0 hp.1.1
    simp only [Function.uncurry_apply_pair, hF, norm_mul, norm_Ec, mul_one]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    have hre : ((-1:ℂ) + ((t + 2 * Real.pi * ρ : ℝ) : ℂ) * I).re = -1 := by simp
    rw [hre, Real.rpow_neg_one, mul_comm]
    gcongr
    exact hp.1.1
  refine ⟨?_, ?_⟩
  · rw [hHat_eq, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc a b)]
    · rw [setIntegral_congr_fun measurableSet_Icc (g := fun u => ∫ ρ, F u ρ)]
      · rw [integral_integral_swap hint]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
        simp only [hF]
        rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
          (by linarith), inner_eq hc0 ha0 (by linarith)]
        unfold H
        have e1 : c * a = N := by rw [hc, ha]; field_simp
        have e2 : c * b = 2 * N * M := by rw [hc, hb]; field_simp
        rw [e1, e2]
      · intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
        simp only [hF]
        rw [w_sq_eq hw hu0, ← integral_mul_const]
        congr 1; funext ρ
        have hu0' : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
        have : (u:ℂ) ^ ((-1:ℂ) + ((t + 2 * Real.pi * ρ : ℝ) : ℂ) * I) =
            (u:ℂ) ^ ((-1:ℂ) + ((2 * Real.pi * ρ : ℝ) : ℂ) * I) * (u:ℂ) ^ ((t:ℂ) * I) := by
          rw [← Complex.cpow_add _ _ hu0']; congr 1; push_cast; ring
        rw [this]; ring
    · intro u hu
      have : w u = 0 := by
        by_contra h
        have h2 := hw.support_subset (Function.mem_support.2 h)
        exact hu ⟨by linarith [h2.1], by linarith [h2.2]⟩
      simp [this]
  · have := hint.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun ρ => ?_)
    simp only [Function.uncurry_apply_pair, hF]
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (by linarith), inner_eq hc0 ha0 (by linarith)]
    unfold H
    have e1 : c * a = N := by rw [hc, ha]; field_simp
    have e2 : c * b = 2 * N * M := by rw [hc, hb]; field_simp
    rw [e1, e2]

theorem norm_sum_hHat_le {w : ℝ → ℝ} (hw : IsWeight w) (t : ℝ) {N M : ℕ} (hN : 1 ≤ N)
    (hM : 1 ≤ M) :
    ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ≤
      ∫ ρ, ‖𝓕 (Gw w) ρ‖ * ‖dpoly (fun _ => 1) M (-(t + 2 * Real.pi * ρ))‖ *
        ‖Iosc N (2 * N * M) (t + 2 * Real.pi * ρ)‖ := by
  have hsum : ∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N) =
      ∫ ρ, ∑ m ∈ Finset.Icc 1 M, H w t N M m ρ := by
    rw [integral_finsetSum _ (fun m hm =>
      (hHat_m_eq hw t hN (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2).2)]
    exact Finset.sum_congr rfl (fun m hm =>
      (hHat_m_eq hw t hN (Finset.mem_Icc.1 hm).1 (Finset.mem_Icc.1 hm).2).1)
  rw [hsum]
  refine (norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)))
  simp only [H]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have : ∑ m ∈ Finset.Icc 1 M, ((((m:ℝ) * N : ℝ)) : ℂ) ^ ((((-(t + 2 * Real.pi * ρ)) : ℝ) : ℂ) * I) =
      (((N:ℝ)) : ℂ) ^ ((((-(t + 2 * Real.pi * ρ)) : ℝ) : ℂ) * I) *
        dpoly (fun _ => 1) M (-(t + 2 * Real.pi * ρ)) := by
    unfold dpoly
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_natCast]
    ring
  rw [this, norm_mul, norm_mul, norm_mul, GuthMaynardS56.norm_cpow_it hN0]
  ring

end GuthMaynard.S2.PartB
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
alias norm_sum_hHat_le := GuthMaynard.S2.PartB.norm_sum_hHat_le

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


end GuthMaynard.S2.PartD
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform

end GuthMaynard.S2
end

section
namespace GuthMaynard.S2.PartE1
open Complex MeasureTheory FourierTransform
/-! Helpers on `Gw` (same proofs as in Part B, restated here so this file only needs the
Blueprint). -/
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

/-! Dirichlet polynomial facts. -/
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

/-! Cauchy–Schwarz for a nonnegative integrable weight. -/
theorem cs_ineq {f g : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ ρ, 0 ≤ f ρ) (hg : Continuous g)
    {K : ℝ} (hgK : ∀ ρ, |g ρ| ≤ K) :
    (∫ ρ, f ρ * g ρ) ^ 2 ≤ (∫ ρ, f ρ) * ∫ ρ, f ρ * g ρ ^ 2 := by
  have hfg : Integrable (fun ρ => f ρ * g ρ) :=
    hf.mul_bdd hg.aestronglyMeasurable (ae_of_all _ fun ρ => by simpa using hgK ρ)
  have hfg2 : Integrable (fun ρ => f ρ * g ρ ^ 2) :=
    hf.mul_bdd (hg.pow 2).aestronglyMeasurable (c := K ^ 2) (ae_of_all _ fun ρ => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hgK ρ) 2)
  have hq : ∀ x : ℝ, 0 ≤ (∫ ρ, f ρ) * (x * x) + (-2 * ∫ ρ, f ρ * g ρ) * x +
      ∫ ρ, f ρ * g ρ ^ 2 := by
    intro x
    have h0 : 0 ≤ ∫ ρ, f ρ * (g ρ - x) ^ 2 :=
      integral_nonneg fun ρ => mul_nonneg (hf0 ρ) (sq_nonneg _)
    have : ∫ ρ, f ρ * (g ρ - x) ^ 2 =
        ∫ ρ, (f ρ * g ρ ^ 2 + (-2 * x) * (f ρ * g ρ) + (x * x) * f ρ) := by
      congr 1; funext ρ; ring
    have hi : Integrable (fun ρ => f ρ * g ρ ^ 2 + (-2 * x) * (f ρ * g ρ)) :=
      hfg2.add (hfg.const_mul _)
    have e1 : ∫ ρ, (f ρ * g ρ ^ 2 + (-2 * x) * (f ρ * g ρ) + (x * x) * f ρ) =
        (∫ ρ, (f ρ * g ρ ^ 2 + (-2 * x) * (f ρ * g ρ))) + ∫ ρ, (x * x) * f ρ :=
      integral_add hi (hf.const_mul _)
    have e2 : ∫ ρ, (f ρ * g ρ ^ 2 + (-2 * x) * (f ρ * g ρ)) =
        (∫ ρ, f ρ * g ρ ^ 2) + ∫ ρ, (-2 * x) * (f ρ * g ρ) :=
      integral_add hfg2 (hfg.const_mul _)
    rw [this, e1, e2, integral_const_mul, integral_const_mul] at h0
    linarith
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

/-! The three factors of the integrand in `norm_sum_hHat_le`. -/
noncomputable def fF (w : ℝ → ℝ) (ρ : ℝ) : ℝ := ‖𝓕 (Gw w) ρ‖

noncomputable def gD (M : ℕ) (t ρ : ℝ) : ℝ :=
  ‖dpoly (fun _ => 1) M (-(t + 2 * Real.pi * ρ))‖

noncomputable def hI (N M : ℕ) (t ρ : ℝ) : ℝ :=
  ‖Iosc N (2 * N * M) (t + 2 * Real.pi * ρ)‖

theorem gD_continuous (M : ℕ) (t : ℝ) : Continuous (gD M t) :=
  ((continuous_dpoly M).comp (by fun_prop)).norm

theorem integrable_phi : Integrable (fun ρ : ℝ => ((1 + |ρ|) ^ 2)⁻¹) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  refine this.congr (ae_of_all _ fun ρ => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

set_option maxHeartbeats 1000000 in
/-- The intended form of the Blueprint's `norm_sum_hHat_sq_le`, with the integral
parenthesized. (As printed in the Blueprint, `∫ ρ, … ^ 2 + T ^ (-100)` parses with the `+ T^(-100)`
inside the integral; that integrand is not integrable, so the integral is `0` and the printed
statement claims the sum vanishes.) -/
theorem norm_sum_hHat_sq_le {w : ℝ → ℝ} (hw : IsWeight w) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N M : ℕ, 1 ≤ N → 1 ≤ M → (M : ℝ) ≤ T ^ 2 →
      ∀ t : ℝ, T ^ ε ≤ |t| →
        ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ^ 2 ≤
          C / |t| * (∫ ρ, ‖𝓕 (Gw w) ρ‖ * ‖dpoly (fun _ => 1) M (-(t + 2 * Real.pi * ρ))‖ ^ 2) +
            T ^ (-100 : ℝ) := by
  obtain ⟨CA, hCA⟩ := GuthMaynard.S2.norm_Iosc_le
  set j : ℕ := ⌈100 / ε⌉₊ with hj
  have hεj : 100 ≤ ε * j := by
    have := Nat.le_ceil (100 / ε)
    rw [← hj, div_le_iff₀ hε] at this; linarith
  obtain ⟨Cj, hCj⟩ := GuthMaynard.S2.Gw_decay hw (j + 2)
  have hCj0 : 0 ≤ Cj := by
    have := hCj 0; simp at this; exact (norm_nonneg _).trans this
  have hfi : Integrable (fF w) := (fourier_Gw_integrable hw).norm
  have hf0 : ∀ ρ, 0 ≤ fF w ρ := fun ρ => norm_nonneg _
  set A := ∫ ρ, fF w ρ with hA
  set I₂ := ∫ ρ : ℝ, ((1 + |ρ|) ^ 2)⁻¹ with hI₂
  have hA0 : 0 ≤ A := integral_nonneg hf0
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun ρ => by positivity
  set c₁ := 2 * max CA 0 with hc₁
  set K₁ := Cj * (4 * Real.pi) ^ j with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set K₂ := 8 * K₁ ^ 2 * I₂ ^ 2 with hK₂
  refine ⟨2 * c₁ ^ 2 * A, max (max 1 K₂) ((400 : ℝ) ^ (1 / ε)), ?_⟩
  intro T hT N M hN hM hMT t ht
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTK : K₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : 0 < T := by linarith
  have hT400 : (400 : ℝ) ≤ T ^ ε := by
    have h1 : (400 : ℝ) ^ (1 / ε) ≤ T := (le_max_right _ _).trans hT
    calc (400 : ℝ) = ((400 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
      _ ≤ T ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
  have ht400 : 400 ≤ |t| := hT400.trans ht
  set X := T ^ (-100 : ℝ) with hX_def
  have hX0 : 0 < X := Real.rpow_pos_of_pos hT0 _
  have hX : T ^ (100 : ℕ) * X = 1 := by
    rw [hX_def, Real.rpow_neg hT0.le, ← Real.rpow_natCast]
    push_cast
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hT0 _).ne'
  have htj : T ^ (100 : ℕ) ≤ |t| ^ j := by
    calc T ^ (100 : ℕ) = T ^ (100 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
      _ ≤ T ^ (ε * j) := Real.rpow_le_rpow_of_exponent_le hT1 hεj
      _ = (T ^ ε) ^ j := by rw [Real.rpow_mul hT0.le, Real.rpow_natCast]
      _ ≤ |t| ^ j := pow_le_pow_left₀ (by positivity) ht j
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- pointwise bound
  have hpt : ∀ ρ, fF w ρ * gD M t ρ * hI N M t ρ ≤
      c₁ / Real.sqrt |t| * (fF w ρ * gD M t ρ) +
        (2 * K₁ * T ^ 4 * X) * ((1 + |ρ|) ^ 2)⁻¹ := by
    intro ρ
    have hg0 : 0 ≤ gD M t ρ := norm_nonneg _
    have hgM : gD M t ρ ≤ M := norm_dpoly_le M _
    have hh0 : 0 ≤ hI N M t ρ := norm_nonneg _
    have hfg0 : 0 ≤ fF w ρ * gD M t ρ := mul_nonneg (hf0 ρ) hg0
    have hsq : 0 < Real.sqrt |t| := Real.sqrt_pos.2 (by linarith)
    by_cases hρ : |ρ| < |t| / (4 * Real.pi)
    · -- no stationary point nearby
      have h1 : |t| ≤ |t + 2 * Real.pi * ρ| + 2 * Real.pi * |ρ| := by
        have := abs_add_le (t + 2 * Real.pi * ρ) (-(2 * Real.pi * ρ))
        rw [abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at this
        simpa using this
      have h2 : 2 * Real.pi * |ρ| < |t| / 2 := by
        rw [lt_div_iff₀ (by positivity)] at hρ; linarith
      have hτ : |t| / 2 ≤ |t + 2 * Real.pi * ρ| := by linarith
      have hτ200 : 200 ≤ |t + 2 * Real.pi * ρ| := by linarith
      have hb := hCA N (2 * N * M) (t + 2 * Real.pi * ρ) (by linarith) (by nlinarith) hτ200
      have hrp : |t + 2 * Real.pi * ρ| ^ (-(1 / 2 : ℝ)) ≤ 2 / Real.sqrt |t| := by
        rw [Real.rpow_neg (abs_nonneg _), ← Real.sqrt_eq_rpow, inv_le_comm₀ (by positivity)
          (by positivity), inv_div, div_le_iff₀ (by norm_num)]
        calc Real.sqrt |t| ≤ Real.sqrt (4 * |t + 2 * Real.pi * ρ|) :=
              Real.sqrt_le_sqrt (by linarith)
          _ = Real.sqrt |t + 2 * Real.pi * ρ| * 2 := by
              rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
                Real.sqrt_sq (by norm_num)]; ring
      have hh : hI N M t ρ ≤ c₁ / Real.sqrt |t| := by
        refine hb.trans ?_
        calc CA * |t + 2 * Real.pi * ρ| ^ (-(1 / 2 : ℝ))
            ≤ max CA 0 * |t + 2 * Real.pi * ρ| ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max CA 0 * (2 / Real.sqrt |t|) :=
              mul_le_mul_of_nonneg_left hrp (le_max_right _ _)
          _ = c₁ / Real.sqrt |t| := by rw [hc₁]; ring
      have : 0 ≤ (2 * K₁ * T ^ 4 * X) * ((1 + |ρ|) ^ 2)⁻¹ := by positivity
      calc fF w ρ * gD M t ρ * hI N M t ρ ≤ fF w ρ * gD M t ρ * (c₁ / Real.sqrt |t|) :=
            mul_le_mul_of_nonneg_left hh hfg0
        _ ≤ _ := by linarith
    · -- far from the origin: Fourier decay
      push Not at hρ
      have hlog : hI N M t ρ ≤ 2 * M := by
        have := GuthMaynard.S2.norm_Iosc_le_log (a := (N : ℝ)) (b := 2 * N * M) (by linarith)
          (by nlinarith) (t + 2 * Real.pi * ρ)
        refine this.trans ((Real.log_le_self (by positivity)).trans (le_of_eq ?_))
        field_simp
      have hfdec : fF w ρ ≤ K₁ * (X * ((1 + |ρ|) ^ 2)⁻¹) := by
        have hd := hCj ρ
        have hR : |t| / (4 * Real.pi) ≤ 1 + |ρ| := by linarith
        have hRj : T ^ (100 : ℕ) ≤ (4 * Real.pi) ^ j * (1 + |ρ|) ^ j := by
          calc T ^ (100 : ℕ) ≤ |t| ^ j := htj
            _ = (4 * Real.pi) ^ j * (|t| / (4 * Real.pi)) ^ j := by
                rw [div_pow]; field_simp
            _ ≤ (4 * Real.pi) ^ j * (1 + |ρ|) ^ j := by gcongr
        have hkey : fF w ρ * T ^ (100 : ℕ) * (1 + |ρ|) ^ 2 ≤ K₁ := by
          calc fF w ρ * T ^ (100 : ℕ) * (1 + |ρ|) ^ 2
              ≤ fF w ρ * ((4 * Real.pi) ^ j * (1 + |ρ|) ^ j) * (1 + |ρ|) ^ 2 := by
                gcongr; exact hf0 ρ
            _ = (4 * Real.pi) ^ j * (‖𝓕 (Gw w) ρ‖ * (1 + |ρ|) ^ (j + 2)) := by
                rw [fF, pow_add]; ring
            _ ≤ (4 * Real.pi) ^ j * Cj := by gcongr
            _ = K₁ := by rw [hK₁]; ring
        have hphi : (1 + |ρ|) ^ 2 * ((1 + |ρ|) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
        calc fF w ρ = (fF w ρ * T ^ (100 : ℕ) * (1 + |ρ|) ^ 2) * (X * ((1 + |ρ|) ^ 2)⁻¹) := by
              have : fF w ρ * T ^ (100 : ℕ) * (1 + |ρ|) ^ 2 * (X * ((1 + |ρ|) ^ 2)⁻¹) =
                  fF w ρ * (T ^ (100 : ℕ) * X) * ((1 + |ρ|) ^ 2 * ((1 + |ρ|) ^ 2)⁻¹) := by ring
              rw [this, hX, hphi]; ring
          _ ≤ K₁ * (X * ((1 + |ρ|) ^ 2)⁻¹) := mul_le_mul_of_nonneg_right hkey (by positivity)
      have hgh : gD M t ρ * hI N M t ρ ≤ 2 * T ^ 4 := by
        calc gD M t ρ * hI N M t ρ ≤ M * (2 * M) := mul_le_mul hgM hlog hh0 (by positivity)
          _ = 2 * (M : ℝ) ^ 2 := by ring
          _ ≤ 2 * (T ^ 2) ^ 2 := by gcongr
          _ = 2 * T ^ 4 := by ring
      have : 0 ≤ c₁ / Real.sqrt |t| * (fF w ρ * gD M t ρ) := by positivity
      calc fF w ρ * gD M t ρ * hI N M t ρ = fF w ρ * (gD M t ρ * hI N M t ρ) := by ring
        _ ≤ (K₁ * (X * ((1 + |ρ|) ^ 2)⁻¹)) * (2 * T ^ 4) :=
            mul_le_mul hfdec hgh (by positivity) (by positivity)
        _ ≤ _ := by nlinarith
  have hgc := gD_continuous M t
  have hgK : ∀ ρ, |gD M t ρ| ≤ M := fun ρ => by
    rw [gD, abs_of_nonneg (norm_nonneg _)]; exact norm_dpoly_le M _
  have hfg : Integrable (fun ρ => fF w ρ * gD M t ρ) :=
    hfi.mul_bdd hgc.aestronglyMeasurable (ae_of_all _ fun ρ => by
      rw [Real.norm_eq_abs]; exact hgK ρ)
  set B := ∫ ρ, fF w ρ * gD M t ρ with hB
  set Cc := ∫ ρ, fF w ρ * gD M t ρ ^ 2 with hCc
  have hB0 : 0 ≤ B := integral_nonneg fun ρ => mul_nonneg (hf0 ρ) (norm_nonneg _)
  have hCc0 : 0 ≤ Cc := integral_nonneg fun ρ => mul_nonneg (hf0 ρ) (sq_nonneg _)
  have hcs : B ^ 2 ≤ A * Cc := cs_ineq hfi hf0 hgc hgK
  have hRHSi : Integrable (fun ρ => c₁ / Real.sqrt |t| * (fF w ρ * gD M t ρ) +
      (2 * K₁ * T ^ 4 * X) * ((1 + |ρ|) ^ 2)⁻¹) :=
    (hfg.const_mul _).add (integrable_phi.const_mul _)
  have hmain : ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ≤
      c₁ / Real.sqrt |t| * B + (2 * K₁ * T ^ 4 * X) * I₂ := by
    calc ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖
        ≤ ∫ ρ, fF w ρ * gD M t ρ * hI N M t ρ := GuthMaynard.S2.norm_sum_hHat_le hw t hN hM
      _ ≤ ∫ ρ, (c₁ / Real.sqrt |t| * (fF w ρ * gD M t ρ) +
          (2 * K₁ * T ^ 4 * X) * ((1 + |ρ|) ^ 2)⁻¹) :=
          integral_mono_of_nonneg (ae_of_all _ fun ρ =>
            mul_nonneg (mul_nonneg (hf0 ρ) (norm_nonneg _)) (norm_nonneg _)) hRHSi
            (ae_of_all _ hpt)
      _ = c₁ / Real.sqrt |t| * B + (2 * K₁ * T ^ 4 * X) * I₂ := by
          rw [integral_add (hfg.const_mul _) (integrable_phi.const_mul _), integral_const_mul,
            integral_const_mul]
  have hgoal : (∫ ρ, ‖𝓕 (Gw w) ρ‖ * ‖dpoly (fun _ => 1) M (-(t + 2 * Real.pi * ρ))‖ ^ 2) = Cc :=
    rfl
  rw [hgoal]
  have ht0 : 0 < |t| := by linarith
  have hsq : Real.sqrt |t| ^ 2 = |t| := Real.sq_sqrt ht0.le
  have hx0 : 0 ≤ c₁ / Real.sqrt |t| * B := by positivity
  have hy0 : 0 ≤ (2 * K₁ * T ^ 4 * X) * I₂ := by positivity
  have hx2 : 2 * (c₁ / Real.sqrt |t| * B) ^ 2 ≤ 2 * c₁ ^ 2 * A / |t| * Cc := by
    rw [mul_pow, div_pow, hsq]
    have : c₁ ^ 2 / |t| * B ^ 2 ≤ c₁ ^ 2 / |t| * (A * Cc) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    calc 2 * (c₁ ^ 2 / |t| * B ^ 2) ≤ 2 * (c₁ ^ 2 / |t| * (A * Cc)) := by linarith
      _ = 2 * c₁ ^ 2 * A / |t| * Cc := by ring
  have hy2 : 2 * ((2 * K₁ * T ^ 4 * X) * I₂) ^ 2 ≤ X := by
    have hT9 : K₂ * T ^ 8 ≤ T ^ (100 : ℕ) := by
      calc K₂ * T ^ 8 ≤ T * T ^ 8 := by gcongr
        _ = T ^ 9 := by ring
        _ ≤ T ^ (100 : ℕ) := pow_le_pow_right₀ hT1 (by norm_num)
    have h1 : K₂ * T ^ 8 * X ≤ 1 := by
      rw [← hX]; exact mul_le_mul_of_nonneg_right hT9 hX0.le
    calc 2 * ((2 * K₁ * T ^ 4 * X) * I₂) ^ 2 = (K₂ * T ^ 8 * X) * X := by rw [hK₂]; ring
      _ ≤ 1 * X := mul_le_mul_of_nonneg_right h1 hX0.le
      _ = X := one_mul X
  calc ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ^ 2
      ≤ (c₁ / Real.sqrt |t| * B + (2 * K₁ * T ^ 4 * X) * I₂) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hmain 2
    _ ≤ 2 * (c₁ / Real.sqrt |t| * B) ^ 2 + 2 * ((2 * K₁ * T ^ 4 * X) * I₂) ^ 2 := by
        nlinarith [sq_nonneg (c₁ / Real.sqrt |t| * B - (2 * K₁ * T ^ 4 * X) * I₂)]
    _ ≤ 2 * c₁ ^ 2 * A / |t| * Cc + X := add_le_add hx2 hy2

end GuthMaynard.S2.PartE1
end

section
namespace GuthMaynard.S2
open Complex MeasureTheory FourierTransform
/-! ### Part E: the approximate functional equation, squared; the sum over pairs -/
alias norm_sum_hHat_sq_le := GuthMaynard.S2.PartE1.norm_sum_hHat_sq_le

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
theorem solution (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N M : ℕ, 1 ≤ N → 1 ≤ M → (M : ℝ) ≤ T ^ 2 →
      ∀ t : ℝ, T ^ ε ≤ |t| →
        ‖∑ m ∈ Finset.Icc 1 M, hHat w t ((m : ℝ) * N)‖ ^ 2 ≤
          C / |t| * (∫ ρ : ℝ,
            ‖FourierTransform.fourier (fun x : ℝ => ((Real.exp x * w (Real.exp x) ^ 2 : ℝ) : ℂ)) ρ‖ *
              ‖∑ m ∈ Finset.Icc 1 M,
                (m : ℂ) ^ (((-(t + 2 * Real.pi * ρ) : ℝ) : ℂ) * Complex.I)‖ ^ 2) +
            T ^ (-100 : ℝ) := by
  obtain ⟨C, T₀, h⟩ := GuthMaynard.S2.norm_sum_hHat_sq_le hw hε
  refine ⟨C, T₀, fun T hT N M hN hM hMT t ht => ?_⟩
  have := h T hT N M hN hM hMT t ht
  simpa only [GuthMaynard.S2.dpoly, one_mul, show GuthMaynard.S2.Gw w = (fun x : ℝ => ((Real.exp x * w (Real.exp x) ^ 2 : ℝ) : ℂ)) from rfl] using this
end
