-- Prove2me | solution 1 for GuthMaynard.norm_S_one_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T19:57:06.06221+00:00
-- url     : https://prove2.me/submissions/6712caec-1732-42ed-b718-254b65cb44f0

import Definitions.Def_GuthMaynard
import Mathlib

section
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
end

section
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
end

section
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
end

section
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
end

section
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
end

section
section
namespace GuthMaynardS56

open scoped Real

/-- Constants for the decay bounds. -/
structure Consts (w : ℝ → ℝ) (k' : ℕ) (K C0 C2 Ck : ℝ) : Prop where
  bdd : ∀ t ξ : ℝ, ‖GuthMaynard.hHat w t ξ‖ ≤ C0
  c2 : ∀ t ξ : ℝ, ξ ≠ 0 → ‖GuthMaynard.hHat w t ξ‖ * |ξ|^2 ≤ C2 * (1 + |t|)^2
  c100 : ∀ ξ : ℝ, ξ ≠ 0 → ‖GuthMaynard.hHat w 0 ξ‖ * |ξ|^100 ≤ K
  ck : ∀ t : ℝ, 1 ≤ |t| → ‖GuthMaynard.hHat w t 0‖ * |t|^k' ≤ Ck

theorem caseB {w : ℝ → ℝ} {k' : ℕ} {K C0 C2 Ck : ℝ} (hc : Consts w k' K C0 C2 Ck)
    {u τ : ℝ} (hu : 1 ≤ u) (hτ : 1 ≤ τ) (hτk : u^68 ≤ τ^k')
    {N : ℕ} (hN1 : u^3 ≤ N)
    {d m n : ℝ} (hd : |d| ≤ u^4) (hm : τ ≤ |m|) {z : ℤ} (hz : z ≠ 0) :
    ‖GuthMaynard.hHat w d (z * N)‖ * ‖GuthMaynard.hHat w m 0‖ * ‖GuthMaynard.hHat w n 0‖ *
      u^66 * (z:ℝ)^2 ≤ 4 * |C2| * C0 * |Ck| := by
  have hC0 : 0 ≤ C0 := (norm_nonneg _).trans (hc.bdd 0 0)
  have hz1 : (1:ℝ) ≤ |(z:ℝ)| := by
    have : (1:ℤ) ≤ |z| := Int.one_le_abs hz
    exact_mod_cast this
  have hu0 : 0 < u := by linarith
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hN1
  have hξ : ((z:ℝ) * N) ≠ 0 := mul_ne_zero (by exact_mod_cast hz) hN0.ne'
  have hξa : |(z:ℝ) * N| = |(z:ℝ)| * N := by rw [abs_mul, abs_of_pos hN0]
  set a := ‖GuthMaynard.hHat w d (z * N)‖ with ha
  set b := ‖GuthMaynard.hHat w m 0‖ with hb
  set c := ‖GuthMaynard.hHat w n 0‖ with hcdef
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hc0 : 0 ≤ c := norm_nonneg _
  have hcb : c ≤ C0 := hc.bdd n 0
  -- A1
  have A1 : a * (z:ℝ)^2 ≤ 4 * |C2| * u^2 := by
    have h1 := hc.c2 d (z * N) hξ
    rw [hξa] at h1
    have h2 : (1 + |d|)^2 ≤ 4 * u^8 := by
      have : 1 + |d| ≤ 2 * u^4 := by
        have : (1:ℝ) ≤ u^4 := one_le_pow₀ hu
        linarith
      calc (1 + |d|)^2 ≤ (2 * u^4)^2 := by gcongr
        _ = 4 * u^8 := by ring
    have hN2 : u^6 ≤ (N:ℝ)^2 := by
      calc u^6 = (u^3)^2 := by ring
        _ ≤ (N:ℝ)^2 := by gcongr
    have h3 : a * ((z:ℝ)^2 * u^6) ≤ |C2| * (4 * u^8) := by
      calc a * ((z:ℝ)^2 * u^6) ≤ a * ((z:ℝ)^2 * (N:ℝ)^2) := by gcongr
        _ = a * (|(z:ℝ)| * N)^2 := by rw [mul_pow, sq_abs]
        _ ≤ C2 * (1 + |d|)^2 := h1
        _ ≤ |C2| * (4 * u^8) := by
          calc C2 * (1 + |d|)^2 ≤ |C2| * (1 + |d|)^2 := by gcongr; exact le_abs_self _
            _ ≤ |C2| * (4 * u^8) := by gcongr
    have hu6 : 0 < u^6 := by positivity
    have : (a * (z:ℝ)^2) * u^6 ≤ (4 * |C2| * u^2) * u^6 := by
      calc (a * (z:ℝ)^2) * u^6 = a * ((z:ℝ)^2 * u^6) := by ring
        _ ≤ |C2| * (4 * u^8) := h3
        _ = (4 * |C2| * u^2) * u^6 := by ring
    exact le_of_mul_le_mul_right this hu6
  -- A2
  have A2 : b * u^68 ≤ |Ck| := by
    have hm1 : 1 ≤ |m| := hτ.trans hm
    have h1 := hc.ck m hm1
    have h2 : u^68 ≤ |m|^k' := by
      refine hτk.trans ?_
      gcongr
    calc b * u^68 ≤ b * |m|^k' := by gcongr
      _ ≤ Ck := h1
      _ ≤ |Ck| := le_abs_self _
  have hu2 : 0 < u^2 := by positivity
  have hprod : (a * (z:ℝ)^2) * (b * u^66) * u^2 ≤ (4 * |C2| * |Ck|) * u^2 := by
    calc (a * (z:ℝ)^2) * (b * u^66) * u^2 = (a * (z:ℝ)^2) * (b * u^68) := by ring
      _ ≤ (4 * |C2| * u^2) * |Ck| := by gcongr
      _ = (4 * |C2| * |Ck|) * u^2 := by ring
  have hprod' : (a * (z:ℝ)^2) * (b * u^66) ≤ 4 * |C2| * |Ck| := le_of_mul_le_mul_right hprod hu2
  calc a * b * c * u^66 * (z:ℝ)^2 = ((a * (z:ℝ)^2) * (b * u^66)) * c := by ring
    _ ≤ (4 * |C2| * |Ck|) * C0 := by
        apply mul_le_mul hprod' hcb hc0
        positivity
    _ = 4 * |C2| * C0 * |Ck| := by ring

theorem key_bound {w : ℝ → ℝ} {k' : ℕ} {K C0 C2 Ck : ℝ} (hc : Consts w k' K C0 C2 Ck)
    {u τ : ℝ} (hu : 1 ≤ u) (hτ : 1 ≤ τ) (hτk : u^68 ≤ τ^k')
    {N : ℕ} (hN1 : u^3 ≤ N)
    {d e f : ℝ} (hsum : d + e + f = 0) (hd : |d| ≤ u^4)
    (he : e = 0 ∨ τ ≤ |e|) (hf : f = 0 ∨ τ ≤ |f|) {z : ℤ} (hz : z ≠ 0) :
    ‖GuthMaynard.hHat w d (z * N)‖ * ‖GuthMaynard.hHat w e 0‖ * ‖GuthMaynard.hHat w f 0‖ *
      u^66 * (z:ℝ)^2 ≤ |K| * C0^2 + 4 * |C2| * C0 * |Ck| := by
  have hC0 : 0 ≤ C0 := (norm_nonneg _).trans (hc.bdd 0 0)
  have hK : 0 ≤ 4 * |C2| * C0 * |Ck| := by positivity
  have hK' : 0 ≤ |K| * C0^2 := by positivity
  by_cases he0 : e = 0
  · by_cases hf0 : f = 0
    · -- diagonal
      have hd0 : d = 0 := by linarith
      subst hd0; subst he0; subst hf0
      have hz1 : (1:ℝ) ≤ |(z:ℝ)| := by
        have : (1:ℤ) ≤ |z| := Int.one_le_abs hz
        exact_mod_cast this
      have hu0 : 0 < u := by linarith
      have hN0 : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hN1
      have hξ : ((z:ℝ) * N) ≠ 0 := mul_ne_zero (by exact_mod_cast hz) hN0.ne'
      have hξa : |(z:ℝ) * N| = |(z:ℝ)| * N := by rw [abs_mul, abs_of_pos hN0]
      have h1 := hc.c100 ((z:ℝ) * N) hξ
      rw [hξa] at h1
      have hz2 : (z:ℝ)^2 ≤ |(z:ℝ)|^100 := by
        rw [← sq_abs]; exact pow_le_pow_right₀ hz1 (by norm_num)
      have hN3 : u^66 ≤ (N:ℝ)^100 := by
        calc u^66 ≤ u^300 := pow_le_pow_right₀ hu (by norm_num)
          _ = (u^3)^100 := by ring
          _ ≤ (N:ℝ)^100 := by gcongr
      have hle : u^66 * (z:ℝ)^2 ≤ (|(z:ℝ)| * N)^100 := by
        rw [mul_pow]
        calc u^66 * (z:ℝ)^2 ≤ (N:ℝ)^100 * |(z:ℝ)|^100 := by gcongr
          _ = _ := by ring
      set a := ‖GuthMaynard.hHat w 0 ((z:ℝ) * N)‖
      have ha0 : 0 ≤ a := norm_nonneg _
      have hb := hc.bdd 0 0
      calc a * ‖GuthMaynard.hHat w 0 0‖ * ‖GuthMaynard.hHat w 0 0‖ * u^66 * (z:ℝ)^2
          = (a * (u^66 * (z:ℝ)^2)) * (‖GuthMaynard.hHat w 0 0‖ * ‖GuthMaynard.hHat w 0 0‖) := by ring
        _ ≤ K * (C0 * C0) := by
            have hK0 : 0 ≤ K := (mul_nonneg ha0 (by positivity)).trans h1
            have hA : a * (u^66 * (z:ℝ)^2) ≤ K :=
              (mul_le_mul_of_nonneg_left hle ha0).trans h1
            exact mul_le_mul hA (mul_le_mul hb hb (norm_nonneg _) hC0) (by positivity) hK0
        _ ≤ |K| * C0^2 := by
            rw [← sq]; gcongr; exact le_abs_self _
        _ ≤ _ := by linarith
    · have hf' : τ ≤ |f| := hf.resolve_left hf0
      have := caseB hc hu hτ hτk hN1 (n := e) (m := f) hd hf' hz
      calc _ = ‖GuthMaynard.hHat w d (z * N)‖ * ‖GuthMaynard.hHat w f 0‖ * ‖GuthMaynard.hHat w e 0‖ *
            u^66 * (z:ℝ)^2 := by ring
        _ ≤ _ := this
        _ ≤ _ := by linarith
  · have he' : τ ≤ |e| := he.resolve_left he0
    have := caseB hc hu hτ hτk hN1 (n := f) (m := e) hd he' hz
    linarith

end GuthMaynardS56

end
end

section
section
namespace GuthMaynardS56

/-- the index set of `S k`, for `k = 1` -/
abbrev Sub1 := {m : Fin 3 → ℤ // (Finset.univ.filter fun i => m i ≠ 0).card = 1}

theorem sub_unique {m : Fin 3 → ℤ} (h : (Finset.univ.filter fun i => m i ≠ 0).card = 1) :
    ∃ a, m a ≠ 0 ∧ ∀ j, j ≠ a → m j = 0 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
  refine ⟨a, ?_, fun j hj => ?_⟩
  · have : a ∈ Finset.univ.filter fun i => m i ≠ 0 := by rw [ha]; simp
    simpa using this
  · by_contra hne
    have : j ∈ Finset.univ.filter fun i => m i ≠ 0 := by simpa using hne
    rw [ha] at this
    exact hj (by simpa using this)

theorem card_single (i : Fin 3) {z : ℤ} (hz : z ≠ 0) :
    (Finset.univ.filter fun j => (Pi.single i z : Fin 3 → ℤ) j ≠ 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  by_cases h : j = i
  · subst h; simp [hz]
  · simp [Pi.single_apply, h]

/-- the weight function whose sum over `Sub1` is finite -/
noncomputable def gSub (m : Sub1) : ℝ := ∑ i, (((m.1 i : ℤ) : ℝ)^2)⁻¹

theorem summable_coord (i : Fin 3) : Summable (fun m : Sub1 => (((m.1 i : ℤ) : ℝ)^2)⁻¹) := by
  let ψ : {z : ℤ // z ≠ 0} → Sub1 := fun z => ⟨Pi.single i z.1, card_single i z.2⟩
  have hψ : Function.Injective ψ := by
    intro z z' h
    have := congrArg (fun m : Sub1 => m.1 i) h
    simp [ψ] at this
    exact Subtype.ext this
  rw [← hψ.summable_iff]
  · have h1 : Summable (fun n : ℤ => 1 / ((n:ℝ))^2) := by
      exact_mod_cast (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    have h2 := h1.subtype {z : ℤ | z ≠ 0}
    refine h2.congr ?_
    intro z
    simp [ψ]
  · intro m hm
    by_contra hne
    apply hm
    have hmi : m.1 i ≠ 0 := by
      intro h0; apply hne; simp [h0]
    obtain ⟨a, ha, hj⟩ := sub_unique m.2
    have hia : i = a := by
      by_contra hh; exact hmi (hj i hh)
    subst hia
    refine ⟨⟨m.1 i, hmi⟩, ?_⟩
    apply Subtype.ext
    funext j
    by_cases hji : j = i
    · subst hji; simp [ψ]
    · simp [ψ, Pi.single_apply, hji, hj j hji]

theorem summable_gSub : Summable gSub := by
  unfold gSub
  exact summable_sum (fun i _ => summable_coord i)

theorem gSub_nonneg (m : Sub1) : 0 ≤ gSub m := by
  unfold gSub; exact Finset.sum_nonneg (fun i _ => by positivity)

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
end

section
section
namespace GuthMaynardS56

open GuthMaynard

theorem le_of_key {X Kb p q : ℝ} (hp : 0 < p) (hq : 0 < q) (h : X * p * q ≤ Kb) :
    X ≤ Kb * p⁻¹ * q⁻¹ := by
  have : X ≤ Kb / (p * q) := (le_div_iff₀ (mul_pos hp hq)).2 (by linarith [h, show X * (p*q) = X*p*q by ring])
  calc X ≤ Kb / (p * q) := this
    _ = Kb * p⁻¹ * q⁻¹ := by field_simp

theorem gSub_eq (m : Sub1) (a : Fin 3) (hj : ∀ j, j ≠ a → m.1 j = 0) :
    gSub m = (((m.1 a : ℤ) : ℝ)^2)⁻¹ := by
  unfold gSub
  rw [Finset.sum_eq_single a]
  · intro j _ hja; simp [hj j hja]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem iterm_bound {w : ℝ → ℝ} {k' : ℕ} {K C0 C2 Ck : ℝ} (hc : Consts w k' K C0 C2 Ck)
    {u τ : ℝ} (hu : 1 ≤ u) (hτ : 1 ≤ τ) (hτk : u^68 ≤ τ^k')
    {N : ℕ} (hN1 : u^3 ≤ N) {W : Finset ℝ}
    (hsep : ∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → τ ≤ |t - t'|)
    (hint : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ u^4) (m : Sub1) :
    ‖Iterm w N W m.1‖ ≤ (N:ℝ)^3 * (W.card:ℝ)^3 *
      ((|K| * C0^2 + 4 * |C2| * C0 * |Ck|) * (u^66)⁻¹ * gSub m) := by
  obtain ⟨a, ha, hj⟩ := sub_unique m.2
  have hu0 : 0 < u := by linarith
  have hp : 0 < u^66 := by positivity
  have hz2 : 0 < (((m.1 a : ℤ) : ℝ))^2 := by
    have : ((m.1 a : ℤ) : ℝ) ≠ 0 := by exact_mod_cast ha
    positivity
  have hdiff : ∀ p ∈ W, ∀ q ∈ W, (p - q = 0 ∨ τ ≤ |p - q|) := by
    intro p hp q hq
    by_cases h : p = q
    · left; simp [h]
    · right; exact hsep p hp q hq h
  have hg := gSub_eq m a hj
  set M := (|K| * C0^2 + 4 * |C2| * C0 * |Ck|) * (u^66)⁻¹ * gSub m with hM
  have htriple : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W,
      ‖hHat w (t₁ - t₂) (m.1 0 * N) * hHat w (t₂ - t₃) (m.1 1 * N) * hHat w (t₃ - t₁) (m.1 2 * N)‖ ≤ M := by
    intro t₁ h₁ t₂ h₂ t₃ h₃
    rw [hM, hg]
    have H12 := hdiff t₁ h₁ t₂ h₂
    have H23 := hdiff t₂ h₂ t₃ h₃
    have H31 := hdiff t₃ h₃ t₁ h₁
    have D12 := hint t₁ h₁ t₂ h₂
    have D23 := hint t₂ h₂ t₃ h₃
    have D31 := hint t₃ h₃ t₁ h₁
    fin_cases a
    · have h1 : m.1 1 = 0 := hj 1 (by decide)
      have h2 : m.1 2 = 0 := hj 2 (by decide)
      have hk := key_bound hc hu hτ hτk hN1 (d := t₁ - t₂) (e := t₂ - t₃) (f := t₃ - t₁)
        (by ring) D12 H23 H31 (z := m.1 0) (by simpa using ha)
      simp only [h1, h2, Int.cast_zero, zero_mul, norm_mul]
      simp only [Fin.zero_eta] at hg ⊢
      exact le_of_key hp hz2 hk
    · have h1 : m.1 0 = 0 := hj 0 (by decide)
      have h2 : m.1 2 = 0 := hj 2 (by decide)
      have hk := key_bound hc hu hτ hτk hN1 (d := t₂ - t₃) (e := t₁ - t₂) (f := t₃ - t₁)
        (by ring) D23 H12 H31 (z := m.1 1) (by simpa using ha)
      simp only [h1, h2, Int.cast_zero, zero_mul, norm_mul]
      have := le_of_key hp hz2 hk
      simp only [Fin.mk_one] at hg ⊢
      calc _ = ‖hHat w (t₂ - t₃) (↑(m.1 1) * ↑N)‖ * ‖hHat w (t₁ - t₂) 0‖ * ‖hHat w (t₃ - t₁) 0‖ := by ring
        _ ≤ _ := this
    · have h1 : m.1 0 = 0 := hj 0 (by decide)
      have h2 : m.1 1 = 0 := hj 1 (by decide)
      have hk := key_bound hc hu hτ hτk hN1 (d := t₃ - t₁) (e := t₁ - t₂) (f := t₂ - t₃)
        (by ring) D31 H12 H23 (z := m.1 2) (by simpa using ha)
      simp only [h1, h2, Int.cast_zero, zero_mul, norm_mul]
      have := le_of_key hp hz2 hk
      calc _ = ‖hHat w (t₃ - t₁) (↑(m.1 2) * ↑N)‖ * ‖hHat w (t₁ - t₂) 0‖ * ‖hHat w (t₂ - t₃) 0‖ := by ring
        _ ≤ _ := this
  unfold Iterm
  rw [norm_mul]
  have hN : ‖(N:ℂ)^3‖ = (N:ℝ)^3 := by simp
  rw [hN]
  have hsum : ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      hHat w (t₁ - t₂) (m.1 0 * N) * hHat w (t₂ - t₃) (m.1 1 * N) * hHat w (t₃ - t₁) (m.1 2 * N)‖
      ≤ (W.card:ℝ)^3 * M := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ t₁ ∈ W, ‖∑ t₂ ∈ W, ∑ t₃ ∈ W,
      hHat w (t₁ - t₂) (m.1 0 * N) * hHat w (t₂ - t₃) (m.1 1 * N) * hHat w (t₃ - t₁) (m.1 2 * N)‖
        ≤ (W.card:ℝ)^2 * M := by
      intro t₁ h₁
      refine (norm_sum_le _ _).trans ?_
      have : ∀ t₂ ∈ W, ‖∑ t₃ ∈ W,
        hHat w (t₁ - t₂) (m.1 0 * N) * hHat w (t₂ - t₃) (m.1 1 * N) * hHat w (t₃ - t₁) (m.1 2 * N)‖
          ≤ (W.card:ℝ) * M := by
        intro t₂ h₂
        refine (norm_sum_le _ _).trans ?_
        calc _ ≤ ∑ t₃ ∈ W, M := Finset.sum_le_sum (fun t₃ h₃ => htriple t₁ h₁ t₂ h₂ t₃ h₃)
          _ = _ := by simp
      calc _ ≤ ∑ t₂ ∈ W, (W.card:ℝ) * M := Finset.sum_le_sum this
        _ = _ := by simp; ring
    calc _ ≤ ∑ t₁ ∈ W, (W.card:ℝ)^2 * M := Finset.sum_le_sum this
      _ = _ := by simp; ring
  calc (N:ℝ)^3 * _ ≤ (N:ℝ)^3 * ((W.card:ℝ)^3 * M) := by gcongr
    _ = _ := by ring

end GuthMaynardS56

end
end

section
section
namespace GuthMaynardS56

open GuthMaynard

theorem norm_S_one_le_dev (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 1 w N W‖ ≤ C * T ^ (-10 : ℝ) := by
  obtain ⟨C0, hC0⟩ := hHat_bdd hw
  obtain ⟨C2, hC2⟩ := hHat_decay_freq hw 2
  obtain ⟨K, hK⟩ := hHat_decay_freq hw 100
  obtain ⟨Ck, hCk⟩ := hHat_decay_zero hw ⌈17 / ε⌉₊
  have hc : Consts w ⌈17 / ε⌉₊ K C0 C2 Ck :=
    ⟨hC0, hC2, fun ξ hξ => by simpa using hK 0 ξ hξ, hCk⟩
  have hC0nn : 0 ≤ C0 := (norm_nonneg _).trans (hC0 0 0)
  set Kb := |K| * C0^2 + 4 * |C2| * C0 * |Ck| with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  set G := ∑' m : Sub1, gSub m with hG
  have hG0 : 0 ≤ G := tsum_nonneg gSub_nonneg
  refine ⟨8 * Kb * G, ?_⟩
  intro T N hN W a hsep hWi
  have hT0 : 0 ≤ T := by
    have := hN.2
    have : (0:ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  by_cases hN0 : N = 0
  · subst hN0
    have : S 1 w 0 W = 0 := by
      unfold S Iterm
      simp
    rw [this, norm_zero]
    positivity
  · have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
    have hT1 : 1 ≤ T := hN1.trans hN.2
    set u : ℝ := T ^ (1/4 : ℝ) with hu
    have hu1 : 1 ≤ u := Real.one_le_rpow hT1 (by norm_num)
    have hu0 : 0 < u := by linarith
    have hu4 : u^4 = T := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hT0]; norm_num
    have hu3 : u^3 = T ^ (3/4 : ℝ) := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hT0]; norm_num
    have hτ : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
    have hτk : u^68 ≤ (T ^ ε)^⌈17 / ε⌉₊ := by
      have h1 : u^68 = T^(17:ℝ) := by
        rw [show u^68 = (u^4)^17 by ring, hu4]; norm_cast
      rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hT0]
      apply Real.rpow_le_rpow_of_exponent_le hT1
      have := Nat.le_ceil (17 / ε)
      calc (17:ℝ) = ε * (17 / ε) := by field_simp
        _ ≤ ε * ⌈17 / ε⌉₊ := by gcongr
    have hN3 : u^3 ≤ N := by rw [hu3]; exact hN.1
    have hNu : (N:ℝ) ≤ u^4 := by rw [hu4]; exact hN.2
    have hint : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ u^4 := by
      intro t ht t' ht'
      have h1 := hWi t ht
      have h2 := hWi t' ht'
      rw [hu4, abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hcard : (W.card : ℝ) ≤ 2 * u^4 := by
      have := card_le_of_sep hτ hT0 hsep hWi
      rw [hu4]; linarith
    have hterm : ∀ m : Sub1, ‖Iterm w N W m.1‖ ≤ (8 * Kb * T ^ (-10:ℝ)) * gSub m := by
      intro m
      have hb := iterm_bound hc hu1 hτ hτk hN3 hsep hint m
      refine hb.trans ?_
      have hg := gSub_nonneg m
      have e1 : (T ^ (-10:ℝ)) = (u^40)⁻¹ := by
        rw [Real.rpow_neg hT0, ← hu4]
        congr 1
        rw [show u^40 = (u^4)^10 by ring]
        norm_cast
      rw [e1]
      have hn : (W.card:ℝ)^3 ≤ (2 * u^4)^3 := by gcongr
      have hNn : (N:ℝ)^3 ≤ (u^4)^3 := by gcongr
      have hA : (N:ℝ)^3 * (W.card:ℝ)^3 ≤ 8 * u^24 := by
        calc (N:ℝ)^3 * (W.card:ℝ)^3 ≤ (u^4)^3 * (2 * u^4)^3 := by gcongr
          _ = 8 * u^24 := by ring
      have hpow : u^24 * (u^66)⁻¹ ≤ (u^40)⁻¹ := by
        have : u^24 * (u^66)⁻¹ = (u^42)⁻¹ := by
          field_simp
        rw [this]
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_right₀ hu1 (by norm_num)
      have hM : 0 ≤ Kb * gSub m := by positivity
      calc (N:ℝ)^3 * (W.card:ℝ)^3 * (Kb * (u^66)⁻¹ * gSub m)
          ≤ (8 * u^24) * (Kb * (u^66)⁻¹ * gSub m) := by gcongr
        _ = 8 * Kb * (u^24 * (u^66)⁻¹) * gSub m := by ring
        _ ≤ 8 * Kb * (u^40)⁻¹ * gSub m := by gcongr
    have hsum : HasSum (fun m : Sub1 => (8 * Kb * T ^ (-10:ℝ)) * gSub m)
        ((8 * Kb * T ^ (-10:ℝ)) * G) := summable_gSub.hasSum.mul_left _
    have := tsum_of_norm_bounded hsum hterm
    calc ‖S 1 w N W‖ ≤ (8 * Kb * T ^ (-10:ℝ)) * G := this
      _ = 8 * Kb * G * T ^ (-10:ℝ) := by ring

end GuthMaynardS56

end
end

section
open GuthMaynard

theorem solution (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 1 w N W‖ ≤ C * T ^ (-10 : ℝ) := by
  exact GuthMaynardS56.norm_S_one_le_dev w hw ε hε

end
