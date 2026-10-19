-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.polynomial_decay
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:15:53.975744+00:00
-- url     : https://prove2.me/submissions/f5bddf08-a6f3-4e99-a2ba-9f265d7ef60d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/QuadraticTail.lean:L179-L232
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.polynomial_decay. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma phase_norm (t u x : ℝ) : ‖phase t u x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

lemma phase_smooth (t u : ℝ) : ContDiff ℝ ∞ (phase t u) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ ↦ 2*Real.pi*(t*x^2/2-u*x)) := by fun_prop
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ Complex.I)).mul
    (Complex.ofRealCLM.contDiff.comp hc)).cexp

lemma phase_deriv (t u x : ℝ) : HasDerivAt (phase t u)
    (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x) x := by
  have hr : HasDerivAt (fun y : ℝ ↦ 2*Real.pi*(t*y^2/2-u*y))
      (2*Real.pi*(t*x-u)) x := by
    convert (((((hasDerivAt_id x).pow 2).const_mul t).div_const 2).sub
      ((hasDerivAt_id x).const_mul u)).const_mul (2*Real.pi) using 1 <;> first | rfl | (dsimp; ring)
  have hh := (hr.ofReal_comp.const_mul Complex.I).cexp
  change HasDerivAt (phase t u) _ x at hh
  convert hh using 1
  dsimp only [phase]
  push_cast
  ring

lemma amp_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (t u : ℝ) (k : ℕ)
    (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) : ContDiff ℝ ∞ (amp g t u k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases h : t*x-u = 0
  · have hx : x ∉ tsupport g := fun hx ↦ havoid x hx h
    rw [notMem_tsupport_iff_eventuallyEq] at hx
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (0:ℂ)) x).congr_of_eventuallyEq
    filter_upwards [hx] with y hy
    simp [amp, hy]
  · have hr : ContDiff ℝ ∞ (fun y : ℝ ↦ t*y-u) := by fun_prop
    have hd : ContDiff ℝ ∞ (fun y : ℝ ↦ ((t*y-u : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hr
    simpa only [amp, div_eq_mul_inv, Pi.inv_apply] using! hg.contDiffAt.mul
      ((hd.contDiffAt.pow k).inv (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h)))

lemma amp_support (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) :
    tsupport (amp g t u k) ⊆ tsupport g := by
  apply closure_mono
  intro x hx
  change amp g t u k x ≠ 0 at hx
  change g x ≠ 0
  intro h
  exact hx (by simp [amp, h])

lemma amp_compact {g : ℝ → ℂ} (hg : HasCompactSupport g) (t u : ℝ) (k : ℕ) :
    HasCompactSupport (amp g t u k) :=
  hg.mono' ((subset_tsupport _).trans (amp_support g t u k))

lemma amp_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (t u : ℝ) (k : ℕ)
    (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) (x : ℝ) :
    HasDerivAt (amp g t u (k+1))
      (amp (deriv g) t u (k+1) x - ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x) x := by
  by_cases h : t*x-u = 0
  · have hx : x ∉ tsupport g := fun hx ↦ havoid x hx h
    have hz : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hd : deriv g x = 0 := by
      exact (hz.hasDerivAt_iff.mpr (hasDerivAt_const x (0 : ℂ))).deriv
    simp only [amp, hd, h, Complex.ofReal_zero, zero_pow (by omega : k+1 ≠ 0),
      zero_pow (by omega : k+2 ≠ 0), div_zero, mul_zero, sub_zero]
    apply (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [amp, hy]
  · have hd : HasDerivAt (fun y : ℝ ↦ ((t*y-u : ℝ) : ℂ)) (t : ℂ) x := by
      simpa using (((hasDerivAt_id x).const_mul t).sub_const u).ofReal_comp
    have hh := (hg.differentiable (by norm_num) x).hasDerivAt.div (hd.pow (k+1))
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h))
    change HasDerivAt (amp g t u (k+1)) _ x at hh
    convert hh using 1
    simp only [amp, Pi.pow_apply, Nat.add_sub_cancel]
    have hc : ((t*x-u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
    rw [show k+2=(k+1)+1 by omega, pow_succ, pow_succ]
    field_simp [hc]
    ring

lemma osc_integrable {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (t u : ℝ) (k : ℕ) (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) :
    Integrable (fun x ↦ amp g t u k x * phase t u x) :=
  ((amp_smooth hgs t u k havoid).continuous.mul (phase_smooth t u).continuous).integrable_of_hasCompactSupport
    ((amp_compact hg t u k).mul_right)

lemma osc_parts {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (t u : ℝ) (k : ℕ) (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) :
    (2*Real.pi*Complex.I)*osc g t u k =
      -(osc (deriv g) t u (k+1) - ((k+1 : ℕ) : ℂ)*(t : ℂ)*osc g t u (k+2)) := by
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hgs).2
  have havd : ∀ x ∈ tsupport (deriv g), t*x-u ≠ 0 :=
    fun x hx ↦ havoid x (tsupport_deriv_subset hx)
  have hi1 := osc_integrable hg hgs t u k havoid
  have hi2 := osc_integrable hg.deriv hgd t u (k+1) havd
  have hi3 := osc_integrable hg hgs t u (k+2) havoid
  have hprod (x : ℝ) : amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x) =
      (2*Real.pi*Complex.I)*(amp g t u k x*phase t u x) := by
    by_cases h : t*x-u=0
    · have hx : g x=0 := Function.notMem_support.mp (fun hx ↦ havoid x (subset_tsupport _ hx) h)
      simp [amp, hx]
    · dsimp [amp]
      have hc : ((t*x-u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
      rw [pow_succ]
      field_simp [hc]
  have hprod2 (x : ℝ) : (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x =
      amp (deriv g) t u (k+1) x*phase t u x -
      (((k+1 : ℕ) : ℂ)*(t : ℂ))*(amp g t u (k+2) x*phase t u x) := by ring
  have hh := MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.mul ℝ ℂ)
    (fun x _ ↦ amp_deriv hgs t u k havoid x)
    (fun x _ ↦ phase_deriv t u x)
    (show Integrable (fun x ↦ amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x)) volume by
      simp_rw [hprod]; exact hi1.const_mul _)
    (show Integrable (fun x ↦ (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x) volume by
      simp_rw [hprod2]; exact hi2.sub (hi3.const_mul _))
    (osc_integrable hg hgs t u (k+1) havoid)
  change (∫ x : ℝ, amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x)) =
    -(∫ x : ℝ, (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x) at hh
  simp_rw [hprod, hprod2] at hh
  rw [integral_const_mul, integral_sub hi2 (hi3.const_mul _), integral_const_mul] at hh
  exact hh

lemma osc_bound_zero {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {c M : ℝ} (hc : 0 < c) (hM : 0 < M) (t u : ℝ) (k : ℕ)
    (hsep : ∀ x ∈ tsupport g, c*M ≤ |t*x-u|) :
    M^k * ‖osc g t u k‖ ≤ (∫ x : ℝ, ‖g x‖) / c^k := by
  have hav : ∀ x ∈ tsupport g, t*x-u ≠ 0 := by
    intro x hx hz
    have := hsep x hx
    rw [hz, abs_zero] at this
    nlinarith [mul_pos hc hM]
  have hi := osc_integrable hg hgs t u k hav
  have hpoint (x : ℝ) : M^k * ‖amp g t u k x*phase t u x‖ ≤ ‖g x‖ / c^k := by
    by_cases hx : g x=0
    · simp [amp, hx]
    · have hx' := subset_tsupport g hx
      have hz : 0 < |t*x-u| := lt_of_lt_of_le (mul_pos hc hM) (hsep x hx')
      rw [norm_mul, phase_norm, mul_one, amp, norm_div, norm_pow, Complex.norm_real]
      rw [Real.norm_eq_abs, ← mul_div_assoc, div_le_div_iff₀ (pow_pos hz _) (pow_pos hc _)]
      have hp := pow_le_pow_left₀ (le_of_lt (mul_pos hc hM)) (hsep x hx') k
      rw [mul_pow] at hp
      nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg (g x))]
  calc
    M^k * ‖osc g t u k‖ ≤ M^k * ∫ x : ℝ, ‖amp g t u k x*phase t u x‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (pow_nonneg hM.le _)
    _ = ∫ x : ℝ, M^k * ‖amp g t u k x*phase t u x‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ x : ℝ, ‖g x‖ / c^k := integral_mono (hi.norm.const_mul _)      ((hgs.continuous.norm.integrable_of_hasCompactSupport hg.norm).div_const _) hpoint
    _ = (∫ x : ℝ, ‖g x‖) / c^k := integral_div _ _

/-- Uniform repeated nonstationary integration by parts, with the support condition
on the actual amplitude. The parameters may vary, but c and B stay fixed. -/
theorem polynomial_decay (l : ℕ) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B) :
    ∀ (g : ℝ → ℂ), HasCompactSupport g → ContDiff ℝ ∞ g → ∀ k : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t u M : ℝ), 0 < M → |t| ≤ B*M →
      (∀ x ∈ tsupport g, c*M ≤ |t*x-u|) → M^(k+l)*‖osc g t u k‖ ≤ C := by
  induction l with
  | zero =>
      intro g hg hgs k
      refine ⟨(∫ x : ℝ, ‖g x‖)/c^k, div_nonneg (integral_nonneg (fun x ↦ norm_nonneg _))
        (pow_nonneg hc.le _), ?_⟩
      intro t u M hM ht hs
      simpa using osc_bound_zero hg hgs hc hM t u k hs
  | succ l ih =>
      intro g hg hgs k
      have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hgs).2
      obtain ⟨C1, hC1, h1⟩ := ih (deriv g) hg.deriv hgd (k+1)
      obtain ⟨C2, hC2, h2⟩ := ih g hg hgs (k+2)
      refine ⟨(C1+(k+1)*B*C2)/(2*Real.pi), by positivity, ?_⟩
      intro t u M hM ht hs
      have hav : ∀ x ∈ tsupport g, t*x-u ≠ 0 := by
        intro x hx hz
        have := hs x hx
        rw [hz, abs_zero] at this
        nlinarith [mul_pos hc hM]
      have hs' : ∀ x ∈ tsupport (deriv g), c*M ≤ |t*x-u| :=
        fun x hx ↦ hs x (tsupport_deriv_subset hx)
      have hh1 := h1 t u M hM ht hs'
      have hh2 := h2 t u M hM ht hs
      have hnorm : (2*Real.pi)*‖osc g t u k‖ ≤
          ‖osc (deriv g) t u (k+1)‖+(k+1)*|t| * ‖osc g t u (k+2)‖ := by
        have he := congrArg norm (osc_parts hg hgs t u k hav)
        have htriangle := norm_sub_le (osc (deriv g) t u (k+1))
          (((k+1 : ℕ) : ℂ)*(t : ℂ)*osc g t u (k+2))
        simp only [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_natCast] at he htriangle
        push_cast at he htriangle
        linarith
      have hterm : M^(k+l+1)*|t| * ‖osc g t u (k+2)‖ ≤ B*C2 := by
        calc
          _ ≤ M^(k+l+1)*(B*M)*‖osc g t u (k+2)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (pow_nonneg hM.le _)) (norm_nonneg _)
          _ = B*(M^(k+2+l)*‖osc g t u (k+2)‖) := by
            rw [show k+2+l=(k+l+1)+1 by omega, pow_succ]; ring
          _ ≤ B*C2 := mul_le_mul_of_nonneg_left hh2 hB
      rw [le_div_iff₀ (by positivity : 0 < 2*Real.pi)]
      have hp := mul_le_mul_of_nonneg_left hnorm (pow_nonneg hM.le (k+l+1))
      have hk : (0:ℝ) ≤ k+1 := by positivity
      have hterm' := mul_le_mul_of_nonneg_left hterm hk
      have e1 : k+1+l=k+l+1 := by omega
      rw [e1] at hh1
      have e2 : k+(l+1)=k+l+1 := by omega
      rw [e2]
      nlinarith only [hp, hh1, hterm']

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.polynomial_decay := @_root_.OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.polynomial_decay
