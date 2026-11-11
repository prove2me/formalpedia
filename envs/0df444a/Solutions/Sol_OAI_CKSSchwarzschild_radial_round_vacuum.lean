-- Prove2me | solution 1 for OAI.CKSSchwarzschild.radial_round_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:50:09.507661+00:00
-- url     : https://prove2.me/submissions/9a8de7b7-f048-4799-8d59-537f410affa4

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_Q227CKS002

section
-- module Solutions.Q227_CKS.Relativity_CKS_SmoothOuterDEC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_add (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y + g y) x = D e f x + D e g x := by
  simp [D, fderiv_fun_add hf hg]
lemma D_sub (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y - g y) x = D e f x - D e g x := by
  simp [D, fderiv_fun_sub hf hg]

lemma D_D {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (e w : E) :
    D w (D e f) x = fderiv ℝ (fderiv ℝ f) x w e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold D
  rw [fderiv_clm_apply hd (differentiableAt_const e)]
  simp

lemma D_comm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (e w : E) :
    D w (D e f) x = D e (D w f) x := by
  rw [D_D hf, D_D hf]
  exact hf.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) w e

lemma D_D_mul (e w : E) {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    D w (D e (fun y => f y * g y)) x =
      f x * D w (D e g) x + g x * D w (D e f) x +
        D w f x * D e g x + D w g x * D e f x := by
  have heq : D e (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => f y * D e g y + g y * D e f y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact D_mul e (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  have hf1 := hf.differentiableAt (by norm_num)
  have hg1 := hg.differentiableAt (by norm_num)
  have hfe := (contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  have hge := (contDiffAt_D hg (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  rw [D_congr heq w, D_add w (hf1.fun_mul hge) (hg1.fun_mul hfe),
    D_mul w hf1 hge, D_mul w hg1 hfe]
  ring

lemma D_inv (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    D e (fun y => (f y)⁻¹) x = -(D e f x) / (f x) ^ 2 := by
  unfold D
  change fderiv ℝ ((fun z : ℝ => z⁻¹) ∘ f) x e = _
  rw [((hasDerivAt_inv h0).comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp
  ring

lemma D_div (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h0 : g x ≠ 0) :
    D e (fun y => f y / g y) x =
      (D e f x * g x - f x * D e g x) / (g x) ^ 2 := by
  simp only [div_eq_mul_inv]
  rw [D_mul (g := fun y => (g y)⁻¹) e hf (hg.inv h0), D_inv e hg h0]
  field_simp
  ring

lemma diffAt_div {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h0 : g x ≠ 0) :
    DifferentiableAt ℝ (fun y => f y / g y) x := by
  have hgi : DifferentiableAt ℝ (fun y => (g y)⁻¹) x := hg.inv h0
  simpa only [div_eq_mul_inv] using
    (show DifferentiableAt ℝ (fun y => f y * (g y)⁻¹) x from hf.fun_mul hgi)

lemma D_pow (e : E) {f : E → ℝ} {x : E} (n : ℕ)
    (hf : DifferentiableAt ℝ f x) :
    D e (fun y => f y ^ n) x = n * f x ^ (n - 1) * D e f x := by
  unfold D
  rw [fderiv_fun_pow n hf]
  simp

lemma D_inv_sq (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    D e (fun y => 1 / f y ^ 2) x = -2 * D e f x / f x ^ 3 := by
  rw [D_div (g := fun y => f y ^ 2) e (differentiableAt_const 1) (hf.pow 2) (pow_ne_zero _ h0),
    D_const, D_pow e 2 hf]
  norm_num
  field_simp

lemma D_D_inv_sq (e w : E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (h0 : f x ≠ 0) :
    D w (D e (fun y => 1 / f y ^ 2)) x =
      6 * D e f x * D w f x / f x ^ 4 - 2 * D w (D e f) x / f x ^ 3 := by
  have hnear : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuousAt.eventually_ne h0
  have heq : D e (fun y => 1 / f y ^ 2) =ᶠ[𝓝 x]
      (fun y => -2 * D e f y / f y ^ 3) := by
    filter_upwards [hf.eventually (by norm_num), hnear] with y hyf hy0
    exact D_inv_sq e (hyf.differentiableAt (by norm_num)) hy0
  have hf1 := hf.differentiableAt (by norm_num)
  have hfe := (contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  rw [D_congr heq w,
    D_div (f := fun y => -2 * D e f y) (g := fun y => f y ^ 3) w
      (hfe.const_mul (-2)) (hf1.pow 3) (pow_ne_zero _ h0),
    D_const_mul w (-2) hfe, D_pow w 3 hf1]
  norm_num
  field_simp
  ring

lemma D_D_sin (e w : E) {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    D w (D e (fun y => Real.sin (f y))) x =
      Real.cos (f x) * D w (D e f) x - Real.sin (f x) * D w f x * D e f x := by
  have heq : D e (fun y => Real.sin (f y)) =ᶠ[𝓝 x]
      (fun y => Real.cos (f y) * D e f y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact D_sin e (hy.differentiableAt (by norm_num))
  have hf1 := hf.differentiableAt (by norm_num)
  have hfe := (contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  rw [D_congr heq w, D_mul (f := fun y => Real.cos (f y)) w hf1.cos hfe, D_cos w hf1]
  ring

lemma D_D_sq (e w : E) {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    D w (D e (fun y => f y ^ 2)) x = 2 * D w f x * D e f x + 2 * f x * D w (D e f) x := by
  simp only [pow_two]
  rw [D_D_mul e w hf hf]
  ring

lemma D_D_clm (e w x : E) (A : E →L[ℝ] ℝ) : D w (D e A) x = 0 := by
  have heq : D e A = fun _ => A e := funext (fun y => D_clm e y A)
  rw [heq, D_const]

lemma D_D_const (e w x : E) (c : ℝ) : D w (D e (fun _ => c)) x = 0 := by
  have h : D e (fun _ : E => c) = fun _ => 0 := funext (fun y => D_const e y c)
  rw [h, D_const]

lemma D_D_add (e w : E) {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    D w (D e (fun y => f y + g y)) x = D w (D e f) x + D w (D e g) x := by
  have heq : D e (fun y => f y + g y) =ᶠ[𝓝 x]
      (fun y => D e f y + D e g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact D_add e (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [D_congr heq w]
  exact D_add w ((contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num))
    ((contDiffAt_D hg (m := 1) (by norm_num) e).differentiableAt (by norm_num))

lemma D_D_sub (e w : E) {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    D w (D e (fun y => f y - g y)) x = D w (D e f) x - D w (D e g) x := by
  have heq : D e (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => D e f y - D e g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact D_sub e (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [D_congr heq w]
  exact D_sub w ((contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num))
    ((contDiffAt_D hg (m := 1) (by norm_num) e).differentiableAt (by norm_num))

lemma D_D_const_mul (e w : E) {f : E → ℝ} {x : E} (c : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    D w (D e (fun y => c * f y)) x = c * D w (D e f) x := by
  rw [D_D_mul e w (contDiffAt_const (c := c)) hf]
  simp [D_const, D_D_const]

lemma D_inv_inv (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0) :
    D e (fun y => 1 / f y) x = - D e f x / f x ^ 2 := by
  simpa only [one_div] using D_inv e hf h0

lemma D_D_inv (e w : E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (h0 : f x ≠ 0) :
    D w (D e (fun y => 1 / f y)) x =
      2 * D e f x * D w f x / f x ^ 3 - D w (D e f) x / f x ^ 2 := by
  have heq : D e (fun y => 1 / f y) =ᶠ[𝓝 x]
      (fun y => (-1) * D e f y / f y ^ 2) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually_ne h0]
      with y hyf hy0
    simpa using D_inv_inv e (hyf.differentiableAt (by norm_num)) hy0
  have hf1 := hf.differentiableAt (by norm_num)
  have hfe := (contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  rw [D_congr heq w,
    D_div (f := fun y => (-1) * D e f y) (g := fun y => f y ^ 2) w
      (hfe.const_mul (-1)) (hf1.pow 2) (pow_ne_zero _ h0),
    D_const_mul w (-1) hfe, D_pow w 2 hf1]
  norm_num
  field_simp
  ring

lemma D_D_div (e w : E) {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (h0 : g x ≠ 0) :
    D w (D e (fun y => f y / g y)) x =
      D w (D e f) x / g x -
      (D e f x * D w g x + D w f x * D e g x + f x * D w (D e g) x) / g x ^ 2 +
      2 * f x * D e g x * D w g x / g x ^ 3 := by
  rw [show (fun y => f y / g y) = (fun y => f y * (1 / g y)) by
    funext y; simp [div_eq_mul_inv]]
  rw [D_D_mul (g := fun y => 1 / g y) e w hf ((contDiffAt_const (c := (1 : ℝ))).div hg h0),
    D_D_inv e w hg h0,
    D_inv_inv w (hg.differentiableAt (by norm_num)) h0,
    D_inv_inv e (hg.differentiableAt (by norm_num)) h0]
  field_simp
  ring

lemma D_sqrt (e : E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (h0 : 0 < f x) :
    D e (fun y => Real.sqrt (f y)) x = D e f x / (2 * Real.sqrt (f x)) := by
  unfold D
  change fderiv ℝ (Real.sqrt ∘ f) x e = _
  rw [((Real.hasDerivAt_sqrt h0.ne').comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  simp
  ring

lemma D_D_sqrt (e w : E) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (h0 : 0 < f x) :
    D w (D e (fun y => Real.sqrt (f y))) x =
      D w (D e f) x / (2 * Real.sqrt (f x)) -
      D e f x * D w f x / (4 * Real.sqrt (f x) ^ 3) := by
  have heq : D e (fun y => Real.sqrt (f y)) =ᶠ[𝓝 x]
      (fun y => D e f y / (2 * Real.sqrt (f y))) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually (eventually_gt_nhds h0)]
      with y hyf hy0
    exact D_sqrt e (hyf.differentiableAt (by norm_num)) hy0
  have hf1 := hf.differentiableAt (by norm_num)
  have hfe := (contDiffAt_D hf (m := 1) (by norm_num) e).differentiableAt (by norm_num)
  have hsq := hf1.sqrt h0.ne'
  have hs0 : Real.sqrt (f x) ≠ 0 := (Real.sqrt_pos.2 h0).ne'
  rw [D_congr heq w, D_div (f := D e f) (g := fun y => 2 * Real.sqrt (f y)) w
    hfe (hsq.const_mul 2) (mul_ne_zero (by norm_num) hs0),
    D_const_mul w 2 hsq, D_sqrt w hf1 h0]
  field_simp
  ring

end
end CKSCalculus

end

noncomputable section
namespace CKSRound
noncomputable section

namespace LapseJet

lemma gamma_round (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).gamma = j.roundGamma r s c := by
  funext a i k
  fin_cases a <;> fin_cases i <;> fin_cases k <;>
    simp [MetricJet.gamma, roundMetric, roundGamma, first, Fin.sum_univ_three]
  all_goals field_simp

lemma dInv_round (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).dInv = j.roundDInv r s c := by
  funext a i k
  fin_cases a <;> fin_cases i <;> fin_cases k <;>
    simp [MetricJet.dInv, roundMetric, roundDInv, first, Fin.sum_univ_three]
  all_goals field_simp

lemma ricci00_round (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).ricci 0 0 =
      -2 * j.ur / (r * j.u) + j.utt / (r ^ 2 * j.u ^ 3) -
      2 * j.ut ^ 2 / (r ^ 2 * j.u ^ 4) + c * j.ut / (r ^ 2 * s * j.u ^ 3) +
      j.upp / (r ^ 2 * s ^ 2 * j.u ^ 3) - 2 * j.up ^ 2 / (r ^ 2 * s ^ 2 * j.u ^ 4) := by
  unfold MetricJet.ricci
  simp only [gamma_round j hr hs hu, MetricJet.dGamma, dInv_round j hr hs hu]
  simp [roundGamma, roundDInv, roundMetric, first, second, Fin.sum_univ_three]
  field_simp
  ring

lemma ricci11_round (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).ricci 1 1 =
      1 - j.u ^ 2 - r * j.u * j.ur + j.utt / j.u - 2 * j.ut ^ 2 / j.u ^ 2 := by
  unfold MetricJet.ricci
  simp only [gamma_round j hr hs hu, MetricJet.dGamma, dInv_round j hr hs hu]
  simp [roundGamma, roundDInv, roundMetric, first, second, Fin.sum_univ_three]
  field_simp
  ring

lemma ricci22_round (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).ricci 2 2 =
      s ^ 2 * (1 - j.u ^ 2 - r * j.u * j.ur) + j.upp / j.u -
      2 * j.up ^ 2 / j.u ^ 2 + s * c * j.ut / j.u := by
  unfold MetricJet.ricci
  simp only [gamma_round j hr hs hu, MetricJet.dGamma, dInv_round j hr hs hu]
  simp [roundGamma, roundDInv, roundMetric, first, second, Fin.sum_univ_three]
  field_simp
  ring

theorem scalar_round (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).scalar =
      2 * (1 - j.u ^ 2) / r ^ 2 - 4 * j.u * j.ur / r -
      2 / r ^ 2 * (-j.utt / j.u + 2 * j.ut ^ 2 / j.u ^ 2 -
        c * j.ut / (s * j.u) - j.upp / (s ^ 2 * j.u) +
        2 * j.up ^ 2 / (s ^ 2 * j.u ^ 2)) := by
  unfold MetricJet.scalar
  simp only [Fin.sum_univ_three]
  change j.u ^ 2 * _ + 0 * _ + 0 * _ + (0 * _ + 1 / r ^ 2 * _ + 0 * _) +
    (0 * _ + 0 * _ + 1 / (r ^ 2 * s ^ 2) * _) = _
  simp only [zero_mul, add_zero, zero_add]
  rw [ricci00_round j hr hs hu, ricci11_round j hr hs hu, ricci22_round j hr hs hu]
  field_simp
  ring

end LapseJet

namespace RoundTensor

lemma trace_round (k : RoundTensor) (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).trace (k.jet j r s c) = k.L + 2 * k.v / r := by
  simp [MetricJet.trace, LapseJet.roundMetric, jet, Fin.sum_univ_three]
  field_simp
  ring

lemma normSq_round (k : RoundTensor) (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).normSq (k.jet j r s c) =
      k.L ^ 2 + 2 * k.v ^ 2 / r ^ 2 + 2 * k.a ^ 2 / r ^ 4 +
        2 * k.b ^ 2 / (r ^ 4 * s ^ 2) := by
  simp [MetricJet.normSq, LapseJet.roundMetric, jet, Fin.sum_univ_three]
  field_simp
  ring

lemma energy_round (k : RoundTensor) (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).energy (k.jet j r s c) =
      (1 - j.u ^ 2) / r ^ 2 - 2 * j.u * j.ur / r -
      1 / r ^ 2 * (-j.utt / j.u + 2 * j.ut ^ 2 / j.u ^ 2 -
        c * j.ut / (s * j.u) - j.upp / (s ^ 2 * j.u) +
        2 * j.up ^ 2 / (s ^ 2 * j.u ^ 2)) +
      2 * k.L * k.v / r + k.v ^ 2 / r ^ 2 -
      k.a ^ 2 / r ^ 4 - k.b ^ 2 / (r ^ 4 * s ^ 2) := by
  unfold MetricJet.energy
  rw [LapseJet.scalar_round j hr hs hu, trace_round k j hr hs hu,
    normSq_round k j hr hs hu]
  field_simp
  ring

theorem normal_momentum_round (k : RoundTensor) (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    j.u * (j.roundMetric r s c).momentum (k.jet j r s c) 0 =
      2 * j.u / r * (k.L - k.vp) := by
  unfold MetricJet.momentum MetricJet.tensorDivergence MetricJet.dTrace
  simp only [LapseJet.gamma_round j hr hs hu, LapseJet.dInv_round j hr hs hu]
  simp [LapseJet.roundGamma, LapseJet.roundDInv, LapseJet.roundMetric,
    LapseJet.first, jet, Fin.sum_univ_three]
  field_simp
  ring

theorem theta_momentum_round (k : RoundTensor) (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).momentum (k.jet j r s c) 1 =
      (k.aθ + k.bp / s ^ 2 + 2 * c * k.a / s) / r ^ 2 - k.Lt +
      (k.L - k.v / r) * j.ut / j.u -
      (k.a * j.ut + k.b * j.up / s ^ 2) / (r ^ 2 * j.u) := by
  unfold MetricJet.momentum MetricJet.tensorDivergence MetricJet.dTrace
  simp only [LapseJet.gamma_round j hr hs hu, LapseJet.dInv_round j hr hs hu]
  simp [LapseJet.roundGamma, LapseJet.roundDInv, LapseJet.roundMetric,
    LapseJet.first, jet, Fin.sum_univ_three]
  field_simp
  ring

theorem phi_momentum_round (k : RoundTensor) (j : LapseJet) {r s c : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hu : j.u ≠ 0) :
    (j.roundMetric r s c).momentum (k.jet j r s c) 2 =
      (k.bt - k.ap + c * k.b / s) / r ^ 2 - k.Lp +
      (k.L - k.v / r) * j.up / j.u -
      (k.b * j.ut - k.a * j.up) / (r ^ 2 * j.u) := by
  unfold MetricJet.momentum MetricJet.tensorDivergence MetricJet.dTrace
  simp only [LapseJet.gamma_round j hr hs hu, LapseJet.dInv_round j hr hs hu]
  simp [LapseJet.roundGamma, LapseJet.roundDInv, LapseJet.roundMetric,
    LapseJet.first, jet, Fin.sum_univ_three]
  field_simp
  ring

end RoundTensor

namespace MassJet

lemma lapse_laplacian (f : MassJet) {r u v vp vpp s c : ℝ}
    (hr : r ≠ 0) (hu : u ≠ 0) (hs : s ≠ 0) :
    let j := f.lapse r u v vp vpp
    1 / r ^ 2 * (-j.utt / j.u + 2 * j.ut ^ 2 / j.u ^ 2 -
      c * j.ut / (s * j.u) - j.upp / (s ^ 2 * j.u) +
      2 * j.up ^ 2 / (s ^ 2 * j.u ^ 2)) =
    f.laplace s c / (r ^ 3 * u ^ 2) +
      3 * f.gradientSq s / (r ^ 4 * u ^ 4) := by
  dsimp [lapse, laplace, gradientSq]
  field_simp
  ring

theorem energy_mass_form (f : MassJet) (k : RoundTensor) {r u vpp s c : ℝ}
    (hr : r ≠ 0) (hu : u ≠ 0) (hs : s ≠ 0)
    (hmass : u ^ 2 = 1 + k.v ^ 2 - 2 * f.F / r) :
    let j := f.lapse r u k.v k.vp vpp
    (j.roundMetric r s c).energy (k.jet j r s c) =
      2 * k.v / r * (k.L - k.vp) + 2 * f.Fr / r ^ 2 -
      f.laplace s c / (r ^ 3 * u ^ 2) -
      3 * f.gradientSq s / (r ^ 4 * u ^ 4) -
      k.a ^ 2 / r ^ 4 - k.b ^ 2 / (r ^ 4 * s ^ 2) := by
  dsimp only
  rw [RoundTensor.energy_round k _ hr hs hu, lapse_laplacian f hr hu hs]
  dsimp only [lapse]
  have hrad : (1 - u ^ 2) / r ^ 2 -
      2 * u * ((k.v * k.vp - f.Fr / r + f.F / r ^ 2) / u) / r +
      2 * k.L * k.v / r + k.v ^ 2 / r ^ 2 =
      2 * k.v / r * (k.L - k.vp) + 2 * f.Fr / r ^ 2 := by
    rw [hmass]
    field_simp
    ring
  linear_combination hrad

end MassJet

end
end CKSRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound
open scoped Topology ContDiff

lemma D_D_coord (a b c : Idx) (x : Point) :
    D (basis a) (D (basis b) (coord c)) x = 0 := D_D_clm _ _ _ _

lemma lapse_first (u : Point → ℝ) (x : Point) (a : Idx) :
    (lapseJet u x).first a = D (basis a) u x := by
  fin_cases a <;> simp [lapseJet, LapseJet.first]

lemma lapse_second (u : Point → ℝ) (x : Point) (hu : ContDiffAt ℝ 2 u x)
    (a b : Idx) : (lapseJet u x).second a b = D (basis a) (D (basis b) u) x := by
  fin_cases a <;> fin_cases b <;> simp [lapseJet, LapseJet.second]
  all_goals exact D_comm hu _ _

lemma metric_inv (u : Point → ℝ) (x : Point)
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) (hu : u x ≠ 0) :
    (metric u x)⁻¹ =
    !![u x ^ 2, 0, 0; 0, 1 / x 0 ^ 2, 0; 0, 0, 1 / (x 0 ^ 2 * Real.sin (x 1) ^ 2)] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [metric, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp [hu, hr, hs]

lemma D_r_sq (a : Idx) (x : Point) :
    D (basis a) (fun y => y 0 ^ 2) x = (![2 * x 0, 0, 0] : Point) a := by
  change D (basis a) (fun y => coord 0 y ^ 2) x = _
  rw [D_pow _ 2 (coord 0).differentiableAt, D_coord]
  fin_cases a <;> simp [coord]

lemma D_D_r_sq (a b : Idx) (x : Point) :
    D (basis a) (D (basis b) (fun y => y 0 ^ 2)) x =
    (!![2, 0, 0; 0, 0, 0; 0, 0, 0] : Mat) a b := by
  change D (basis a) (D (basis b) (fun y => coord 0 y ^ 2)) x = _
  rw [D_D_sq _ _ (coord 0).contDiff.contDiffAt, D_D_coord, D_coord, D_coord]
  fin_cases a <;> fin_cases b <;> simp

lemma D_sin_sq (a : Idx) (x : Point) :
    D (basis a) (fun y => Real.sin (y 1) ^ 2) x =
      (![0, 2 * Real.sin (x 1) * Real.cos (x 1), 0] : Point) a := by
  change D (basis a) (fun y => Real.sin (coord 1 y) ^ 2) x = _
  rw [D_pow _ 2 (coord 1).differentiableAt.sin, D_sin _ (coord 1).differentiableAt, D_coord]
  fin_cases a <;> simp [coord]

lemma D_D_sin_sq (a b : Idx) (x : Point) :
    D (basis a) (D (basis b) (fun y => Real.sin (y 1) ^ 2)) x =
      (!![0, 0, 0; 0, 2 * (Real.cos (x 1) ^ 2 - Real.sin (x 1) ^ 2), 0;
        0, 0, 0] : Mat) a b := by
  change D (basis a) (D (basis b) (fun y => Real.sin (coord 1 y) ^ 2)) x = _
  rw [D_D_sq _ _ (coord 1).contDiff.sin.contDiffAt,
    D_D_sin _ _ (coord 1).contDiff.contDiffAt, D_D_coord,
    D_sin _ (coord 1).differentiableAt, D_sin _ (coord 1).differentiableAt,
    D_coord, D_coord]
  fin_cases a <;> fin_cases b <;> simp [coord]
  ring

lemma D_r_sin_sq (a : Idx) (x : Point) :
    D (basis a) (fun y => y 0 ^ 2 * Real.sin (y 1) ^ 2) x =
      (![2 * x 0 * Real.sin (x 1) ^ 2,
        2 * x 0 ^ 2 * Real.sin (x 1) * Real.cos (x 1), 0] : Point) a := by
  rw [D_mul _ (f := fun y : Point => y 0 ^ 2) (g := fun y => Real.sin (y 1) ^ 2)
    (by fun_prop) (by fun_prop), D_r_sq, D_sin_sq]
  fin_cases a <;> simp <;> ring

lemma D_D_r_sin_sq (a b : Idx) (x : Point) :
    D (basis a) (D (basis b) (fun y => y 0 ^ 2 * Real.sin (y 1) ^ 2)) x =
      (!![2 * Real.sin (x 1) ^ 2, 4 * x 0 * Real.sin (x 1) * Real.cos (x 1), 0;
      4 * x 0 * Real.sin (x 1) * Real.cos (x 1),
        2 * x 0 ^ 2 * (Real.cos (x 1) ^ 2 - Real.sin (x 1) ^ 2), 0;
      0, 0, 0] : Mat) a b := by
  rw [D_D_mul _ _ (f := fun y : Point => y 0 ^ 2) (g := fun y => Real.sin (y 1) ^ 2)
    (by fun_prop) (by fun_prop), D_D_r_sq, D_D_sin_sq,
    D_r_sq, D_r_sq, D_sin_sq, D_sin_sq]
  fin_cases a <;> fin_cases b <;> simp <;> ring

theorem metricJet_eq_round (u : Point → ℝ) (x : Point)
    (hC : ContDiffAt ℝ 2 u x) (hu : u x ≠ 0)
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) :
    metricJet u x = (lapseJet u x).roundMetric (x 0) (Real.sin (x 1)) (Real.cos (x 1)) := by
  have hdiff := hC.differentiableAt (by norm_num)
  apply MetricJet.ext_data
  · exact metric_inv u x hr hs hu
  · funext a i j
    fin_cases i <;> fin_cases j <;>
      simp [metricJet, metric, LapseJet.roundMetric, D_const]
    · rw [lapse_first]
      simpa [lapseJet] using D_inv_sq (basis a) hdiff hu
    · exact D_r_sq a x
    · exact D_r_sin_sq a x
  · funext a b i j
    fin_cases i <;> fin_cases j <;>
      simp [metricJet, metric, LapseJet.roundMetric, D_D_const]
    · rw [lapse_first, lapse_first, lapse_second u x hC]
      have h := D_D_inv_sq (basis b) (basis a) hC hu
      simp only [one_div] at h
      dsimp only [lapseJet]
      rw [h]
      ring
    · rw [D_D_r_sq]
      fin_cases a <;> fin_cases b <;> rfl
    · rw [D_D_r_sin_sq]
      fin_cases a <;> fin_cases b <;> rfl

end
end CKSRealizedRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound Filter
open scoped Topology ContDiff

lemma contDiffAt_radial {v : ℝ → ℝ} {x : Point} {n : ℕ∞ω}
    (hv : ContDiffAt ℝ n v (x 0)) : ContDiffAt ℝ n (radial v) x :=
  hv.comp x (coord 0).contDiff.contDiffAt

lemma D_radial (a : Idx) {v : ℝ → ℝ} {x : Point}
    (hv : DifferentiableAt ℝ v (x 0)) :
    D (basis a) (radial v) x = (![deriv v (x 0), 0, 0] : Point) a := by
  change D (basis a) (fun y => v (coord 0 y)) x = _
  rw [D_comp_real (basis a) (g := coord 0) hv (coord 0).differentiableAt, D_coord]
  fin_cases a <;> simp [coord]

lemma D_D_radial (a b : Idx) {v : ℝ → ℝ} {x : Point}
    (hv : ContDiffAt ℝ 2 v (x 0)) :
    D (basis a) (D (basis b) (radial v)) x =
      (!![deriv (deriv v) (x 0), 0, 0; 0, 0, 0; 0, 0, 0] : Mat) a b := by
  have hv' : DifferentiableAt ℝ (deriv v) (x 0) :=
    (contDiffAt_D hv (m := 1) (by norm_num) (1 : ℝ)).differentiableAt (by norm_num)
  have heq : D (basis b) (radial v) =ᶠ[𝓝 x]
      (fun y => (![deriv v (y 0), 0, 0] : Point) b) := by
    filter_upwards [(coord 0).continuous.continuousAt.eventually (hv.eventually (by norm_num))]
      with y hy
    exact D_radial b (hy.differentiableAt (by norm_num))
  rw [D_congr heq (basis a)]
  fin_cases b
  · change D (basis a) (radial (deriv v)) x = _
    rw [D_radial a hv']
    fin_cases a <;> rfl
  · fin_cases a <;> simpa using D_const (basis _) x (0 : ℝ)
  · fin_cases a <;> simpa using D_const (basis _) x (0 : ℝ)

lemma contDiffAt_radicand {F : Point → ℝ} {v : ℝ → ℝ} {x : Point} {n : ℕ∞ω}
    (hF : ContDiffAt ℝ n F x) (hv : ContDiffAt ℝ n v (x 0)) (hr : x 0 ≠ 0) :
    ContDiffAt ℝ n (radicand F v) x := by
  exact ((contDiffAt_const (c := (1 : ℝ))).add ((contDiffAt_radial hv).pow 2)).sub
    (((contDiffAt_const (c := (2 : ℝ))).mul hF).div (coord 0).contDiff.contDiffAt hr)

lemma contDiffAt_lapse {F : Point → ℝ} {v : ℝ → ℝ} {x : Point} {n : ℕ∞ω}
    (hF : ContDiffAt ℝ n F x) (hv : ContDiffAt ℝ n v (x 0)) (hr : x 0 ≠ 0)
    (hpos : 0 < radicand F v x) : ContDiffAt ℝ n (lapse F v) x :=
  (contDiffAt_radicand hF hv hr).sqrt hpos.ne'

lemma lapse_pos {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hpos : 0 < radicand F v x) : 0 < lapse F v x := Real.sqrt_pos.2 hpos

lemma lapse_sq {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hpos : 0 < radicand F v x) :
    lapse F v x ^ 2 = 1 + v (x 0) ^ 2 - 2 * F x / x 0 :=
  Real.sq_sqrt hpos.le

lemma D_radicand (a : Idx) {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hF : DifferentiableAt ℝ F x) (hv : DifferentiableAt ℝ v (x 0)) (hr : x 0 ≠ 0) :
    D (basis a) (radicand F v) x =
      2 * v (x 0) * (![deriv v (x 0), 0, 0] : Point) a -
      (2 * D (basis a) F x * x 0 - 2 * F x * (![1, 0, 0] : Point) a) / (x 0) ^ 2 := by
  have hrv : DifferentiableAt ℝ (radial v) x := hv.comp x (coord 0).differentiableAt
  change D (basis a) (fun y => 1 + radial v y ^ 2 - 2 * F y / coord 0 y) x = _
  rw [D_sub (basis a) (f := fun y => 1 + radial v y ^ 2) (g := fun y => 2 * F y / coord 0 y) ((differentiableAt_const 1).fun_add (hrv.pow 2))
    (diffAt_div (hF.const_mul 2) (coord 0).differentiableAt hr),
    D_add (basis a) (g := fun y => radial v y ^ 2) (differentiableAt_const 1) (hrv.pow 2), D_const,
    D_pow (basis a) 2 hrv, D_radial _ hv,
    D_div (basis a) (f := fun y => 2 * F y) (g := coord 0) (hF.const_mul 2) (coord 0).differentiableAt hr,
    D_const_mul (basis a) 2 hF, D_coord]
  fin_cases a <;> simp [coord, radial]

lemma D_D_radicand (a b : Idx) {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hF : ContDiffAt ℝ 2 F x) (hv : ContDiffAt ℝ 2 v (x 0)) (hr : x 0 ≠ 0) :
    D (basis a) (D (basis b) (radicand F v)) x =
      2 * (![deriv v (x 0), 0, 0] : Point) a * (![deriv v (x 0), 0, 0] : Point) b +
      2 * v (x 0) * (!![deriv (deriv v) (x 0), 0, 0; 0, 0, 0; 0, 0, 0] : Mat) a b -
      (2 * D (basis a) (D (basis b) F) x / x 0 -
        (2 * D (basis b) F x * (![1, 0, 0] : Point) a +
          2 * D (basis a) F x * (![1, 0, 0] : Point) b) / x 0 ^ 2 +
        4 * F x * (![1, 0, 0] : Point) a * (![1, 0, 0] : Point) b / x 0 ^ 3) := by
  have hrv := contDiffAt_radial hv
  have hv1 := hv.differentiableAt (by norm_num)
  change D (basis a) (D (basis b)
    (fun y => 1 + radial v y ^ 2 - 2 * F y / coord 0 y)) x = _
  rw [D_D_sub (basis b) (basis a) (f := fun y => 1 + radial v y ^ 2) (g := fun y => 2 * F y / coord 0 y) ((contDiffAt_const (c := (1 : ℝ))).add (hrv.pow 2))
    (((contDiffAt_const (c := (2 : ℝ))).mul hF).div (coord 0).contDiff.contDiffAt hr),
    D_D_add _ _ (contDiffAt_const (c := (1 : ℝ))) (hrv.pow 2), D_D_const,
    D_D_sq _ _ hrv, D_radial _ hv1, D_radial _ hv1, D_D_radial _ _ hv,
    D_D_div (basis b) (basis a) (f := fun y => 2 * F y) (g := coord 0) ((contDiffAt_const (c := (2 : ℝ))).mul hF) (coord 0).contDiff.contDiffAt hr,
    D_D_const_mul _ _ 2 hF,
    D_const_mul _ 2 (hF.differentiableAt (by norm_num)),
    D_const_mul _ 2 (hF.differentiableAt (by norm_num)),
    D_D_coord, D_coord, D_coord]
  fin_cases a <;> fin_cases b <;> simp [coord, radial]
  ring

lemma D_lapse (a : Idx) {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hF : ContDiffAt ℝ 2 F x) (hv : ContDiffAt ℝ 2 v (x 0)) (hr : x 0 ≠ 0)
    (hpos : 0 < radicand F v x) :
    D (basis a) (lapse F v) x = D (basis a) (radicand F v) x / (2 * lapse F v x) :=
  D_sqrt _ ((contDiffAt_radicand hF hv hr).differentiableAt (by norm_num)) hpos

lemma D_D_lapse (a b : Idx) {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hF : ContDiffAt ℝ 2 F x) (hv : ContDiffAt ℝ 2 v (x 0)) (hr : x 0 ≠ 0)
    (hpos : 0 < radicand F v x) :
    D (basis a) (D (basis b) (lapse F v)) x =
      D (basis a) (D (basis b) (radicand F v)) x / (2 * lapse F v x) -
      D (basis b) (radicand F v) x * D (basis a) (radicand F v) x /
        (4 * lapse F v x ^ 3) :=
  D_D_sqrt _ _ (contDiffAt_radicand hF hv hr) hpos

theorem lapseJet_eq_mass {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hF : ContDiffAt ℝ 2 F x) (hv : ContDiffAt ℝ 2 v (x 0)) (hr : x 0 ≠ 0)
    (hpos : 0 < radicand F v x) :
    lapseJet (lapse F v) x =
      (massJet F x).lapse (x 0) (lapse F v x) (v (x 0)) (deriv v (x 0))
        (deriv (deriv v) (x 0)) := by
  have hu : lapse F v x ≠ 0 := (lapse_pos hpos).ne'
  have hF1 := hF.differentiableAt (by norm_num)
  have hv1 := hv.differentiableAt (by norm_num)
  unfold lapseJet MassJet.lapse
  congr 1
  all_goals first | rw [D_D_lapse _ _ hF hv hr hpos] | rw [D_lapse _ hF hv hr hpos]
  all_goals simp [D_radicand _ hF1 hv1 hr, D_D_radicand _ _ hF hv hr, massJet]
  all_goals field_simp
  all_goals ring

theorem constructed_metricJet {F : Point → ℝ} {v : ℝ → ℝ} {x : Point}
    (hF : ContDiffAt ℝ 2 F x) (hv : ContDiffAt ℝ 2 v (x 0)) (hr : x 0 ≠ 0)
    (hs : Real.sin (x 1) ≠ 0) (hpos : 0 < radicand F v x) :
    metricJet (lapse F v) x =
      ((massJet F x).lapse (x 0) (lapse F v x) (v (x 0)) (deriv v (x 0))
        (deriv (deriv v) (x 0))).roundMetric (x 0) (Real.sin (x 1)) (Real.cos (x 1)) := by
  rw [metricJet_eq_round _ _ (contDiffAt_lapse hF hv hr hpos) (lapse_pos hpos).ne' hr hs,
    lapseJet_eq_mass hF hv hr hpos]

end
end CKSRealizedRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound
open scoped Topology ContDiff

lemma D_normal_tensor (d : Idx) {u L : Point → ℝ} {x : Point}
    (hu : DifferentiableAt ℝ u x) (hL : DifferentiableAt ℝ L x) (hu0 : u x ≠ 0) :
    D (basis d) (fun y => L y / u y ^ 2) x =
      D (basis d) L x / u x ^ 2 - 2 * L x * D (basis d) u x / u x ^ 3 := by
  rw [D_div (basis d) (g := fun y => u y ^ 2) hL (hu.pow 2) (pow_ne_zero _ hu0),
    D_pow (basis d) 2 hu]
  norm_num
  field_simp

lemma D_radial_times_r (d : Idx) {v : ℝ → ℝ} {x : Point}
    (hv : DifferentiableAt ℝ v (x 0)) :
    D (basis d) (fun y => radial v y * y 0) x =
      (![deriv v (x 0) * x 0 + v (x 0), 0, 0] : Point) d := by
  change D (basis d) (fun y => radial v y * coord 0 y) x = _
  rw [D_mul (basis d) (f := radial v) (g := coord 0)
    (hv.comp x (coord 0).differentiableAt) (coord 0).differentiableAt,
    D_coord, D_radial d hv]
  fin_cases d <;> simp [radial, coord]
  ring

lemma D_tangential_tensor11 (d : Idx) {v : ℝ → ℝ} {a : Point → ℝ} {x : Point}
    (hv : DifferentiableAt ℝ v (x 0)) (ha : DifferentiableAt ℝ a x) :
    D (basis d) (fun y => radial v y * y 0 + a y) x =
      (![deriv v (x 0) * x 0 + v (x 0) + D (basis 0) a x,
        D (basis 1) a x, D (basis 2) a x] : Point) d := by
  rw [D_add (basis d) (f := fun y => radial v y * y 0)
    ((hv.comp x (coord 0).differentiableAt).fun_mul (coord 0).differentiableAt) ha,
    D_radial_times_r d hv]
  fin_cases d <;> simp

lemma D_tangential_tensor22 (d : Idx) {v : ℝ → ℝ} {a : Point → ℝ} {x : Point}
    (hv : DifferentiableAt ℝ v (x 0)) (ha : DifferentiableAt ℝ a x) :
    D (basis d) (fun y => (radial v y * y 0 - a y) * Real.sin (y 1) ^ 2) x =
      (![(deriv v (x 0) * x 0 + v (x 0) - D (basis 0) a x) * Real.sin (x 1) ^ 2,
        -D (basis 1) a x * Real.sin (x 1) ^ 2 +
          2 * (v (x 0) * x 0 - a x) * Real.sin (x 1) * Real.cos (x 1),
        -D (basis 2) a x * Real.sin (x 1) ^ 2] : Point) d := by
  have hvR : DifferentiableAt ℝ (radial v) x := hv.comp x (coord 0).differentiableAt
  have hp : DifferentiableAt ℝ (fun y : Point => radial v y * y 0) x :=
    hvR.fun_mul (coord 0).differentiableAt
  rw [D_mul (basis d) (f := fun y => radial v y * y 0 - a y)
    (g := fun y => Real.sin (y 1) ^ 2) (hp.fun_sub ha) (by fun_prop),
    D_sub (basis d) hp ha, D_radial_times_r d hv, D_sin_sq]
  fin_cases d <;> simp [radial] <;> ring

theorem tensorJet_eq_round (u : Point → ℝ) (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v (x 0))
    (hL : DifferentiableAt ℝ L x) (ha : DifferentiableAt ℝ a x)
    (hu0 : u x ≠ 0) :
    tensorJet u v L a b x =
      (roundTensor v L a b x).jet (lapseJet u x) (x 0) (Real.sin (x 1)) (Real.cos (x 1)) := by
  change TensorJet.mk _ _ = TensorJet.mk _ _
  congr 1
  funext d i j
  fin_cases i <;> fin_cases j <;>
    simp [tensor, D_const]
  · rw [D_normal_tensor d hu hL hu0, lapse_first]
    fin_cases d <;> rfl
  · rw [D_tangential_tensor11 d hv ha]
    fin_cases d <;> rfl
  · fin_cases d <;> rfl
  · fin_cases d <;> rfl
  · rw [D_tangential_tensor22 d hv ha]
    fin_cases d <;> simp [roundTensor, neg_mul]

end
end CKSRealizedRound

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_InducedSphereCalculus
attribute [-simp] _root_.OAI.CKSSphericalChart.pair_add_left _root_.OAI.CKSSphericalChart.pair_add_right _root_.OAI.CKSSphericalChart.pair_neg_left _root_.OAI.CKSSphericalChart.pair_neg_right _root_.OAI.CKSSphericalChart.pair_smul_left _root_.OAI.CKSSphericalChart.pair_smul_right _root_.OAI.CKSSphericalChart.pair_zero_left _root_.OAI.CKSSphericalChart.pair_zero_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

attribute [local instance] CKSLorentz.two_atLeastTwo

@[simp] lemma e_apply (i j : Ix) : e i j = if j = i then 1 else 0 := by
  simp [e, eq_comm]

@[simp] lemma pd_const (k : Ix) (c : ℝ) (x : E) : pd k (fun _ => c) x = 0 := by
  simp [pd]

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_FullSphereHeat
attribute [-simp] _root_.OAI.CKSSphericalChart.pair_add_left _root_.OAI.CKSSphericalChart.pair_add_right _root_.OAI.CKSSphericalChart.pair_neg_left _root_.OAI.CKSSphericalChart.pair_neg_right _root_.OAI.CKSSphericalChart.pair_smul_left _root_.OAI.CKSSphericalChart.pair_smul_right _root_.OAI.CKSSphericalChart.pair_zero_left _root_.OAI.CKSSphericalChart.pair_zero_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

@[simp] lemma pd_const_add (m : ℝ) (F : E → ℝ) (k : Ix) (x : E) :
    pd k (fun y => m + F y) x = pd k F x := by
  simp only [pd, fderiv_const_add]

@[simp] lemma pd_const_add_fun (m : ℝ) (F : E → ℝ) (k : Ix) :
    pd k (fun y => m + F y) = pd k F := by
  funext x
  exact pd_const_add m F k x

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildVacuumRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSCalculus CKSRound CKSRealizedRound CKSAngularGeometry
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma radial_round_vacuum_oai {m : ℝ} {v : ℝ → ℝ} {x : PhysicalPoint}
    (hv : ContDiffAt ℝ ∞ v (x 0)) (hr : x 0 ≠ 0)
    (hs : Real.sin (x 1) ≠ 0) (hp : 0 < CKSRealizedRound.radicand (fun _ => m) v x) :
    let g := metricJet (CKSRealizedRound.lapse (fun _ => m) v) x
    let k := tensorJet (CKSRealizedRound.lapse (fun _ => m) v) v
      (radial (deriv v)) (fun _ => 0) (fun _ => 0) x
    g.energy k = 0 ∧ g.momentum k = 0 := by
  dsimp only
  have hu := contDiffAt_lapse (contDiffAt_const (c := m)) hv hr hp
  have hu0 := (CKSRealizedRound.lapse_pos hp).ne'
  have hvd : DifferentiableAt ℝ (deriv v) (x 0) :=
    (hv.derivWithin (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hL : DifferentiableAt ℝ (radial (deriv v)) x := hvd.comp x (coord 0).differentiableAt
  rw [constructed_metricJet (contDiffAt_const (c := m)) (hv.of_le (by change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞); exact WithTop.coe_le_coe.mpr le_top)) hr hs hp,
    tensorJet_eq_round _ _ _ _ _ _ (hu.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hv.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hL (differentiableAt_const 0) hu0,
    lapseJet_eq_mass (contDiffAt_const (c := m)) (hv.of_le (by change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞); exact WithTop.coe_le_coe.mpr le_top)) hr hp]
  let f := massJet (fun _ : PhysicalPoint => m) x
  let k := roundTensor v (radial (deriv v)) (fun _ => 0) (fun _ => 0) x
  have hf : f.Fr = 0 ∧ f.Ft = 0 ∧ f.Fp = 0 ∧ f.Ftt = 0 ∧ f.Fpp = 0 := by
    simp [f,massJet,D_const,D_D_const]
  have hmass : (CKSRealizedRound.lapse (fun _ => m) v x)^2 =
      1+k.v^2-2*f.F/x 0 := CKSRealizedRound.lapse_sq hp
  let j := f.lapse (x 0) (CKSRealizedRound.lapse (fun _ => m) v x) k.v k.vp (deriv (deriv v) (x 0))
  change (j.roundMetric (x 0) (Real.sin (x 1)) (Real.cos (x 1))).energy
    (k.jet j (x 0) (Real.sin (x 1)) (Real.cos (x 1))) = 0 ∧
    (j.roundMetric (x 0) (Real.sin (x 1)) (Real.cos (x 1))).momentum
    (k.jet j (x 0) (Real.sin (x 1)) (Real.cos (x 1))) = 0
  constructor
  · rw [MassJet.energy_mass_form f k (c := Real.cos (x 1)) (vpp := deriv (deriv v) (x 0)) hr hu0 hs hmass]
    simp [k,roundTensor,radial,f,massJet,MassJet.laplace,MassJet.gradientSq,D_const,D_D_const]
  · funext i
    fin_cases i
    all_goals dsimp only [Pi.zero_apply]
    · have h := RoundTensor.normal_momentum_round k
        j (c := Real.cos (x 1)) hr hs hu0
      have hz : k.L-k.vp = 0 := by simp [k,roundTensor,radial]
      rw [hz,mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hu0
    · apply (RoundTensor.theta_momentum_round k j (c := Real.cos (x 1)) hr hs hu0).trans
      simp [k,roundTensor,radial,j,MassJet.lapse,f,massJet,D_const,D_radial 1 hvd]
    · apply (RoundTensor.phi_momentum_round k j (c := Real.cos (x 1)) hr hs hu0).trans
      simp [k,roundTensor,radial,j,MassJet.lapse,f,massJet,D_const,D_radial 2 hvd]
end CKSSchwarzschild

end

end OAI
end

theorem solution : type_of% @OAI.CKSSchwarzschild.radial_round_vacuum_oai := @OAI.CKSSchwarzschild.radial_round_vacuum_oai
