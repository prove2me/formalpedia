-- Prove2me | solution 1 for OAI.CKSSphericalChart.constructed_outer_DEC
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:23:08.191209+00:00
-- url     : https://prove2.me/submissions/5d2824cf-6929-4a21-950b-474e06482053

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSSphericalChart_outerMass_smooth
import Theorems.Thm_OAI_CKSSphericalChart_outerA_smooth
import Theorems.Thm_OAI_CKSSphericalChart_outerPhi_smooth
import Theorems.Thm_OAI_CKSSphericalChart_outerMass_heat
import Theorems.Thm_OAI_CKSSphericalChart_outer_divergence
import Theorems.Thm_OAI_CKSSphericalChart_outer_uniform_bounds

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_congr {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (e : E) : D e f x = D e g x := by
  unfold D
  rw [h.fderiv_eq]

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]
lemma D_add (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y + g y) x = D e f x + D e g x := by
  simp [D, fderiv_fun_add hf hg]
lemma D_sub (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y - g y) x = D e f x - D e g x := by
  simp [D, fderiv_fun_sub hf hg]

lemma D_const_mul (e : E) {f : E → ℝ} {x : E} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) : D e (fun y => c * f y) x = c * D e f x := by
  rw [D_mul e (differentiableAt_const c) hf, D_const]
  ring

lemma contDiffAt_D {f : E → ℝ} {x : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f x)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) (e : E) : ContDiffAt ℝ m (D e f) x :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

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
  exact hf.isSymmSndFDerivAt (by simp) w e

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

lemma D_comp_real (e : E) {f : ℝ → ℝ} {g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f (g y)) x = deriv f (g x) * D e g x := by
  unfold D
  change fderiv ℝ (f ∘ g) x e = _
  rw [(hf.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt).fderiv]
  simp

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


structure LapseJet where
  u : ℝ
  ur : ℝ
  ut : ℝ
  up : ℝ
  urr : ℝ
  urt : ℝ
  urp : ℝ
  utt : ℝ
  utp : ℝ
  upp : ℝ

namespace LapseJet

def first (j : LapseJet) : Idx → ℝ := ![j.ur, j.ut, j.up]
def second (j : LapseJet) : Mat :=
  !![j.urr, j.urt, j.urp; j.urt, j.utt, j.utp; j.urp, j.utp, j.upp]

def roundMetric (j : LapseJet) (r s c : ℝ) : MetricJet where
  inv := !![j.u ^ 2, 0, 0; 0, 1 / r ^ 2, 0; 0, 0, 1 / (r ^ 2 * s ^ 2)]
  d := fun a => !![-2 * j.first a / j.u ^ 3, 0, 0;
    0, (![2 * r, 0, 0] : Idx → ℝ) a, 0;
    0, 0, (![2 * r * s ^ 2, 2 * r ^ 2 * s * c, 0] : Idx → ℝ) a]
  dd := fun a b => !![6 * j.first a * j.first b / j.u ^ 4 -
      2 * j.second a b / j.u ^ 3, 0, 0;
    0, (!![2, 0, 0; 0, 0, 0; 0, 0, 0] : Mat) a b, 0;
    0, 0, (!![2 * s ^ 2, 4 * r * s * c, 0;
      4 * r * s * c, 2 * r ^ 2 * (c ^ 2 - s ^ 2), 0;
      0, 0, 0] : Mat) a b]

def roundGamma (j : LapseJet) (r s c : ℝ) : Idx → Mat := ![
  !![-j.ur / j.u, -j.ut / j.u, -j.up / j.u;
    -j.ut / j.u, -r * j.u ^ 2, 0;
    -j.up / j.u, 0, -r * j.u ^ 2 * s ^ 2],
  !![j.ut / (r ^ 2 * j.u ^ 3), 1 / r, 0;
    1 / r, 0, 0;
    0, 0, -s * c],
  !![j.up / (r ^ 2 * s ^ 2 * j.u ^ 3), 0, 1 / r;
    0, 0, c / s;
    1 / r, c / s, 0]]

def roundDInv (j : LapseJet) (r s c : ℝ) : Idx → Mat := fun a =>
  !![2 * j.u * j.first a, 0, 0;
    0, (![-2 / r ^ 3, 0, 0] : Idx → ℝ) a, 0;
    0, 0, (![-2 / (r ^ 3 * s ^ 2), -2 * c / (r ^ 2 * s ^ 3), 0] : Idx → ℝ) a]

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


structure RoundTensor where
  v : ℝ
  vp : ℝ
  L : ℝ
  Lr : ℝ
  Lt : ℝ
  Lp : ℝ
  a : ℝ
  ar : ℝ
  aθ : ℝ
  ap : ℝ
  b : ℝ
  br : ℝ
  bt : ℝ
  bp : ℝ

namespace RoundTensor

def jet (k : RoundTensor) (j : LapseJet) (r s c : ℝ) : TensorJet where
  val := !![k.L / j.u ^ 2, 0, 0;
    0, k.v * r + k.a, k.b;
    0, k.b, (k.v * r - k.a) * s ^ 2]
  d := fun i => !![
    (![k.Lr, k.Lt, k.Lp] : Idx → ℝ) i / j.u ^ 2 -
      2 * k.L * j.first i / j.u ^ 3, 0, 0;
    0, (![k.vp * r + k.v + k.ar, k.aθ, k.ap] : Idx → ℝ) i,
      (![k.br, k.bt, k.bp] : Idx → ℝ) i;
    0, (![k.br, k.bt, k.bp] : Idx → ℝ) i,
      (![(k.vp * r + k.v - k.ar) * s ^ 2,
        -k.aθ * s ^ 2 + 2 * (k.v * r - k.a) * s * c,
        -k.ap * s ^ 2] : Idx → ℝ) i]

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

def gradientSq (f : MassJet) (s : ℝ) : ℝ := f.Ft ^ 2 + f.Fp ^ 2 / s ^ 2

def lapse (f : MassJet) (r u v vp vpp : ℝ) : LapseJet where
  u := u
  ur := (v * vp - f.Fr / r + f.F / r ^ 2) / u
  ut := -f.Ft / (r * u)
  up := -f.Fp / (r * u)
  urr := (vp ^ 2 + v * vpp - f.Frr / r + 2 * f.Fr / r ^ 2 -
      2 * f.F / r ^ 3) / u - (v * vp - f.Fr / r + f.F / r ^ 2) ^ 2 / u ^ 3
  urt := (-f.Frt / r + f.Ft / r ^ 2) / u +
    (v * vp - f.Fr / r + f.F / r ^ 2) * f.Ft / (r * u ^ 3)
  urp := (-f.Frp / r + f.Fp / r ^ 2) / u +
    (v * vp - f.Fr / r + f.F / r ^ 2) * f.Fp / (r * u ^ 3)
  utt := -f.Ftt / (r * u) - f.Ft ^ 2 / (r ^ 2 * u ^ 3)
  utp := -f.Ftp / (r * u) - f.Ft * f.Fp / (r ^ 2 * u ^ 3)
  upp := -f.Fpp / (r * u) - f.Fp ^ 2 / (r ^ 2 * u ^ 3)

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

def correction (r v vp vpp β βp a at_ ap b bt bp ar br : ℝ) : RoundTensor where
  v := v
  vp := vp
  L := vp + β / r ^ 2
  Lr := vpp + βp / r ^ 2 - 2 * β / r ^ 3
  Lt := 0
  Lp := 0
  a := (r * (vp - v / r) / (1 + v ^ 2)) * a
  ar := ar
  aθ := (r * (vp - v / r) / (1 + v ^ 2)) * at_
  ap := (r * (vp - v / r) / (1 + v ^ 2)) * ap
  b := (r * (vp - v / r) / (1 + v ^ 2)) * b
  br := br
  bt := (r * (vp - v / r) / (1 + v ^ 2)) * bt
  bp := (r * (vp - v / r) / (1 + v ^ 2)) * bp

theorem gradient_cancellation_theta (f : MassJet)
    {r u v vp vpp s c β βp a at_ ap b bt bp ar br : ℝ}
    (hr : r ≠ 0) (hu : u ≠ 0) (hs : s ≠ 0)
    (hdiv : at_ + bp / s ^ 2 + 2 * c * a / s = f.Ft) :
    let j := f.lapse r u v vp vpp
    let k := correction r v vp vpp β βp a at_ ap b bt bp ar br
    (j.roundMetric r s c).momentum (k.jet j r s c) 1 =
      ((vp - v / r) / r * (1 / (1 + v ^ 2) - 1 / u ^ 2) -
       β / (r ^ 3 * u ^ 2)) * f.Ft +
      (k.a * f.Ft + k.b * f.Fp / s ^ 2) / (r ^ 3 * u ^ 2) := by
  dsimp only
  rw [RoundTensor.theta_momentum_round _ _ hr hs hu]
  dsimp [lapse, correction]
  have hA : 1 + v ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rw [← hdiv]
  field_simp
  ring

theorem gradient_cancellation_phi (f : MassJet)
    {r u v vp vpp s c β βp a at_ ap b bt bp ar br : ℝ}
    (hr : r ≠ 0) (hu : u ≠ 0) (hs : s ≠ 0)
    (hdiv : bt - ap + c * b / s = f.Fp) :
    let j := f.lapse r u v vp vpp
    let k := correction r v vp vpp β βp a at_ ap b bt bp ar br
    (j.roundMetric r s c).momentum (k.jet j r s c) 2 =
      ((vp - v / r) / r * (1 / (1 + v ^ 2) - 1 / u ^ 2) -
       β / (r ^ 3 * u ^ 2)) * f.Fp +
      (k.b * f.Ft - k.a * f.Fp) / (r ^ 3 * u ^ 2) := by
  dsimp only
  rw [RoundTensor.phi_momentum_round _ _ hr hs hu]
  dsimp [lapse, correction]
  have hA : 1 + v ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rw [← hdiv]
  field_simp
  ring

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

def lapseJet (u : Point → ℝ) (x : Point) : LapseJet where
  u := u x
  ur := D (basis 0) u x
  ut := D (basis 1) u x
  up := D (basis 2) u x
  urr := D (basis 0) (D (basis 0) u) x
  urt := D (basis 1) (D (basis 0) u) x
  urp := D (basis 2) (D (basis 0) u) x
  utt := D (basis 1) (D (basis 1) u) x
  utp := D (basis 2) (D (basis 1) u) x
  upp := D (basis 2) (D (basis 2) u) x

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

def roundTensor (v : ℝ → ℝ) (L a b : Point → ℝ) (x : Point) : RoundTensor where
  v := v (x 0)
  vp := deriv v (x 0)
  L := L x
  Lr := D (basis 0) L x
  Lt := D (basis 1) L x
  Lp := D (basis 2) L x
  a := a x
  ar := D (basis 0) a x
  aθ := D (basis 1) a x
  ap := D (basis 2) a x
  b := b x
  br := D (basis 0) b x
  bt := D (basis 1) b x
  bp := D (basis 2) b x

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

noncomputable section
namespace CKSBending
noncomputable section

def tfApply (a b : ℝ) (x : Vec2) : Vec2 :=
  WithLp.toLp 2 (a * x.fst + b * x.snd, b * x.fst - a * x.snd)

lemma tfApply_norm_sq (a b : ℝ) (x : Vec2) :
    ‖tfApply a b x‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖x‖ ^ 2 := by
  simp [tfApply, WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs]
  ring

lemma tfApply_norm_le {a b T : ℝ} (x : Vec2) (hT : 0 ≤ T)
    (hab : a ^ 2 + b ^ 2 ≤ T ^ 2) : ‖tfApply a b x‖ ≤ T * ‖x‖ := by
  have h := mul_le_mul_of_nonneg_right hab (sq_nonneg ‖x‖)
  rw [← tfApply_norm_sq] at h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (norm_nonneg _))).1
  simpa only [mul_pow] using h

def Q (r u β : ℝ) : ℝ := 2 * u * β / r ^ 3

def C (r u v d β ζ Δ a b : ℝ) (grad : Vec2) : ℝ :=
  2 * v * β / r ^ 3 + 2 / (r ^ 3 * Real.sqrt r) +
  Δ / r ^ 3 * (ζ / A v - 1 / u ^ 2) -
  3 * ‖grad‖ ^ 2 / (r ^ 4 * u ^ 4) -
  d ^ 2 * (a ^ 2 + b ^ 2) / (r ^ 2 * A v ^ 2)

def Z (r u v d β a b : ℝ) (grad : Vec2) : Vec2 :=
  (d / r ^ 2 * (1 / A v - 1 / u ^ 2)) • grad -
  (β / (r ^ 4 * u ^ 2)) • grad +
  (d / (r ^ 3 * A v * u ^ 2)) • tfApply a b grad

def energyError (M D V T : ℝ) : ℝ :=
  (1 + 4 * M) * D + 12 * D ^ 2 + V ^ 2 * T ^ 2 + 2 * (1 + 2 * M)

def momentumError (M D V T : ℝ) : ℝ := 4 * M * V * D + 2 * D + 2 * V * T * D

lemma A_one_le (v : ℝ) : 1 ≤ A v := by unfold A; nlinarith [sq_nonneg v]
lemma A_pos (v : ℝ) : 0 < A v := lt_of_lt_of_le zero_lt_one (A_one_le v)

lemma lapse_comparison {r u v F M : ℝ} (hr : 0 < r)
    (hm : |F| ≤ M) (hR : 4 * M ≤ r)
    (hu : u ^ 2 = A v - 2 * F / r) :
    A v / 2 ≤ u ^ 2 ∧ u ^ 2 ≤ 3 * A v / 2 := by
  have hA := A_one_le v
  have hab := abs_le.mp hm
  have hfupper : 2 * F / r ≤ 1 / 2 := by
    apply (div_le_iff₀ hr).2
    linarith
  have hflower : -(1 / 2) ≤ 2 * F / r := by
    apply (le_div_iff₀ hr).2
    linarith
  constructor <;> linarith

lemma reciprocal_difference {r u v F : ℝ} (hr : r ≠ 0) (hu : u ≠ 0)
    (hmass : u ^ 2 = A v - 2 * F / r) :
    1 / A v - 1 / u ^ 2 = -2 * F / (r * A v * u ^ 2) := by
  have hA : A v ≠ 0 := (A_pos v).ne'
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero hr hA) (pow_ne_zero 2 hu))).2
  field_simp at hmass ⊢
  nlinarith [hmass]

lemma inv_u_sq_le {u v : ℝ} (hu : 0 < u) (hl : A v / 2 ≤ u ^ 2) :
    1 / u ^ 2 ≤ 2 / A v := by
  apply (div_le_div_iff₀ (sq_pos_of_pos hu) (A_pos v)).2
  linarith

lemma abs_reciprocal_difference {r u v F M : ℝ} (hr : 0 < r)
    (hu : 0 < u) (hm : |F| ≤ M) (hl : A v / 2 ≤ u ^ 2)
    (hmass : u ^ 2 = A v - 2 * F / r) :
    |1 / A v - 1 / u ^ 2| ≤ 4 * M / (r * A v ^ 2) := by
  rw [reciprocal_difference hr.ne' hu.ne' hmass]
  have hi := inv_u_sq_le hu hl
  have hM : 0 ≤ M := (abs_nonneg F).trans hm
  have hA := A_pos v
  rw [abs_div, abs_mul, abs_of_neg (show (-2 : ℝ) < 0 by norm_num)]
  rw [abs_of_pos (by positivity : 0 < r * A v * u ^ 2)]
  simp only [neg_neg]
  calc
    2 * |F| / (r * A v * u ^ 2) ≤ 2 * M / (r * A v * u ^ 2) := by gcongr
    _ = (2 * M / (r * A v)) * (1 / u ^ 2) := by ring
    _ ≤ (2 * M / (r * A v)) * (2 / A v) := by gcongr
    _ = 4 * M / (r * A v ^ 2) := by ring

lemma inv_A_le_one (v : ℝ) : 1 / A v ≤ 1 := by
  apply (div_le_iff₀ (A_pos v)).2
  simpa using A_one_le v

lemma inv_u_sq_le_two {u v : ℝ} (hu : 0 < u) (hl : A v / 2 ≤ u ^ 2) :
    1 / u ^ 2 ≤ 2 := by
  have hi := inv_u_sq_le hu hl
  have hA := inv_A_le_one v
  linear_combination hi + 2 * hA

lemma beta_buffer {r u v F M β : ℝ}
    (hr : 1 ≤ r) (hu : 0 < u) (hm : |F| ≤ M)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβv : β ≠ 0 → v = r)
    (hmass : u ^ 2 = A v - 2 * F / r) :
    |2 * β * (v - u) / r ^ 3| ≤ 2 * (1 + 2 * M) / r ^ 4 := by
  have hr0 : 0 < r := by linarith
  have hM : 0 ≤ M := (abs_nonneg F).trans hm
  by_cases hβ : β = 0
  · subst β
    simp only [mul_zero, zero_mul, zero_div, abs_zero]
    positivity
  · have hv := hβv hβ
    subst v
    have hF : 2 * |F| / r ≤ 2 * M := by
      apply (div_le_iff₀ hr0).2
      nlinarith
    have hd : |r - u| ≤ (1 + 2 * M) / r := by
      apply (le_div_iff₀ hr0).2
      calc
        |r - u| * r ≤ |r - u| * (r + u) := by gcongr; linarith
        _ = |2 * F / r - 1| := by
          rw [← abs_of_pos (add_pos hr0 hu), ← abs_mul]
          congr 1
          dsimp [A] at hmass
          nlinarith
        _ ≤ |2 * F / r| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ 1 + 2 * M := by
          simp only [abs_div, abs_mul, abs_of_pos hr0, show |(2 : ℝ)| = 2 by norm_num, abs_one]
          linarith
    calc
      |2 * β * (r - u) / r ^ 3| = 2 * β * |r - u| / r ^ 3 := by
        rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hβ0,
          abs_of_pos (pow_pos hr0 3), show |(2 : ℝ)| = 2 by norm_num]
      _ ≤ 2 * 1 * ((1 + 2 * M) / r) / r ^ 3 := by gcongr
      _ = 2 * (1 + 2 * M) / r ^ 4 := by ring

lemma heat_switch_error {r v ζ : ℝ} (hr : 0 < r)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hζv : ζ ≠ 1 → v = r) :
    |(ζ - 1) / A v| ≤ 1 / r ^ 2 := by
  by_cases hζ : ζ = 1
  · subst ζ
    simp only [sub_self, zero_div, abs_zero]
    positivity
  · have hv := hζv hζ
    subst v
    rw [abs_div, abs_of_pos (A_pos r)]
    have hn : |ζ - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc
      |ζ - 1| / A r ≤ 1 / A r := by gcongr; exact (A_pos r).le
      _ ≤ 1 / r ^ 2 := by
        apply one_div_le_one_div_of_le (sq_pos_of_pos hr)
        unfold A
        linarith

lemma full_laplacian_gap {r u v F M ζ : ℝ} (hr : 0 < r)
    (hu : 0 < u) (hm : |F| ≤ M) (hl : A v / 2 ≤ u ^ 2)
    (hmass : u ^ 2 = A v - 2 * F / r)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hζv : ζ ≠ 1 → v = r) :
    |ζ / A v - 1 / u ^ 2| ≤ 1 / r ^ 2 + 4 * M / r := by
  have hM : 0 ≤ M := (abs_nonneg F).trans hm
  have hA := A_one_le v
  have h1 := heat_switch_error hr hζ0 hζ1 hζv
  have h2 := abs_reciprocal_difference hr hu hm hl hmass
  calc
    |ζ / A v - 1 / u ^ 2| = |(ζ - 1) / A v + (1 / A v - 1 / u ^ 2)| := by congr 1; ring
    _ ≤ |(ζ - 1) / A v| + |1 / A v - 1 / u ^ 2| := abs_add_le _ _
    _ ≤ 1 / r ^ 2 + 4 * M / (r * A v ^ 2) := add_le_add h1 h2
    _ ≤ 1 / r ^ 2 + 4 * M / r := by
      gcongr
      nlinarith [sq_nonneg (A v - 1)]

lemma laplacian_term_bound {r u v F M D ζ Δ : ℝ} (hr : 1 ≤ r)
    (hu : 0 < u) (hm : |F| ≤ M) (hl : A v / 2 ≤ u ^ 2)
    (hmass : u ^ 2 = A v - 2 * F / r)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hζv : ζ ≠ 1 → v = r)
    (hΔ : |Δ| ≤ D) :
    |Δ / r ^ 3 * (ζ / A v - 1 / u ^ 2)| ≤ (1 + 4 * M) * D / r ^ 4 := by
  have hr0 : 0 < r := by linarith
  have hM : 0 ≤ M := (abs_nonneg F).trans hm
  have hD : 0 ≤ D := (abs_nonneg Δ).trans hΔ
  have hgap := full_laplacian_gap hr0 hu hm hl hmass hζ0 hζ1 hζv
  rw [abs_mul, abs_div, abs_of_pos (pow_pos hr0 3)]
  calc
    |Δ| / r ^ 3 * |ζ / A v - 1 / u ^ 2| ≤
        D / r ^ 3 * (1 / r ^ 2 + 4 * M / r) := by gcongr
    _ = D / r ^ 5 + 4 * M * D / r ^ 4 := by ring
    _ ≤ D / r ^ 4 + 4 * M * D / r ^ 4 := by
      gcongr
      nlinarith [pow_nonneg (by linarith : 0 ≤ r) 4]
    _ = (1 + 4 * M) * D / r ^ 4 := by ring

lemma gradient_term_bound {r u v D : ℝ} {grad : Vec2}
    (hr : 0 < r) (hu : 0 < u) (hl : A v / 2 ≤ u ^ 2)
    (hg : ‖grad‖ ≤ D) :
    3 * ‖grad‖ ^ 2 / (r ^ 4 * u ^ 4) ≤ 12 * D ^ 2 / r ^ 4 := by
  have hi := inv_u_sq_le_two hu hl
  have hD : 0 ≤ D := (norm_nonneg _).trans hg
  calc
    3 * ‖grad‖ ^ 2 / (r ^ 4 * u ^ 4) = (3 * ‖grad‖ ^ 2 / r ^ 4) * (1 / u ^ 2) ^ 2 := by ring
    _ ≤ (3 * D ^ 2 / r ^ 4) * 2 ^ 2 := by gcongr
    _ = 12 * D ^ 2 / r ^ 4 := by ring

lemma tensor_energy_bound {r v d a b V T : ℝ}
    (hr : 0 < r) (_hV : 0 ≤ V) (_hT : 0 ≤ T)
    (hd : |d| / A v ≤ V / r) (ht : a ^ 2 + b ^ 2 ≤ T ^ 2) :
    d ^ 2 * (a ^ 2 + b ^ 2) / (r ^ 2 * A v ^ 2) ≤ V ^ 2 * T ^ 2 / r ^ 4 := by
  have hA := A_pos v
  calc
    d ^ 2 * (a ^ 2 + b ^ 2) / (r ^ 2 * A v ^ 2) =
        (|d| / A v) ^ 2 * (a ^ 2 + b ^ 2) / r ^ 2 := by rw [div_pow, sq_abs]; ring
    _ ≤ (V / r) ^ 2 * T ^ 2 / r ^ 2 := by gcongr
    _ = V ^ 2 * T ^ 2 / r ^ 4 := by ring

theorem energy_lower_bound {r u v F d β ζ Δ a b M D V T : ℝ} {grad : Vec2}
    (hr : 1 ≤ r) (hu : 0 < u) (hm : |F| ≤ M) (hl : A v / 2 ≤ u ^ 2)
    (hmass : u ^ 2 = A v - 2 * F / r)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβv : β ≠ 0 → v = r)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hζv : ζ ≠ 1 → v = r)
    (hΔ : |Δ| ≤ D) (hg : ‖grad‖ ≤ D) (hV : 0 ≤ V) (hT : 0 ≤ T)
    (hd : |d| / A v ≤ V / r) (ht : a ^ 2 + b ^ 2 ≤ T ^ 2) :
    2 / (r ^ 3 * Real.sqrt r) - energyError M D V T / r ^ 4 ≤
      C r u v d β ζ Δ a b grad - Q r u β := by
  have hr0 : 0 < r := by linarith
  have hb := (abs_le.mp (beta_buffer hr hu hm hβ0 hβ1 hβv hmass)).1
  have hΔb := (abs_le.mp (laplacian_term_bound hr hu hm hl hmass hζ0 hζ1 hζv hΔ)).1
  have hg' := gradient_term_bound hr0 hu hl hg
  have ht' := tensor_energy_bound hr0 hV hT hd ht
  unfold C Q energyError
  linear_combination hb + hΔb + hg' + ht'

theorem momentum_upper_bound {r u v F d β a b M D V T : ℝ} {grad : Vec2}
    (hr : 0 < r) (hu : 0 < u) (hm : |F| ≤ M) (hl : A v / 2 ≤ u ^ 2)
    (hmass : u ^ 2 = A v - 2 * F / r)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hg : ‖grad‖ ≤ D) (hV : 0 ≤ V) (hT : 0 ≤ T)
    (hd : |d| / A v ≤ V / r) (ht : a ^ 2 + b ^ 2 ≤ T ^ 2) :
    ‖Z r u v d β a b grad‖ ≤ momentumError M D V T / r ^ 4 := by
  have hM : 0 ≤ M := (abs_nonneg F).trans hm
  have hD : 0 ≤ D := (norm_nonneg _).trans hg
  have hA := A_pos v
  have hAi := inv_A_le_one v
  have hui := inv_u_sq_le_two hu hl
  have hgap := abs_reciprocal_difference hr hu hm hl hmass
  have hTgrad : ‖tfApply a b grad‖ ≤ T * D :=
    (tfApply_norm_le grad hT ht).trans (mul_le_mul_of_nonneg_left hg hT)
  have h₁ : ‖(d / r ^ 2 * (1 / A v - 1 / u ^ 2)) • grad‖ ≤
      4 * M * V * D / r ^ 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (sq_pos_of_pos hr)]
    calc
      |d| / r ^ 2 * |1 / A v - 1 / u ^ 2| * ‖grad‖ ≤
          |d| / r ^ 2 * (4 * M / (r * A v ^ 2)) * D := by gcongr
      _ = 4 * M / r ^ 3 * (|d| / A v) * (1 / A v) * D := by ring
      _ ≤ 4 * M / r ^ 3 * (V / r) * 1 * D := by gcongr
      _ = 4 * M * V * D / r ^ 4 := by ring
  have h₂ : ‖(β / (r ^ 4 * u ^ 2)) • grad‖ ≤ 2 * D / r ^ 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ β / (r ^ 4 * u ^ 2))]
    calc
      β / (r ^ 4 * u ^ 2) * ‖grad‖ = β / r ^ 4 * (1 / u ^ 2) * ‖grad‖ := by ring
      _ ≤ 1 / r ^ 4 * 2 * D := by gcongr
      _ = 2 * D / r ^ 4 := by ring
  have h₃ : ‖(d / (r ^ 3 * A v * u ^ 2)) • tfApply a b grad‖ ≤
      2 * V * T * D / r ^ 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < r ^ 3 * A v * u ^ 2)]
    calc
      |d| / (r ^ 3 * A v * u ^ 2) * ‖tfApply a b grad‖ =
          (|d| / A v) * (1 / u ^ 2) * ‖tfApply a b grad‖ / r ^ 3 := by ring
      _ ≤ (V / r) * 2 * (T * D) / r ^ 3 := by gcongr
      _ = 2 * V * T * D / r ^ 4 := by ring
  calc
    ‖Z r u v d β a b grad‖ ≤
        ‖(d / r ^ 2 * (1 / A v - 1 / u ^ 2)) • grad‖ +
        ‖(β / (r ^ 4 * u ^ 2)) • grad‖ +
        ‖(d / (r ^ 3 * A v * u ^ 2)) • tfApply a b grad‖ := by
      unfold Z
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 4 * M * V * D / r ^ 4 + 2 * D / r ^ 4 + 2 * V * T * D / r ^ 4 :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = momentumError M D V T / r ^ 4 := by unfold momentumError; ring

theorem outer_DEC_of_source_data {r u v F d β ζ Δ a b M D V T : ℝ} {grad : Vec2}
    (hr : 1 ≤ r) (hu : 0 < u) (hm : |F| ≤ M)
    (hmass : u ^ 2 = A v - 2 * F / r) (hRmass : 4 * M ≤ r)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβv : β ≠ 0 → v = r)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hζv : ζ ≠ 1 → v = r)
    (hΔ : |Δ| ≤ D) (hg : ‖grad‖ ≤ D) (hV : 0 ≤ V) (hT : 0 ≤ T)
    (hd : |d| / A v ≤ V / r) (ht : a ^ 2 + b ^ 2 ≤ T ^ 2)
    (hRerror : (energyError M D V T + momentumError M D V T) ^ 2 ≤ r) :
    Real.sqrt ((Q r u β) ^ 2 + ‖Z r u v d β a b grad‖ ^ 2) ≤
      C r u v d β ζ Δ a b grad := by
  have hr0 : 0 < r := by linarith
  have hl := (lapse_comparison hr0 hm hRmass hmass).1
  have he := energy_lower_bound hr hu hm hl hmass hβ0 hβ1 hβv hζ0 hζ1 hζv hΔ hg hV hT hd ht
  have hz := momentum_upper_bound hr0 hu hm hl hmass hβ0 hβ1 hg hV hT hd ht
  have hM : 0 ≤ M := (abs_nonneg F).trans hm
  have hD : 0 ≤ D := (norm_nonneg _).trans hg
  have hE : 0 ≤ energyError M D V T := by unfold energyError; positivity
  have hP : 0 ≤ momentumError M D V T := by unfold momentumError; positivity
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hs2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hEs : energyError M D V T + momentumError M D V T ≤ Real.sqrt r := by nlinarith
  have hc : (energyError M D V T + momentumError M D V T) / r ^ 4 ≤
      1 / (r ^ 3 * Real.sqrt r) := by
    calc
      (energyError M D V T + momentumError M D V T) / r ^ 4 ≤ Real.sqrt r / r ^ 4 := by gcongr
      _ = 1 / (r ^ 3 * Real.sqrt r) := by field_simp; nlinarith [hs2]
  have hs : 0 ≤ 1 / (r ^ 3 * Real.sqrt r) := by positivity
  have hq : 0 ≤ Q r u β := by unfold Q; positivity
  have hcz : Q r u β + ‖Z r u v d β a b grad‖ ≤ C r u v d β ζ Δ a b grad := by
    linear_combination he + hz + hc + hs
  apply le_trans _ hcz
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [mul_nonneg hq (norm_nonneg (Z r u v d β a b grad))]

end
end CKSBending

end

noncomputable section
namespace CKSLocalBending
noncomputable section
open CKSRound CKSBending

def tangentialMomentum (j : LapseJet) (k : RoundTensor) (r s c : ℝ) : Vec2 :=
  WithLp.toLp 2 ((j.roundMetric r s c).momentum (k.jet j r s c) 1 / r,
    (j.roundMetric r s c).momentum (k.jet j r s c) 2 / (r * s))

lemma sphereGrad_sq (f : MassJet) (s : ℝ) :
    ‖sphereGrad f s‖ ^ 2 = f.gradientSq s := by
  simp [sphereGrad, MassJet.gradientSq, WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, div_pow]

lemma physical_momentumSq (j : LapseJet) (k : RoundTensor) (r s c : ℝ) :
    momentumSq (j.roundMetric r s c) (k.jet j r s c) =
    (j.u * (j.roundMetric r s c).momentum (k.jet j r s c) 0) ^ 2 +
      ‖tangentialMomentum j k r s c‖ ^ 2 := by
  let m := (j.roundMetric r s c).momentum (k.jet j r s c)
  change (∑ i, ∑ l, (!![j.u ^ 2, 0, 0; 0, 1 / r ^ 2, 0;
    0, 0, 1 / (r ^ 2 * s ^ 2)] : Mat) i l * m i * m l) =
    (j.u * m 0) ^ 2 + ‖WithLp.toLp 2 (m 1 / r, m 2 / (r * s))‖ ^ 2
  have hn : ‖WithLp.toLp 2 (m 1 / r, m 2 / (r * s))‖ ^ 2 =
      (m 1 / r) ^ 2 + (m 2 / (r * s)) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change |m 1 / r| ^ 2 + |m 2 / (r * s)| ^ 2 = _
    rw [sq_abs, sq_abs]
  rw [hn]
  simp [Fin.sum_univ_three]
  ring

lemma computed_energy_eq_residual (f : MassJet)
    {r u v vp vpp s c β βp ζ a at_ ap b bt bp ar br : ℝ}
    (hr : r ≠ 0) (hu : u ≠ 0) (hs : s ≠ 0)
    (hmass : u ^ 2 = A v - 2 * f.F / r)
    (hheat : f.Fr = ζ * f.laplace s c / (2 * r * A v) + 1 / (r * Real.sqrt r)) :
    let j := f.lapse r u v vp vpp
    let k := MassJet.correction r v vp vpp β βp a at_ ap b bt bp ar br
    (j.roundMetric r s c).energy (k.jet j r s c) =
      C r u v (vp - v / r) β ζ (f.laplace s c) a (b / s) (sphereGrad f s) := by
  dsimp only
  have h := MassJet.energy_mass_form f
    (MassJet.correction r v vp vpp β βp a at_ ap b bt bp ar br)
      (vpp := vpp) (c := c) hr hu hs hmass
  dsimp only [MassJet.correction] at h ⊢
  rw [h]
  rw [hheat]
  unfold C A
  rw [sphereGrad_sq]
  field_simp
  ring

lemma computed_tangential_eq_residual (f : MassJet)
    {r u v vp vpp s c β βp a at_ ap b bt bp ar br : ℝ}
    (hr : r ≠ 0) (hu : u ≠ 0) (hs : s ≠ 0)
    (hdivθ : at_ + bp / s ^ 2 + 2 * c * a / s = f.Ft)
    (hdivφ : bt - ap + c * b / s = f.Fp) :
    let j := f.lapse r u v vp vpp
    let k := MassJet.correction r v vp vpp β βp a at_ ap b bt bp ar br
    tangentialMomentum j k r s c =
      Z r u v (vp - v / r) β a (b / s) (sphereGrad f s) := by
  dsimp only [tangentialMomentum]
  rw [MassJet.gradient_cancellation_theta f hr hu hs hdivθ,
    MassJet.gradient_cancellation_phi f hr hu hs hdivφ]
  apply WithLp.ofLp_injective 2
  ext <;> simp [Z, sphereGrad, tfApply, MassJet.correction, A]
  all_goals field_simp

lemma computed_normal_eq_residual (f : MassJet)
    {r u v vp vpp s c β βp a at_ ap b bt bp ar br : ℝ}
    (hr : r ≠ 0) (hu : u ≠ 0) (hs : s ≠ 0) :
    let j := f.lapse r u v vp vpp
    let k := MassJet.correction r v vp vpp β βp a at_ ap b bt bp ar br
    j.u * (j.roundMetric r s c).momentum (k.jet j r s c) 0 = Q r u β := by
  dsimp only
  rw [RoundTensor.normal_momentum_round _ _ hr hs hu]
  simp [MassJet.correction, MassJet.lapse, Q]
  ring

theorem computed_outer_DEC (f : MassJet)
    {r u v vp vpp s c β βp ζ a at_ ap b bt bp ar br M D V T : ℝ}
    (hr : 1 ≤ r) (hu : 0 < u) (hs : s ≠ 0)
    (hmass : u ^ 2 = A v - 2 * f.F / r)
    (hheat : f.Fr = ζ * f.laplace s c / (2 * r * A v) + 1 / (r * Real.sqrt r))
    (hdivθ : at_ + bp / s ^ 2 + 2 * c * a / s = f.Ft)
    (hdivφ : bt - ap + c * b / s = f.Fp)
    (hm : |f.F| ≤ M) (hRmass : 4 * M ≤ r)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hβv : β ≠ 0 → v = r)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hζv : ζ ≠ 1 → v = r)
    (hΔ : |f.laplace s c| ≤ D) (hg : ‖sphereGrad f s‖ ≤ D)
    (hV : 0 ≤ V) (hT : 0 ≤ T)
    (hd : |vp - v / r| / A v ≤ V / r) (ht : a ^ 2 + (b / s) ^ 2 ≤ T ^ 2)
    (hRerror : (energyError M D V T + momentumError M D V T) ^ 2 ≤ r) :
    let j := f.lapse r u v vp vpp
    let k := MassJet.correction r v vp vpp β βp a at_ ap b bt bp ar br
    DEC (j.roundMetric r s c) (k.jet j r s c) := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith : 0 < r)
  dsimp only [DEC]
  rw [physical_momentumSq,
    computed_energy_eq_residual f hr0 hu.ne' hs hmass hheat,
    computed_normal_eq_residual f hr0 hu.ne' hs,
    computed_tangential_eq_residual f hr0 hu.ne' hs hdivθ hdivφ]
  exact outer_DEC_of_source_data hr hu hm hmass hRmass hβ0 hβ1 hβv hζ0 hζ1 hζv
    hΔ hg hV hT hd ht hRerror

end
end CKSLocalBending

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound CKSLocalBending CKSBending
open scoped Topology ContDiff

lemma diffAt_deriv {v : ℝ → ℝ} {r : ℝ} (hv : ContDiffAt ℝ 2 v r) :
    DifferentiableAt ℝ (deriv v) r := by
  exact (hv.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)

lemma diffAt_normalEntry {v β : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ 2 v r) (hβ : DifferentiableAt ℝ β r) (hr : r ≠ 0) :
    DifferentiableAt ℝ (normalEntry v β) r := by
  exact (diffAt_deriv hv).fun_add (diffAt_div hβ (differentiableAt_id.pow 2) (pow_ne_zero _ hr))

lemma deriv_normalEntry {v β : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ 2 v r) (hβ : DifferentiableAt ℝ β r) (hr : r ≠ 0) :
    deriv (normalEntry v β) r =
      deriv (deriv v) r + deriv β r / r ^ 2 - 2 * β r / r ^ 3 := by
  unfold normalEntry
  rw [deriv_fun_add (f := deriv v) (g := fun r => β r / r ^ 2) (diffAt_deriv hv)
    (diffAt_div hβ (differentiableAt_id.pow 2) (pow_ne_zero _ hr)),
    deriv_fun_div (c := β) (d := fun r => r ^ 2) hβ (differentiableAt_id.pow 2) (pow_ne_zero _ hr)]
  try simp only [deriv_fun_pow, differentiableAt_id, deriv_id'', mul_one]
  norm_num
  field_simp
  ring

lemma diffAt_correctionCoeff {v : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ 2 v r) (hr : r ≠ 0) :
    DifferentiableAt ℝ (correctionCoeff v) r := by
  have hv1 := hv.differentiableAt (by norm_num)
  apply diffAt_div
  · exact differentiableAt_id.fun_mul ((diffAt_deriv hv).fun_sub
      (diffAt_div hv1 differentiableAt_id hr))
  · exact (differentiableAt_const 1).fun_add (hv1.pow 2)
  · exact ne_of_gt (by positivity)

lemma D_correctedComponent (i : Idx) {v : ℝ → ℝ} {a : Point → ℝ} {x : Point}
    (hv : ContDiffAt ℝ 2 v (x 0)) (ha : DifferentiableAt ℝ a x) (hr : x 0 ≠ 0) :
    D (basis i) (correctedComponent v a) x =
      correctionCoeff v (x 0) * D (basis i) a x +
      a x * (![deriv (correctionCoeff v) (x 0), 0, 0] : Point) i := by
  change D (basis i) (fun y => radial (correctionCoeff v) y * a y) x = _
  rw [D_mul (basis i) (f := radial (correctionCoeff v))
    ((diffAt_correctionCoeff hv hr).comp x (coord 0).differentiableAt) ha,
    D_radial i (diffAt_correctionCoeff hv hr)]
  rfl

lemma diffAt_correctedComponent {v : ℝ → ℝ} {a : Point → ℝ} {x : Point}
    (hv : ContDiffAt ℝ 2 v (x 0)) (ha : DifferentiableAt ℝ a x) (hr : x 0 ≠ 0) :
    DifferentiableAt ℝ (correctedComponent v a) x :=
  ((diffAt_correctionCoeff hv hr).comp x (coord 0).differentiableAt).fun_mul ha

theorem roundTensor_correction {v β : ℝ → ℝ} {a b : Point → ℝ} {x : Point}
    (hv : ContDiffAt ℝ 2 v (x 0)) (hβ : DifferentiableAt ℝ β (x 0))
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (hr : x 0 ≠ 0) :
    roundTensor v (radial (normalEntry v β)) (correctedComponent v a)
        (correctedComponent v b) x =
      MassJet.correction (x 0) (v (x 0)) (deriv v (x 0))
        (deriv (deriv v) (x 0)) (β (x 0)) (deriv β (x 0))
        (a x) (D (basis 1) a x) (D (basis 2) a x)
        (b x) (D (basis 1) b x) (D (basis 2) b x)
        (D (basis 0) (correctedComponent v a) x)
        (D (basis 0) (correctedComponent v b) x) := by
  unfold roundTensor MassJet.correction
  rw [D_radial 0 (diffAt_normalEntry hv hβ hr),
    D_radial 1 (diffAt_normalEntry hv hβ hr), D_radial 2 (diffAt_normalEntry hv hβ hr),
    deriv_normalEntry hv hβ hr,
    D_correctedComponent 1 hv ha hr, D_correctedComponent 2 hv ha hr,
    D_correctedComponent 1 hv hb hr, D_correctedComponent 2 hv hb hr]
  simp [radial, normalEntry, correctedComponent, correctionCoeff]

theorem smooth_outer_DEC {F a b : Point → ℝ} {v β : ℝ → ℝ} {x : Point}
    {ζ M B V T : ℝ}
    (hF : ContDiffAt ℝ 2 F x) (hv : ContDiffAt ℝ 2 v (x 0))
    (hβ : DifferentiableAt ℝ β (x 0))
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hr : 1 ≤ x 0) (hs : Real.sin (x 1) ≠ 0)
    (hm : |F x| ≤ M) (hRmass : 4 * M ≤ x 0)
    (hheat : D (basis 0) F x =
      ζ * (massJet F x).laplace (Real.sin (x 1)) (Real.cos (x 1)) /
        (2 * x 0 * A (v (x 0))) + 1 / (x 0 * Real.sqrt (x 0)))
    (hdivθ : D (basis 1) a x + D (basis 2) b x / Real.sin (x 1) ^ 2 +
      2 * Real.cos (x 1) * a x / Real.sin (x 1) = D (basis 1) F x)
    (hdivφ : D (basis 1) b x - D (basis 2) a x +
      Real.cos (x 1) * b x / Real.sin (x 1) = D (basis 2) F x)
    (hβ0 : 0 ≤ β (x 0)) (hβ1 : β (x 0) ≤ 1)
    (hβv : β (x 0) ≠ 0 → v (x 0) = x 0)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hζv : ζ ≠ 1 → v (x 0) = x 0)
    (hΔ : |(massJet F x).laplace (Real.sin (x 1)) (Real.cos (x 1))| ≤ B)
    (hg : ‖sphereGrad (massJet F x) (Real.sin (x 1))‖ ≤ B)
    (hV : 0 ≤ V) (hT : 0 ≤ T)
    (hd : |deriv v (x 0) - v (x 0) / x 0| / A (v (x 0)) ≤ V / x 0)
    (ht : a x ^ 2 + (b x / Real.sin (x 1)) ^ 2 ≤ T ^ 2)
    (hRerror : (energyError M B V T + momentumError M B V T) ^ 2 ≤ x 0) :
    DEC (metricJet (lapse F v) x)
      (tensorJet (lapse F v) v (radial (normalEntry v β))
        (correctedComponent v a) (correctedComponent v b) x) := by
  have hrp : 0 < x 0 := by linarith
  have hradpos : 0 < radicand F v x := by
    have hFM : F x ≤ M := (le_abs_self _).trans hm
    have hFbound : 2 * F x / x 0 ≤ 1 / 2 := by
      apply (div_le_iff₀ hrp).2
      linarith
    dsimp [radicand, radial]
    nlinarith [sq_nonneg (v (x 0))]
  have hlapse := (contDiffAt_lapse hF hv hrp.ne' hradpos).differentiableAt (by norm_num)
  rw [constructed_metricJet hF hv hrp.ne' hs hradpos,
    tensorJet_eq_round (lapse F v) v (radial (normalEntry v β))
      (correctedComponent v a) (correctedComponent v b) x hlapse (hv.differentiableAt (by norm_num))
      ((diffAt_normalEntry hv hβ hrp.ne').comp x (coord 0).differentiableAt)
      (diffAt_correctedComponent hv ha hrp.ne') (lapse_pos hradpos).ne',
    lapseJet_eq_mass hF hv hrp.ne' hradpos,
    roundTensor_correction hv hβ ha hb hrp.ne']
  apply computed_outer_DEC (massJet F x) hr (lapse_pos hradpos) hs
    (by simpa [A, massJet] using lapse_sq hradpos) hheat hdivθ hdivφ hm hRmass
    hβ0 hβ1 hβv hζ0 hζ1 hζv hΔ hg hV hT hd ht hRerror

end
end CKSRealizedRound

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma phi_one {x : ℝ} (hx : x ≤ 6) : phi x = 1 := by
  simp [phi,Real.smoothTransition.zero_of_nonpos (show (x-6)/6 ≤ 0 by linarith)]
lemma phi_tail {x : ℝ} (hx : 12 ≤ x) : phi x = (x⁻¹)^3 := by
  simp [phi,Real.smoothTransition.one_of_one_le (show 1 ≤ (x-6)/6 by linarith)]
lemma phi_pos {x : ℝ} (hx : 0 < x) : 0 < phi x := by
  have h0 := Real.smoothTransition.nonneg ((x-6)/6)
  have h1 := Real.smoothTransition.le_one ((x-6)/6)
  have hp : 0 < (x⁻¹)^3 := pow_pos (inv_pos.mpr hx) _
  unfold phi
  by_cases he : Real.smoothTransition ((x-6)/6) = 0
  · simp [he]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr h1) (mul_pos (lt_of_le_of_ne h0 (Ne.symm he)) hp)
lemma phi_le_one {x : ℝ} (hx : 0 < x) : phi x ≤ 1 := by
  by_cases h6 : x ≤ 6
  · rw [phi_one h6]
  · have h1x : 1 ≤ x := by linarith
    have hi : x⁻¹ ≤ 1 := (inv_le_one₀ hx).mpr h1x
    have hp : (x⁻¹)^3 ≤ 1 := by simpa using pow_le_pow_left₀ (inv_nonneg.mpr hx.le) hi 3
    have h0 := Real.smoothTransition.nonneg ((x-6)/6)
    have hprod := mul_le_mul_of_nonneg_left hp h0
    unfold phi
    linarith

lemma phi_smooth : ContDiffOn ℝ ∞ phi (Ioi 0) := by
  unfold phi
  have hc : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition ((x-6)/6)) := by fun_prop
  exact (contDiffOn_const.sub hc.contDiffOn).add
    (hc.contDiffOn.mul ((contDiffOn_id.inv (fun x hx => ne_of_gt hx)).pow 3))
lemma xi_smooth : ContDiff ℝ ∞ xi := by unfold xi; fun_prop

lemma beta_smooth : ContDiff ℝ ∞ beta := by unfold beta; fun_prop

lemma xi_nonneg (x : ℝ) : 0 ≤ xi x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma xi_le_one (x : ℝ) : xi x ≤ 1 := by unfold xi; linarith [Real.smoothTransition.nonneg (x-1)]
lemma xi_one {x : ℝ} (hx : x ≤ 1) : xi x = 1 := by
  simp [xi,Real.smoothTransition.zero_of_nonpos (show x-1 ≤ 0 by linarith)]
lemma xi_zero {x : ℝ} (hx : 2 ≤ x) : xi x = 0 := by
  simp [xi,Real.smoothTransition.one_of_one_le (show 1 ≤ x-1 by linarith)]
lemma zeta_nonneg (x : ℝ) : 0 ≤ zeta x := Real.smoothTransition.nonneg _
lemma zeta_le_one (x : ℝ) : zeta x ≤ 1 := Real.smoothTransition.le_one _

lemma zeta_one {x : ℝ} (hx : 5 ≤ x) : zeta x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma beta_nonneg (x : ℝ) : 0 ≤ beta x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma beta_le_one (x : ℝ) : beta x ≤ 1 := by unfold beta; linarith [Real.smoothTransition.nonneg (2*x-7)]

lemma beta_zero {x : ℝ} (hx : 4 ≤ x) : beta x = 0 := by
  simp [beta,Real.smoothTransition.one_of_one_le (show 1 ≤ 2*x-7 by linarith)]

lemma bendingV_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (bendingV R) (Ioi 0) := by
  unfold bendingV
  have hc : ContDiffOn ℝ ∞ (fun r : ℝ => phi (r/R)) (Ioi 0) :=
    phi_smooth.comp (contDiffOn_id.div_const R) (fun r hr => div_pos hr hR)
  exact (contDiffOn_id.mul hc).mul
    ((xi_smooth.comp (contDiff_id.div_const (R^2))).contDiffOn)

lemma bendingBeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingBeta R) :=
  beta_smooth.comp (contDiff_id.div_const R)

lemma bendingV_nonneg {R r : ℝ} (hR : 0 < R) (hr : 0 < r) : 0 ≤ bendingV R r :=
  mul_nonneg (mul_nonneg hr.le (phi_pos (div_pos hr hR)).le) (xi_nonneg _)

lemma bendingV_initial {R r : ℝ} (hR : 12 ≤ R) (hr : r ≤ 6*R) : bendingV R r = r := by
  have hRp : 0 < R := by linarith
  have hp : r/R ≤ 6 := (div_le_iff₀ hRp).mpr hr
  have hx : r/R^2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr (by nlinarith)
  simp [bendingV,phi_one hp,xi_one hx]

lemma beta_support {R r : ℝ} (hR : 12 ≤ R) (hb : bendingBeta R r ≠ 0) : bendingV R r = r := by
  apply bendingV_initial hR
  have hRp : 0 < R := by linarith
  have hh : r/R < 4 := by
    by_contra h
    exact hb (beta_zero (le_of_not_gt h))
  have hx := (div_lt_iff₀ hRp).mp hh
  linarith
lemma zeta_support {R r : ℝ} (hR : 12 ≤ R) (hz : bendingZeta R r ≠ 1) : bendingV R r = r := by
  apply bendingV_initial hR
  have hRp : 0 < R := by linarith
  have hh : r/R < 5 := by
    by_contra h
    exact hz (zeta_one (le_of_not_gt h))
  have hx := (div_lt_iff₀ hRp).mp hh
  linarith

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma phi_deriv_continuous : ContinuousOn (deriv phi) (Ioi 0) :=
  (phi_smooth.deriv_of_isOpen isOpen_Ioi (m := ∞) (by simp)).continuousOn
lemma xi_deriv_continuous : Continuous (deriv xi) :=
  xi_smooth.continuous_deriv (by simp)

lemma phi_deriv_initial {x : ℝ} (hx : 0 < x) (h6 : x ≤ 6) : deriv phi x = 0 := by
  have hm : IsLocalMax phi x := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [phi_one h6]
    exact phi_le_one hy
  exact hm.deriv_eq_zero
lemma xi_deriv_initial {x : ℝ} (hx : x ≤ 1) : deriv xi x = 0 := by
  have hm : IsLocalMax xi x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [xi_one hx]
    exact xi_le_one y
  exact hm.deriv_eq_zero
lemma xi_deriv_tail {x : ℝ} (hx : 2 ≤ x) : deriv xi x = 0 := by
  have hm : IsLocalMin xi x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [xi_zero hx]
    exact xi_nonneg y
  exact hm.deriv_eq_zero

lemma phi_deriv_tail {x : ℝ} (hx : 12 ≤ x) : x * deriv phi x = -3 * phi x := by
  have hxp : 0 < x := by linarith
  let c : ℝ → ℝ := fun y => Real.smoothTransition ((y-6)/6)
  have hc : ContDiff ℝ ∞ c := by dsimp [c]; fun_prop
  have hc1 : c x = 1 := Real.smoothTransition.one_of_one_le (by linarith)
  have hcm : IsLocalMax c x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [hc1]
    exact Real.smoothTransition.le_one _
  have hcd : HasDerivAt c 0 x := by
    simpa only [hcm.deriv_eq_zero] using (hc.differentiable (by simp) x).hasDerivAt
  have hp := ((hasDerivAt_const x (1:ℝ)).sub hcd).add
    (hcd.mul ((hasDerivAt_inv hxp.ne').pow 3))
  have he : deriv phi x = ((0-0) + (0*(x⁻¹)^3 + c x * (3*(x⁻¹)^2*(-x⁻¹^2)))) := by
    convert! hp.deriv using 1
    simp [c]
  rw [he,hc1,phi_tail hx]
  field_simp
  ring

theorem phi_scaled_deriv_bound : ∃ C : ℝ, 3 ≤ C ∧ ∀ x : ℝ, 0 < x → |x * deriv phi x| ≤ C * phi x := by
  have hc : ContinuousOn (fun x : ℝ => (x * deriv phi x) / phi x) (Icc 6 12) :=
    (continuousOn_id.mul (phi_deriv_continuous.mono (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1))).div
      (phi_smooth.continuousOn.mono (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1))
      (fun x hx => (phi_pos (lt_of_lt_of_le (by norm_num) hx.1)).ne')
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max 3 C, le_max_left _ _, ?_⟩
  intro x hx
  by_cases h6 : x ≤ 6
  · rw [phi_deriv_initial hx h6,mul_zero,abs_zero]
    exact mul_nonneg (le_trans (by norm_num) (le_max_left _ _)) (phi_pos hx).le
  by_cases h12 : 12 ≤ x
  · rw [phi_deriv_tail h12,abs_mul,abs_of_pos (phi_pos hx)]
    norm_num
    exact mul_le_mul_of_nonneg_right (le_max_left 3 C) (phi_pos hx).le
  · have hb := hC x ⟨le_of_not_ge h6,le_of_not_ge h12⟩
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (phi_pos hx)] at hb
    exact (div_le_iff₀ (phi_pos hx)).mp (hb.trans (le_max_right 3 C))

theorem xi_scaled_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |x * deriv xi x| ≤ C := by
  have hc : Continuous (fun x : ℝ => x * deriv xi x) := continuous_id.mul xi_deriv_continuous
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (1:ℝ) 2) hc.continuousOn
  refine ⟨max 0 C,le_max_left _ _,fun x => ?_⟩
  by_cases h1 : x ≤ 1
  · simp only [xi_deriv_initial h1,mul_zero,abs_zero]
    exact le_max_left _ _
  by_cases h2 : 2 ≤ x
  · simp only [xi_deriv_tail h2,mul_zero,abs_zero]
    exact le_max_left _ _
  · have hb := hC x ⟨le_of_not_ge h1,le_of_not_ge h2⟩
    have hh : |x * deriv xi x| ≤ C := by simpa only [Real.norm_eq_abs] using hb
    exact hh.trans (le_max_right _ _)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics
open CKSInducedSphere (E Ix Mat U)
open scoped Topology ContDiff

lemma positiveChart_open : IsOpen positiveChart := isOpen_lt continuous_const (coord 0).continuous

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma bendingV_deriv {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    deriv (bendingV R) r =
      (phi (r/R) + r * (deriv phi (r/R)/R)) * xi (r/R^2) +
        r * phi (r/R) * (deriv xi (r/R^2)/R^2) := by
  have hp := (phi_smooth.contDiffAt (isOpen_Ioi.mem_nhds (div_pos hr hR))).differentiableAt (by simp)
  have hpd := hp.hasDerivAt.comp r ((hasDerivAt_id r).div_const R)
  have hxd := (xi_smooth.differentiable (by simp) (r/R^2)).hasDerivAt.comp r
    ((hasDerivAt_id r).div_const (R^2))
  convert! (((hasDerivAt_id r).mul hpd).mul hxd).deriv using 1
  simp
  ring

lemma bendingV_reduced_deriv {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    r * deriv (bendingV R) r - bendingV R r =
      r * ((r/R) * deriv phi (r/R)) * xi (r/R^2) +
        r * phi (r/R) * ((r/R^2) * deriv xi (r/R^2)) := by
  rw [bendingV_deriv hR hr]
  unfold bendingV
  ring

lemma base_tail {R r : ℝ} (hR : 12 ≤ R) (hr : R^2 ≤ r) :
    r * phi (r/R) = R^3/r^2 := by
  have hRp : 0 < R := by linarith
  have hrp : 0 < r := lt_of_lt_of_le (sq_pos_of_pos hRp) hr
  have hx : 12 ≤ r/R := (le_div_iff₀ hRp).mpr (by nlinarith)
  rw [phi_tail hx]
  field_simp

lemma base_tail_le_one {R r : ℝ} (hR : 12 ≤ R) (hr : R^2 ≤ r) :
    r * phi (r/R) ≤ 1 := by
  have hRp : 0 < R := by linarith
  have hrp : 0 < r := lt_of_lt_of_le (sq_pos_of_pos hRp) hr
  rw [base_tail hR hr]
  apply (div_le_iff₀ (sq_pos_of_pos hrp)).mpr
  have hR1 : 1 ≤ R := by linarith
  have hrr : R^2 * R^2 ≤ r*r := mul_self_le_mul_self (sq_nonneg R) hr
  have hp := mul_le_mul_of_nonneg_left hR1 (pow_nonneg hRp.le 3)
  nlinarith

lemma v_le_sqrt (z : ℝ) (hz : 0 ≤ z) : z ≤ Real.sqrt (1+z^2) := by
  apply (Real.le_sqrt hz (by positivity)).mpr
  nlinarith
lemma one_le_sqrt (z : ℝ) : 1 ≤ Real.sqrt (1+z^2) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [sq_nonneg z]

theorem bendingV_first_scaled : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 12 ≤ R →
    ∀ r : ℝ, 0 < r → |r * deriv (bendingV R) r - bendingV R r| ≤
      C * Real.sqrt (1 + (bendingV R r)^2) := by
  obtain ⟨C,hC,hphi⟩ := phi_scaled_deriv_bound
  obtain ⟨K,hK,hxi⟩ := xi_scaled_deriv_bound
  have hC0 : 0 ≤ C := by linarith
  refine ⟨C+K,add_nonneg hC0 hK,fun R hR r hr => ?_⟩
  have hRp : 0 < R := by linarith
  have hv0 := bendingV_nonneg hRp hr
  have hvs := v_le_sqrt _ hv0
  have hs1 := one_le_sqrt (bendingV R r)
  have hmain : |r * ((r/R) * deriv phi (r/R)) * xi (r/R^2)| ≤ C * bendingV R r := by
    rw [abs_mul,abs_mul,abs_of_pos hr,abs_of_nonneg (xi_nonneg _)]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hphi (r/R) (div_pos hr hRp)) hr.le) (xi_nonneg (r/R^2))
    convert! hh using 1
    simp only [bendingV]
    ring
  have hcut : |r * phi (r/R) * ((r/R^2) * deriv xi (r/R^2))| ≤ K * Real.sqrt (1+(bendingV R r)^2) := by
    by_cases hc : r ≤ R^2
    · have hy : r/R^2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr (by simpa using hc)
      rw [xi_deriv_initial hy,mul_zero,mul_zero,abs_zero]
      exact mul_nonneg hK (Real.sqrt_nonneg _)
    · rw [abs_mul,abs_mul,abs_of_pos hr,abs_of_pos (phi_pos (div_pos hr hRp))]
      calc
        _ ≤ r * phi (r/R) * K := mul_le_mul_of_nonneg_left (hxi _) (mul_nonneg hr.le (phi_pos (div_pos hr hRp)).le)
        _ ≤ K := by nlinarith [base_tail_le_one hR (le_of_not_ge hc)]
        _ ≤ K * Real.sqrt (1+(bendingV R r)^2) := by nlinarith
  rw [bendingV_reduced_deriv hRp hr]
  calc
    _ ≤ |r * ((r/R) * deriv phi (r/R)) * xi (r/R^2)| +
      |r * phi (r/R) * ((r/R^2) * deriv xi (r/R^2))| := abs_add_le _ _
    _ ≤ C * bendingV R r + K * Real.sqrt (1+(bendingV R r)^2) := add_le_add hmain hcut
    _ ≤ (C+K) * Real.sqrt (1+(bendingV R r)^2) := by nlinarith

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

lemma bending_reduced_bound : ∃ V : ℝ, 0 ≤ V ∧ ∀ R : ℝ, 12 ≤ R → ∀ r : ℝ, 0 < r →
    |deriv (bendingV R) r - bendingV R r/r| / A (bendingV R r) ≤ V/r := by
  obtain ⟨V,hV,h⟩ := bendingV_first_scaled
  refine ⟨V,hV,fun R hR r hr => ?_⟩
  have hA : 0 < A (bendingV R r) := by unfold A; positivity
  have hS : Real.sqrt (A (bendingV R r)) ≤ A (bendingV R r) := by
    have hh : 1 ≤ A (bendingV R r) := by unfold A; nlinarith [sq_nonneg (bendingV R r)]
    have he := Real.sq_sqrt hA.le
    have hs := Real.sqrt_nonneg (A (bendingV R r))
    nlinarith
  have hv := (h R hR r hr).trans (mul_le_mul_of_nonneg_left hS hV)
  have he : |r*deriv (bendingV R) r - bendingV R r| =
      |deriv (bendingV R) r - bendingV R r/r| * r := by
    calc
      _ = |(deriv (bendingV R) r - bendingV R r/r)*r| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_mul,abs_of_pos hr]
  rw [he] at hv
  exact (div_le_div_iff₀ hA hr).mpr hv

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

theorem constructed_outer_DEC (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : Point,
    3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
    DEC (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x)
      (tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
        (radial (normalEntry (bendingV R) (bendingBeta R)))
        (correctedComponent (bendingV R) (outerA f₀ R))
        (correctedComponent (bendingV R) (outerPhi f₀ R)) x) := by
  obtain ⟨M,B,T,hM,hB,hT,hbound⟩ := outer_uniform_bounds f₀ hf₀ m
  obtain ⟨V,hV,hvbound⟩ := bending_reduced_bound
  let Q := (energyError M B V T + momentumError M B V T)^2
  refine ⟨max 12 (max (4*M) Q),le_max_left _ _,?_⟩
  intro R hR x hr hs
  have hR12 : 12 ≤ R := (le_max_left _ _).trans hR
  have hRmass : 4*M ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRerr : Q ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hRp : 0 < R := by linarith
  have hrp : 0 < x 0 := by linarith
  have hxm : x ∈ positiveChart := hrp
  have hF := (outerMass_smooth f₀ hf₀ m hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  have hv := (bendingV_smooth hRp).contDiffAt (isOpen_Ioi.mem_nhds hrp)
  have ha := (outerA_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  have hb := (outerPhi_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  obtain ⟨hm,hΔ,hg,ht⟩ := hbound R hR12 x hr hs
  obtain ⟨hdθ,hdφ⟩ := outer_divergence f₀ hf₀ m hRp hrp hs
  exact smooth_outer_DEC
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((bendingBeta_smooth R).differentiable (by simp) _)
    (ha.differentiableAt (by simp)) (hb.differentiableAt (by simp))
    (by linarith) hs hm (by linarith)
    (outerMass_heat f₀ hf₀ m hRp hr hs) hdθ hdφ
    (beta_nonneg _) (beta_le_one _) (beta_support hR12)
    (zeta_nonneg _) (zeta_le_one _) (zeta_support hR12)
    hΔ hg hV hT (hvbound R hR12 (x 0) hrp) ht (by dsimp [Q] at hRerr; linarith)

end
end CKSSphericalChart

end

end OAI
end

theorem solution : type_of% @OAI.CKSSphericalChart.constructed_outer_DEC := @OAI.CKSSphericalChart.constructed_outer_DEC
