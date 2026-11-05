-- Prove2me | solution 1 for OAI.CKSCartesianOuter.constructed_cartesian_energy_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:24:06.964059+00:00
-- url     : https://prove2.me/submissions/0cb3ee24-c5ab-426b-a214-b602255a4eaa

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSInducedSphere_smoothDatum_rapid
import Theorems.Thm_OAI_CKSSphericalChart_outerMass_smooth
import Theorems.Thm_OAI_CKSSphericalChart_outerA_smooth
import Theorems.Thm_OAI_CKSSphericalChart_outerPhi_smooth
import Theorems.Thm_OAI_CKSSphericalChart_outerMass_heat
import Theorems.Thm_OAI_CKSSphericalChart_outer_uniform_bounds
import Theorems.Thm_OAI_CKSCartesianOuter_cartesian_radicand_positive
import Theorems.Thm_OAI_CKSCartesianOuter_spherical_physical_energy

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

def C (r u v d β ζ Δ a b : ℝ) (grad : Vec2) : ℝ :=
  2 * v * β / r ^ 3 + 2 / (r ^ 3 * Real.sqrt r) +
  Δ / r ^ 3 * (ζ / A v - 1 / u ^ 2) -
  3 * ‖grad‖ ^ 2 / (r ^ 4 * u ^ 4) -
  d ^ 2 * (a ^ 2 + b ^ 2) / (r ^ 2 * A v ^ 2)

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

end
end CKSBending

end

noncomputable section
namespace CKSLocalBending
noncomputable section
open CKSRound CKSBending

lemma sphereGrad_sq (f : MassJet) (s : ℝ) :
    ‖sphereGrad f s‖ ^ 2 = f.gradientSq s := by
  simp [sphereGrad, MassJet.gradientSq, WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, div_pow]

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

lemma phi_smooth : ContDiffOn ℝ ∞ phi (Ioi 0) := by
  unfold phi
  have hc : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition ((x-6)/6)) := by fun_prop
  exact (contDiffOn_const.sub hc.contDiffOn).add
    (hc.contDiffOn.mul ((contDiffOn_id.inv (fun x hx => ne_of_gt hx)).pow 3))
lemma xi_smooth : ContDiff ℝ ∞ xi := by unfold xi; fun_prop
lemma zeta_smooth : ContDiff ℝ ∞ zeta := by unfold zeta; fun_prop
lemma beta_smooth : ContDiff ℝ ∞ beta := by unfold beta; fun_prop

lemma xi_zero {x : ℝ} (hx : 2 ≤ x) : xi x = 0 := by
  simp [xi,Real.smoothTransition.one_of_one_le (show 1 ≤ x-1 by linarith)]

lemma zeta_one {x : ℝ} (hx : 5 ≤ x) : zeta x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma beta_zero {x : ℝ} (hx : 4 ≤ x) : beta x = 0 := by
  simp [beta,Real.smoothTransition.one_of_one_le (show 1 ≤ 2*x-7 by linarith)]

lemma bendingV_smooth {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ∞ (bendingV R) (Ioi 0) := by
  unfold bendingV
  have hc : ContDiffOn ℝ ∞ (fun r : ℝ => phi (r/R)) (Ioi 0) :=
    phi_smooth.comp (contDiffOn_id.div_const R) (fun r hr => div_pos hr hR)
  exact (contDiffOn_id.mul hc).mul
    ((xi_smooth.comp (contDiff_id.div_const (R^2))).contDiffOn)
lemma bendingZeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingZeta R) :=
  zeta_smooth.comp (contDiff_id.div_const R)
lemma bendingBeta_smooth (R : ℝ) : ContDiff ℝ ∞ (bendingBeta R) :=
  beta_smooth.comp (contDiff_id.div_const R)

lemma bendingV_tail {R r : ℝ} (hR : 0 < R) (hr : 2*R^2 ≤ r) : bendingV R r = 0 := by
  have hx : 2 ≤ r/R^2 := (le_div_iff₀ (sq_pos_of_pos hR)).mpr hr
  simp [bendingV,xi_zero hx]

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma matrix_det_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) : ContDiffAt ℝ ∞ (fun y => (G y).det) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  simp only [Matrix.det_fin_three]
  fun_prop

lemma matrix_inv_component_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => (G y)⁻¹ i j) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hd := (matrix_det_contDiffAt hg).inv h0
  simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul,
    Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 1 * G y 2 2 - G y 1 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 1 * G y 2 2) + G y 0 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 1 * G y 1 2 - G y 0 2 * G y 1 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 1 0 * G y 2 2) + G y 1 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 2 2 - G y 0 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 1 2) + G y 0 2 * G y 1 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 0 * G y 2 1 - G y 1 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 2 1) + G y 0 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 1 1 - G y 0 1 * G y 1 0)) x
    exact hd.mul (by fun_prop)

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

lemma rotation_apply (i j : Fin 3) (p : Poly) :
    rotation i j p = X i * pderiv j p - X j * pderiv i p := by
  simp [rotation, smul_eq_mul]

lemma sphereEval_X (i : Fin 3) : sphereEval (X i) = sphereCoordinate i :=
  aeval_X _ _

open MeasureTheory

open scoped Pointwise
def sphereHome (u : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  u.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      u.norm_map])

def rotatedCoordinate (i j : Fin 3) (t : ℝ) (k : Fin 3) : C(Sphere, ℝ) :=
  if k = i then Real.cos t • sphereCoordinate i - Real.sin t • sphereCoordinate j
  else if k = j then Real.sin t • sphereCoordinate i + Real.cos t • sphereCoordinate j
  else sphereCoordinate k

def rotationAction (i j : Fin 3) (t : ℝ) : Poly →ₐ[ℝ] C(Sphere, ℝ) :=
  aeval (rotatedCoordinate i j t)

lemma rotationAction_zero (i j : Fin 3) : rotationAction i j 0 = sphereEval := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [rotationAction, sphereEval, aeval_X, rotatedCoordinate, Real.cos_zero,
    Real.sin_zero, one_smul, zero_smul, sub_zero, zero_add]
  split_ifs with hi hj
  · subst k; rfl
  · subst k; rfl
  · rfl

lemma rotationAction_apply (i j : Fin 3) (hij : i ≠ j) (t : ℝ)
    (p : Poly) (x : Sphere) :
    rotationAction i j t p x = sphereEval p (sphereHome (planeRotation i j hij t) x) := by
  have h : (ContinuousMap.evalAlgHom ℝ ℝ x).comp (rotationAction i j t) =
      (ContinuousMap.evalAlgHom ℝ ℝ (sphereHome (planeRotation i j hij t) x)).comp
        sphereEval := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, ContinuousMap.evalAlgHom_apply, rotationAction,
      aeval_X, sphereEval]
    change rotatedCoordinate i j t k x = (planeRotationMap i j t x.1) k
    rw [planeRotationMap_apply]
    simp only [rotatedCoordinate]
    split_ifs <;> rfl
  exact congrArg (fun f : Poly →ₐ[ℝ] ℝ => f p) h

lemma rotatedCoordinate_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (k : Fin 3) :
    HasDerivAt (fun t => rotatedCoordinate i j t k)
      (sphereEval (rotation i j (X k))) 0 := by
  have hs := (Real.hasDerivAt_sin (0 : ℝ))
  have hc := (Real.hasDerivAt_cos (0 : ℝ))
  by_cases hi : k = i
  · subst k
    convert! (hc.smul_const (sphereCoordinate i)).sub
        (hs.smul_const (sphereCoordinate j)) using 1 <;>
      simp [rotatedCoordinate, rotation_apply, hij, pderiv_X, sphereEval_X]
    rfl
  · by_cases hj : k = j
    · subst k
      convert! (hs.smul_const (sphereCoordinate i)).add
          (hc.smul_const (sphereCoordinate j)) using 1 <;>
        simp [rotatedCoordinate, rotation_apply, hij.symm, pderiv_X, sphereEval_X]
      rfl
    · simpa [rotatedCoordinate, rotation_apply, hi, hj, Ne.symm hi, Ne.symm hj,
        pderiv_X] using hasDerivAt_const (0 : ℝ) (sphereCoordinate k)

lemma rotationAction_hasDerivAt_zero (i j : Fin 3) (hij : i ≠ j) (p : Poly) :
    HasDerivAt (fun t => rotationAction i j t p) (sphereEval (rotation i j p)) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [rotationAction, rotation_apply] using
      hasDerivAt_const (0 : ℝ) (algebraMap ℝ C(Sphere, ℝ) a)
  | add p q hp hq =>
    convert! hp.add hq using 1 <;> simp only [map_add]
    rfl
  | mul_X p k hp =>
    have hk : HasDerivAt (fun t => rotationAction i j t (X k))
        (sphereEval (rotation i j (X k))) 0 :=
      by simpa only [rotationAction, aeval_X] using
        rotatedCoordinate_hasDerivAt_zero i j hij k
    convert! hp.mul hk using 1
    · funext t; exact map_mul (rotationAction i j t) p (X k)
    · rw [Derivation.leibniz, map_add]
      simp only [smul_eq_mul, map_mul, rotationAction_zero]
      ring

open scoped Manifold ContDiff Topology
open Set

lemma rotationGenerator_apply (i j k : Fin 3) (x : Ambient) :
    rotationGenerator i j x k = (if k = j then x i else 0) - (if k = i then x j else 0) := rfl

attribute [local instance] cksLocalInst_1853

lemma planeRotation_hasDerivAt (i j : Fin 3) (hij : i ≠ j) (x : Ambient) (t : ℝ) :
    HasDerivAt (fun s => planeRotation i j hij s x)
      (rotationGenerator i j (planeRotation i j hij t x)) t := by
  have h : HasDerivAt (fun s => fun k : Fin 3 =>
      if k = i then Real.cos s * x i - Real.sin s * x j
      else if k = j then Real.sin s * x i + Real.cos s * x j else x k)
      (fun k => (rotationGenerator i j (planeRotation i j hij t x)) k) t := by
    apply hasDerivAt_pi.mpr
    intro k
    by_cases hi : k = i
    · subst k
      convert! ((Real.hasDerivAt_cos t).mul_const (x i)).sub
        ((Real.hasDerivAt_sin t).mul_const (x j)) using 1
      · funext s; simp
      · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij, hij.symm]
        ring
    · by_cases hj : k = j
      · subst k
        convert! ((Real.hasDerivAt_sin t).mul_const (x i)).add
          ((Real.hasDerivAt_cos t).mul_const (x j)) using 1
        · funext s; simp [hij.symm]
        · simp [rotationGenerator_apply, planeRotation_apply, planeRotationMap_apply, hij.symm]
          ring
      · simpa [rotationGenerator_apply, hi, hj] using hasDerivAt_const t (x k)
  convert! (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t h using 1

def polynomialExtension (p : Poly) (x : Ambient) : ℝ := aeval (fun i => x i) p

lemma polynomialExtension_smooth (p : Poly) : ContDiff ℝ ∞ (polynomialExtension p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    convert! (contDiff_const : ContDiff ℝ ∞ (fun _ : Ambient => a)) using 1
    funext x; simp [polynomialExtension]
  | add p q hp hq =>
    convert! hp.add hq using 1
    funext x; exact map_add (aeval (fun i => x i)) p q
  | mul_X p k hp =>
    convert! hp.mul (EuclideanSpace.proj k).contDiff using 1
    funext x; simp [polynomialExtension]

lemma polynomialExtension_on_sphere (p : Poly) (x : Sphere) :
    polynomialExtension p x = sphereEval p x := by
  have h : aeval (fun i => (x : Ambient) i) =
      (ContinuousMap.evalAlgHom ℝ ℝ x).comp sphereEval := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [sphereEval, sphereCoordinate]
    rfl
  exact congrArg (fun h : Poly →ₐ[ℝ] ℝ => h p) h

lemma radialExtension_pos_smul (f : Sphere → ℝ) (x : Ambient) {a : ℝ} (ha : 0 < a) :
    radialExtension f (a • x) = radialExtension f x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  rw [radialExtension, dite_eq_left (smul_ne_zero ha.ne' hx), radialExtension, dite_eq_left hx]
  congr 1
  apply Subtype.ext
  simp only [normalizeSphere, norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_inv_rev,
    smul_smul]
  congr 1
  field_simp

lemma radialExtension_isometry (f : Sphere → ℝ) (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (x : Ambient) (hx : x ≠ 0) :
    radialExtension f (e x) = f (sphereHome e (normalizeSphere ⟨x, hx⟩)) := by
  rw [radialExtension, dite_eq_left (by simpa using e.injective.ne hx)]
  congr 1
  apply Subtype.ext
  simp [normalizeSphere, sphereHome]

lemma polynomial_sphere_smooth (p : Poly) : SmoothSphere (sphereEval p) := by
  have h := (polynomialExtension_smooth p).contMDiff.comp (contMDiff_coe_sphere (n := 2))
  convert! h using 1
  funext x
  exact (polynomialExtension_on_sphere p x).symm

lemma radialExtension_fderiv_self {f : Sphere → ℝ} (hf : SmoothSphere f)
    {x : Ambient} (hx : x ≠ 0) : fderiv ℝ (radialExtension f) x x = 0 := by
  have hd := ((radialExtension_smooth hf).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension f) (fderiv ℝ (radialExtension f) x) ((1 : ℝ) • x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have he : (fun s : ℝ => radialExtension f (s • x)) =ᶠ[nhds 1]
      (fun _ => radialExtension f x) := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact radialExtension_pos_smul f x hs
  have h2 := (hasDerivAt_const (1 : ℝ) (radialExtension f x)).congr_of_eventuallyEq he
  simpa using h1.unique h2

lemma smoothRotation_radial_polynomial (p : Poly) (i j : Fin 3) {x : Ambient} (hx : x ≠ 0) :
    smoothRotation i j (radialExtension (sphereEval p)) x =
      radialExtension (sphereEval (rotation i j p)) x := by
  by_cases hij : i = j
  · subst j
    have hg : rotationGenerator i i x = 0 := by ext k; simp [rotationGenerator_apply]
    simp [smoothRotation, hg, rotation_apply, radialExtension]
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd' : HasFDerivAt (radialExtension (sphereEval p))
      (fderiv ℝ (radialExtension (sphereEval p)) x) (planeRotation i j hij 0 x) := by
    simpa using hd.hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) (planeRotation_hasDerivAt i j hij x 0)
  let y : Sphere := normalizeSphere ⟨x, hx⟩
  have h2 := (ContinuousMap.evalCLM (R := ℝ) y).hasFDerivAt.comp_hasDerivAt 0
    (rotationAction_hasDerivAt_zero i j hij p)
  have he : (fun t => radialExtension (sphereEval p) (planeRotation i j hij t x)) =
      fun t => rotationAction i j t p y := by
    funext t
    rw [rotationAction_apply i j hij]
    exact radialExtension_isometry _ _ _ hx
  change HasDerivAt (fun s => radialExtension (sphereEval p) (planeRotation i j hij s x)) _ 0 at h1
  rw [he] at h1
  have h := h1.unique h2
  simpa [smoothRotation, radialExtension, hx, y] using h

lemma rotationGenerator_decomposition (x v : Ambient) :
    ‖x‖ ^ 2 • v = (∑ i : Fin 3, ∑ j : Fin 3, (x i * v j) • rotationGenerator i j x) +
      (∑ i : Fin 3, x i * v i) • x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [Fin.sum_univ_three, rotationGenerator_apply] <;> ring

lemma radial_polynomial_fderiv (p : Poly) {x : Ambient} (hx : x ≠ 0) (v : Ambient) :
    fderiv ℝ (radialExtension (sphereEval p)) x v =
      ∑ i : Fin 3, ∑ j : Fin 3, (x i * v j / ‖x‖ ^ 2) *
        radialExtension (sphereEval (rotation i j p)) x := by
  have h := congrArg (fderiv ℝ (radialExtension (sphereEval p)) x)
    (rotationGenerator_decomposition x v)
  simp only [map_add, map_sum, map_smul, radialExtension_fderiv_self (polynomial_sphere_smooth p) hx,
    smul_eq_mul] at h
  have hrot (i j : Fin 3) : fderiv ℝ (radialExtension (sphereEval p)) x (rotationGenerator i j x) =
      radialExtension (sphereEval (rotation i j p)) x := smoothRotation_radial_polynomial p i j hx
  simp only [hrot] at h
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).mpr
  simpa [mul_comm, mul_zero] using h

end
end CKSSphericalHarmonics

end

noncomputable section
namespace CKSSpectralHeat
noncomputable section
open Set Filter Real
open scoped Topology ContDiff

lemma eigenvalue_ge_six (n : ℕ) : 6 ≤ eigenvalue n := by
  unfold eigenvalue
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith
lemma eigenvalue_pos (n : ℕ) : 0 < eigenvalue n := by linarith [eigenvalue_ge_six n]

lemma kernel_smooth : ContDiff ℝ ∞ kernel := by unfold kernel; fun_prop

lemma kernel_nonneg_time {t : ℝ} (ht : 0 ≤ t) : kernel t = exp (-t) := by
  simp [kernel, smoothTransition.one_of_one_le (show 1 ≤ t + 1 by linarith)]

lemma kernel_zero {t : ℝ} (ht : t ≤ -1) : kernel t = 0 := by
  simp [kernel, smoothTransition.zero_of_nonpos (show t + 1 ≤ 0 by linarith)]

lemma kernel_derivative_bounded (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, ‖iteratedDeriv b kernel t‖ ≤ C := by
  have hc : Continuous (iteratedDeriv b kernel) :=
    kernel_smooth.continuous_iteratedDeriv b (by exact_mod_cast (le_top : (b : ℕ∞) ≤ ⊤))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro t
  by_cases htlo : t < -2
  · have heq : kernel =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds (show t < -1 by linarith)] with x hx
      exact kernel_zero hx.le
    rw [heq.iteratedDeriv_eq b]
    simp [le_trans zero_le_one (le_max_right C 1)]
  by_cases hthi : 1 < t
  · have heq : kernel =ᶠ[𝓝 t] (fun x => exp (-1 * x)) := by
      filter_upwards [Ioi_mem_nhds (show 0 < t by linarith)] with x hx
      simpa using kernel_nonneg_time hx.le
    rw [heq.iteratedDeriv_eq b, iteratedDeriv_exp_const_mul]
    have he : exp (-t) ≤ 1 := exp_le_one_iff.2 (by linarith)
    calc
      ‖(-1 : ℝ) ^ b * exp (-1 * t)‖ = exp (-t) := by
        rw [norm_mul, norm_pow]
        simp [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      _ ≤ 1 := he
      _ ≤ max C 1 := le_max_right _ _
  · exact (hC t ⟨not_lt.mp htlo, not_lt.mp hthi⟩).trans (le_max_left _ _)

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

def Rapid (coeff : ℕ → B) : Prop :=
  ∀ b : ℕ, Summable (fun n => eigenvalue n ^ b * ‖coeff n‖)

def inverseCoeff (coeff : ℕ → B) (n : ℕ) : B :=
  (1 - eigenvalue n / 2)⁻¹ • coeff n

lemma inverse_denominator_bound (n : ℕ) : |(1 - eigenvalue n / 2)⁻¹| ≤ 1 / 2 := by
  have he := eigenvalue_ge_six n
  have hd : 2 ≤ |1 - eigenvalue n / 2| := by
    rw [abs_of_neg (by linarith)]
    linarith
  rw [abs_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd

omit [CompleteSpace B] in
lemma inverseCoeff_rapid [CompleteSpace B] (coeff : ℕ → B) (h : Rapid coeff) : Rapid (inverseCoeff coeff) := by
  intro b
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (eigenvalue_pos n).le _) (norm_nonneg _))
    _ ((h b).mul_left (1 / 2))
  intro n
  rw [inverseCoeff, norm_smul, Real.norm_eq_abs]
  calc
    eigenvalue n ^ b * (|(1 - eigenvalue n / 2)⁻¹| * ‖coeff n‖) ≤
      eigenvalue n ^ b * ((1 / 2) * ‖coeff n‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (inverse_denominator_bound n) (norm_nonneg _))
          (pow_nonneg (eigenvalue_pos n).le _)
    _ = (1 / 2) * (eigenvalue n ^ b * ‖coeff n‖) := by ring

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]

end
end CKSSpectralHeat

end

end OAI
end

section
namespace OAI


noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

lemma U_open : IsOpen U := isClosed_singleton.isOpen_compl

attribute [local instance] CKSLorentz.two_atLeastTwo

lemma partial_smooth {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) (i : Ix) :
    ContDiffOn ℝ ∞ (pd i F) U :=
  (hF.fderiv_of_isOpen U_open (by simp)).clm_apply contDiffOn_const

lemma smooth_diff {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ F x := (hF.contDiffAt (U_open.mem_nhds hx)).differentiableAt (by simp)

lemma pd_add {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y + G y) x = pd k F x + pd k G x := by
  simp only [pd, fderiv_fun_add hF hG, add_apply]

lemma pd_mul {F G : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (k : Ix) :
    pd k (fun y => F y * G y) x = pd k F x * G x + F x * pd k G x := by
  rw [pd, fderiv_fun_mul hF hG]
  simp only [add_apply, smul_apply, smul_eq_mul, pd]
  ring

lemma coordinate_smooth (i : Ix) : ContDiffOn ℝ ∞ (fun x : E => x i) U :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Ix) i).contDiff.contDiffOn

lemma proj_smooth (i j : Ix) : ContDiffOn ℝ ∞ (fun x : E => proj (fun a => x a) i j) U :=
  contDiffOn_const.sub ((coordinate_smooth i).mul (coordinate_smooth j))

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma radialExtension_norm_bound (f : C(Sphere, ℝ)) (x : Ambient) :
    ‖radialExtension f x‖ ≤ ‖f‖ := by
  by_cases hx : x ≠ 0
  · rw [radialExtension, dite_eq_left hx]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp [radialExtension, hx]

def angularField (i j : Fin 3) (x : Ambient) : Ambient →L[ℝ] ℝ :=
  (x i / ‖x‖ ^ 2) • EuclideanSpace.proj j

lemma angularField_smooth (i j : Fin 3) : ContDiffOn ℝ ∞ (angularField i j) puncturedSpace := by
  have hn : ContDiffOn ℝ ∞ (fun x : Ambient => ‖x‖) puncturedSpace := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.contDiffOn.div (hn.pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul contDiffOn_const

lemma radial_polynomial_hasFDerivAt (p : Poly) {x : Ambient} (hx : x ≠ 0) :
    HasFDerivAt (radialExtension (sphereEval p))
      (∑ i : Fin 3, ∑ j : Fin 3,
        radialExtension (sphereEval (rotation i j p)) x • angularField i j x) x := by
  have hd := ((radialExtension_smooth (polynomial_sphere_smooth p)).contDiffAt
    (puncturedSpace.isOpen.mem_nhds hx)).differentiableAt (by simp)
  convert! hd.hasFDerivAt using 1
  ext v
  rw [radial_polynomial_fderiv p hx v]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    angularField, EuclideanSpace.proj, PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma temporalJet_hasDerivAt (b n : ℕ) (t : ℝ) :
    HasDerivAt (temporalJet b n) (temporalJet (b + 1) n t) t := by
  have hk := (CKSSpectralHeat.kernel_smooth.differentiable_iteratedDeriv b
    (by exact_mod_cast (ENat.natCast_lt_top b))).differentiableAt (x := CKSSpectralHeat.eigenvalue n * t) |>.hasDerivAt
  have h := (hk.comp t ((hasDerivAt_id t).const_mul (CKSSpectralHeat.eigenvalue n))).const_mul
    (CKSSpectralHeat.eigenvalue n ^ b)
  convert! h using 1
  simp only [temporalJet, iteratedDeriv_succ, pow_succ]
  ring

lemma temporalJet_bound (b : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n t,
    ‖temporalJet b n t‖ ≤ C * CKSSpectralHeat.eigenvalue n ^ b := by
  obtain ⟨C, hC, hb⟩ := CKSSpectralHeat.kernel_derivative_bounded b
  refine ⟨C, hC, fun n t => ?_⟩
  rw [temporalJet, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (CKSSpectralHeat.eigenvalue_pos n)]
  nlinarith [mul_le_mul_of_nonneg_left (hb (CKSSpectralHeat.eigenvalue n * t))
    (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le b)]

def heatDomain : Set SpaceTime := {z | z.2 ≠ 0}

lemma heatDomain_open : IsOpen heatDomain :=
  isOpen_ne_fun continuous_snd continuous_const

def heatField : Option (Fin 3 × Fin 3) → SpaceTime → SpaceTime →L[ℝ] ℝ
  | none, _ => ContinuousLinearMap.fst ℝ ℝ Ambient
  | some ij, z => (angularField ij.1 ij.2 z.2).comp (ContinuousLinearMap.snd ℝ ℝ Ambient)

lemma heatField_smooth (o : Option (Fin 3 × Fin 3)) : ContDiffOn ℝ ∞ (heatField o) heatDomain := by
  cases o with
  | none => exact contDiffOn_const
  | some ij =>
    exact ((angularField_smooth ij.1 ij.2).comp contDiffOn_snd
      (fun z hz => hz)).clm_comp contDiffOn_const

def heatNext (a : HeatJet) : Option (Fin 3 × Fin 3) → HeatJet
  | none => (a.1 + 1, a.2)
  | some ij => (a.1, ij :: a.2)

lemma heatTerm_derivative_identity (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime) :
    (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) =
    temporalJet a.1 n z.1 •
      ((∑ i : Fin 3, ∑ j : Fin 3,
        radialExtension (sphereEval (rotation i j (rotationWord a.2 (p n)))) z.2 •
          angularField i j z.2).comp (ContinuousLinearMap.snd ℝ ℝ Ambient)) +
    radialExtension (sphereEval (rotationWord a.2 (p n))) z.2 •
      ((ContinuousLinearMap.toSpanSingleton ℝ (temporalJet (a.1 + 1) n z.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ Ambient)) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [Fintype.sum_option, Fintype.sum_prod_type, heatTerm, heatNext, heatField,
    rotationWord, sum_apply, smul_apply,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Finset.mul_sum]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  exact add_comm _ _

lemma heatTerm_hasFDerivAt (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime)
    (hz : z ∈ heatDomain) :
    HasFDerivAt (heatTerm p a n)
      (∑ o : Option (Fin 3 × Fin 3), heatTerm p (heatNext a o) n z • heatField o z) z := by
  have ht := (temporalJet_hasDerivAt a.1 n z.1).hasFDerivAt.comp z
    (ContinuousLinearMap.fst ℝ ℝ Ambient).hasFDerivAt
  have hx := (radial_polynomial_hasFDerivAt (rotationWord a.2 (p n)) hz).comp z
    (ContinuousLinearMap.snd ℝ ℝ Ambient).hasFDerivAt
  rw [heatTerm_derivative_identity]
  convert! ht.mul hx using 1

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSDifferentialSeries
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]
variable {s : Set E} (hs : IsOpen s)
variable (A : J → E → E →L[ℝ] ℝ) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) s)
variable (next : I → J → I) (F : I → ℕ → E → ℝ)
variable (hF : ∀ i n x, x ∈ s → HasFDerivAt (F i n)
  (∑ j, F (next i j) n x • A j x) x)
variable (bound : ∀ i, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n x, x ∈ s → ‖F i n x‖ ≤ u n)

def series (i : I) (x : E) : ℝ := ∑' n, F i n x

include bound

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma series_summable [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : I) {x : E} (hx : x ∈ s) : Summable (fun n => F i n x) := by
  obtain ⟨u, hu, hb⟩ := bound i
  exact Summable.of_norm_bounded hu (fun n => hb n x hx)

include hF

lemma series_continuous (i : I) : ContinuousOn (series F i) s := by
  obtain ⟨u, hu, hb⟩ := bound i
  exact continuousOn_tsum (fun n x hx => (hF i n x hx).continuousAt.continuousWithinAt) hu hb

include hs hA

lemma series_hasFDerivAt (i : I) {x : E} (hx : x ∈ s) :
    HasFDerivAt (series F i) (∑ j, series F (next i j) x • A j x) x := by
  have bounds := bound
  choose u hu hb using bounds
  let K : ℝ := (∑ j, ‖A j x‖) + 1
  have hc : ContinuousAt (fun y => ∑ j, ‖A j y‖) x := by
    exact (continuousOn_finsetSum _ (fun j _ =>
      (hA j).continuousOn.norm)).continuousAt (hs.mem_nhds hx)
  have he : ∀ᶠ y in 𝓝 x, (∑ j, ‖A j y‖) < K :=
    hc.eventually_lt continuousAt_const (by dsimp [K]; linarith)
  have hn : {y | y ∈ s ∧ (∑ j, ‖A j y‖) < K} ∈ 𝓝 x :=
    inter_mem (hs.mem_nhds hx) he
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hn
  have hlocal (j : J) (y : E) (hy : y ∈ Metric.ball x r) : ‖A j y‖ ≤ K := by
    exact (Finset.single_le_sum (fun k _ => norm_nonneg (A k y))
      (Finset.mem_univ j)).trans (hrs hy).2.le
  have hus : Summable (fun n => K * ∑ j, u (next i j) n) :=
    (summable_sum (fun j _ => hu (next i j))).mul_left K
  have hderiv := hasFDerivAt_tsum_of_isPreconnected hus Metric.isOpen_ball
    (convex_ball x r).isPreconnected
    (fun n y hy => hF i n y (hrs hy).1)
    (fun n y hy => (show ‖∑ j, F (next i j) n y • A j y‖ ≤ K * ∑ j, u (next i j) n from by
      calc
        ‖∑ j, F (next i j) n y • A j y‖ ≤ ∑ j, ‖F (next i j) n y • A j y‖ := norm_sum_le _ _
        _ ≤ ∑ j, u (next i j) n * K := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul]
          exact mul_le_mul (hb _ n y (hrs hy).1) (hlocal j y hy) (norm_nonneg _)
            ((norm_nonneg _).trans (hb _ n y (hrs hy).1))
        _ = K * ∑ j, u (next i j) n := by rw [← Finset.sum_mul]; ring))
    (Metric.mem_ball_self hr) (series_summable F bound i hx) (Metric.mem_ball_self hr)
  convert! hderiv using 1
  symm
  rw [Summable.tsum_finsetSum (fun j _ => (series_summable F bound (next i j) hx).smul_const (A j x))]
  apply Finset.sum_congr rfl
  intro j hj
  exact (series_summable F bound (next i j) hx).tsum_smul_const (A j x)

theorem series_contDiff (i : I) : ContDiffOn ℝ ∞ (series F i) s := by
  apply contDiffOn_infty.mpr
  intro N
  induction N generalizing i with
  | zero => exact contDiffOn_zero.mpr (series_continuous A next F hF bound i)
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs.uniqueDiffOn).mpr
    refine ⟨by simp, ⟨fun x => ∑ j, series F (next i j) x • A j x, ?_, ?_⟩⟩
    · exact ContDiffOn.sum (fun j _ => (ih (next i j)).smul ((hA j).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ ⊤))))
    · intro x hx
      exact (series_hasFDerivAt hs A hA next F hF bound i hx).hasFDerivWithinAt

end
end CKSDifferentialSeries

end

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

lemma heatTerm_bound (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n z, z ∈ heatDomain → ‖heatTerm p a n z‖ ≤ u n := by
  obtain ⟨C, hC, hb⟩ := temporalJet_bound a.1
  refine ⟨fun n => C * (CKSSpectralHeat.eigenvalue n ^ a.1 *
    ‖sphereEval (rotationWord a.2 (p n))‖), (hp a.2 a.1).mul_left C, ?_⟩
  intro n z hz
  dsimp only
  rw [heatTerm, norm_mul, ← mul_assoc]
  exact mul_le_mul (hb n z.1) (radialExtension_norm_bound _ _) (norm_nonneg _)
    (mul_nonneg hC (pow_nonneg (CKSSpectralHeat.eigenvalue_pos n).le _))

theorem jointHeatSeries_smooth (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet) :
    ContDiffOn ℝ ∞ (jointHeatSeries p a) heatDomain :=
  CKSDifferentialSeries.series_contDiff heatDomain_open heatField heatField_smooth
    heatNext (heatTerm p) (heatTerm_hasFDerivAt p) (heatTerm_bound p hp) a

lemma jointHeatSeries_hasFDerivAt (p : ℕ → Poly) (hp : PolynomialRapid p) (a : HeatJet)
    {z : SpaceTime} (hz : z ∈ heatDomain) :
    HasFDerivAt (jointHeatSeries p a)
      (∑ o : Option (Fin 3 × Fin 3), jointHeatSeries p (heatNext a o) z • heatField o z) z :=
  CKSDifferentialSeries.series_hasFDerivAt heatDomain_open heatField heatField_smooth
    heatNext (heatTerm p) (heatTerm_hasFDerivAt p) (heatTerm_bound p hp) a hz

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma positive_uIcc {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : uIcc a r ⊆ Ioi 0 := by
  intro s hs
  exact lt_of_lt_of_le (lt_min ha hr) hs.1

lemma positive_interval_integrable {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IntervalIntegrable q volume a r :=
  (hq.mono (positive_uIcc ha hr)).intervalIntegrable

lemma primitive_hasDerivAt {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : HasDerivAt (primitive a q) (q r) r := by
  exact intervalIntegral.integral_hasDerivAt_right (positive_interval_integrable hq ha hr)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hq r hr)
    (hq.continuousAt (isOpen_Ioi.mem_nhds hr))

lemma primitive_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    {a : ℝ} (ha : 0 < a) : ContDiffOn ℝ ∞ (primitive a q) (Ioi 0) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  constructor
  · intro r hr
    exact (primitive_hasDerivAt hq.continuousOn ha hr).differentiableAt.differentiableWithinAt
  · exact hq.congr (fun r hr => (primitive_hasDerivAt hq.continuousOn ha hr).deriv)

lemma paddingDensity_smooth : ContDiffOn ℝ ∞ paddingDensity (Ioi 0) := by
  exact contDiffOn_const.div (contDiffOn_id.mul (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)))
    (fun r hr => mul_ne_zero (ne_of_gt hr) (Real.sqrt_ne_zero'.mpr hr))

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
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma paddingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (paddingWeight R) := by
  unfold paddingWeight
  fun_prop

lemma paddingIntegrand_smooth (R : ℝ) :
    ContDiffOn ℝ ∞ (fun r => paddingWeight R r * paddingDensity r) (Ioi 0) :=
  (paddingWeight_smooth R).contDiffOn.mul paddingDensity_smooth
lemma paddingMass_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (paddingMass R) (Ioi 0) :=
  primitive_smooth (paddingIntegrand_smooth R) hR

lemma heatDensity_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatDensity R) (Ioi 0) := by
  unfold heatDensity
  exact (bendingZeta_smooth R).contDiffOn.div
    ((contDiffOn_const.mul contDiffOn_id).mul (contDiffOn_const.add ((bendingV_smooth hR).pow 2)))
    (fun r hr => ne_of_gt (mul_pos (mul_pos (by norm_num) hr) (by positivity)))

lemma heatTime_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (heatTime R) (Ioi 0) :=
  primitive_smooth (heatDensity_smooth hR) (by positivity)

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff
open CKSSphericalHarmonics

inductive HeatGenerated (p : ℕ → Poly) : (ℝ → E → ℝ) → Prop
  | basic (a : HeatJet) : HeatGenerated p (spatialHeat p a)
  | zero : HeatGenerated p (fun _ _ => 0)
  | add {F G} : HeatGenerated p F → HeatGenerated p G →
      HeatGenerated p (fun t x => F t x + G t x)
  | coeff (c : E → ℝ) {F} : ContDiffOn ℝ ∞ c U → HeatGenerated p F →
      HeatGenerated p (fun t x => c x * F t x)
  | congr {F G} : HeatGenerated p F → (∀ t x, x ∈ U → F t x = G t x) →
      HeatGenerated p G

variable {p : ℕ → Poly} (hp : PolynomialRapid p)
include hp

lemma HeatGenerated.joint_smooth {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => F z.1 z.2) heatDomain := by
  induction hF with
  | basic a => exact jointHeatSeries_smooth p hp a
  | zero => exact contDiffOn_const
  | add _ _ hF hG => exact hF.add hG
  | coeff c hc _ hF =>
    exact (hc.comp contDiffOn_snd (fun z hz => hz)).mul hF
  | congr _ he hF =>
    exact hF.congr (fun z hz => (he z.1 z.2 hz).symm)

lemma HeatGenerated.spatial_smooth {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (t : ℝ) :
    ContDiffOn ℝ ∞ (F t) U :=
  (hF.joint_smooth hp).comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

omit hp in
lemma HeatGenerated.sum {J : Type*} (s : Finset J) {F : J → ℝ → E → ℝ}
    (h : ∀ j ∈ s, HeatGenerated p (F j)) :
    HeatGenerated p (fun t x => ∑ j ∈ s, F j t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (HeatGenerated.zero (p := p))
  | @insert j s hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (mem_insert_self j s)).add (ih (fun k hk => h k (mem_insert_of_mem hk)))

omit hp in
lemma angularCoefficient_smooth (i : Ix) :
    ContDiffOn ℝ ∞ (fun x : E => x i / ‖x‖ ^ 2) U := by
  have hn : ContDiffOn ℝ ∞ (fun x : E => ‖x‖) U := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  exact (coordinate_smooth i).div (hn.pow 2)
    (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

lemma pd_spatialHeat (a : HeatJet) (t : ℝ) {x : E} (hx : x ∈ U) (j : Ix) :
    pd j (spatialHeat p a t) x =
      ∑ i : Ix, (x i / ‖x‖ ^ 2) * spatialHeat p (a.1, (i,j) :: a.2) t x := by
  have hd := (jointHeatSeries_hasFDerivAt p hp a (z := (t,x)) hx).comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change HasFDerivAt (spatialHeat p a t) _ x at hd
  rw [pd, hd.fderiv]
  change (∑ o, jointHeatSeries p (heatNext a o) (t,x) • heatField o (t,x)) (0, e j) = _
  simp only [Fintype.sum_option, add_apply,
    _root_.sum_apply, smul_apply, heatField,
    angularField, ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, mul_zero, zero_add,
    Fintype.sum_prod_type, EuclideanSpace.proj, PiLp.proj_apply, e_apply, heatNext]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply sum_congr rfl
  intro i hi
  exact mul_comm _ _

lemma HeatGenerated.partial {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (j : Ix) :
    HeatGenerated p (fun t x => pd j (F t) x) := by
  induction hF with
  | basic a =>
    apply HeatGenerated.congr (HeatGenerated.sum univ (fun i _ =>
      HeatGenerated.coeff _ (angularCoefficient_smooth i) (HeatGenerated.basic (a.1,(i,j)::a.2))))
    intro t x hx
    exact (pd_spatialHeat hp a t hx j).symm
  | zero => simpa only [pd_const] using (HeatGenerated.zero (p := p))
  | @add F G hF hG ihF ihG =>
    apply HeatGenerated.congr (ihF.add ihG)
    intro t x hx
    exact (pd_add (smooth_diff (hF.spatial_smooth hp t) hx)
      (smooth_diff (hG.spatial_smooth hp t) hx) j).symm
  | @coeff c F hc hF ih =>
    apply HeatGenerated.congr ((HeatGenerated.coeff _ (partial_smooth hc j) hF).add
      (HeatGenerated.coeff _ hc ih))
    intro t x hx
    exact (pd_mul (smooth_diff hc hx) (smooth_diff (hF.spatial_smooth hp t) hx) j).symm
  | @congr F G hF he ih =>
    apply HeatGenerated.congr ih
    intro t x hx
    have he' : F t =ᶠ[𝓝 x] G t := by
      filter_upwards [U_open.mem_nhds hx] with y hy
      exact he t y hy
    exact congrArg (fun A : E →L[ℝ] ℝ => A (e j)) he'.fderiv_eq

end
end CKSInducedSphere

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma rotationWord_smul (w : List (Fin 3 × Fin 3)) (c : ℝ) (p : Poly) :
    rotationWord w (c • p) = c • rotationWord w p := by
  induction w with
  | nil => rfl
  | cons ij w ih => simp only [rotationWord, ih, Derivation.map_smul]

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

lemma inversePolynomials_rapid (p : ℕ → Poly) (hp : PolynomialRapid p) :
    PolynomialRapid (inversePolynomials p) := by
  intro w b
  have h := CKSSpectralHeat.inverseCoeff_rapid (fun n => sphereEval (rotationWord w (p n))) (hp w) b
  simpa only [inversePolynomials, rotationWord_smul, map_smul, CKSSpectralHeat.inverseCoeff] using h

end
end CKSSphericalHarmonics

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

lemma HeatGenerated.neg {p : ℕ → Poly} {F : ℝ → E → ℝ} (hF : HeatGenerated p F) :
    HeatGenerated p (fun t x => -F t x) := by
  simpa only [neg_one_mul] using HeatGenerated.coeff (fun _ => (-1:ℝ)) contDiffOn_const hF

lemma HeatGenerated.sub {p : ℕ → Poly} {F G : ℝ → E → ℝ}
    (hF : HeatGenerated p F) (hG : HeatGenerated p G) :
    HeatGenerated p (fun t x => F t x - G t x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma heatTensor_generated (p : ℕ → Poly) (hp : PolynomialRapid p) (i j : Ix) :
    HeatGenerated (inversePolynomials p) (fun t x => heatTensor p t x i j) := by
  have hi := inversePolynomials_rapid p hp
  have hH (a b : Ix) : HeatGenerated (inversePolynomials p)
      (fun t x => hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b) :=
    ((HeatGenerated.basic (0,[]) (p := inversePolynomials p)).partial hi b).partial hi a
  change HeatGenerated _ (fun t x =>
    (∑ a, ∑ b, proj (fun c => x c) i a * hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b * proj (fun c => x c) b j) -
    (∑ a, ∑ b, proj (fun c => x c) a b * hess (spatialHeat (inversePolynomials p) (0,[]) t) x a b) / 2 * proj (fun c => x c) i j)
  apply HeatGenerated.sub
  · apply HeatGenerated.congr (HeatGenerated.sum univ (fun a _ => HeatGenerated.sum univ (fun b _ =>
      HeatGenerated.coeff _ ((proj_smooth i a).mul (proj_smooth b j)) (hH a b))))
    intro t x hx
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    ring
  · apply HeatGenerated.congr (HeatGenerated.coeff
      (fun x => proj (fun c => x c) i j / 2) ((proj_smooth i j).div_const 2)
      (HeatGenerated.sum univ (fun a _ => HeatGenerated.sum univ (fun b _ =>
        HeatGenerated.coeff _ (proj_smooth a b) (hH a b)))))
    intro t x hx
    ring

end
end CKSInducedSphere

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
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere
open scoped Topology ContDiff

lemma canonicalF_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalF f₀ m z.1 z.2) heatDomain :=
  contDiffOn_const.add (jointHeatSeries_smooth _ (smoothDatum_rapid f₀ hf₀) (0,[]))
lemma canonicalT_joint (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (i j : Ix) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => canonicalT f₀ z.1 z.2 i j) heatDomain :=
  (heatTensor_generated _ (smoothDatum_rapid f₀ hf₀) i j).joint_smooth
    (inversePolynomials_rapid _ (smoothDatum_rapid f₀ hf₀))

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSRealizedRound
noncomputable section
open Set Filter CKSCalculus CKSRound CKSBending CKSLocalBending
open scoped Topology ContDiff

lemma smooth_energy_residual {F a b : Point → ℝ} {v β : ℝ → ℝ} {x : Point} {ζ : ℝ}
    (hF : ContDiffAt ℝ 2 F x) (hv : ContDiffAt ℝ 2 v (x 0))
    (hβ : DifferentiableAt ℝ β (x 0))
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hr : x 0 ≠ 0) (hs : Real.sin (x 1) ≠ 0) (hpos : 0 < radicand F v x)
    (hheat : D (basis 0) F x = ζ * (massJet F x).laplace (Real.sin (x 1)) (Real.cos (x 1)) /
      (2*x 0*A (v (x 0))) + 1/(x 0*Real.sqrt (x 0))) :
    (metricJet (lapse F v) x).energy (tensorJet (lapse F v) v (radial (normalEntry v β))
      (correctedComponent v a) (correctedComponent v b) x) =
      C (x 0) (lapse F v x) (v (x 0)) (deriv v (x 0)-v (x 0)/x 0)
        (β (x 0)) ζ ((massJet F x).laplace (Real.sin (x 1)) (Real.cos (x 1)))
        (a x) (b x/Real.sin (x 1)) (sphereGrad (massJet F x) (Real.sin (x 1))) := by
  have hlapse := (contDiffAt_lapse hF hv hr hpos).differentiableAt (by norm_num)
  rw [constructed_metricJet hF hv hr hs hpos,
    tensorJet_eq_round (lapse F v) v (radial (normalEntry v β))
      (correctedComponent v a) (correctedComponent v b) x hlapse (hv.differentiableAt (by norm_num))
      ((diffAt_normalEntry hv hβ hr).comp x (coord 0).differentiableAt)
      (diffAt_correctedComponent hv ha hr) (lapse_pos hpos).ne',
    lapseJet_eq_mass hF hv hr hpos,roundTensor_correction hv hβ ha hb hr]
  exact computed_energy_eq_residual (massJet F x) hr (lapse_pos hpos).ne' hs
    (by simpa [A,massJet] using lapse_sq hpos) hheat

end
end CKSRealizedRound

end

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma bendingV_tail_deriv {R r : ℝ} (hR : 0 < R) (hr : 2*R^2 < r) :
    deriv (bendingV R) r = 0 := by
  have hh : bendingV R =ᶠ[𝓝 r] (fun _ => 0) := by
    filter_upwards [eventually_gt_nhds hr] with y hy
    exact bendingV_tail hR hy.le
  rw [hh.deriv_eq]
  exact deriv_const _ _

lemma bendingBeta_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    bendingBeta R r = 0 := by
  apply beta_zero
  exact (le_div_iff₀ (by linarith : 0 < R)).mpr (by nlinarith)

lemma bendingZeta_tail {R r : ℝ} (hR : 12 ≤ R) (hr : 2*R^2 ≤ r) :
    bendingZeta R r = 1 := by
  apply zeta_one
  exact (le_div_iff₀ (by linarith : 0 < R)).mpr (by nlinarith)

lemma vanishing_tail_energy_bound {r u F M B Δ a b : ℝ} {grad : Vec2}
    (hr : 1 ≤ r) (hu : 0 < u) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hm : |F| ≤ M) (hR : 4*M ≤ r) (hmass : u^2 = A 0-2*F/r)
    (hΔ : |Δ| ≤ B) (hg : ‖grad‖ ≤ B) :
    |C r u 0 0 0 1 Δ a b grad| ≤ (2+4*M*B+12*B^2)/(r^3*Real.sqrt r) := by
  have hrp : 0 < r := by linarith
  have hl := (lapse_comparison hrp hm hR hmass).1
  have hi := inv_u_sq_le_two hu hl
  have hd := abs_reciprocal_difference hrp hu hm hl hmass
  have hd' : |1-1/u^2| ≤ 4*M/r := by simpa [A] using hd
  have hterm : |Δ/r^3*(1-1/u^2)| ≤ 4*M*B/r^4 := by
    rw [abs_mul,abs_div,abs_of_pos (pow_pos hrp _)]
    calc
      _ ≤ (B/r^3)*(4*M/r) := mul_le_mul (div_le_div_of_nonneg_right hΔ (pow_nonneg hrp.le _))
        hd' (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hg2 : ‖grad‖^2 ≤ B^2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have hi2 : (1/u^2)^2 ≤ 4 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1/u^2) hi 2
    norm_num at hh ⊢
    exact hh
  have hgrad : 3*‖grad‖^2/(r^4*u^4) ≤ 12*B^2/r^4 := by
    calc
      _ = (3*‖grad‖^2/r^4)*(1/u^2)^2 := by ring
      _ ≤ (3*B^2/r^4)*4 := mul_le_mul (by gcongr) hi2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hs : Real.sqrt r ≤ r := (Real.sqrt_le_iff).mpr ⟨hrp.le,by nlinarith⟩
  have hp : 0 < r^3*Real.sqrt r := by positivity
  have hpoly : r^3*Real.sqrt r ≤ r^4 := by calc
    _ ≤ r^3*r := by gcongr
    _ = _ := by ring
  have hsum : |C r u 0 0 0 1 Δ a b grad| ≤
      2/(r^3*Real.sqrt r) + (4*M*B+12*B^2)/r^4 := by
    simp only [C,A,zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,zero_div,
      add_zero,one_pow,div_one,zero_add,sub_zero]
    rw [add_div]
    obtain ⟨hlΔ,huΔ⟩ := abs_le.mp hterm
    have hpad : 0 ≤ 2/(r^3*Real.sqrt r) := by positivity
    have hgg : 0 ≤ 3*‖grad‖^2/(r^4*u^4) := by positivity
    have hmb : 0 ≤ 4*M*B/r^4 := by positivity
    have hbb : 0 ≤ 12*B^2/r^4 := by positivity
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ ≤ _ := hsum
    _ ≤ 2/(r^3*Real.sqrt r)+(4*M*B+12*B^2)/(r^3*Real.sqrt r) := by
      gcongr
    _ = _ := by ring

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Finset CKSInducedSphere
open scoped RealInnerProductSpace ContDiff

lemma normal_sq {x : E} (hx : x ≠ 0) : ∑ i : Ix, normal x i ^ 2 = 1 := by
  simp only [normal,div_pow,← Finset.sum_div]
  have hs : (∑ i : Ix, x i ^ 2) = ‖x‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm
  rw [hs]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

end
end CKSADM

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRound CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

def constructedTensorJet (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : Point) : TensorJet :=
  tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
    (radial (normalEntry (bendingV R) (bendingBeta R)))
    (correctedComponent (bendingV R) (outerA f₀ R))
    (correctedComponent (bendingV R) (outerPhi f₀ R)) x

end
end CKSSphericalChart

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter MeasureTheory CKSSphericalHarmonics CKSSphericalChart CKSBending CKSInducedSphere
open scoped Topology ContDiff

lemma unitVector_norm {x : E} (hx : x ≠ 0) : ‖unitVector x‖ = 1 := by
  simpa only [unitVector,Metric.mem_sphere,dist_zero_right] using normalize_mem_sphere x hx

lemma unitVector_smooth {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ unitVector x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

lemma cartMass_smooth (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0 < R) {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (cartMass f₀ m R) x := by
  have hn : ContDiffAt ℝ ∞ (fun x : E => ‖x‖) x := contDiffAt_norm ℝ hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : ContDiffAt ℝ ∞ (fun y : E => heatTime R ‖y‖) x :=
    ((heatTime_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  have hc : ContDiffAt ℝ ∞ (fun y : E => paddingMass R ‖y‖) x :=
    ((paddingMass_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  have hu : unitVector x ≠ 0 := by
    intro hh
    have hq := unitVector_norm hx
    rw [hh,norm_zero] at hq
    norm_num at hq
  have hz : (heatTime R ‖x‖,unitVector x) ∈ heatDomain := hu
  have hh : ContDiffAt ℝ ∞ (fun z : ℝ × E => canonicalF f₀ m z.1 z.2)
      (heatTime R ‖x‖,unitVector x) :=
    (canonicalF_joint f₀ hf₀ m).contDiffAt (heatDomain_open.mem_nhds hz)
  have hcomp := hh.comp x (ht.prodMk (unitVector_smooth hx))
  exact hc.add hcomp

end
end CKSADM

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart
open scoped Topology ContDiff

lemma unitVector_ne {x : E} (hx : x ≠ 0) : unitVector x ≠ 0 := by
  intro hh
  have h := unitVector_norm hx
  simp [hh] at h

end
end CKSADM

end

end OAI
end

section
namespace OAI


noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRound CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

def constructedEnergy (f₀ : C(Sphere,ℝ)) (m R : ℝ) (x : Point) : ℝ :=
  (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x).energy
    (constructedTensorJet f₀ m R x)

theorem constructed_energy_tail_bound (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ C : ℝ, 12 ≤ R₀ ∧ 0 ≤ C ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : Point,
      2*R^2 < x 0 → Real.sin (x 1) ≠ 0 →
      |constructedEnergy f₀ m R x| ≤ C/((x 0)^3*Real.sqrt (x 0)) := by
  obtain ⟨M,B,T,hM,hB,hT,hbound⟩ := outer_uniform_bounds f₀ hf₀ m
  refine ⟨max 12 (4*M),2+4*M*B+12*B^2,le_max_left _ _,by positivity,?_⟩
  intro R hR x hr hs
  have hR12 : 12 ≤ R := (le_max_left _ _).trans hR
  have hRM : 4*M ≤ R := (le_max_right _ _).trans hR
  have hRp : 0 < R := by linarith
  have hrp : 0 < x 0 := lt_trans (by positivity : 0 < 2*R^2) hr
  have hr3 : 3*R ≤ x 0 := by nlinarith
  have hrM : 4*M ≤ x 0 := by linarith
  have hv0 := bendingV_tail hRp hr.le
  have hvp := bendingV_tail_deriv hRp hr
  have hβ0 := bendingBeta_tail hR12 hr.le
  have hζ1 := bendingZeta_tail hR12 hr.le
  obtain ⟨hm,hΔ,hg,ht⟩ := hbound R hR12 x hr3 hs
  have hpos : 0 < radicand (outerMass f₀ m R) (bendingV R) x := by
    have hq : 2*outerMass f₀ m R x/x 0 ≤ 1/2 :=
      (div_le_iff₀ hrp).mpr (by linarith [(le_abs_self _).trans hm])
    dsimp [radicand,radial]
    nlinarith [sq_nonneg (bendingV R (x 0))]
  have hF : ContDiffAt ℝ 2 (outerMass f₀ m R) x :=
    ((outerMass_smooth f₀ hf₀ m hRp).contDiffAt (positiveChart_open.mem_nhds hrp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hv : ContDiffAt ℝ 2 (bendingV R) (x 0) :=
    ((bendingV_smooth hRp).contDiffAt (isOpen_Ioi.mem_nhds hrp)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have ha := ((outerA_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hrp)).differentiableAt (by simp)
  have hb := ((outerPhi_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hrp)).differentiableAt (by simp)
  have he := smooth_energy_residual hF hv ((bendingBeta_smooth R).differentiable (by simp) _) ha hb
    hrp.ne' hs hpos (outerMass_heat f₀ hf₀ m hRp hr3 hs)
  rw [hv0,hvp,hβ0,hζ1] at he
  simp only [zero_div,sub_zero] at he
  change |(metricJet _ x).energy _| ≤ _
  rw [constructedTensorJet,he]
  apply vanishing_tail_energy_bound (by linarith) (lapse_pos hpos) hM hB hm hrM _ hΔ hg
  simpa only [A,radial,hv0] using lapse_sq hpos

end
end CKSSphericalChart

end











noncomputable section
namespace CKSRealizedRound
noncomputable section
open Matrix CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma contDiffAt_normalEntry {v β : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ ∞ v r) (hβ : ContDiffAt ℝ ∞ β r) (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (normalEntry v β) r := by
  exact (hv.derivWithin (m := ∞) (by simp)).add
    (hβ.div (contDiffAt_id.pow 2) (pow_ne_zero _ hr))

lemma contDiffAt_correctionCoeff {v : ℝ → ℝ} {r : ℝ}
    (hv : ContDiffAt ℝ ∞ v r) (hr : r ≠ 0) :
    ContDiffAt ℝ ∞ (correctionCoeff v) r := by
  exact (contDiffAt_id.mul ((hv.derivWithin (m := ∞) (by simp)).sub
    (hv.div contDiffAt_id hr))).div (contDiffAt_const.add (hv.pow 2))
      (ne_of_gt (by positivity))

end
end CKSRealizedRound

end



noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma normal_smoothAt {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (normal : E → Fin 3 → ℝ) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact (EuclideanSpace.proj i).contDiff.contDiffAt.div (contDiffAt_norm ℝ hx)
    (norm_ne_zero_iff.mpr hx)
lemma radicand_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (radicand f₀ m R) x := by
  have hn := contDiffAt_norm ℝ hx (n := ∞)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv := ((bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)).comp x hn
  exact (contDiffAt_const.add (hv.pow 2)).sub
    ((contDiffAt_const.mul (cartMass_smooth f₀ hf₀ m hR hx)).div hn hr.ne')
lemma metric_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (hp : radicand f₀ m R x ≠ 0) :
    ContDiffAt ℝ ∞ (metric f₀ m R) x := by
  have hi := (radicand_smoothAt f₀ hf₀ m hR hx).inv hp
  have hn := normal_smoothAt hx
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  change ContDiffAt ℝ ∞ (fun y => (if i=j then 1 else 0) +
    ((radicand f₀ m R y)⁻¹-1)*(normal y i*normal y j)) x
  exact contDiffAt_const.add ((hi.sub contDiffAt_const).mul
    ((contDiffAt_pi.mp hn i).mul (contDiffAt_pi.mp hn j)))
lemma cartTensorHeat_component_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (i j : Ix) :
    ContDiffAt ℝ ∞ (fun y : E => canonicalT f₀ (heatTime R ‖y‖) (unitVector y) i j) x := by
  have hh : ContDiffAt ℝ ∞ (heatTime R) ‖x‖ :=
    (heatTime_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))
  have ht : ContDiffAt ℝ ∞ (fun y : E => heatTime R ‖y‖) x :=
    hh.comp x (contDiffAt_norm ℝ hx (n:=∞))
  have hz : (heatTime R ‖x‖,unitVector x) ∈ heatDomain := unitVector_ne hx
  have hc : ContDiffAt ℝ ∞ (fun z : ℝ × E => canonicalT f₀ z.1 z.2 i j)
      (heatTime R ‖x‖,unitVector x) :=
    (canonicalT_joint f₀ hf₀ i j).contDiffAt (heatDomain_open.mem_nhds hz)
  exact hc.comp x (ht.prodMk (unitVector_smooth hx))
lemma cartTensorHeat_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => canonicalT f₀ (heatTime R ‖y‖) (unitVector y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact cartTensorHeat_component_smoothAt f₀ hf₀ hR hx i j
lemma tensor_smoothAt (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 0<R) {x : E} (hx : x ≠ 0) (hp : radicand f₀ m R x ≠ 0) :
    ContDiffAt ℝ ∞ (tensor f₀ m R) x := by
  have hn := contDiffAt_norm ℝ hx (n:=∞)
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv := (bendingV_smooth hR).contDiffAt (isOpen_Ioi.mem_nhds hr)
  have hL := (contDiffAt_normalEntry hv (bendingBeta_smooth R).contDiffAt hr.ne').comp x hn
  have hc := (contDiffAt_correctionCoeff hv hr.ne').comp x hn
  have hU := radicand_smoothAt f₀ hf₀ m hR hx
  have hnormal := normal_smoothAt hx
  have hT := cartTensorHeat_smoothAt f₀ hf₀ hR hx
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hi := contDiffAt_pi.mp hnormal i
  have hj := contDiffAt_pi.mp hnormal j
  exact (((hL.div hU hp).mul (hi.mul hj)).add
    (((hv.comp x hn).div hn hr.ne').mul (contDiffAt_const.sub (hi.mul hj)))).add
    ((hc.div (hn.pow 2) (pow_ne_zero _ hr.ne')).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hT i) j))
lemma rankOne_positive {n : Fin 3 → ℝ} (hn : ∑ i, n i^2=1)
    {a : ℝ} (ha : 0<a) : (1+(a-1) • vecMulVec n n : Mat).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [Matrix.add_apply, Matrix.vecMulVec, mul_comm,
      mul_assoc, Matrix.one_apply, eq_comm]
  · intro v hv
    have hq : 0 < ∑ i, v i^2 := by
      have h := (Matrix.PosDef.one : (1 : Mat).PosDef).dotProduct_mulVec_pos hv
      simpa [dotProduct, pow_two] using h
    have hcs : (∑ i, n i*v i)^2 ≤ ∑ i, v i^2 := by
      simpa only [hn,one_mul] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ n v
    have he : star v ⬝ᵥ ((1+(a-1) • vecMulVec n n : Mat) *ᵥ v) =
        (∑ i, v i^2)+(a-1)*(∑ i, n i*v i)^2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.vecMulVec, Fin.sum_univ_succ, Matrix.one_apply]
      ring
    rw [he]
    by_cases hh : 1 ≤ a
    · have hnn := mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg (∑ i, n i*v i))
      linarith
    · have hnn := mul_nonneg (show 0≤1-a by linarith) (sub_nonneg.mpr hcs)
      have hp := mul_pos ha hq
      nlinarith
lemma metric_positive {f₀ : C(Sphere,ℝ)} {m R : ℝ} {x : E} (hx : x ≠ 0)
    (hp : 0 < radicand f₀ m R x) : (metric f₀ m R x).PosDef :=
  rankOne_positive (normal_sq hx) (inv_pos.mpr hp)

end
end CKSCartesianOuter

end














noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma sphericalMap_euclidean (x : PhysicalPoint) :
    toPoint.symm (sphericalMap x) = x 0 • sphereParam x := toPoint.symm_apply_apply _
lemma sphericalMap_norm {x : PhysicalPoint} (hx : 0 < x 0) :
    ‖toPoint.symm (sphericalMap x)‖ = x 0 := by
  rw [sphericalMap_euclidean,norm_smul,Real.norm_eq_abs,abs_of_pos hx,sphereParam_norm,mul_one]

end
end CKSCartesianOuter

end










noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
theorem sphericalMap_surjective_radial (y : E) :
    ∃ x : PhysicalPoint, x 0=‖y‖ ∧ sphericalMap x=toPoint y := by
  let z : ℂ := ⟨y 0,y 1⟩
  let w : ℂ := ⟨y 2,‖z‖⟩
  have hw : ‖w‖=‖y‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm,Complex.normSq_apply,EuclideanSpace.real_norm_sq_eq]
    change y 2*y 2+‖z‖*‖z‖=∑ i,y i^2
    rw [←pow_two ‖z‖,Complex.sq_norm,Complex.normSq_apply]
    simp only [z,Fin.sum_univ_three]
    ring
  have hs : ‖y‖*Real.sin w.arg=‖z‖ := by
    rw [←hw]
    exact Complex.norm_mul_sin_arg w
  have hc : ‖y‖*Real.cos w.arg=y 2 := by
    rw [←hw]
    exact Complex.norm_mul_cos_arg w
  have hz0 : ‖z‖*Real.cos z.arg=y 0 := Complex.norm_mul_cos_arg z
  have hz1 : ‖z‖*Real.sin z.arg=y 1 := Complex.norm_mul_sin_arg z
  refine ⟨![‖y‖,w.arg,z.arg],rfl,?_⟩
  apply toPoint.symm.injective
  rw [toPoint.symm_apply_apply]
  change (‖y‖ • sphereParam ![‖y‖,w.arg,z.arg] : E)=y
  ext i
  fin_cases i
  · change ‖y‖*(Real.sin w.arg*Real.cos z.arg)=y 0
    rw [←mul_assoc,hs,hz0]
  · change ‖y‖*(Real.sin w.arg*Real.sin z.arg)=y 1
    rw [←mul_assoc,hs,hz1]
  · change ‖y‖*Real.cos w.arg=y 2
    exact hc
end
end CKSCartesianOuter

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
structure ContinuousMetricJetAt (g : PhysicalPoint → CKSRound.MetricJet) (x : PhysicalPoint) : Prop where
  inv : ∀ i j, ContinuousAt (fun y => (g y).inv i j) x
  d : ∀ a i j, ContinuousAt (fun y => (g y).d a i j) x
  dd : ∀ a b i j, ContinuousAt (fun y => (g y).dd a b i j) x
structure ContinuousTensorJetAt (k : PhysicalPoint → CKSRound.TensorJet) (x : PhysicalPoint) : Prop where
  val : ∀ i j, ContinuousAt (fun y => (k y).val i j) x
  d : ∀ a i j, ContinuousAt (fun y => (k y).d a i j) x
lemma ContinuousMetricJetAt.gamma {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a i j : Fin 3) :
    ContinuousAt (fun y => (g y).gamma a i j) x := by
  have hi := h.inv
  have hd := h.d
  unfold CKSRound.MetricJet.gamma
  fun_prop
lemma ContinuousMetricJetAt.dInv {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a i j : Fin 3) :
    ContinuousAt (fun y => (g y).dInv a i j) x := by
  have hi := h.inv
  have hd := h.d
  unfold CKSRound.MetricJet.dInv
  fun_prop
lemma ContinuousMetricJetAt.dGamma {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (a b i j : Fin 3) :
    ContinuousAt (fun y => (g y).dGamma a b i j) x := by
  have hi := h.inv
  have hd := h.d
  have hdd := h.dd
  have hdi := h.dInv
  unfold CKSRound.MetricJet.dGamma
  fun_prop
lemma ContinuousMetricJetAt.ricci {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (i j : Fin 3) :
    ContinuousAt (fun y => (g y).ricci i j) x := by
  have hc := h.gamma
  have hd := h.dGamma
  unfold CKSRound.MetricJet.ricci
  fun_prop
lemma ContinuousMetricJetAt.scalar {g : PhysicalPoint → CKSRound.MetricJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) : ContinuousAt (fun y => (g y).scalar) x := by
  have hi := h.inv
  have hr := h.ricci
  unfold CKSRound.MetricJet.scalar
  fun_prop
lemma ContinuousMetricJetAt.trace {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).trace (k y)) x := by
  have hi := h.inv
  have hv := hk.val
  unfold CKSRound.MetricJet.trace
  fun_prop
lemma ContinuousMetricJetAt.normSq {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).normSq (k y)) x := by
  have hi := h.inv
  have hv := hk.val
  unfold CKSRound.MetricJet.normSq
  fun_prop

lemma ContinuousMetricJetAt.energy {g : PhysicalPoint → CKSRound.MetricJet}
    {k : PhysicalPoint → CKSRound.TensorJet} {x : PhysicalPoint}
    (h : ContinuousMetricJetAt g x) (hk : ContinuousTensorJetAt k x) :
    ContinuousAt (fun y => (g y).energy (k y)) x := by
  have hs := h.scalar
  have ht := h.trace hk
  have hn := h.normSq hk
  unfold CKSRound.MetricJet.energy
  fun_prop

lemma physicalMetricJet_continuousAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) : ContinuousMetricJetAt (physicalMetricJet G) x := by
  have hc (i j) := contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  refine ⟨fun i j => (matrix_inv_component_contDiffAt hg h0 i j).continuousAt,?_,?_⟩
  · intro a i j
    exact (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
  · intro a b i j
    exact (contDiffAt_D (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis b))
      (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt
lemma physicalTensorJet_continuousAt {K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hk : ContDiffAt ℝ ∞ K x) : ContinuousTensorJetAt (physicalTensorJet K) x := by
  have hc (i j) := contDiffAt_pi.mp (contDiffAt_pi.mp hk i) j
  refine ⟨fun i j => (hc i j).continuousAt,?_⟩
  intro a i j
  exact (contDiffAt_D (hc i j) (m := ∞) (by simp) (CKSRealizedRound.basis a)).continuousAt

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma regular_angular_approximation (x : PhysicalPoint) (hs : Real.sin (x 1)=0) :
    ∃ u : ℕ → PhysicalPoint, Tendsto u atTop (𝓝 x) ∧
      ∀ n, u n 0=x 0 ∧ Real.sin (u n 1)≠0 := by
  have hc : Real.cos (x 1)≠0 := by
    intro hh
    have h := Real.sin_sq_add_cos_sq (x 1)
    simp [hs,hh] at h
  let u : ℕ → PhysicalPoint := fun n => ![x 0,x 1+1/((n:ℝ)+1),x 2]
  refine ⟨u,?_,?_⟩
  · apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · simpa [u] using
        (tendsto_const_nhds (x := x 1)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact tendsto_const_nhds
  · intro n
    refine ⟨rfl,?_⟩
    change Real.sin (x 1+1/((n:ℝ)+1))≠0
    rw [Real.sin_add,hs,zero_mul,zero_add]
    apply mul_ne_zero hc
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    have hle : (1:ℝ)/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith [Real.pi_gt_three]

end
end CKSCartesianOuter

end






















































noncomputable section
namespace CKSCartesianOuter
noncomputable section
open Set Filter Matrix CKSADM CKSInducedSphere CKSSphericalHarmonics CKSSphericalChart CKSBending
  CKSRealizedRound CKSAngularGeometry CKSCalculus
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma spherical_energy_bound_extend_poles {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G (sphericalMap x)) (hk : ContDiffAt ℝ ∞ K (sphericalMap x))
    (h0 : (G (sphericalMap x)).det≠0) {b : ℝ}
    (hb : ∀ p : PhysicalPoint, p 0=x 0 → Real.sin (p 1)≠0 →
      |(physicalMetricJet G (sphericalMap p)).energy
        (physicalTensorJet K (sphericalMap p))| ≤ b) :
    |(physicalMetricJet G (sphericalMap x)).energy
      (physicalTensorJet K (sphericalMap x))| ≤ b := by
  by_cases hs : Real.sin (x 1)≠0
  · exact hb x rfl hs
  · obtain ⟨u,hu,hreg⟩ := regular_angular_approximation x (not_ne_iff.mp hs)
    have hc := ((physicalMetricJet_continuousAt hg h0).energy
      (physicalTensorJet_continuousAt hk)).abs
    exact le_of_tendsto (hc.tendsto.comp (sphericalMap_smooth.continuous.continuousAt.tendsto.comp hu))
      (Eventually.of_forall fun n => hb (u n) (hreg n).1 (hreg n).2)

theorem constructed_cartesian_energy_tail_bound (f₀ : C(Sphere,ℝ))
    (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ C : ℝ, 12 ≤ R₀ ∧ 0 ≤ C ∧ ∀ R : ℝ, R₀ ≤ R → ∀ y : E,
      2*R^2 < ‖y‖ →
      |(physicalMetricJet (physicalMetric f₀ m R) (toPoint y)).energy
        (physicalTensorJet (physicalTensor f₀ m R) (toPoint y))| ≤
        C/(‖y‖^3*Real.sqrt ‖y‖) := by
  obtain ⟨R₁,hR₁,hpos⟩ := cartesian_radicand_positive f₀ hf₀ m
  obtain ⟨R₂,C,hR₂,hC,hbound⟩ := constructed_energy_tail_bound f₀ hf₀ m
  refine ⟨max R₁ R₂,C,hR₁.trans (le_max_left _ _),hC,?_⟩
  intro R hR y hy
  have hRR₁ : R₁≤R := (le_max_left _ _).trans hR
  have hRR₂ : R₂≤R := (le_max_right _ _).trans hR
  have hR12 : 12≤R := hR₁.trans hRR₁
  have hRp : 0<R := by linarith
  have hy3 : 3*R≤‖y‖ := by nlinarith
  have hyp : y≠0 := norm_pos_iff.mp (by linarith : 0<‖y‖)
  obtain ⟨x,hxr,hx⟩ := sphericalMap_surjective_radial y
  have hpx := hpos R hRR₁ y hy3
  have hg : ContDiffAt ℝ ∞ (physicalMetric f₀ m R) (sphericalMap x) := by
    rw [hx]
    exact (metric_smoothAt f₀ hf₀ m hRp hyp hpx.ne').comp (toPoint y) toPoint.symm.contDiff.contDiffAt
  have hk : ContDiffAt ℝ ∞ (physicalTensor f₀ m R) (sphericalMap x) := by
    rw [hx]
    exact (tensor_smoothAt f₀ hf₀ m hRp hyp hpx.ne').comp (toPoint y) toPoint.symm.contDiff.contDiffAt
  rw [←hx]
  apply spherical_energy_bound_extend_poles hg hk
  · change (metric f₀ m R (toPoint.symm (sphericalMap x))).det≠0
    rw [hx,toPoint.symm_apply_apply]
    exact (metric_positive hyp hpx).det_pos.ne'
  · intro p hpr hs
    have hpr' : 0<p 0 := by rw [hpr,hxr]; linarith
    have hprR : 3*R≤p 0 := by rw [hpr,hxr]; exact hy3
    have hp := hpos R hRR₁ (toPoint.symm (sphericalMap p)) (by rwa [sphericalMap_norm hpr'])
    rw [spherical_physical_energy f₀ hf₀ m hRp hpr' hs hp]
    have hb := hbound R hRR₂ p (by rwa [hpr,hxr]) hs
    simpa only [constructedEnergy,constructedTensorJet,hpr,hxr] using hb
end
end CKSCartesianOuter

end





























end OAI
end

theorem solution : type_of% @OAI.CKSCartesianOuter.constructed_cartesian_energy_tail_bound := @OAI.CKSCartesianOuter.constructed_cartesian_energy_tail_bound
