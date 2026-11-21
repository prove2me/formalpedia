-- Prove2me | solution 1 for MasulloRH.dyadic_shell_mellin_diagonal_cutoff_order
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:15:53.417105+00:00
-- url     : https://prove2.me/submissions/40551691-e562-4fe7-a7ba-12e89fb2fb82

import Theorems.Thm_MasulloRH_smooth_compact_dyadic_shell_mellin_counterexample
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Positivity
section

open MeasureTheory Measure Set Filter
open scoped Topology

namespace MasulloDiagonal

private noncomputable abbrev ray := volume.restrict (Ioi (0 : ℝ))

private theorem dilation_quotient_qmp :
    QuasiMeasurePreserving (fun z : ℝ × ℝ => z.2 / z.1) (ray.prod ray) ray := by
  have hm : Measurable (fun z : ℝ × ℝ => z.2 / z.1) := measurable_snd.div measurable_fst
  refine ⟨hm, Measure.AbsolutelyContinuous.mk (fun {S} hS hzero => ?_)⟩
  rw [Measure.map_apply hm hS]
  apply Measure.measure_prod_null_of_ae_null (hm hS)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))] with r hr
  change 0 < r at hr
  have hdiv : QuasiMeasurePreserving (fun t : ℝ => t / r) volume volume := by
    refine ⟨measurable_id.div_const r, ?_⟩
    simp only [div_eq_mul_inv, Real.map_volume_mul_right (inv_ne_zero (ne_of_gt hr))]
    exact Measure.smul_absolutelyContinuous
  exact (hdiv.restrict (s := Ioi (0 : ℝ)) (t := Ioi (0 : ℝ))
    (fun _ ht => div_pos ht hr)).preimage_null hzero

private theorem integral_div_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), f (t / r) = r • ∫ t in Ioi (0 : ℝ), f t := by
  simpa only [div_eq_mul_inv, mul_comm r⁻¹, mul_zero, zero_mul, inv_inv] using
    integral_comp_mul_left_Ioi f 0 (inv_pos.mpr hr)

/-- Multiplicative convolution of two absolutely Mellin integrable complex functions. -/
theorem hasMellin_multiplicative_convolution (k f : ℝ → ℂ) (s : ℂ)
    (hks : MellinConvergent k s) (hfs : MellinConvergent f s) :
    HasMellin (fun t : ℝ => ∫ r in Ioi (0 : ℝ), (k r / (r : ℂ)) * f (t / r))
      s (mellin k s * mellin f s) := by
  let w (t : ℝ) := (t : ℂ) ^ (s - 1)
  let K (r : ℝ) := w r * k r
  let F (t : ℝ) := w t * f t
  have hK : Integrable K ray := hks
  have hF : Integrable F ray := hfs
  let H (z : ℝ × ℝ) := (K z.1 / (z.1 : ℂ)) * F (z.2 / z.1)
  have hHmeas : AEStronglyMeasurable H (ray.prod ray) := by
    apply AEStronglyMeasurable.mul
    · exact (hK.aestronglyMeasurable.comp_quasiMeasurePreserving quasiMeasurePreserving_fst).div₀
        (Complex.continuous_ofReal.measurable.comp measurable_fst).aestronglyMeasurable
    · exact hF.aestronglyMeasurable.comp_quasiMeasurePreserving dilation_quotient_qmp
  have hH : Integrable H (ray.prod ray) := by
    apply (integrable_prod_iff hHmeas).2
    constructor
    · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))] with r hr
      change 0 < r at hr
      have hfdiv : IntegrableOn (fun t : ℝ => F (t / r)) (Ioi (0 : ℝ)) := by
        simpa only [div_eq_mul_inv, mul_comm r⁻¹] using
          (integrableOn_Ioi_comp_mul_left_iff F 0 (inv_pos.mpr hr)).2 (by simpa only [mul_zero] using! hF)
      exact hfdiv.const_mul (K r / (r : ℂ))
    · apply (hK.norm.mul_const (∫ u, ‖F u‖ ∂ray)).congr
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))] with r hr
      change 0 < r at hr
      change ‖K r‖ * _ = ∫ t in Ioi (0 : ℝ), ‖(K r / (r : ℂ)) * F (t / r)‖
      simp only [norm_mul, integral_const_mul, integral_div_Ioi (fun t => ‖F t‖) hr,
        norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, smul_eq_mul]
      field_simp [ne_of_gt hr]
  have hfactor (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
      w t * (k r / (r : ℂ) * f (t / r)) = H (r,t) := by
    have hw : w r * w (t / r) = w t := by
      dsimp [w]
      rw [← Complex.mul_cpow_ofReal_nonneg hr.le (div_nonneg ht.le hr.le),
        ← Complex.ofReal_mul, mul_div_cancel₀ t hr.ne']
    dsimp [H, K, F]
    rw [← hw]
    ring
  have houter {t : ℝ} (ht : 0 < t) :
      w t * (∫ r in Ioi (0 : ℝ), (k r / (r : ℂ)) * f (t / r)) = ∫ r, H (r,t) ∂ray := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => hfactor r t hr ht)
  have hinner {r : ℝ} (hr : 0 < r) :
      ∫ t, H (r,t) ∂ray = K r * (∫ u, F u ∂ray) := by
    change (∫ t in Ioi (0 : ℝ), (K r / (r : ℂ)) * F (t/r)) = _
    rw [integral_const_mul, integral_div_Ioi F hr, Complex.real_smul]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  constructor
  · exact hH.integral_prod_right.congr (by
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
      exact (houter ht).symm)
  · calc
      _ = ∫ t, ∫ r, H (r,t) ∂ray ∂ray := setIntegral_congr_fun measurableSet_Ioi (fun _ ht => houter ht)
      _ = ∫ r, ∫ t, H (r,t) ∂ray ∂ray := (integral_integral_swap (f := fun r t => H (r,t)) hH).symm
      _ = ∫ r, K r * (∫ u, F u ∂ray) ∂ray := setIntegral_congr_fun measurableSet_Ioi (fun _ hr => hinner hr)
      _ = _ := integral_mul_const _ _

end MasulloDiagonal
end

section

open MeasureTheory Set

namespace MasulloRH

private theorem diagonal_dilate_integrand {r u : ℝ} (hr : 0 < r) (hu : 0 < u)
    (k f w : ℝ → ℂ) :
    r • ((w (r*u) / ((r*u:ℝ):ℂ)) * ((k r / (r:ℂ)) * f ((r*u) / r))) =
      (f u / (u:ℂ)) * ((k r / (r:ℂ)) * w (r*u)) := by
  have hur : (u:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hrr : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simp only [mul_div_cancel_left₀ _ hr.ne', Complex.real_smul, Complex.ofReal_mul]
  field_simp

private theorem diagonal_dilate {r : ℝ} (hr : 0 < r) (k f w : ℝ → ℂ) :
    (∫ x in Ioi (0:ℝ), (w x / (x:ℂ)) * ((k r / (r:ℂ)) * f (x / r))) =
      ∫ u in Ioi (0:ℝ), (f u / (u:ℂ)) * ((k r / (r:ℂ)) * w (r*u)) := by
  let H (x : ℝ) : ℂ := (w x / (x:ℂ)) * ((k r / (r:ℂ)) * f (x / r))
  have h := integral_comp_mul_left_Ioi' H 0 hr
  simp only [mul_zero] at h
  change (∫ x in Ioi (0:ℝ), H x) = _
  rw [← h, ← integral_smul]
  exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => diagonal_dilate_integrand hr hu k f w)

private theorem integrable_of_positive_shear {L R : ℝ × ℝ → ℂ}
    (hL : Measurable L)
    (hrel : ∀ r u : ℝ, 0 < r → 0 < u → r • L (r*u,r) = R (u,r))
    (hR : Integrable R ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) :
    Integrable L ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff' hL.aestronglyMeasurable).2
  constructor
  · filter_upwards [hR.prod_left_ae, ae_restrict_mem measurableSet_Ioi] with r hir hr
    have hc : IntegrableOn (fun u : ℝ => r • L (r*u,r)) (Ioi 0) :=
      hir.congr (ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => (hrel r u hr hu).symm))
    change 0 < r at hr
    have hs := (integrable_fun_smul_iff hr.ne' (fun u : ℝ => L (r*u,r))).1 hc
    simpa only [mul_zero, IntegrableOn] using
      (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => L (x,r)) 0 hr).1 hs
  · apply hR.integral_norm_prod_right.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have h := integral_comp_mul_left_Ioi' (fun x : ℝ => ‖L (x,r)‖) 0 hr
    rw [mul_zero, ← integral_smul] at h
    rw [← h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change ‖R (u,r)‖ = r * ‖L (r*u,r)‖
    rw [← hrel r u hr hu, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

/-- Fubini in the two coordinate systems requires only one absolute integral. -/
theorem multiplicative_convolution_diagonal_pairing (k f w : ℝ → ℂ)
    (hk : Measurable k) (hf : Measurable f) (hw : Measurable w)
    (hright : Integrable (fun z : ℝ × ℝ =>
      (f z.1 / (z.1 : ℂ)) * ((k z.2 / (z.2 : ℂ)) * w (z.2 * z.1)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) :
    (∫ x in Ioi (0:ℝ), (w x / (x:ℂ)) * (∫ r in Ioi (0:ℝ), (k r / (r:ℂ)) * f (x/r))) =
      ∫ u in Ioi (0:ℝ), (f u / (u:ℂ)) * (∫ r in Ioi (0:ℝ), (k r / (r:ℂ)) * w (r*u)) := by
  have hleft : Integrable (fun z : ℝ × ℝ =>
      (w z.1 / (z.1 : ℂ)) * ((k z.2 / (z.2 : ℂ)) * f (z.1 / z.2)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    integrable_of_positive_shear (by fun_prop) (fun _ _ hr hu => diagonal_dilate_integrand hr hu k f w) hright
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (f := fun x r : ℝ => (w x / (x:ℂ)) * ((k r / (r:ℂ)) * f (x/r))) hleft,
      integral_integral_swap (f := fun u r : ℝ => (f u / (u:ℂ)) * ((k r / (r:ℂ)) * w (r*u))) hright]
  exact setIntegral_congr_fun measurableSet_Ioi (fun _ hr => diagonal_dilate hr k f w)

end MasulloRH

namespace MasulloRH

/-- A power bound on the second input gives absolute integrability of the diagonal pairing
from the two separate absolute Mellin integrals. -/
theorem multiplicative_diagonal_pairing_integrable (k f w : ℝ → ℂ) (a C : ℝ)
    (hk : Measurable k) (hf : Measurable f) (hw : Measurable w)
    (hkM : MellinConvergent k (a : ℂ)) (hfM : MellinConvergent f (a : ℂ))
    (hC : ∀ t : ℝ, 0 < t → ‖w t‖ ≤ C * t^a) :
    Integrable (fun z : ℝ × ℝ =>
      (f z.1 / (z.1 : ℂ)) * ((k z.2 / (z.2 : ℂ)) * w (z.2 * z.1)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let S := Ioi (0:ℝ)
  have hI (v : ℝ → ℂ) (hv : Measurable v) (hM : MellinConvergent v (a : ℂ)) :
      Integrable (fun t : ℝ => t^(a-1) * ‖v t‖) (volume.restrict S) := by
    simpa only [Complex.ofReal_re, IntegrableOn] using
      (mellin_convergent_iff_norm (T := S) (s := (a:ℂ)) (Subset.rfl) measurableSet_Ioi
        hv.aestronglyMeasurable).1 hM
  have hdom := ((hI f hf hfM).mul_prod (hI k hk hkM)).const_mul C
  apply hdom.mono' (by fun_prop)
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  rintro ⟨u,r⟩ ⟨hu,hr⟩
  change 0 < u at hu
  change 0 < r at hr
  simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, abs_of_pos hr]
  change ‖f u‖ / u * (‖k r‖ / r * ‖w (r*u)‖) ≤ C * ((u^(a-1) * ‖f u‖) * (r^(a-1) * ‖k r‖))
  calc
    _ ≤ ‖f u‖ / u * (‖k r‖ / r * (C * (r*u)^a)) := by gcongr; exact hC _ (mul_pos hr hu)
    _ = _ := by rw [Real.mul_rpow hr.le hu.le, Real.rpow_sub_one hu.ne', Real.rpow_sub_one hr.ne']; ring

end MasulloRH
end

section

open Set MeasureTheory

theorem MasulloDiagonal.kernel_bump_exists :
    ∃ b : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      tsupport b ⊆ Icc 1 2 ∧ (∀ t : ℝ, t ≤ 1 ∨ 2 ≤ t → b t = 0) ∧
      MellinConvergent (fun t => (b t : ℂ)) (1/2 : ℂ) ∧
      mellin (fun t => (b t : ℂ)) (1/2 : ℂ) ≠ 0 := by
  let φ : ContDiffBump (3/2 : ℝ) := ⟨1/8, 1/4, by norm_num, by norm_num⟩
  have hz (t : ℝ) (h : t ≤ 1 ∨ 2 ≤ t) : φ t = 0 := by
    apply φ.zero_of_le_dist
    change 1/4 ≤ dist t (3/2)
    rw [Real.dist_eq]
    rcases h with h | h
    · linarith [neg_le_abs (t-3/2)]
    · linarith [le_abs_self (t-3/2)]
  have hts : tsupport (fun t : ℝ => φ t) ⊆ Icc 1 2 := by
    rw [φ.tsupport_eq]
    intro t ht
    change dist t (3/2) ≤ 1/4 at ht
    rw [Real.dist_eq, abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let w (t : ℝ) := (max t 1) ^ (-(1/2:ℝ))
  let g (t : ℝ) := w t * φ t
  have hmax (t : ℝ) : 0 < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hw : Continuous w :=
    (continuous_id.max continuous_const).rpow_const fun t => Or.inl (hmax t).ne'
  have hg : Continuous g := hw.mul φ.continuous
  have hgc : HasCompactSupport g := φ.hasCompactSupport.mul_left (f:=w)
  have hg0 (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.rpow_nonneg (hmax t).le _) φ.nonneg
  have hcenter : φ (3/2) = 1 :=
    φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
  have hgp : 0 < ∫ t : ℝ, g t := by
    apply hg.integral_pos_of_hasCompactSupport_nonneg_nonzero hgc hg0 (x := (3/2:ℝ))
    simp only [g, hcenter, mul_one]
    exact (Real.rpow_pos_of_pos (hmax _) _).ne'
  have he : (1/2 : ℂ)-1 = ((-(1/2:ℝ) : ℝ) : ℂ) := by norm_num
  have hc : EqOn (fun t : ℝ => (t : ℂ) ^ ((1/2:ℂ)-1) • (φ t : ℂ))
      (fun t => (g t : ℂ)) (Ioi 0) := by
    intro t ht
    by_cases h : t ≤ 1
    · simp [g, hz t (Or.inl h)]
    · simp only [smul_eq_mul, g, w, max_eq_left (le_of_not_ge h), Complex.ofReal_mul,
        Complex.ofReal_cpow (le_of_lt ht), he]
  have hgp' : (∫ t in Ioi (0:ℝ), g t) = ∫ t, g t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro t ht
      have ht' : t ≤ 0 := le_of_not_gt ht
      simp [g, hz t (Or.inl (by linarith))])
  refine ⟨φ,φ.contDiff,φ.hasCompactSupport,hts,hz,?_,?_⟩
  · exact (integrableOn_congr_fun hc measurableSet_Ioi).mpr
      (hg.integrable_of_hasCompactSupport hgc).ofReal.integrableOn
  · unfold mellin
    rw [setIntegral_congr_fun measurableSet_Ioi hc]
    have hr : (∫ t in Ioi (0:ℝ), (g t:ℂ)) = Complex.ofReal (∫ t in Ioi (0:ℝ), g t) :=
      integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0:ℝ))) (f := g)
    rw [hr, hgp']
    exact Complex.ofReal_ne_zero.mpr hgp.ne'
end

section

open Filter Set MeasureTheory
open scoped Topology
namespace MasulloDiagonal

private theorem eventually_eq_localized_radial
    (v : ℕ → ℝ → ℂ) (g φ : ℝ → ℂ)
    (hφ : ∀ r : ℝ, 2 < r → φ r = 0)
    (hvg : ∀ a : ℝ, 0 < a → ∀ᶠ B : ℕ in atTop, ∀ x : ℝ, a ≤ x → v B x = g x)
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ B : ℕ in atTop, ∀ x : ℝ, a ≤ x →
      (∫ r in Ioi (0:ℝ), (φ r / (r:ℂ)) * v B (x/r)) = ∫ r in Ioi (0:ℝ), (φ r / (r:ℂ)) * g (x/r) := by
  filter_upwards [hvg (a/2) (by positivity)] with B hB
  intro x hx
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hrpos
  by_cases hr : 2 < r
  · simp [hφ _ hr]
  · have hx' : a/2 ≤ x/r := by
      calc
        a/2 ≤ a/r := div_le_div_of_nonneg_left ha.le hrpos (le_of_not_gt hr)
        _ ≤ x/r := div_le_div_of_nonneg_right hx (le_of_lt hrpos)
    exact congrArg (fun z => φ r / (r:ℂ) * z) (hB _ hx')

private theorem exhaust_windows (v : ℝ → ℂ) (s : ℂ) (hv : MellinConvergent v s) :
    Tendsto (fun j : ℕ => ∫ x in Ioo (1/((j:ℝ)+1)) ((j:ℝ)+1), (x:ℂ)^(s-1) * v x)
      atTop (𝓝 (mellin v s)) := by
  let E (j : ℕ) := Ioo (1/((j:ℝ)+1)) ((j:ℝ)+1)
  have hm : Monotone E := by
    intro i j hij
    have hij' : (i:ℝ)+1 ≤ (j:ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hij
    exact Ioo_subset_Ioo (one_div_le_one_div_of_le (by positivity) hij') hij'
  have hcover : (⋃ j : ℕ, E j) = Ioi (0:ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Ioi]
    constructor
    · rintro ⟨j,hj⟩
      exact (show (0:ℝ) < 1/((j:ℝ)+1) by positivity).trans hj.1
    · intro hx
      obtain ⟨j,hj⟩ := exists_nat_gt (max x (1/x))
      refine ⟨j,?_,?_⟩
      · have hj' : 1/x < (j:ℝ)+1 := by linarith [le_max_right x (1/x)]
        rw [div_lt_iff₀ hx] at hj'
        exact (div_lt_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+1)).mpr (by linarith only [hj',mul_comm ((j:ℝ)+1) x])
      · linarith [le_max_left x (1/x)]
  have h := tendsto_setIntegral_of_monotone (μ:=volume) (f:=fun x : ℝ => (x:ℂ)^(s-1)*v x)
    (s:=E) (fun _ => measurableSet_Ioo) hm (by simpa only [hcover, MellinConvergent, smul_eq_mul] using hv)
  simpa only [hcover, mellin, smul_eq_mul] using h

end MasulloDiagonal
end

section
open Set Filter Finset MeasureTheory
open scoped Topology

theorem solution :
    (∀ (k f w : ℝ → ℂ) (a C : ℝ), Measurable k → Measurable f → Measurable w →
      MellinConvergent k (a:ℂ) → MellinConvergent f (a:ℂ) →
      (∀ t : ℝ, 0 < t → ‖w t‖ ≤ C * t^a) →
      (∫ x in Ioi (0:ℝ), (w x / (x:ℂ)) *
        (∫ r in Ioi (0:ℝ), (k r / (r:ℂ)) * f (x/r))) =
      ∫ u in Ioi (0:ℝ), (f u / (u:ℂ)) *
        (∫ r in Ioi (0:ℝ), (k r / (r:ℂ)) * w (r*u))) ∧
    ∃ ψ g k : ℝ → ℝ,
      let s : ℂ := 1/2
      let F (t : ℝ) : ℂ := ∑' n : ℕ, (ψ (((n:ℝ)+1)*t) : ℂ)
      let Q (B : ℕ) := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ 2)
      let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
        (-1:ℂ)^U.card * F ((2*∏ l ∈ U, (l:ℝ))*t)
      let T (v : ℝ → ℂ) (x : ℝ) := ∫ r in Ioi (0:ℝ), ((k r:ℂ)/(r:ℂ))*v (x/r)
      let D (v : ℝ → ℂ) (j : ℕ) := ∫ x in Ioo (1/((j:ℝ)+1)) ((j:ℝ)+1),
        (x:ℂ)^(s-1) * T v x
      let gC (t : ℝ) : ℂ := g t
      let c := mellin (fun t : ℝ => (k t:ℂ)) s * mellin gC s
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      (∀ t : ℝ, t ≤ 0 ∨ 8 ≤ t → ψ t = 0) ∧ (∫ t in Ioi (0:ℝ), ψ t) = 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∀ t : ℝ, 0 < t → (∑' j : ℕ, (ψ (2^(j+1)*t):ℂ)) = gC t) ∧
      ContDiff ℝ (⊤ : ℕ∞) k ∧ tsupport k ⊆ Icc 1 2 ∧
      (∀ B : ℕ, HasMellin (T (G B)) s
        (mellin (fun t : ℝ => (k t:ℂ)) s * mellin (G B) s)) ∧
      HasMellin (T gC) s c ∧ c ≠ 0 ∧
      (∀ j : ℕ, ∀ᶠ B : ℕ in atTop, D (G B) j = D gC j) ∧
      Tendsto (D gC) atTop (𝓝 c) ∧
      (∀ B : ℕ, Tendsto (D (G B)) atTop (𝓝 (mellin (T (G B)) s))) ∧
      Tendsto (fun B : ℕ => mellin (T (G B)) s) atTop (𝓝 0) := by
  constructor
  · intro k f w a C hk hf hw hkM hfM hW
    apply MasulloRH.multiplicative_convolution_diagonal_pairing k f w hk hf hw
    exact MasulloRH.multiplicative_diagonal_pairing_integrable k f w a C hk hf hw hkM hfM hW
  obtain ⟨ψ,g,hψ,hψc,hv,hm,hg,hgc,hpow,hstab,hMG,hzero,hMg,hne⟩ :=
    MasulloRH.smooth_compact_dyadic_shell_mellin_counterexample
  obtain ⟨k,hk,_,hks,hkz,hMk,hkn⟩ := MasulloDiagonal.kernel_bump_exists
  let kc (r:ℝ) : ℂ := k r
  let gc (r:ℝ) : ℂ := g r
  let F (t : ℝ) : ℂ := ∑' n : ℕ, (ψ (((n:ℝ)+1)*t) : ℂ)
  let Q (B : ℕ) := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ 2)
  let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
    (-1:ℂ)^U.card * F ((2*∏ l ∈ U, (l:ℝ))*t)
  let T (v : ℝ → ℂ) (x : ℝ) := ∫ r in Ioi (0:ℝ), (kc r/(r:ℂ))*v (x/r)
  let s : ℂ := 1/2
  have hT (v : ℝ → ℂ) (hv : MellinConvergent v s) :
      HasMellin (T v) s (mellin kc s * mellin v s) :=
    MasulloDiagonal.hasMellin_multiplicative_convolution kc v s hMk hv
  have hG (B : ℕ) : HasMellin (T (G B)) s (mellin kc s * mellin (G B) s) := hT _ (hMG B)
  have hg' := hT gc hMg
  refine ⟨ψ,g,k,hψ,hψc,hv,hm,hg,hgc,hpow,hk,hks,hG,hg',mul_ne_zero hkn hne,?_,?_,?_,?_⟩
  · intro j
    have hloc := MasulloDiagonal.eventually_eq_localized_radial G gc kc
      (fun r hr => by dsimp [kc]; exact_mod_cast hkz r (Or.inr hr.le)) hstab
      (1/((j:ℝ)+1)) (by positivity)
    filter_upwards [hloc] with B hB
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    exact congrArg _ (hB x hx.1.le)
  · have h := MasulloDiagonal.exhaust_windows (T gc) s hg'.1
    rw [hg'.2] at h
    exact h
  · exact fun B => MasulloDiagonal.exhaust_windows (T (G B)) s (hG B).1
  · change Tendsto (fun B : ℕ => mellin (T (G B)) s) atTop (𝓝 0)
    simp_rw [(hG _).2]
    simpa only [mul_zero] using (tendsto_const_nhds.mul hzero :
      Tendsto (fun B : ℕ => mellin kc s * mellin (G B) s) atTop (𝓝 (mellin kc s * 0)))
end
