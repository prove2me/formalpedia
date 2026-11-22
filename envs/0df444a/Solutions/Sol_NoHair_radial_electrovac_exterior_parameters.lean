-- Prove2me | solution 1 for NoHair.radial_electrovac_exterior_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:00:31.952267+00:00
-- url     : https://prove2.me/submissions/dfa27f8f-01bb-4a0c-9640-d116c52d5f62

import Definitions.Def_NoHair_coordinates

open Set NoHair

private lemma constant_on_ray {R : ℝ} {f : ℝ → ℝ}
    (h : ∀ r, R < r → HasDerivAt f 0 r) :
    ∃ c : ℝ, ∀ r, R < r → f r = c := by
  apply isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
  · exact fun r hr => (h r hr).differentiableAt.differentiableWithinAt
  · exact fun _ hr => (h _ hr).deriv

private lemma constant_flux {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (h : ∀ r, R < r → HasDerivAt f (-2 * f r / r) r) :
    ∃ q : ℝ, ∀ r, R < r → r ^ 2 * f r = q := by
  apply constant_on_ray (f := fun r => r ^ 2 * f r)
  intro r hr
  have hr0 := (hR.trans hr).ne'
  have hd := ((hasDerivAt_id' r).fun_pow 2).fun_mul (h r hr)
  apply hd.congr_deriv
  norm_num <;> try field_simp [hr0]
  all_goals ring

theorem solution (R : ℝ) (μ u v : ℝ → ℝ)
    (hR : 0 < R) (hcont : ContinuousOn μ (Ici R)) (horizon : 2 * μ R = R)
    (exterior : ∀ r, R < r → 2 * μ r < r)
    (electric : ∀ r, R < r → HasDerivAt u (-2 * u r / r) r)
    (magnetic : ∀ r, R < r → HasDerivAt v (-2 * v r / r) r)
    (mass : ∀ r, R < r → HasDerivAt μ (r ^ 2 * (u r ^ 2 + v r ^ 2) / 2) r) :
    ∃ m e β : ℝ, 0 ≤ e ∧ IsKerrNewmanBlackHoleParams m 0 e ∧
      kerrNewmanOuterRadius m 0 e = R ∧
      ∀ r, R < r → μ r = m - e ^ 2 / (2 * r) ∧
        r ^ 2 * u r = Real.cos β * e ∧ r ^ 2 * v r = Real.sin β * e := by
  obtain ⟨q, hq⟩ := constant_flux hR electric
  obtain ⟨p, hp⟩ := constant_flux hR magnetic
  let z : ℂ := ⟨q, p⟩
  let e : ℝ := ‖z‖
  have he : e ^ 2 = q ^ 2 + p ^ 2 := by
    change ‖(⟨q, p⟩ : ℂ)‖ ^ 2 = q ^ 2 + p ^ 2
    rw [Complex.sq_norm, Complex.normSq_mk]
    ring
  have corrected (r : ℝ) (hr : R < r) :
      HasDerivAt (fun t => μ t + (e ^ 2 / 2) * t⁻¹) 0 r := by
    have hr0 := (hR.trans hr).ne'
    have heq : e ^ 2 = (r ^ 2 * u r) ^ 2 + (r ^ 2 * v r) ^ 2 := by
      rw [hq r hr, hp r hr, he]
    apply ((mass r hr).fun_add ((hasDerivAt_inv hr0).const_mul (e ^ 2 / 2))).congr_deriv
    rw [heq]
    field_simp [hr0] <;> ring
  obtain ⟨m, hm⟩ := constant_on_ray corrected
  have balance (r : ℝ) (hr : R < r) : 2 * r * μ r = 2 * m * r - e ^ 2 := by
    have h := hm r hr
    change μ r + e ^ 2 / 2 * r⁻¹ = m at h
    field_simp [(hR.trans hr).ne'] at h
    linarith only [h]
  have hEq : EqOn (fun r => 2 * r * μ r) (fun r => 2 * m * r - e ^ 2) (Ioi R) :=
    fun _ hr => balance _ hr
  have onClosed : EqOn (fun r => 2 * r * μ r) (fun r => 2 * m * r - e ^ 2) (Ici R) :=
    hEq.of_subset_closure ((continuousOn_const.mul continuousOn_id).mul hcont)
      (by fun_prop) Ioi_subset_Ici_self (by rw [closure_Ioi])
  have hboundary := onClosed (Set.mem_Ici.mpr (le_refl R))
  change 2 * R * μ R = 2 * m * R - e ^ 2 at hboundary
  have rootEq : R ^ 2 - 2 * m * R + e ^ 2 = 0 := by
    linear_combination hboundary - R * horizon
  have hmpos : 0 < m := by
    refine pos_of_mul_pos_left (b := R) ?_ hR.le
    nlinarith only [rootEq, sq_pos_of_pos hR, sq_nonneg e]
  have outside (r : ℝ) (hr : R < r) : 0 < r ^ 2 - 2 * m * r + e ^ 2 := by
    have hlt := mul_lt_mul_of_pos_right (exterior r hr) (hR.trans hr)
    linarith only [hlt, balance r hr]
  have houter : m ≤ R := by
    by_contra! h
    have hpos := outside (2 * m - R) (by linarith)
    nlinarith only [hpos, rootEq]
  have hdisc : m ^ 2 - (0 : ℝ) ^ 2 - e ^ 2 = (R - m) ^ 2 := by
    nlinarith only [rootEq]
  have hadm : IsKerrNewmanBlackHoleParams m 0 e :=
    ⟨hmpos, by nlinarith only [hdisc, sq_nonneg (R - m)]⟩
  have hradius : kerrNewmanOuterRadius m 0 e = R := by
    unfold kerrNewmanOuterRadius
    rw [hdisc, Real.sqrt_sq (sub_nonneg.mpr houter)]
    ring
  refine ⟨m, e, z.arg, norm_nonneg _, hadm, hradius, ?_⟩
  intro r hr
  refine ⟨?_, (hq r hr).trans ?_, (hp r hr).trans ?_⟩
  · field_simp [(hR.trans hr).ne']
    linarith only [balance r hr]
  · change z.re = Real.cos z.arg * ‖z‖
    rw [mul_comm, Complex.norm_mul_cos_arg]
  · change z.im = Real.sin z.arg * ‖z‖
    rw [mul_comm, Complex.norm_mul_sin_arg]
