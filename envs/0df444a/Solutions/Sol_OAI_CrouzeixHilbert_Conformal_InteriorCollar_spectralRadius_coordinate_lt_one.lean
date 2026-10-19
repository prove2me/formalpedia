-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Conformal.InteriorCollar.spectralRadius_coordinate_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:51:18.261383+00:00
-- url     : https://prove2.me/submissions/47fdce87-0210-46a8-9d78-1f3febc5971e

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000
import Theorems.Thm_OAI_CrouzeixHilbert_exists_polynomial_uniform_approx
import Theorems.Thm_OAI_CrouzeixHilbert_sum_integral_eq_zero_of_null_homology

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Existence. -/

noncomputable section

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

open Set Filter Metric

namespace CrouzeixHilbert

theorem sub_div_sub_mem_slitPlane {a b w : ℂ} (hw : w ∉ segment ℝ a b) :
    (w - a) / (w - b) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hwb : w - b ≠ 0 := by
    intro he
    exact hw ((sub_eq_zero.mp he) ▸ right_mem_segment ℝ a b)
  let r : ℝ := ((w - a) / (w - b)).re
  have hr : r ≤ 0 := h.1
  have hrc : (r : ℂ) = (w - a) / (w - b) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using h.2.symm
  have hmul : (r : ℂ) * (w - b) = w - a := by rw [hrc, div_mul_cancel₀ _ hwb]
  have hp : 0 < 1 - r := by linarith
  have hpn : (1 - (r : ℂ)) ≠ 0 := by exact_mod_cast hp.ne'
  apply hw
  refine ⟨(1 - r)⁻¹, -r / (1 - r), inv_nonneg.mpr hp.le,
    div_nonneg (neg_nonneg.mpr hr) hp.le, ?_, ?_⟩
  · field_simp
    ring
  · simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_neg]
    apply (mul_right_cancel₀ hpn)
    field_simp
    linear_combination hmul

theorem SmoothContour.intervalIntegrable_indexIntegrand (Γ : SmoothContour) {a : ℂ}
    (ha : a ∉ Γ.path '' Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => deriv Γ.path t / (Γ.path t - a))
      MeasureTheory.volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  apply Γ.smooth.continuous_deriv_one.continuousOn.div
    (Γ.smooth.continuous.sub continuous_const).continuousOn
  intro t ht he
  exact ha ⟨t, ht, sub_eq_zero.mp he⟩

theorem SmoothContour.index_eq_of_segment_avoids (Γ : SmoothContour) {a b : ℂ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, Γ.path t ∉ segment ℝ a b) :
    Γ.index a = Γ.index b := by
  have hnza (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    exact h t ht ((sub_eq_zero.mp he) ▸ left_mem_segment ℝ a b)
  have hnzb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - b ≠ 0 := by
    intro he
    exact h t ht ((sub_eq_zero.mp he) ▸ right_mem_segment ℝ a b)
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnza t ht (sub_eq_zero.mpr he)
  have hb : b ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnzb t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log ((Γ.path t - a) / (Γ.path t - b)))
        (deriv Γ.path t / (Γ.path t - a) - deriv Γ.path t / (Γ.path t - b)) t := by
    have hg := (Γ.smooth.differentiable (by norm_num) t).hasDerivAt
    have he := ((hg.sub_const a).div (hg.sub_const b) (hnzb t ht)).clog_real
      (sub_div_sub_mem_slitPlane (h t ht))
    simp only [Pi.div_apply] at he
    convert! he using 1
    field_simp [hnza t ht, hnzb t ht]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    ((Γ.intervalIntegrable_indexIntegrand ha).sub (Γ.intervalIntegrable_indexIntegrand hb))
  rw [Γ.closed, sub_self, intervalIntegral.integral_sub
    (Γ.intervalIntegrable_indexIntegrand ha) (Γ.intervalIntegrable_indexIntegrand hb)] at he
  unfold SmoothContour.index
  rw [sub_eq_zero.mp he]

theorem SmoothContour.index_eq_zero_of_re_pos (Γ : SmoothContour) {a c : ℂ}
    (hc : c ≠ 0) (h : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (c * (Γ.path t - a)).re) :
    Γ.index a = 0 := by
  have hnz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Γ.path t - a ≠ 0 := by
    intro he
    simpa only [he, mul_zero, Complex.zero_re, lt_self_iff_false] using h t ht
  have ha : a ∉ Γ.path '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    exact hnz t ht (sub_eq_zero.mpr he)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => Complex.log (c * (Γ.path t - a)))
        (deriv Γ.path t / (Γ.path t - a)) t := by
    have he := (((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.sub_const a).const_mul c).clog_real
      (Complex.mem_slitPlane_iff.mpr (Or.inl (h t ht)))
    simpa only [mul_div_mul_left _ _ hc] using he
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    (Γ.intervalIntegrable_indexIntegrand ha)
  rw [Γ.closed, sub_self] at he
  simp only [SmoothContour.index, he, mul_zero]

theorem SmoothContour.index_eq_zero_of_convex (Γ : SmoothContour) {V : Set ℂ}
    (hV : Convex ℝ V) (hVc : IsClosed V) (hΓ : Γ.path '' Icc (0 : ℝ) 1 ⊆ V)
    {a : ℂ} (ha : a ∉ V) :
    Γ.index a = 0 := by
  obtain ⟨l, r, hla, hlV⟩ :=
    RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) hV hVc ha
  have hl (z : ℂ) : l z = l 1 * z := by
    calc
      l z = l (z • (1 : ℂ)) := by simp
      _ = z • l 1 := l.map_smul z 1
      _ = l 1 * z := by simp [mul_comm]
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 < (l 1 * (Γ.path t - a)).re := by
    rw [← hl, map_sub, Complex.sub_re]
    exact sub_pos.mpr (hla.trans (hlV _ (hΓ ⟨t, ht, rfl⟩)))
  apply Γ.index_eq_zero_of_re_pos ?_ hp
  intro he
  have := hp 0 ⟨le_rfl, zero_le_one⟩
  simp only [he, zero_mul, Complex.zero_re, lt_self_iff_false] at this

theorem exists_smooth_radial_frontier_approx {V : Set ℂ}
    (hV : Convex ℝ V) (hV0 : V ∈ 𝓝 (0 : ℂ)) (hVb : Bornology.IsBounded V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℂ → ℝ, ContDiff ℝ 1 q ∧ (∀ z, 0 < q z) ∧
      ∀ z : ℂ, ‖z‖ = 1 → ∃ w ∈ frontier V, dist (q z • z) w < ε := by
  obtain ⟨R, hR, hVR⟩ := hVb.subset_closedBall_lt 0 0
  let r : ℂ → ℝ := fun z => (max R⁻¹ (gauge V z))⁻¹
  have hrp (z : ℂ) : 0 < r z := inv_pos.mpr ((inv_pos.mpr hR).trans_le (le_max_left _ _))
  have hrc : Continuous r :=
    (continuous_const.max (continuous_gauge hV hV0)).inv₀ (fun z => ((inv_pos.mpr hR).trans_le (le_max_left _ _)).ne')
  obtain ⟨q, hq, hqr, -⟩ := hrc.exists_contDiff_approx 1
    (continuous_const.min (hrc.div_const 2)) (fun z => lt_min hε (half_pos (hrp z)))
  refine ⟨q, by simpa using hq, ?_, ?_⟩
  · intro z
    have he := (abs_lt.mp (hqr z)).1
    have := min_le_right ε (r z / 2)
    linarith [hrp z]
  · intro z hz
    have hg : R⁻¹ ≤ gauge V z := by
      simpa only [hz, one_div] using
        (le_gauge_of_subset_closedBall (absorbent_nhds_zero hV0) hR.le hVR (x := z))
    have hr : r z = (gauge V z)⁻¹ := inv_inj.mpr (max_eq_right hg)
    have hgz : gauge V z ≠ 0 := ne_of_gt ((inv_pos.mpr hR).trans_le hg)
    refine ⟨r z • z, (gauge_eq_one_iff_mem_frontier hV hV0).mp ?_, ?_⟩
    · rw [gauge_smul_of_nonneg (hrp z).le, smul_eq_mul, hr, inv_mul_cancel₀ hgz]
    · calc
        dist (q z • z) (r z • z) = |q z - r z| := by
          rw [dist_eq_norm, ← sub_smul, norm_smul, hz, mul_one, Real.norm_eq_abs]
        _ < min ε (r z / 2) := hqr z
        _ ≤ ε := min_le_left _ _

theorem unitCirclePath_ne_zero (t : ℝ) : unitCirclePath t ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [unitCirclePath_norm]
  norm_num

theorem hasDerivAt_unitCirclePath (t : ℝ) :
    HasDerivAt unitCirclePath (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) t := by
  convert! (hasDerivAt_circleMap 0 1 (2 * Real.pi * t)).scomp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi)) using 1
  simp only [unitCirclePath, mul_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem radialContour_index_center (a : ℂ) (q : ℂ → ℝ) (hq : ContDiff ℝ 1 q)
    (hqp : ∀ z, 0 < q z) : (radialContour a q hq).index a = 1 := by
  let f : ℝ → ℝ := fun t => q (unitCirclePath t)
  have hf : ContDiff ℝ 1 f := hq.comp unitCirclePath_smooth
  have hfp (t : ℝ) : f t ≠ 0 := (hqp _).ne'
  have hfc : f 0 = f 1 := by dsimp [f]; rw [unitCirclePath_closed]
  have hdiff (t : ℝ) : HasDerivAt f (deriv f t) t :=
    (hf.differentiable (by norm_num) t).hasDerivAt
  have hd (t : ℝ) : deriv (radialContour a q hq).path t =
      f t • (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) +
        deriv f t • unitCirclePath t :=
    ((hdiff t).smul (hasDerivAt_unitCirclePath t)).const_add a |>.deriv
  have hi : IntervalIntegrable (fun t => deriv f t / f t) MeasureTheory.volume (0 : ℝ) 1 :=
    (hf.continuous_deriv_one.div hf.continuous hfp).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => (hdiff t).log (hfp t)) hi
  rw [← hfc, sub_self] at he
  have heq (t : ℝ) : deriv (radialContour a q hq).path t /
      ((radialContour a q hq).path t - a) =
        ((deriv f t / f t : ℝ) : ℂ) + 2 * (Real.pi : ℂ) * Complex.I := by
    rw [hd]
    change ((f t : ℂ) * (unitCirclePath t * (2 * (Real.pi : ℂ) * Complex.I)) +
      ((deriv f t : ℝ) : ℂ) * unitCirclePath t) /
      (a + (f t : ℂ) * unitCirclePath t - a) = _
    rw [add_sub_cancel_left, Complex.ofReal_div]
    field_simp [Complex.ofReal_ne_zero.mpr (hfp t), unitCirclePath_ne_zero t]
    ring
  have hic : IntervalIntegrable (fun t => ((deriv f t / f t : ℝ) : ℂ))
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Complex.continuous_ofReal.comp (hf.continuous_deriv_one.div hf.continuous hfp)).intervalIntegrable 0 1
  simp only [SmoothContour.index, heq]
  rw [intervalIntegral.integral_add hic intervalIntegrable_const,
    intervalIntegral.integral_ofReal, he, Complex.ofReal_zero, zero_add,
    intervalIntegral.integral_const]
  simp only [sub_zero, one_smul]
  apply inv_mul_cancel₀
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

theorem exists_calculusContour {K U : Set ℂ} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hU : IsOpen U) (hKU : K ⊆ U) :
    Nonempty (CalculusContour K U) := by
  obtain ⟨a, ha⟩ := hKne
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  let e : ℂ ≃ₜ ℂ := Homeomorph.addLeft a
  let V : Set ℂ := e ⁻¹' (cthickening (ε / 2) K)
  have hV : Convex ℝ V := by
    convert! (hKc.cthickening (ε / 2)).translate (-a) using 1
    ext z
    constructor
    · intro hz
      exact ⟨a + z, hz, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      change a + (-a + w) ∈ cthickening (ε / 2) K
      simpa using hw
  have hV0 : V ∈ 𝓝 (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds]
    change 0 ∈ interior (e ⁻¹' (cthickening (ε / 2) K))
    rw [← e.preimage_interior]
    change a + 0 ∈ interior (cthickening (ε / 2) K)
    rw [add_zero]
    exact thickening_subset_interior_cthickening _ _ (self_subset_thickening (half_pos hε) _ ha)
  have hVb : Bornology.IsBounded V := (e.isCompact_preimage.mpr hK.cthickening).isBounded
  obtain ⟨q, hq, hqp, hqV⟩ := exists_smooth_radial_frontier_approx hV hV0 hVb
    (div_pos hε (by norm_num : (0 : ℝ) < 4))
  let Γ : SmoothContour := radialContour a q hq
  have hΓ (t : ℝ) : Γ.path t ∈ cthickening ε K ∧ Γ.path t ∉ K := by
    obtain ⟨w, hw, hd⟩ := hqV (unitCirclePath t) (unitCirclePath_norm t)
    have hw' : a + w ∈ frontier (cthickening (ε / 2) K) := by
      change w ∈ e ⁻¹' frontier (cthickening (ε / 2) K)
      rw [e.preimage_frontier]
      exact hw
    have hiw : infDist (a + w) K = ε / 2 := by
      unfold infDist
      rw [frontier_cthickening_subset K hw', ENNReal.toReal_ofReal (half_pos hε).le]
    have hd' : dist (Γ.path t) (a + w) < ε / 4 := by
      simpa only [Γ, radialContour, dist_add_left] using hd
    have hi : infDist (Γ.path t) K < ε := by
      have hle := infDist_le_infDist_add_dist (s := K) (x := Γ.path t) (y := a + w)
      rw [hiw] at hle
      linarith
    refine ⟨thickening_subset_cthickening ε K ((mem_thickening_iff_infDist_lt ⟨a, ha⟩).mpr hi), ?_⟩
    intro htK
    have hle := infDist_le_infDist_add_dist (s := K) (x := a + w) (y := Γ.path t)
    rw [hiw, infDist_zero_of_mem htK, zero_add, dist_comm] at hle
    linarith
  refine ⟨{ toSmoothContour := Γ, avoids := ?_, index_inside := ?_, index_outside := ?_ }⟩
  · intro t _ht
    exact ⟨hεU (hΓ t).1, (hΓ t).2⟩
  · intro z hz
    calc
      Γ.index z = Γ.index a := Γ.index_eq_of_segment_avoids (fun t _ht htz =>
        (hΓ t).2 (hKc.segment_subset hz ha htz))
      _ = 1 := radialContour_index_center a q hq hqp
  · intro z hz
    exact Γ.index_eq_zero_of_convex (hKc.cthickening ε) isClosed_cthickening
      (by rintro _ ⟨t, _ht, rfl⟩; exact (hΓ t).1) (fun he => hz (hεU he))

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.NumericalRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact numerical closure, supremum norms, and spectral containment. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_le_of_mem_numericalRange (A : Operator H) {z : ℂ}
    (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc
    ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
    _ = ‖A‖ := by rw [hx]; ring

theorem numericalRange_subset_closedBall (A : Operator H) :
    numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_le_of_mem_numericalRange A hz

theorem numericalClosure_subset_closedBall (A : Operator H) :
    numericalClosure A ⊆ Metric.closedBall 0 ‖A‖ :=
  closure_minimal (numericalRange_subset_closedBall A) Metric.isClosed_closedBall

theorem isCompact_numericalClosure (A : Operator H) : IsCompact (numericalClosure A) :=
  (isCompact_closedBall (0 : ℂ) ‖A‖).of_isClosed_subset isClosed_closure
    (numericalClosure_subset_closedBall A)

theorem numericalRange_nonempty [Nontrivial H] (A : Operator H) :
    (numericalRange A).Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨⟪x, A x⟫_ℂ, x, hx, rfl⟩

theorem numericalClosure_nonempty [Nontrivial H] (A : Operator H) :
    (numericalClosure A).Nonempty :=
  (numericalRange_nonempty A).mono subset_closure

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Convexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of the numerical range and its closure. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem phase_real (u v : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (c * u + star c * v).im = 0 := by
  let d : ℂ := u - star v
  have him (c : ℂ) : (c * u + star c * v).im = (c * d).im := by
    simp only [d, mul_sub, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  by_cases hd : d = 0
  · refine ⟨1, norm_one, ?_⟩
    rw [him, hd, mul_zero, Complex.zero_im]
  · refine ⟨(‖d‖ : ℂ)⁻¹ * star d, ?_, ?_⟩
    · simp [hd]
    · rw [him, mul_assoc]
      simp only [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_inv,
        ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem unit_interval_of_quadratic_endpoints (B : Operator H)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hBx : ⟪x, B x⟫_ℂ = 0) (hBy : ⟪y, B y⟫_ℂ = 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ w : H, ‖w‖ = 1 ∧ ⟪w, B w⟫_ℂ = (t : ℂ) := by
  obtain ⟨c, hc, hcross⟩ := phase_real ⟪x, B y⟫_ℂ ⟪y, B x⟫_ℂ
  let y' : H := c • y
  have hy' : ‖y'‖ = 1 := by simp [y', norm_smul, hc, hy]
  have hy'B : ⟪y', B y'⟫_ℂ = 1 := by
    simp only [y', map_smul, inner_smul_left, inner_smul_right, hBy, mul_one,
      Complex.mul_conj', hc, Complex.ofReal_one, one_pow]
  have hc' : (⟪x, B y'⟫_ℂ + ⟪y', B x⟫_ℂ).im = 0 := by
    simpa only [y', map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply] using hcross
  let q : ℝ → H := fun s => ((1 - s : ℝ) : ℂ) • x + (s : ℂ) • y'
  have hq0 (s : ℝ) : q s ≠ 0 := by
    intro hz
    have heq : (((1 - s : ℝ) : ℂ) • x) = -(s : ℂ) • y' := by
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hz
    have hq := congrArg (fun z : H => ⟪z, B z⟫_ℂ) heq
    simp only [map_smul, inner_smul_left, inner_smul_right, hBx, hy'B, mul_zero,
      mul_one, map_neg, Complex.conj_ofReal, neg_mul_neg] at hq
    have hs : s = 0 := by
      have hh := congrArg Complex.re hq
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.zero_re] at hh
      nlinarith
    simp [q, hs] at hz
    rw [hz] at hx
    norm_num at hx
  have hq : Continuous q := by
    dsimp [q]
    fun_prop
  have hqi (s : ℝ) : (⟪q s, B (q s)⟫_ℂ).im = 0 := by
    have heq : ⟪q s, B (q s)⟫_ℂ = (s : ℂ) ^ 2 +
        (s : ℂ) * (1 - (s : ℂ)) * (⟪x, B y'⟫_ℂ + ⟪y', B x⟫_ℂ) := by
      simp only [q, map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal, hBx, hy'B, map_sub, map_one,
        mul_zero, mul_one, zero_add, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    rw [heq]
    simp [Complex.add_im, Complex.mul_im, hc', pow_two]
  let g : ℝ → H := fun s => (‖q s‖ : ℂ)⁻¹ • q s
  have hg (s : ℝ) : ‖g s‖ = 1 := by
    simp [g, norm_smul, hq0 s]
  have hgc : Continuous g := by
    apply Continuous.smul _ hq
    apply Continuous.inv₀ (Complex.continuous_ofReal.comp hq.norm)
    intro s
    change (‖q s‖ : ℂ) ≠ 0
    exact_mod_cast norm_ne_zero_iff.mpr (hq0 s)
  have hgi (s : ℝ) : (⟪g s, B (g s)⟫_ℂ).im = 0 := by
    simp only [g, map_smul, inner_smul_left, inner_smul_right, ← Complex.ofReal_inv,
      Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hqi s]
    ring
  let f : ℝ → ℝ := fun s => (⟪g s, B (g s)⟫_ℂ).re
  have hfc : Continuous f := Complex.continuous_re.comp (hgc.inner (𝕜 := ℂ) (B.continuous.comp hgc))
  have hf0 : f 0 = 0 := by simp [f, g, q, hx, hBx]
  have hf1 : f 1 = 1 := by simp [f, g, q, hy', hy'B]
  have hmem : t ∈ Icc (f 0) (f 1) := by simpa only [hf0, hf1] using ht
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hfc.continuousOn hmem
  refine ⟨g s, hg s, ?_⟩
  apply Complex.ext
  · exact hs
  · exact hgi s

theorem convex_numericalRange (A : Operator H) : Convex ℝ (numericalRange A) := by
  intro a ha b hb α β hα hβ hsum
  by_cases hab : a = b
  · subst b
    rw [← add_smul, hsum, one_smul]
    exact ha
  obtain ⟨x, hx, hAx⟩ := ha
  obtain ⟨y, hy, hAy⟩ := hb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let B : Operator H := (b - a)⁻¹ • (A - a • 1)
  have hform (v : H) (hv : ‖v‖ = 1) :
      ⟪v, B v⟫_ℂ = (b - a)⁻¹ * (⟪v, A v⟫_ℂ - a) := by
    simp [B, inner_self_eq_norm_sq_to_K, hv]
  have hBx : ⟪x, B x⟫_ℂ = 0 := by rw [hform x hx, hAx, sub_self, mul_zero]
  have hBy : ⟪y, B y⟫_ℂ = 1 := by rw [hform y hy, hAy, inv_mul_cancel₀ hba]
  obtain ⟨w, hw, hwB⟩ := unit_interval_of_quadratic_endpoints B x y hx hy hBx hBy
    β ⟨hβ, by linarith⟩
  refine ⟨w, hw, ?_⟩
  rw [hform w hw] at hwB
  have hid := congrArg (fun z : ℂ => (b - a) * z) hwB
  simp only [← mul_assoc, mul_inv_cancel₀ hba, one_mul] at hid
  have hsumC : (α : ℂ) + (β : ℂ) = 1 := by exact_mod_cast hsum
  calc
    ⟪w, A w⟫_ℂ = (⟪w, A w⟫_ℂ - a) + a := by ring
    _ = (b - a) * (β : ℂ) + a := by rw [hid]
    _ = α • a + β • b := by
      simp only [Complex.real_smul]
      linear_combination -a * hsumC

theorem convex_numericalClosure (A : Operator H) : Convex ℝ (numericalClosure A) :=
  (convex_numericalRange A).closure

end CrouzeixHilbert
end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Homotopy. -/

noncomputable section

open scoped InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem numericalClosure_operatorHomotopy_subset (A : Operator H) {a : ℂ}
    (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    numericalClosure (operatorHomotopy A a s) ⊆ numericalClosure A := by
  apply closure_minimal _ isClosed_closure
  rintro z ⟨x, hx, rfl⟩
  have h := (convex_numericalClosure A).add_smul_sub_mem ha
    (subset_closure (show ⟪x, A x⟫_ℂ ∈ numericalRange A from ⟨x, hx, rfl⟩)) hs
  simpa [operatorHomotopy, ContinuousLinearMap.algebraMap_apply,
    inner_self_eq_norm_sq_to_K, hx] using! h

theorem homotopy_resolvent_isUnit [CompleteSpace H] (A : Operator H) {a z : ℂ}
    (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : z ∉ numericalClosure A) :
    IsUnit (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) := by
  change z ∈ resolventSet ℂ (operatorHomotopy A a s)
  by_contra he
  exact hz (numericalClosure_operatorHomotopy_subset A ha hs
    (spectrum_subset_numericalClosure _ he))

theorem continuousOn_homotopyResolvent [CompleteSpace H] (A : Operator H)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (fun p : ℝ × ℂ => homotopyResolvent A a p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ (numericalClosure A)ᶜ) := by
  have hc : Continuous (fun p : ℝ × ℂ =>
      algebraMap ℂ (Operator H) p.2 - operatorHomotopy A a p.1) :=
    by simp only [operatorHomotopy, Algebra.algebraMap_eq_smul_one]; fun_prop
  intro p hp
  exact ((differentiableAt_inverse (𝕜 := ℝ)
    (homotopy_resolvent_isUnit A ha hp.1 hp.2)).continuousAt.comp
      (f := fun q : ℝ × ℂ => algebraMap ℂ (Operator H) q.2 - operatorHomotopy A a q.1)
      (x := p) hc.continuousAt).continuousWithinAt

theorem commute_homotopyResolvent (A : Operator H) (a : ℂ) (s : ℝ) (z : ℂ) :
    Commute (A - algebraMap ℂ (Operator H) a) (homotopyResolvent A a s z) := by
  let D := A - algebraMap ℂ (Operator H) a
  have hc : Commute D (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) := by
    apply Commute.sub_right (Algebra.commutes z D).symm
    exact (show Commute D (algebraMap ℂ (Operator H) a) from (Algebra.commutes a D).symm).add_right ((Commute.refl D).smul_right s)
  by_cases hu : IsUnit (algebraMap ℂ (Operator H) z - operatorHomotopy A a s)
  · rcases hu with ⟨v, hv⟩
    change Commute D (Ring.inverse _)
    rw [← hv, Ring.inverse_unit]
    exact (show Commute D (v : Operator H) from hv.symm ▸ hc).units_inv_right
  · simp only [homotopyResolvent, Ring.inverse_non_unit _ hu]
    exact Commute.zero_right _

theorem hasDerivAt_homotopyResolvent [CompleteSpace H] (A : Operator H)
    {a z : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : z ∉ numericalClosure A) :
    HasDerivAt (fun r : ℝ => homotopyResolvent A a r z)
      (homotopyResolvent A a s z * (A - algebraMap ℂ (Operator H) a) *
        homotopyResolvent A a s z) s := by
  have hu := homotopy_resolvent_isUnit A ha hs hz
  have h₁ : HasFDerivAt Ring.inverse _
      (algebraMap ℂ (Operator H) z - operatorHomotopy A a s) :=
    hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  have h₂ : HasDerivAt (fun r : ℝ => algebraMap ℂ (Operator H) z - operatorHomotopy A a r)
      (-(A - algebraMap ℂ (Operator H) a)) s := by
    simpa only [operatorHomotopy, one_smul, zero_add, zero_sub, id_eq] using!
      (((hasDerivAt_id s).smul_const (A - algebraMap ℂ (Operator H) a)).const_add
        (algebraMap ℂ (Operator H) a)).const_sub (algebraMap ℂ (Operator H) z)
  simpa only [homotopyResolvent, Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ← Ring.inverse_unit hu.unit, hu.unit_spec,
    mul_neg, neg_mul, neg_neg] using! h₁.comp_hasDerivAt s h₂

theorem hasDerivAt_homotopyResolvent_path [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => homotopyResolvent A a s (Γ.path r))
      (-(deriv Γ.path t) • (homotopyResolvent A a s (Γ.path t)) ^ 2) t := by
  have hu := homotopy_resolvent_isUnit A ha hs (Γ.avoids t ht).2
  have h₁ := spectrum.hasDerivAt_resolvent_const_left (𝕜 := ℂ) hu
  have h₂ : HasDerivAt Γ.path (deriv Γ.path t) t :=
    (Γ.smooth.differentiable (by norm_num) t).hasDerivAt
  have h := (h₁.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t h₂
  simpa [homotopyResolvent, resolvent, neg_smul, Function.comp_def] using! h

theorem continuousOn_homotopyResolvent_path [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (fun p : ℝ × ℝ => homotopyResolvent A a p.1 (Γ.path p.2))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
  (continuousOn_homotopyResolvent A ha).comp
    ((continuous_fst.prodMk (Γ.smooth.continuous.comp continuous_snd)).continuousOn)
    (fun p hp => ⟨hp.1, (Γ.avoids p.2 hp.2).2⟩)

theorem continuousOn_homotopyKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    ContinuousOn (Function.uncurry (homotopyKernel A a Γ.toSmoothContour))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hr := continuousOn_homotopyResolvent_path A Γ ha
  exact (Γ.smooth.continuous_deriv_one.comp continuous_snd).continuousOn.smul
    ((hr.mul continuousOn_const).mul hr)

theorem intervalIntegrable_homotopyKernel_left [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => homotopyKernel A a Γ.toSmoothContour s t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hc := (continuousOn_homotopyKernel A Γ ha).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, ht⟩)
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le zero_le_one, Function.comp_def, Function.uncurry_def] using! hc

theorem intervalIntegrable_homotopyKernel_right [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (homotopyKernel A a Γ.toSmoothContour s)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hc := (continuousOn_homotopyKernel A Γ ha).comp
    (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le zero_le_one, Function.comp_def, Function.uncurry_def] using! hc

theorem integral_homotopyKernel_left [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) =
      deriv Γ.path t • homotopyResolvent A a 1 (Γ.path t) -
        deriv Γ.path t • homotopyResolvent A a 0 (Γ.path t) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => deriv Γ.path t • homotopyResolvent A a r (Γ.path t)) _
    (intervalIntegrable_homotopyKernel_left A Γ ha ht)
  intro s hs
  exact (hasDerivAt_homotopyResolvent A ha (by simpa using hs) (Γ.avoids t ht).2).const_smul
    (deriv Γ.path t)

theorem hasDerivAt_homotopyKernel_primitive [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => -((A - algebraMap ℂ (Operator H) a) *
        homotopyResolvent A a s (Γ.path r)))
      (homotopyKernel A a Γ.toSmoothContour s t) t := by
  have h := (hasDerivAt_homotopyResolvent_path A Γ ha hs ht).const_mul
    (A - algebraMap ℂ (Operator H) a) |>.neg
  have hc := (commute_homotopyResolvent A a s (Γ.path t)).eq
  simpa only [homotopyKernel, mul_smul_comm, neg_smul, mul_neg, neg_neg,
    sq, ← mul_assoc, hc] using! h

theorem integral_homotopyKernel_right [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) = 0 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_homotopyKernel_primitive A Γ ha hs (by simpa using ht))
    (intervalIntegrable_homotopyKernel_right A Γ ha hs)
  simpa only [Γ.closed, sub_self] using he

theorem integral_integral_homotopyKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, homotopyKernel A a Γ.toSmoothContour s t) = 0 := by
  have hc := continuousOn_homotopyKernel A Γ ha
  have hi := (hc.integrableOn_compact (μ := MeasureTheory.volume) (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hFub := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := homotopyKernel A a Γ.toSmoothContour)
    (a := (0 : ℝ)) (b := 1) (c := 0) (d := 1) (by simpa using! hi)
  rw [← hFub]
  calc
    _ = ∫ _s in (0 : ℝ)..1, (0 : Operator H) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact integral_homotopyKernel_right A Γ ha (by simpa using hs)
    _ = 0 := by simp

theorem integral_resolvent_homotopy [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {a : ℂ} (ha : a ∈ numericalClosure A) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t • Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - A)) =
      ∫ t in (0 : ℝ)..1, deriv Γ.path t •
        Ring.inverse (algebraMap ℂ (Operator H) (Γ.path t) - algebraMap ℂ (Operator H) a) := by
  have hint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (fun t => deriv Γ.path t • homotopyResolvent A a s (Γ.path t))
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hc := (continuousOn_homotopyResolvent_path A Γ ha).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using!
      Γ.smooth.continuous_deriv_one.continuousOn.smul hc
  have he : (∫ t in (0 : ℝ)..1, deriv Γ.path t • homotopyResolvent A a 1 (Γ.path t)) =
      ∫ t in (0 : ℝ)..1, deriv Γ.path t • homotopyResolvent A a 0 (Γ.path t) := by
    apply sub_eq_zero.mp
    rw [← intervalIntegral.integral_sub (hint 1 ⟨zero_le_one, le_rfl⟩) (hint 0 ⟨le_rfl, zero_le_one⟩)]
    convert integral_integral_homotopyKernel A Γ ha using 1
    apply intervalIntegral.integral_congr
    intro t ht
    exact (integral_homotopyKernel_left A Γ ha (by simpa using ht)).symm
  simpa only [homotopyResolvent, operatorHomotopy_one, operatorHomotopy_zero] using he

theorem ring_inverse_algebraMap (z : ℂ) :
    Ring.inverse (algebraMap ℂ (Operator H) z) = z⁻¹ • (1 : Operator H) := by
  by_cases hz : z = 0
  · simp [hz]
  have hu : IsUnit (algebraMap ℂ (Operator H) z) :=
    (isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ (Operator H))
  have he := (Ring.inverse_mul_eq_iff_eq_mul (algebraMap ℂ (Operator H) z)
    1 (z⁻¹ • (1 : Operator H)) hu).mpr (by
      rw [← Algebra.algebraMap_eq_smul_one, ← map_mul, mul_inv_cancel₀ hz, map_one])
  simpa only [mul_one] using he

theorem contourEval_one [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) :
    contourEval A Γ.toSmoothContour (fun _ => 1) = 1 := by
  nontriviality H
  obtain ⟨a, ha⟩ := numericalClosure_nonempty A
  unfold contourEval
  simp only [mul_one]
  rw [integral_resolvent_homotopy A Γ ha]
  simp only [← map_sub, ring_inverse_algebraMap, smul_smul,
    intervalIntegral.integral_smul_const, smul_smul]
  change Γ.toSmoothContour.index a • (1 : Operator H) = 1
  rw [Γ.index_inside a ha, one_smul]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ResolventBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent Bounds. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuousOn_contourKernel [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) :
    ContinuousOn (contourKernel A Γ.toSmoothContour) (Icc (0 : ℝ) 1) := by
  apply Γ.smooth.continuous_deriv_one.continuousOn.smul
  exact (continuousOn_resolvent A).comp Γ.smooth.continuous.continuousOn
    (fun t ht => (Γ.avoids t ht).2)

theorem contourEval_eq_kernel (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) :
    contourEval A Γ f = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      ∫ t in (0 : ℝ)..1, f (Γ.path t) • contourKernel A Γ t := by
  unfold contourEval contourKernel
  simp only [smul_smul, mul_comm (f _)]

theorem intervalIntegrable_contourIntegrand [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace) :
    IntervalIntegrable (fun t => f (Γ.path t) • contourKernel A Γ.toSmoothContour t)
      MeasureTheory.volume (0 : ℝ) 1 := by
  have hfc : ContinuousOn (fun t => f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    hf.comp Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)
  have hcont := hfc.smul (continuousOn_contourKernel A Γ)
  rw [← uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hcont
  exact hcont.intervalIntegrable

theorem tendsto_contourEval [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {f : ℂ → ℂ} {fs : ℕ → ℂ → ℂ}
    (hc : ∀ n, ContinuousOn (fs n) Γ.toSmoothContour.trace)
    (hu : TendstoUniformlyOn fs f atTop Γ.toSmoothContour.trace) :
    Tendsto (fun n => contourEval A Γ.toSmoothContour (fs n)) atTop
      (𝓝 (contourEval A Γ.toSmoothContour f)) := by
  let k := contourKernel A Γ.toSmoothContour
  have hk : ContinuousOn k (Icc (0 : ℝ) 1) := continuousOn_contourKernel A Γ
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hk.norm
  let M := max C 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hkb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖k t‖ ≤ M :=
    (hC (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have huc : TendstoUniformlyOn (fun n t => fs n (Γ.path t) • k t)
      (fun t => f (Γ.path t) • k t) atTop (Icc (0 : ℝ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (ε / M) (div_pos hε hM)]
      with n hn
    intro t ht
    have hn' := hn (Γ.path t) (mem_image_of_mem _ ht)
    calc
      dist (f (Γ.path t) • k t) (fs n (Γ.path t) • k t) =
          ‖f (Γ.path t) - fs n (Γ.path t)‖ * ‖k t‖ := by
            rw [dist_eq_norm, ← sub_smul, norm_smul]
      _ ≤ ‖f (Γ.path t) - fs n (Γ.path t)‖ * M :=
        mul_le_mul_of_nonneg_left (hkb t ht) (norm_nonneg _)
      _ < (ε / M) * M := mul_lt_mul_of_pos_right (by simpa only [dist_eq_norm] using hn') hM
      _ = ε := div_mul_cancel₀ _ hM.ne'
  have hcon (n : ℕ) : ContinuousOn (fun t => fs n (Γ.path t) • k t)
      (Icc (0 : ℝ) 1) :=
    ((hc n).comp Γ.smooth.continuous.continuousOn
      (fun t ht => mem_image_of_mem _ ht)).smul hk
  have hi : Tendsto (fun n => ∫ t in (0 : ℝ)..1, fs n (Γ.path t) • k t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f (Γ.path t) • k t)) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · exact Eventually.of_forall (fun n => by simpa only [uIcc_of_le zero_le_one] using hcon n)
    · simpa only [uIcc_of_le zero_le_one] using huc
  simpa only [contourEval_eq_kernel] using hi.const_smul ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ContourPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour Polynomials. -/

noncomputable section

open scoped InnerProductSpace Topology TensorProduct Matrix.Norms.L2Operator

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SmoothContour.integral_deriv_mul_pow (Γ : SmoothContour) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * (Γ.path t) ^ n) = 0 := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hder (t : ℝ) : HasDerivAt (fun r : ℝ => (n + 1 : ℂ)⁻¹ * Γ.path r ^ (n + 1))
      (deriv Γ.path t * Γ.path t ^ n) t := by
    have h := ((Γ.smooth.differentiable (by norm_num) t).hasDerivAt.pow (n + 1)).const_mul
      (n + 1 : ℂ)⁻¹
    convert! h using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, mul_comm]
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * Γ.path t ^ n)
      MeasureTheory.volume (0 : ℝ) 1 :=
    (Γ.smooth.continuous_deriv_one.mul (Γ.smooth.continuous.pow n)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) hi
  simpa only [Γ.closed, sub_self] using he

theorem smul_resolvent_eq [CompleteSpace H] (A : Operator H) {z : ℂ}
    (hz : z ∉ numericalClosure A) :
    z • Ring.inverse (algebraMap ℂ (Operator H) z - A) =
      1 + A * Ring.inverse (algebraMap ℂ (Operator H) z - A) := by
  have hu : IsUnit (algebraMap ℂ (Operator H) z - A) := by
    change z ∈ resolventSet ℂ A
    by_contra he
    exact hz (spectrum_subset_numericalClosure A he)
  have he := Ring.mul_inverse_cancel _ hu
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at he
  exact sub_eq_iff_eq_add.mp he

theorem contourEval_mul_id_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0) :
    contourEval A Γ.toSmoothContour (fun z => z * f z) =
      A * contourEval A Γ.toSmoothContour f := by
  let p := fun t : ℝ => f (Γ.path t) • contourKernel A Γ.toSmoothContour t
  let q := fun t : ℝ => deriv Γ.path t * f (Γ.path t)
  let L := ContinuousLinearMap.mul ℂ (Operator H) A
  have hfc : ContinuousOn (fun t => f (Γ.path t)) (Icc (0 : ℝ) 1) :=
    hf.comp Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)
  have hp : ContinuousOn p (Icc (0 : ℝ) 1) := hfc.smul (continuousOn_contourKernel A Γ)
  have hq : ContinuousOn q (Icc (0 : ℝ) 1) := Γ.smooth.continuous_deriv_one.continuousOn.mul hfc
  have hip : IntervalIntegrable p MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_contourIntegrand A Γ hf
  have hiL : IntervalIntegrable (fun t => L (p t)) MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one, Function.comp_def] using!
      L.continuous.comp_continuousOn hp
  have hiq : IntervalIntegrable (fun t => q t • (1 : Operator H))
      MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using! hq.smul continuousOn_const
  have halg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (Γ.path t * f (Γ.path t)) • contourKernel A Γ.toSmoothContour t =
        q t • (1 : Operator H) + L (p t) := by
    have he := smul_resolvent_eq A (Γ.avoids t ht).2
    have hscalar : Γ.path t * f (Γ.path t) * deriv Γ.path t =
        (deriv Γ.path t * f (Γ.path t)) * Γ.path t := by ring
    dsimp only [contourKernel, p, q, L]
    rw [smul_smul, hscalar, ← smul_smul, he, smul_add]
    congr 1
    simp only [ContinuousLinearMap.mul_apply', mul_smul_comm, smul_smul]
    rw [mul_comm (f (Γ.path t))]
  rw [contourEval_eq_kernel, contourEval_eq_kernel]
  have hi : (∫ t in (0 : ℝ)..1, (Γ.path t * f (Γ.path t)) • contourKernel A Γ.toSmoothContour t) =
      L (∫ t in (0 : ℝ)..1, p t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, q t • (1 : Operator H) + L (p t) :=
        intervalIntegral.integral_congr (fun t ht => halg t (by simpa using ht))
      _ = (∫ t in (0 : ℝ)..1, q t) • (1 : Operator H) + L (∫ t in (0 : ℝ)..1, p t) := by
        rw [intervalIntegral.integral_add hiq hiL, intervalIntegral.integral_smul_const,
          L.intervalIntegral_comp_comm hip]
      _ = _ := by rw [show (∫ t in (0 : ℝ)..1, q t) = 0 from hzero, zero_smul, zero_add]
  rw [hi]
  exact (map_smul L _ _).symm

theorem contourEval_pow [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (n : ℕ) :
    contourEval A Γ.toSmoothContour (fun z => z ^ n) = A ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using contourEval_one A Γ
  | succ n ih =>
    have he := contourEval_mul_id_of_integral_eq_zero A Γ
      (continuous_pow n).continuousOn (Γ.toSmoothContour.integral_deriv_mul_pow n)
    simpa only [pow_succ', ih] using he

theorem contourEval_const_mul (A : Operator H) (Γ : SmoothContour) (c : ℂ) (f : ℂ → ℂ) :
    contourEval A Γ (fun z => c * f z) = c • contourEval A Γ f := by
  simp only [contourEval_eq_kernel, mul_smul, intervalIntegral.integral_smul]
  exact smul_comm _ _ _

theorem contourEval_sum [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U)
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) Γ.toSmoothContour.trace) :
    contourEval A Γ.toSmoothContour (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, contourEval A Γ.toSmoothContour (f i) := by
  simp only [contourEval_eq_kernel, Finset.sum_smul]
  rw [intervalIntegral.integral_finsetSum (fun i hi => intervalIntegrable_contourIntegrand A Γ (hf i hi)),
    Finset.smul_sum]

theorem contourEval_polynomial [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (p : Polynomial ℂ) :
    contourEval A Γ.toSmoothContour p.eval = Polynomial.aeval A p := by
  simp_rw [Polynomial.eval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  rw [contourEval_sum A Γ (Finset.range (p.natDegree + 1))
    (fun k z => p.coeff k * z ^ k)
    (fun k _ => (continuous_const.mul (continuous_pow k)).continuousOn)]
  apply Finset.sum_congr rfl
  intro k _
  rw [contourEval_const_mul, contourEval_pow]

theorem contourEval_congr (A : Operator H) (Γ : SmoothContour) {f g : ℂ → ℂ}
    (hfg : EqOn f g Γ.trace) : contourEval A Γ f = contourEval A Γ g := by
  unfold contourEval
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hfg (show Γ.path t ∈ Γ.trace from
    mem_image_of_mem _ (by simpa using ht))]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HomologicalCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homological Cauchy. -/

noncomputable section

open Set Filter Metric MeasureTheory

open scoped Topology

namespace CrouzeixHilbert

theorem null_homology_integral {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Γ : ι → SmoothContour) (c : ι → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hΓ : ∀ i, (Γ i).trace ⊆ U)
    (hnull : ∀ w ∉ U, ∑ i, c i * (Γ i).index w = 0)
    {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    ∑ i, c i • (Γ i).integral f = 0 :=
  sum_integral_eq_zero_of_null_homology Γ c hU hΓ hnull hf

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PolynomialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial Approximation. -/

noncomputable section

open scoped Topology

open Set Filter Metric MeasureTheory

namespace CrouzeixHilbert

open scoped Matrix.Norms.L2Operator

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem holomorphicEval_eq_contourEval_of_independent (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (f : ℂ → ℂ)
    (hind : ∀ Δ : CalculusContour (numericalClosure A) U,
      contourEval A Δ.toSmoothContour f = contourEval A Γ.toSmoothContour f) :
    holomorphicEval A U f = contourEval A Γ.toSmoothContour f := by
  classical
  rw [holomorphicEval, dite_eq_left (show Nonempty (CalculusContour (numericalClosure A) U) from ⟨Γ⟩)]
  exact hind _

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HilbertExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert Extension. -/

noncomputable section

open Set Filter Metric

open scoped Topology

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem differentiableOn_resolvent [CompleteSpace H] (A : Operator H) :
    DifferentiableOn ℂ (fun z : ℂ => Ring.inverse (algebraMap ℂ (Operator H) z - A))
      (numericalClosure A)ᶜ := by
  intro z hz
  have hr : z ∈ resolventSet ℂ A := by
    by_contra h
    exact hz (spectrum_subset_numericalClosure A h)
  exact (spectrum.hasDerivAt_resolvent_const_left hr).differentiableAt.differentiableWithinAt

theorem contourEval_eq_integral (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) :
    contourEval A Γ f =
      Γ.integral (fun z => f z • Ring.inverse (algebraMap ℂ (Operator H) z - A)) := by
  simp only [contourEval, SmoothContour.integral, smul_smul]

theorem contourEval_independent [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ Δ : CalculusContour (numericalClosure A) U) :
    contourEval A Γ.toSmoothContour f = contourEval A Δ.toSmoothContour f := by
  let V := U \ numericalClosure A
  have hV : IsOpen V := hU.sdiff isClosed_closure
  let paths : Bool → SmoothContour := fun b => if b then Γ.toSmoothContour else Δ.toSmoothContour
  let c : Bool → ℂ := fun b => if b then 1 else -1
  have hp : ∀ b, (paths b).trace ⊆ V := by
    intro b z hz
    cases b <;> rcases hz with ⟨t, ht, rfl⟩
    · exact Δ.avoids t ht
    · exact Γ.avoids t ht
  have hi : ∀ z ∉ V, ∑ b, c b * (paths b).index z = 0 := by
    intro z hz
    simp only [Fintype.sum_bool, paths, c, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, ← sub_eq_add_neg]
    by_cases hK : z ∈ numericalClosure A
    · rw [Γ.index_inside z hK, Δ.index_inside z hK, sub_self]
    · have hzU : z ∉ U := fun hzU => hz ⟨hzU, hK⟩
      rw [Γ.index_outside z hzU, Δ.index_outside z hzU, sub_self]
  have hd : DifferentiableOn ℂ (fun z => f z •
      Ring.inverse (algebraMap ℂ (Operator H) z - A)) V :=
    (hf.mono (fun _ hz => hz.1)).fun_smul
      ((differentiableOn_resolvent A).mono (fun _ hz => hz.2))
  have h := null_homology_integral paths c hV hp hi hd
  simp only [Fintype.sum_bool, paths, c, Bool.false_eq_true, ite_false, ite_true,
    one_smul, neg_smul, ← sub_eq_add_neg] at h
  rw [contourEval_eq_integral, contourEval_eq_integral]
  exact sub_eq_zero.mp h

theorem holomorphicEval_eq_contourEval [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ : CalculusContour (numericalClosure A) U) :
    holomorphicEval A U f = contourEval A Γ.toSmoothContour f :=
  holomorphicEval_eq_contourEval_of_independent A Γ f (fun Δ => contourEval_independent A hU hf Δ Γ)

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HolomorphicAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic Algebra. -/

noncomputable section

open Set Filter Metric Topology Complex MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

lemma exists_polynomial_tendstoUniformlyOn {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ p : ℕ → Polynomial ℂ, TendstoUniformlyOn (fun n z => (p n).eval z) f atTop K := by
  have happrox (n : ℕ) : ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < (1 : ℝ)/(n+1) :=
    exists_polynomial_uniform_approx hK hc hU hKU hf (by positivity)
  choose p hp using happrox
  refine ⟨p, Metric.tendstoUniformlyOn_iff.mpr (fun ε hε => ?_)⟩
  have ht : Tendsto (fun n : ℕ => (1 : ℝ)/(n+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_comm, dist_eq_norm]
  exact (hp n z hz).trans hn

section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

variable (A : Operator H)

lemma holomorphicEval_polynomial {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) (p : Polynomial ℂ) :
    holomorphicEval A U p.eval = Polynomial.aeval A p := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU p.differentiable.differentiableOn Γ,
    contourEval_polynomial]

lemma holomorphicEval_const {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) (c : ℂ) :
    holomorphicEval A U (fun _ => c) = algebraMap ℂ (Operator H) c := by
  simpa only [Polynomial.eval_C, Polynomial.aeval_C] using
    holomorphicEval_polynomial A hU hKU (Polynomial.C c)

lemma holomorphicEval_restrict {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hKU : numericalClosure A ⊆ U) (hUV : U ⊆ V) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f V) :
    holomorphicEval A U f = holomorphicEval A V f := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  let Δ : CalculusContour (numericalClosure A) V := {
    toSmoothContour := Γ.toSmoothContour
    avoids := fun t ht => ⟨hUV (Γ.avoids t ht).1, (Γ.avoids t ht).2⟩
    index_inside := Γ.index_inside
    index_outside := fun z hz => Γ.index_outside z (fun h => hz (hUV h)) }
  rw [holomorphicEval_eq_contourEval A hU (hf.mono hUV) Γ,
    holomorphicEval_eq_contourEval A hV hf Δ]

lemma holomorphicEval_add {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    holomorphicEval A U (fun z => f z + g z) = holomorphicEval A U f + holomorphicEval A U g := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU (hf.fun_add hg) Γ,
    holomorphicEval_eq_contourEval A hU hf Γ, holomorphicEval_eq_contourEval A hU hg Γ]
  simp only [contourEval_eq_kernel, add_smul]
  rw [intervalIntegral.integral_add
    (intervalIntegrable_contourIntegrand A Γ (hf.continuousOn.mono (by
      rintro z ⟨t,ht,rfl⟩; exact (Γ.avoids t ht).1)))
    (intervalIntegrable_contourIntegrand A Γ (hg.continuousOn.mono (by
      rintro z ⟨t,ht,rfl⟩; exact (Γ.avoids t ht).1))), smul_add]

lemma holomorphicEval_smul {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (c : ℂ) :
    holomorphicEval A U (fun z => c * f z) = c • holomorphicEval A U f := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU (hf.const_mul c) Γ,
    holomorphicEval_eq_contourEval A hU hf Γ, contourEval_const_mul]

lemma holomorphicEval_mul {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    holomorphicEval A U (fun z => f z * g z) = holomorphicEval A U f * holomorphicEval A U g := by
  obtain ⟨ε,hε,hεU⟩ := (isCompact_numericalClosure A).exists_cthickening_subset_open hU hKU
  let K := cthickening ε (numericalClosure A)
  have hK : IsCompact K := (isCompact_numericalClosure A).cthickening
  have hc : Convex ℝ K := (convex_numericalClosure A).cthickening ε
  have hAK : numericalClosure A ⊆ interior K :=
    (self_subset_thickening hε _).trans (thickening_subset_interior_cthickening _ _)
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) isOpen_interior hAK
  let Δ : CalculusContour (numericalClosure A) U := {
    toSmoothContour := Γ.toSmoothContour
    avoids := fun t ht => ⟨hεU (interior_subset (Γ.avoids t ht).1), (Γ.avoids t ht).2⟩
    index_inside := Γ.index_inside
    index_outside := fun z hz => Γ.index_outside z (fun h => hz (hεU (interior_subset h))) }
  have htrace : Δ.toSmoothContour.trace ⊆ K := by
    rintro z ⟨t,ht,rfl⟩
    exact interior_subset (Γ.avoids t ht).1
  obtain ⟨p,hp⟩ := exists_polynomial_tendstoUniformlyOn hK hc hU hεU hf
  obtain ⟨q,hq⟩ := exists_polynomial_tendstoUniformlyOn hK hc hU hεU hg
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fK : C(K,ℂ) := ⟨fun z => f z, (hf.continuousOn.mono hεU).domRestrict⟩
  let gK : C(K,ℂ) := ⟨fun z => g z, (hg.continuousOn.mono hεU).domRestrict⟩
  have hpK : Tendsto (fun n => (p n).toContinuousMapOn K) atTop (𝓝 fK) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hp)
  have hqK : Tendsto (fun n => (q n).toContinuousMapOn K) atTop (𝓝 gK) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hq)
  have hpq : TendstoUniformlyOn (fun n z => (p n * q n).eval z)
      (fun z => f z * g z) atTop K := by
    have hs := ContinuousMap.tendsto_iff_tendstoUniformly.mp (hpK.mul hqK)
    change TendstoUniformly (fun n (z : K) => (p n).eval (z : ℂ) * (q n).eval (z : ℂ))
      (fun z : K => f z * g z) atTop at hs
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [Function.comp_def, Polynomial.eval_mul] using hs
  have hpf := tendsto_contourEval A Δ (fun n => (p n).continuous.continuousOn) (hp.mono htrace)
  have hqg := tendsto_contourEval A Δ (fun n => (q n).continuous.continuousOn) (hq.mono htrace)
  have hmul := tendsto_contourEval A Δ (fun n => (p n * q n).continuous.continuousOn) (hpq.mono htrace)
  simp_rw [contourEval_polynomial] at hpf hqg hmul
  simp only [map_mul] at hmul
  have he := tendsto_nhds_unique hmul (hpf.mul hqg)
  simpa only [← holomorphicEval_eq_contourEval A hU (hf.fun_mul hg) Δ,
    ← holomorphicEval_eq_contourEval A hU hf Δ, ← holomorphicEval_eq_contourEval A hU hg Δ] using he

end

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.HolomorphicSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphic Spectrum. -/

noncomputable section

open Set Filter Metric Topology Complex MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

variable (A : Operator H)

lemma holomorphicEval_congr {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (he : EqOn f g U) :
    holomorphicEval A U f = holomorphicEval A U g := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU hf Γ, holomorphicEval_eq_contourEval A hU hg Γ]
  apply contourEval_congr
  rintro z ⟨t,ht,rfl⟩
  exact he (Γ.avoids t ht).1

lemma isUnit_holomorphicEval {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hn : ∀ z ∈ numericalClosure A, f z ≠ 0) :
    IsUnit (holomorphicEval A U f) := by
  let V := U ∩ {z | f z ≠ 0}
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isOpen_ne
  have hKV : numericalClosure A ⊆ V := fun z hz => ⟨hKU hz,hn z hz⟩
  have hfV := hf.mono (show V ⊆ U from inter_subset_left)
  have hi : DifferentiableOn ℂ (fun z => (f z)⁻¹) V := hfV.inv (fun z hz => hz.2)
  rw [← holomorphicEval_restrict A hV hU hKV inter_subset_left hf]
  refine (isUnit_iff_exists).mpr ⟨holomorphicEval A V (fun z => (f z)⁻¹), ?_, ?_⟩
  · rw [← holomorphicEval_mul A hV hKV hfV hi,
      holomorphicEval_congr A hV hKV (hfV.fun_mul hi) (differentiableOn_const (1 : ℂ))
        (fun z hz => mul_inv_cancel₀ hz.2), holomorphicEval_const A hV hKV, map_one]
  · rw [← holomorphicEval_mul A hV hKV hi hfV,
      holomorphicEval_congr A hV hKV (hi.fun_mul hfV) (differentiableOn_const (1 : ℂ))
        (fun z hz => inv_mul_cancel₀ hz.2), holomorphicEval_const A hV hKV, map_one]

lemma spectrum_holomorphicEval_subset {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    spectrum ℂ (holomorphicEval A U f) ⊆ f '' numericalClosure A := by
  intro z hz
  by_contra hn
  have hnz : ∀ w ∈ numericalClosure A, z + (-1 : ℂ) * f w ≠ 0 := by
    intro w hw he
    apply hn
    refine ⟨w,hw,?_⟩
    linear_combination -he
  have hd := (differentiableOn_const (c := z)).fun_add (hf.const_mul (-1))
  have hu := isUnit_holomorphicEval A hU hKU hd hnz
  rw [holomorphicEval_add A hU hKU (differentiableOn_const z) (hf.const_mul (-1)),
    holomorphicEval_const A hU hKU, holomorphicEval_smul A hU hKU hf] at hu
  simp only [neg_one_smul, ← sub_eq_add_neg] at hu
  exact (spectrum.mem_iff.mp hz) hu

lemma spectralRadius_holomorphicEval_lt_one {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hfK : ∀ z ∈ numericalClosure A, ‖f z‖ < 1) :
    spectralRadius ℂ (holomorphicEval A U f) < 1 := by
  apply spectrum.spectralRadius_lt_of_forall_lt
  intro z hz
  obtain ⟨w,hw,rfl⟩ := spectrum_holomorphicEval_subset A hU hKU hf hz
  exact hfK w hw

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.MetricBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric Boundary. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

lemma spectralRadius_coordinate_lt_one_oai
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (A : Operator H) (hKU : numericalClosure A ⊆ U) :
    spectralRadius ℂ (holomorphicEval A R.domain R.f) < 1 := by
  apply spectralRadius_holomorphicEval_lt_one A R.isOpen_domain
    (hKU.trans (subset_closure.trans R.closure_subset_domain)) R.analytic_f.differentiableOn
  intro z hz
  exact mem_ball_zero_iff.mp (R.bijective_f.mapsTo (hKU hz))

end Conformal.InteriorCollar

end CrouzeixHilbert

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CrouzeixHilbert.Conformal.InteriorCollar.spectralRadius_coordinate_lt_one_oai.{u_1} := @OAI.CrouzeixHilbert.Conformal.InteriorCollar.spectralRadius_coordinate_lt_one_oai.{u_1}
