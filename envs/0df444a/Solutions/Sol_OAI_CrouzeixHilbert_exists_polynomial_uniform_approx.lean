-- Prove2me | solution 1 for OAI.CrouzeixHilbert.exists_polynomial_uniform_approx
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:43:22.031233+00:00
-- url     : https://prove2.me/submissions/44b55a44-a2f6-41d1-8584-f526e8032630

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000

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
-- module Solutions.OAIQW_CrouzeixHilbert.ConvexNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex Neighborhood. -/

noncomputable section

open Set Metric

open scoped Convex InnerProductSpace

namespace CrouzeixHilbert

theorem convex_outward_not_mem {K : Set ℂ} (hK : Convex ℝ K)
    {a x : ℂ} (ha : a ∈ K) (hx : x ∉ K) {t : ℝ} (ht : 1 ≤ t) :
    a + t • (x - a) ∉ K := by
  intro hy
  have htp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hz := hK.add_smul_sub_mem ha hy
    (show t⁻¹ ∈ Icc (0 : ℝ) 1 from
      ⟨inv_nonneg.mpr htp.le, inv_le_one_of_one_le₀ ht⟩)
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htp.ne',
    one_smul, add_sub_cancel] at hz
  exact hx hz

theorem segment_outward_subset_compl {K : Set ℂ} (hK : Convex ℝ K)
    {a x : ℂ} (ha : a ∈ K) (hx : x ∉ K) {r : ℝ} (hr : 1 ≤ r) :
    [x -[ℝ] (a + r • (x - a))] ⊆ Kᶜ := by
  rw [segment_eq_image']
  rintro z ⟨t, ht, rfl⟩
  have he : x + t • (a + r • (x - a) - x) =
      a + (1 + t * (r - 1)) • (x - a) := by module
  dsimp only
  rw [he]
  exact convex_outward_not_mem hK ha hx (by nlinarith [ht.1])

theorem isPathConnected_compl_of_bounded_convex {K : Set ℂ}
    (hK : Bornology.IsBounded K) (hc : Convex ℝ K) : IsPathConnected Kᶜ := by
  rcases K.eq_empty_or_nonempty with h0 | ⟨a, ha⟩
  · rw [h0, compl_empty]
    exact convex_univ.isPathConnected ⟨0, mem_univ _⟩
  have hrank : 1 < Module.rank ℝ ℂ := by simp
  have hn : Kᶜ.Nonempty := by
    obtain ⟨R, hR, hb⟩ := hK.subset_ball_lt 0 a
    obtain ⟨z, hz⟩ := (isPathConnected_sphere hrank a hR.le).nonempty
    refine ⟨z, ?_⟩
    intro hzK
    have := mem_ball.mp (hb hzK)
    rw [mem_sphere.mp hz] at this
    exact lt_irrefl _ this
  apply isPathConnected_iff.mpr
  refine ⟨hn, ?_⟩
  intro x hx y hy
  obtain ⟨R, hR, hb⟩ := hK.subset_ball_lt (max (dist x a) (dist y a)) a
  have hRx : dist x a < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hRy : dist y a < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRp : 0 < R := lt_of_le_of_lt dist_nonneg hRx
  have hsphere : sphere a R ⊆ Kᶜ := by
    intro z hz hzK
    have hlt := mem_ball.mp (hb hzK)
    rw [mem_sphere.mp hz] at hlt
    exact lt_irrefl _ hlt
  have hradial (v : ℂ) (hv : v ∈ Kᶜ) (hRv : dist v a < R) :
      ∃ q ∈ sphere a R, JoinedIn Kᶜ v q := by
    have hvne : v - a ≠ 0 := by
      intro he
      exact hv (sub_eq_zero.mp he ▸ ha)
    have hnv : 0 < ‖v - a‖ := norm_pos_iff.mpr hvne
    have hr : 1 ≤ R / ‖v - a‖ := by
      apply (le_div_iff₀ hnv).mpr
      simpa only [one_mul, dist_eq_norm] using hRv.le
    refine ⟨a + (R / ‖v - a‖) • (v - a), ?_, ?_⟩
    · rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hRp.le hnv.le), div_mul_cancel₀ _ hnv.ne']
    · exact JoinedIn.of_segment_subset (segment_outward_subset_compl hc ha hv hr)
  obtain ⟨qx, hqx, jx⟩ := hradial x hx hRx
  obtain ⟨qy, hqy, jy⟩ := hradial y hy hRy
  exact jx.trans (((isPathConnected_sphere hrank a hRp.le).joinedIn qx hqx qy hqy).mono
    hsphere |>.trans jy.symm)

universe u

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

theorem SmoothContour.integral_deriv_mul_eq_zero_of_holomorphic
    (Γ : SmoothContour) {U : Set ℂ} (hU : IsOpen U) (hc : Convex ℝ U)
    (hΓ : Γ.trace ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0 := by
  obtain ⟨g, hg⟩ := hc.exists_forall_hasDerivWithinAt hf
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => g (Γ.path t)) (deriv Γ.path t * f (Γ.path t)) t := by
    have he := ((hg _ (hΓ ⟨t, ht, rfl⟩)).hasDerivAt
      (hU.mem_nhds (hΓ ⟨t, ht, rfl⟩))).hasFDerivAt.restrictScalars ℝ
    convert! he.comp_hasDerivAt t (Γ.smooth.differentiable (by norm_num) t).hasDerivAt using 1
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * f (Γ.path t))
      volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact Γ.smooth.continuous_deriv_one.continuousOn.mul
      (hf.continuousOn.comp Γ.smooth.continuous.continuousOn
        (fun t ht => hΓ ⟨t, ht, rfl⟩))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht)) hi
  simpa only [Γ.closed, sub_self] using he

theorem SmoothContour.cauchy_formula_convex (Γ : SmoothContour) {U : Set ℂ}
    (hU : IsOpen U) (hc : Convex ℝ U) (hΓ : Γ.trace ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {z : ℂ}
    (hz : z ∈ U) (hzΓ : z ∉ Γ.trace) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t) / (Γ.path t - z)) =
      Γ.index z * f z := by
  have hd : DifferentiableOn ℂ (dslope f z) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hz)).mpr hf
  have hi : IntervalIntegrable (fun t => deriv Γ.path t * dslope f z (Γ.path t))
      volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact Γ.smooth.continuous_deriv_one.continuousOn.mul
      (hd.continuousOn.comp Γ.smooth.continuous.continuousOn (fun t ht => hΓ ⟨t, ht, rfl⟩))
  have he : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t) / (Γ.path t - z)) =
      (∫ t in (0 : ℝ)..1, deriv Γ.path t * dslope f z (Γ.path t)) +
      (∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - z)) * f z := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_add hi
      ((Γ.intervalIntegrable_indexIntegrand hzΓ).mul_const (f z))]
    apply intervalIntegral.integral_congr
    intro t ht
    have hne : Γ.path t ≠ z := fun he => hzΓ ⟨t, by simpa using ht, he⟩
    dsimp only
    rw [dslope_of_ne _ hne]
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    ring
  rw [he, Γ.integral_deriv_mul_eq_zero_of_holomorphic hU hc hΓ hd, zero_add]
  exact (mul_assoc _ _ _).symm

theorem continuous_compactCauchyKernel (K : Set ℂ) : Continuous (compactCauchyKernel K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply ((continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).inv₀
  intro wz he
  apply wz.1.property
  rw [show (wz.1 : ℂ) = (wz.2 : ℂ) from sub_eq_zero.mp he]
  exact wz.2.property

theorem compactCauchyKernel_mem_iff_resolvent {K : Set ℂ}
    (S : Subalgebra ℂ C(K, ℂ)) (x : S) (hx : ∀ z : K, (x : C(K, ℂ)) z = z)
    (w : ↥(Kᶜ)) : compactCauchyKernel K w ∈ S ↔ (w : ℂ) ∈ resolventSet ℂ x := by
  change _ ↔ IsUnit (algebraMap ℂ S (w : ℂ) - x)
  rw [isUnit_iff_exists_inv]
  constructor
  · intro hw
    refine ⟨⟨compactCauchyKernel K w, hw⟩, ?_⟩
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    change ((w : ℂ) - (x : C(K, ℂ)) z) * ((w : ℂ) - z)⁻¹ = 1
    rw [hx]
    exact mul_inv_cancel₀ (fun he => w.property
      ((sub_eq_zero.mp he).symm ▸ z.property))
  · rintro ⟨y, hy⟩
    have he : compactCauchyKernel K w = (y : C(K, ℂ)) := by
      ext z
      have hp := congrArg (fun f : S => (f : C(K, ℂ)) z) hy
      change ((w : ℂ) - (x : C(K, ℂ)) z) * (y : C(K, ℂ)) z = 1 at hp
      rw [hx] at hp
      exact inv_eq_of_mul_eq_one_right hp
    rw [he]
    exact y.property

theorem coordinate_resolventSet_subset_compl {K : Set ℂ}
    (S : Subalgebra ℂ C(K, ℂ)) (x : S) (hx : ∀ z : K, (x : C(K, ℂ)) z = z) :
    resolventSet ℂ x ⊆ Kᶜ := by
  intro v hv hvin
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hv
  have he := congrArg (fun f : S => (f : C(K, ℂ)) ⟨v, hvin⟩) hy
  change (v - (x : C(K, ℂ)) ⟨v, hvin⟩) * (y : C(K, ℂ)) ⟨v, hvin⟩ = 1 at he
  rw [hx, sub_self, zero_mul] at he
  exact zero_ne_one he

theorem compactCauchyKernel_mem_polynomialClosure {K : Set ℂ} [CompactSpace K]
    (hne : K.Nonempty) (hc : IsConnected Kᶜ) (w : ↥(Kᶜ)) :
    compactCauchyKernel K w ∈ (polynomialFunctions K).topologicalClosure := by
  have : Nonempty K := hne.to_subtype
  let S := (polynomialFunctions K).topologicalClosure
  have : IsClosed (S : Set C(K, ℂ)) := (polynomialFunctions K).isClosed_topologicalClosure
  have : CompleteSpace S := IsClosed.completeSpace_coe
  have : NormOneClass S := ⟨by change ‖(1 : C(K, ℂ))‖ = 1; exact norm_one⟩
  let x : S := ⟨Polynomial.X.toContinuousMapOn K,
    (polynomialFunctions K).le_topologicalClosure (by
      rw [← SetLike.mem_coe, polynomialFunctions_coe]
      exact ⟨Polynomial.X, rfl⟩)⟩
  have hx (z : K) : (x : C(K, ℂ)) z = z := by simp [x]
  have hiff := compactCauchyKernel_mem_iff_resolvent S x hx
  have hsub := coordinate_resolventSet_subset_compl S x hx
  have hcl : IsClopen {w : ↥(Kᶜ) | compactCauchyKernel K w ∈ S} := by
    refine ⟨(show IsClosed (S : Set C(K, ℂ)) from inferInstance).preimage
      (continuous_compactCauchyKernel K), ?_⟩
    have he : {w : ↥(Kᶜ) | compactCauchyKernel K w ∈ S} =
        Subtype.val ⁻¹' resolventSet ℂ x := by ext w; exact hiff w
    rw [he]
    exact (spectrum.isOpen_resolventSet x).preimage continuous_subtype_val
  have hgood : {w : ↥(Kᶜ) | compactCauchyKernel K w ∈ S}.Nonempty := by
    let v : ℂ := (‖x‖ + 1 : ℝ)
    have hv : v ∈ resolventSet ℂ x := by
      apply spectrum.mem_resolventSet_of_norm_lt
      simp only [v, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ + 1)]
      linarith
    exact ⟨⟨v, hsub hv⟩, (hiff _).mpr hv⟩
  have : PreconnectedSpace ↥(Kᶜ) := isPreconnected_iff_preconnectedSpace.mp hc.isPreconnected
  have he := Set.mem_univ w
  rwa [← hcl.eq_univ hgood] at he

theorem continuousOn_compactCauchyKernelExtension (K : Set ℂ) :
    ContinuousOn (compactCauchyKernelExtension K) Kᶜ := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert! continuous_compactCauchyKernel K using 1
  ext w z
  exact compactCauchyKernelExtension_apply w.property z

theorem intervalIntegral_mem_closedSubalgebra {E : Type*} [NormedCommRing E]
    [NormedAlgebra ℂ E] [CompleteSpace E] (S : Subalgebra ℂ E)
    (hS : IsClosed (S : Set E)) {g : ℝ → E}
    (hg : IntervalIntegrable g volume 0 1)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ S) :
    (∫ t in (0 : ℝ)..1, g t) ∈ S := by
  have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact (S.toSubmodule.restrictScalars ℝ).convex.integral_mem hS
    ((ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hm t (Ioc_subset_Icc_self ht))) hg.1

theorem holomorphic_mem_polynomialClosure_of_convex_neighborhood
    {K U : Set ℂ} [CompactSpace K] (hK : K.Nonempty) (hcomp : IsConnected Kᶜ)
    (hU : IsOpen U) (hUc : Convex ℝ U) (hKU : K ⊆ U)
    (Γ : CalculusContour K U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (⟨fun z : K => f z, hf.continuousOn.mono hKU |>.domRestrict⟩ : C(K, ℂ)) ∈
      (polynomialFunctions K).topologicalClosure := by
  let S := (polynomialFunctions K).topologicalClosure
  let g : ℝ → C(K, ℂ) := fun t =>
    (deriv Γ.path t * f (Γ.path t)) • compactCauchyKernelExtension K (Γ.path t)
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    exact (Γ.smooth.continuous_deriv_one.continuousOn.mul
      (hf.continuousOn.comp Γ.smooth.continuous.continuousOn
        (fun t ht => (Γ.avoids t ht).1))).smul
      ((continuousOn_compactCauchyKernelExtension K).comp Γ.smooth.continuous.continuousOn
        (fun t ht => (Γ.avoids t ht).2))
  have hi : IntervalIntegrable g volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hg
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ S := by
    intro t ht
    apply S.smul_mem
    classical
    unfold compactCauchyKernelExtension
    split
    · exact compactCauchyKernel_mem_polynomialClosure hK hcomp _
    · rename_i he
      exact (he (Γ.avoids t ht).2).elim
  have he : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∫ t in (0 : ℝ)..1, g t) =
      (⟨fun z : K => f z, hf.continuousOn.mono hKU |>.domRestrict⟩ : C(K, ℂ)) := by
    ext z
    change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (ContinuousMap.evalCLM ℂ z (∫ t in (0 : ℝ)..1, g t)) = f z
    rw [← (ContinuousMap.evalCLM ℂ z).intervalIntegral_comp_comm hi]
    have he : (∫ t in (0 : ℝ)..1, ContinuousMap.evalCLM ℂ z (g t)) =
        (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t) / (Γ.path t - z)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change (deriv Γ.path t * f (Γ.path t)) * compactCauchyKernelExtension K (Γ.path t) z = _
      dsimp only
      rw [compactCauchyKernelExtension_apply (Γ.avoids t (by simpa using ht)).2, div_eq_mul_inv]
    rw [he, Γ.toSmoothContour.cauchy_formula_convex hU hUc
      (by rintro _ ⟨t, ht, rfl⟩; exact (Γ.avoids t ht).1) hf (hKU z.property) ?_, Γ.index_inside z z.property, one_mul]
    rintro ⟨t, ht, htΓ⟩
    exact (Γ.avoids t ht).2 (htΓ.symm ▸ z.property)
  rw [← he]
  exact S.smul_mem (intervalIntegral_mem_closedSubalgebra S
    (polynomialFunctions K).isClosed_topologicalClosure hi hm) _

theorem exists_polynomial_uniform_approx_oai {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < ε := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp [he]⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let V := thickening δ K
  have hVo : IsOpen V := isOpen_thickening
  have hVc : Convex ℝ V := hc.thickening δ
  have hKV : K ⊆ V := self_subset_thickening hδ K
  have hVU : V ⊆ U := (thickening_subset_cthickening δ K).trans hδU
  obtain ⟨Γ⟩ := exists_calculusContour hK hc hne hVo hKV
  let g : C(K, ℂ) := ⟨fun z => f z, (hf.continuousOn.mono hKU).domRestrict⟩
  have hg : g ∈ (polynomialFunctions K).topologicalClosure :=
    holomorphic_mem_polynomialClosure_of_convex_neighborhood hne
      (isPathConnected_compl_of_bounded_convex hK.isBounded hc).isConnected
      hVo hVc hKV Γ (hf.mono hVU)
  change g ∈ closure (polynomialFunctions K : Set C(K, ℂ)) at hg
  obtain ⟨q, hq, hd⟩ := Metric.mem_closure_iff.mp hg ε hε
  rw [polynomialFunctions_coe] at hq
  obtain ⟨p, rfl⟩ := hq
  refine ⟨p, fun z hz => ?_⟩
  have hle := ContinuousMap.dist_apply_le_dist (f := g)
    (g := Polynomial.toContinuousMapOn p K) ⟨z, hz⟩
  rw [← dist_eq_norm, dist_comm]
  exact lt_of_le_of_lt hle hd

open scoped Matrix.Norms.L2Operator

universe u

end CrouzeixHilbert

end

end OAI
end

theorem solution : type_of% @OAI.CrouzeixHilbert.exists_polynomial_uniform_approx_oai := @OAI.CrouzeixHilbert.exists_polynomial_uniform_approx_oai
