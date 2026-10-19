-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:47:43.901409+00:00
-- url     : https://prove2.me/submissions/70e48b13-9b9a-4411-9e40-0c2630f91b55

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000
import Theorems.Thm_OAI_CrouzeixHilbert_Disk_integral_matrixHolomorphic
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
-- module Solutions.OAIQW_CrouzeixHilbert.InteriorCollar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

namespace CrouzeixHilbert.Conformal

namespace InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

lemma zero_mem_disk : (0 : ℂ) ∈ ball 0 R.radius := mem_ball_zero_iff.mpr (by simpa using R.one_lt_radius.trans' zero_lt_one)

lemma h_zero_mem : R.h 0 ∈ U := R.bijective_h.mapsTo (mem_ball_self zero_lt_one)

lemma f_h_zero : R.f (R.h 0) = 0 := R.inverse.2 (R.disk_subset R.zero_mem_disk)

end InteriorCollar

end CrouzeixHilbert.Conformal

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
-- module Solutions.OAIQW_CrouzeixHilbert.DiskCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Calculus. -/

noncomputable section

open MeasureTheory

open scoped Topology

namespace CrouzeixHilbert.Disk

section Series

attribute [local instance] OAI.CrouzeixHilbert.Disk.instFactLtRealOfNat_solutions
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

lemma integral_fourier (n : ℤ) : ∫ t : CircleSpace, fourier n t ∂σ = if n = 0 then 1 else 0 := by
  have h := congrFun (@fourierCoeff_fourier 1 _ n) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Pi.single_apply,
    eq_comm] using h

end Series

end CrouzeixHilbert.Disk

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.TensorDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Density. -/

noncomputable section

open MeasureTheory Set Filter

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorRealNormedSpace
attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorCompleteSpace
theorem tensorOperator_mul (A D : Operator H) {m : ℕ} (B C : Coeff m) :
    tensorOperator (A * D) (B * C) = tensorOperator A B * tensorOperator D C := by
  ext x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (tensorOperator (A * D) (B * C)).continuous
      ((tensorOperator A B).continuous.comp (tensorOperator D C).continuous)) ?_
  intro v
  simp only [tensorOperator, map_mul, mul_apply_eq_comp,
    ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_mul]

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
-- module Solutions.OAIQW_CrouzeixHilbert.ExteriorContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Contour. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma boundaryContour_deriv (t : ℝ) :
    deriv C.boundaryContour.path t =
      (2 * (Real.pi : ℂ) * I) * C.boundaryNormal (t : CircleSpace) := by
  have hc : C.radius < ‖unitCirclePath t‖ := by rw [unitCirclePath_norm]; exact C.radius_lt_one
  have hd := ((C.analytic _ hc).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    t (hasDerivAt_unitCirclePath t)
  change HasDerivAt C.boundaryContour.path _ t at hd
  rw [hd.deriv]
  change (unitCirclePath t * (2 * (Real.pi : ℂ) * I)) * deriv C.G (unitCirclePath t) = _
  change _ = (2 * (Real.pi : ℂ) * I) * (circleCoordinate (t : CircleSpace) * _)
  rw [circleCoordinate_coe]
  change (circleMap 0 1 (2 * Real.pi * t) * (2 * (Real.pi : ℂ) * I)) * _ = _
  unfold unitCirclePath
  ring

lemma boundaryContour_trace_subset : C.boundaryContour.trace ⊆ frontier U := by
  rintro z ⟨t,ht,rfl⟩
  exact C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr (unitCirclePath_norm t))

lemma boundaryContour_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t • f (C.boundaryContour.path t)) =
    ∫ t, C.boundaryNormal t • f (C.boundaryMap t) ∂circleMeasure := by
  rw [integral_circleMeasure_eq_interval, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [C.boundaryContour_deriv, smul_smul, inv_mul_cancel_left₀]
  · congr 1
    change f (C.G (unitCirclePath t)) = f (C.G (circleCoordinate (t : CircleSpace)))
    rw [circleCoordinate_coe]
    rfl
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

lemma exterior_value_not_mem (hU : IsOpen U) {t : ℂ} (ht : 1 ≤ ‖t‖) : C.G t ∉ U := by
  rcases ht.eq_or_lt with he|he
  · have hb := C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr he.symm)
    exact fun hz => hb.2 (hU.interior_eq.symm ▸ hz)
  · exact fun h => C.outside.mapsTo he (subset_closure h)

lemma reciprocalDenominator_inverse {z t : ℂ} (ht : C.radius < ‖t‖) :
    C.reciprocalDenominator z t⁻¹ = t⁻¹ * (C.G t - z) := by
  rw [C.laurent t ht, reciprocalDenominator]
  have hn : t ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  field_simp
  ring

lemma reciprocalDenominator_ne_zero (hU : IsOpen U) {z u : ℂ} (hz : z ∈ U)
    (hu : u ∈ closedBall 0 1) : C.reciprocalDenominator z u ≠ 0 := by
  by_cases hu0 : u = 0
  · simpa only [hu0, reciprocalDenominator, zero_mul, add_zero] using C.leading_ne_zero
  have ht : 1 ≤ ‖u⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hu0)).mpr (mem_closedBall_zero_iff.mp hu)
  have he := C.reciprocalDenominator_inverse (z := z) (C.radius_lt_one.trans_le ht)
  rw [inv_inv] at he
  rw [he]
  exact mul_ne_zero hu0 (sub_ne_zero.mpr (fun h => C.exterior_value_not_mem hU ht (h ▸ hz)))

lemma differentiableOn_reciprocalCauchy (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableOn ℂ (C.reciprocalCauchy z) (closedBall 0 1) := by
  apply DifferentiableOn.div
  · exact (differentiableOn_const _).sub ((differentiableOn_id.pow 2).mul
      (C.regular_analytic.deriv.differentiableOn.mono C.closed_unit_subset_reciprocalDisk))
  · exact (differentiableOn_const _).add (differentiableOn_id.mul
      ((C.regular_analytic.differentiableOn.mono C.closed_unit_subset_reciprocalDisk).sub_const z))
  · exact fun u hu => C.reciprocalDenominator_ne_zero hU hz hu

lemma reciprocalCauchy_boundary (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (t : CircleSpace) :
    C.reciprocalCauchy z (circleCoordinate t)⁻¹ =
      C.boundaryNormal t / (C.boundaryMap t - z) := by
  have ht : C.radius < ‖circleCoordinate t‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  rw [reciprocalCauchy, C.reciprocalDenominator_inverse ht, ← C.deriv_laurent ht]
  change deriv C.G (circleCoordinate t) / ((circleCoordinate t)⁻¹ * (C.G (circleCoordinate t) - z)) = _
  simp only [boundaryNormal, boundaryMap, ContinuousMap.coe_mk]
  have hden : C.G (circleCoordinate t) - z ≠ 0 :=
    sub_ne_zero.mpr fun he =>
      C.exterior_value_not_mem hU (norm_circleCoordinate t).ge (he ▸ hz)
  field_simp [hden]

lemma boundaryContour_index_inside (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    C.boundaryContour.index z = 1 := by
  change (2 * (Real.pi : ℂ) * I)⁻¹ •
    (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t * (C.boundaryContour.path t - z)⁻¹) = 1
  rw [show (fun t : ℝ => deriv C.boundaryContour.path t * (C.boundaryContour.path t - z)⁻¹) =
      fun t => deriv C.boundaryContour.path t • (C.boundaryContour.path t - z)⁻¹ from rfl,
    C.boundaryContour_integral (fun w => (w - z)⁻¹)]
  change (∫ t, C.boundaryNormal t / (C.boundaryMap t - z) ∂circleMeasure) = 1
  simp_rw [← C.reciprocalCauchy_boundary hU hz]
  rw [integral_holomorphic_inverse_circleCoordinate (C.differentiableOn_reciprocalCauchy hU hz)]
  simp [reciprocalCauchy, reciprocalDenominator, C.leading_ne_zero]

lemma boundaryContour_index_outside (hc : Convex ℝ U) {z : ℂ} (hz : z ∉ closure U) :
    C.boundaryContour.index z = 0 :=
  C.boundaryContour.index_eq_zero_of_convex hc.closure isClosed_closure
    (C.boundaryContour_trace_subset.trans frontier_subset_closure) hz

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Transport. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Conformal

open Boundary

lemma angular_derivative_real_nonneg {g : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ = 1)
    (hga : DifferentiableAt ℂ g z) (hnt : ∀ w, ‖w‖ = 1 → ‖g w‖ = 1)
    (hmax : IsLocalMaxOn (fun w => ‖g w‖^2) (closedBall 0 1) z) :
    (z * deriv g z / g z).im = 0 ∧ 0 ≤ (z * deriv g z / g z).re := by
  have hgz : ‖g z‖ = 1 := hnt z hz
  have hinv : (g z)⁻¹ = conj (g z) := Complex.inv_eq_conj hgz
  have hc : HasDerivAt (fun t : ℝ => g (z * circleMap 0 1 t)) ((z * I) * deriv g z) 0 := by
    have hp : HasDerivAt (fun t : ℝ => z * circleMap 0 1 t) (z * I) 0 := by
      simpa [circleMap_zero] using (hasDerivAt_circleMap 0 1 0).const_mul z
    have hg' : HasDerivAt g (deriv g z) (z * circleMap 0 1 (0 : ℝ)) := by
      simpa [circleMap_zero] using hga.hasDerivAt
    simpa [Function.comp_def, mul_comm] using (hg'.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hp
  have hc0 : ∀ t : ℝ, ‖g (z * circleMap 0 1 t)‖ ^ 2 = 1 := by
    intro t
    rw [hnt _ (by rw [norm_mul, hz]; simp), one_pow]
  have hd0 := (hc.norm_sq.congr_of_eventuallyEq (Eventually.of_forall (fun t => (hc0 t).symm))).unique
    (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply] at hd0
  simp only [circleMap_zero, ofReal_one, ofReal_zero, zero_mul, exp_zero, mul_one] at hd0
  have he0 : (z * deriv g z * conj (g z)).im = 0 := by
    have halg : (((z * I) * deriv g z) * conj (g z)).re =
        -(z * deriv g z * conj (g z)).im := by
      simp only [Complex.mul_re, Complex.mul_im, I_re, I_im, mul_zero, mul_one]
      ring
    change 2 * (((z * I) * deriv g z) * conj (g z)).re = 0 at hd0
    rw [halg] at hd0
    linarith
  have hdir := hmax.hasFDerivWithinAt_nonpos
    (hga.hasDerivAt.hasFDerivAt.restrictScalars ℝ).norm_sq.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset
      ((convex_closedBall (0 : ℂ) (1 : ℝ)).segment_subset
        (mem_closedBall_zero_iff.mpr hz.le) (mem_closedBall_self zero_le_one)))
  simp only [ContinuousLinearMap.comp_apply, smul_apply] at hdir
  simp only [innerSL_apply_apply] at hdir
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply] at hdir
  simp only [two_smul, zero_sub] at hdir
  change (((-z) * deriv g z) * conj (g z)).re +
    (((-z) * deriv g z) * conj (g z)).re ≤ 0 at hdir
  simp only [neg_mul, neg_re] at hdir
  rw [div_eq_mul_inv, hinv]
  exact ⟨he0, by linarith⟩

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

lemma angularJacobian_real_nonneg (t : CircleSpace) :
    (C.angularJacobian R t).im = 0 ∧ 0 ≤ (C.angularJacobian R t).re := by
  let g := R.f ∘ C.G
  have ht : C.radius < ‖circleCoordinate t‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  have hfg : DifferentiableAt ℂ R.f (C.G (circleCoordinate t)) :=
    (R.analytic_f _ (R.closure_subset_domain (C.boundaryMap_mem_frontier t).1)).differentiableAt
  have hg : DifferentiableAt ℂ g (circleCoordinate t) :=
    hfg.comp (circleCoordinate t) (C.analytic _ ht).differentiableAt
  have hn : ∀ w, ‖w‖ = 1 → ‖g w‖ = 1 := fun w hw => R.boundary_norm _
    (C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr hw))
  have hmax : IsLocalMaxOn (fun w => ‖g w‖^2) (closedBall 0 1) (circleCoordinate t) := by
    filter_upwards [nhdsWithin_le_nhds (C.parameter_open.mem_nhds ht), self_mem_nhdsWithin] with w hw hw1
    rw [hn _ (norm_circleCoordinate t), one_pow]
    have hwle : ‖g w‖ ≤ 1 := by
      rcases (mem_closedBall_zero_iff.mp hw1).eq_or_lt with h|h
      · exact (hn w h).le
      · exact (mem_ball_zero_iff.mp (R.bijective_f.mapsTo (C.inside ⟨hw,h⟩))).le
    nlinarith [norm_nonneg (g w)]
  have hp := angular_derivative_real_nonneg (norm_circleCoordinate t) hg hn hmax
  have hd : deriv g (circleCoordinate t) = deriv R.f (C.G (circleCoordinate t)) *
      deriv C.G (circleCoordinate t) :=
    deriv_comp _ (R.analytic_f _ (R.closure_subset_domain (C.boundaryMap_mem_frontier t).1)).differentiableAt
      (C.analytic _ ht).differentiableAt
  rw [hd] at hp
  have he : C.angularJacobian R t = circleCoordinate t *
      (deriv R.f (C.G (circleCoordinate t)) * deriv C.G (circleCoordinate t)) / g (circleCoordinate t) := by
    change circleCoordinate t * deriv C.G (circleCoordinate t) *
      deriv R.f (C.G (circleCoordinate t)) / R.f (C.G (circleCoordinate t)) = _
    dsimp only [g, Function.comp_def]
    ring
  rw [he]
  exact hp

lemma physical_integral_zero (hc : Convex ℝ U) {V : Set ℂ}
    (hV : IsOpen V) (hUV : closure U ⊆ V) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g V) :
    (∫ t, C.boundaryNormal t * g (C.boundaryMap t) ∂circleMeasure) = 0 := by
  have hs := null_homology_integral (fun _ : Fin 1 => C.boundaryContour)
    (fun _ => (1 : ℂ)) hV (fun _ => C.boundaryContour_trace_subset.trans
      (frontier_subset_closure.trans hUV))
    (U := V) (fun (w : ℂ) (hw : w ∉ V) => by
      simpa using C.boundaryContour_index_outside hc (z := w)
        (fun hwc => hw (hUV hwc))) hg
  simp only [Fin.sum_univ_one, one_smul] at hs
  change (∫ t, C.boundaryNormal t • g (C.boundaryMap t) ∂circleMeasure) = 0
  rw [← C.boundaryContour_integral g]
  exact hs

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

lemma interiorBoundary_ne_zero (t : CircleSpace) : C.interiorBoundary R t ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [C.norm_interiorBoundary]; exact one_ne_zero)

lemma integral_angularJacobian_pow_succ (hc : Convex ℝ U) (n : ℕ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^(n+1) ∂circleMeasure) = 0 := by
  have hz := C.physical_integral_zero hc R.isOpen_domain R.closure_subset_domain
    (R.analytic_f.deriv.differentiableOn.fun_mul (R.analytic_f.differentiableOn.pow n))
  convert hz using 1
  apply integral_congr_ae
  filter_upwards [] with t
  change (C.boundaryNormal t * deriv R.f (C.boundaryMap t) / C.interiorBoundary R t) *
    C.interiorBoundary R t ^ (n+1) = C.boundaryNormal t *
      (deriv R.f (C.boundaryMap t) * C.interiorBoundary R t ^ n)
  rw [pow_succ]
  field_simp [C.interiorBoundary_ne_zero R t]

lemma integral_angularJacobian (hU : IsOpen U) (hc : Convex ℝ U) :
    (∫ t, C.angularJacobian R t ∂circleMeasure) = 1 := by
  let a := R.h 0
  have haU : a ∈ U := R.h_zero_mem
  have ha : a ∈ R.domain := R.closure_subset_domain (subset_closure haU)
  have hfa : R.f a = 0 := R.f_h_zero
  let g := dslope R.f a
  have hg : AnalyticOnNhd ℂ g R.domain :=
    ((differentiableOn_dslope (R.isOpen_domain.mem_nhds ha)).mpr
      R.analytic_f.differentiableOn).analyticOnNhd R.isOpen_domain
  have hgn : ∀ z ∈ R.domain, g z ≠ 0 := by
    intro z hz
    by_cases he : z = a
    · subst z
      simpa only [g, dslope_same] using deriv_ne_zero_of_injOn R.isOpen_domain R.analytic_f.differentiableOn R.injective_f ha
    · dsimp only [g]
      rw [dslope_of_ne _ he, slope_def_module, hfa, sub_zero, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr he))
        (fun hh => he (R.injective_f hz ha (hh.trans hfa.symm)))
  have hfgg : ∀ z, (z-a) * g z = R.f z := fun z => by
    simpa only [smul_eq_mul, hfa, sub_zero] using sub_smul_dslope R.f a z
  have hd : ∀ z ∈ R.domain, deriv R.f z = g z + (z-a) * deriv g z := by
    intro z hz
    have heq : (fun w => (w-a) * g w) = R.f := funext hfgg
    have ht := ((hasDerivAt_id z).sub_const a).mul (hg z hz).differentiableAt.hasDerivAt
    have hd := ht.deriv
    change deriv (fun w => (w-a) * g w) z = 1 * g z + (z-a) * deriv g z at hd
    simpa only [heq, one_mul] using hd
  let v : ℂ → ℂ := fun z => deriv g z / g z
  have hv : DifferentiableOn ℂ v R.domain := hg.deriv.differentiableOn.div
    hg.differentiableOn hgn
  have hz := C.physical_integral_zero hc R.isOpen_domain R.closure_subset_domain hv
  have hba (t : CircleSpace) : C.boundaryMap t ≠ a := fun he =>
    (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ (he ▸ haU))
  have hbc (t : CircleSpace) : C.boundaryMap t ∈ R.domain :=
    R.closure_subset_domain (C.boundaryMap_mem_frontier t).1
  have heq (t : CircleSpace) : C.angularJacobian R t =
      C.boundaryNormal t / (C.boundaryMap t-a) + C.boundaryNormal t * v (C.boundaryMap t) := by
    change C.boundaryNormal t * deriv R.f (C.boundaryMap t) / R.f (C.boundaryMap t) = _
    rw [hd _ (hbc t), ← hfgg]
    dsimp only [v]
    field_simp [hgn _ (hbc t), sub_ne_zero.mpr (hba t)]
  have hi1 : Integrable (fun t => C.boundaryNormal t / (C.boundaryMap t-a)) circleMeasure :=
    (C.boundaryNormal.continuous.div (C.boundaryMap.continuous.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hba t))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun t => C.boundaryNormal t * v (C.boundaryMap t)) circleMeasure :=
    (C.boundaryNormal.continuous.mul (hv.continuousOn.comp_continuous
      C.boundaryMap.continuous hbc)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp_rw [heq]
  rw [integral_add hi1 hi2, hz, add_zero]
  have hh := C.boundaryContour_index_inside hU haU
  change (2 * (Real.pi : ℂ) * I)⁻¹ •
    (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t * (C.boundaryContour.path t - a)⁻¹) = 1 at hh
  rw [show (fun t : ℝ => deriv C.boundaryContour.path t * (C.boundaryContour.path t - a)⁻¹) =
      fun t => deriv C.boundaryContour.path t • (C.boundaryContour.path t - a)⁻¹ from rfl,
    C.boundaryContour_integral (fun w => (w-a)⁻¹)] at hh
  exact hh

lemma integral_angularJacobian_pow (hU : IsOpen U) (hc : Convex ℝ U) (n : ℕ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^n ∂circleMeasure) =
      if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp only [pow_zero, mul_one, ↓reduceIte]; exact C.integral_angularJacobian R hU hc
  | succ n => simpa only [Nat.succ_ne_zero, ↓reduceIte] using C.integral_angularJacobian_pow_succ R hc n

lemma conj_angularJacobian (t : CircleSpace) : conj (C.angularJacobian R t) = C.angularJacobian R t := by
  apply Complex.ext <;> simp [(C.angularJacobian_real_nonneg R t).1]

lemma integral_angularJacobian_zpow (hU : IsOpen U) (hc : Convex ℝ U) (j : ℤ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^j ∂circleMeasure) =
      if j = 0 then 1 else 0 := by
  cases j with
  | ofNat n =>
    change (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^(n : ℤ) ∂circleMeasure) =
      if (n : ℤ) = 0 then 1 else 0
    simpa only [zpow_natCast, Nat.cast_eq_zero] using C.integral_angularJacobian_pow R hU hc n
  | negSucc n =>
    have he (t : CircleSpace) : C.angularJacobian R t * (C.interiorBoundary R t)^((Int.negSucc n)) =
        conj (C.angularJacobian R t * (C.interiorBoundary R t)^(n+1)) := by
      rw [zpow_negSucc, ← inv_pow, Complex.inv_eq_conj (C.norm_interiorBoundary R t),
        map_mul, C.conj_angularJacobian, map_pow]
    simp_rw [he]
    rw [integral_conj, C.integral_angularJacobian_pow_succ R hc, map_zero]
    simp

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Measure. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

attribute [local instance] OAI.CrouzeixHilbert.Conformal.instFactLtRealOfNat_solutions
variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

lemma circleCoordinate_interiorAngle (t : CircleSpace) :
    circleCoordinate (C.interiorAngle R t) = C.interiorBoundary R t := by
  simp only [circleCoordinate, fourier_one]
  rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1 : ℝ) ≠ 0)]
  exact congrArg Subtype.val ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).apply_symm_apply _)

lemma fourier_interiorAngle (j : ℤ) (t : CircleSpace) :
    fourier j (C.interiorAngle R t) = (C.interiorBoundary R t)^j := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  have he := C.circleCoordinate_interiorAngle R t
  simp only [circleCoordinate, fourier_one] at he
  rw [he]

lemma angularIntegralCLM_eq (hU : IsOpen U) (hc : Convex ℝ U) :
    C.angularIntegralCLM R = circleIntegralCLM := by
  apply ContinuousLinearMap.ext_on (s := range (fourier (T := (1 : ℝ))))
  · rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      span_fourier_closure_eq_top, Submodule.top_coe]
  · rintro f ⟨j,rfl⟩
    change (∫ t, C.angularJacobian R t * fourier j (C.interiorAngle R t) ∂circleMeasure) =
      ∫ t, fourier j t ∂circleMeasure
    simp_rw [C.fourier_interiorAngle]
    rw [C.integral_angularJacobian_zpow R hU hc, Disk.integral_fourier]

lemma integral_angularChange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hU : IsOpen U) (hc : Convex ℝ U) (f : C(CircleSpace, E)) :
    (∫ t, C.angularJacobian R t • f (C.interiorAngle R t) ∂circleMeasure) =
      ∫ t, f t ∂circleMeasure := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro l
  have h1 : Integrable (fun t => C.angularJacobian R t • f (C.interiorAngle R t)) circleMeasure :=
    ((C.angularJacobian R).continuous.smul (f.continuous.comp (C.interiorAngle R).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable f circleMeasure := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← l.integral_comp_comm h1, ← l.integral_comp_comm h2]
  simp only [map_smul, smul_eq_mul]
  exact congrArg (fun L : C(CircleSpace, ℂ) →L[ℂ] ℂ => L ⟨l ∘ f, l.continuous.comp f.continuous⟩)
    (C.angularIntegralCLM_eq R hU hc)

end ExteriorCollar

end CrouzeixHilbert.Conformal

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

lemma holomorphicEval_polynomial_comp {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (p : Polynomial ℂ) :
    holomorphicEval A U (fun z => p.eval (f z)) = Polynomial.aeval (holomorphicEval A U f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, map_add]
    rw [holomorphicEval_add A hU hKU
      (show DifferentiableOn ℂ (fun z => p.eval (f z)) U from p.differentiable.comp_differentiableOn hf)
      (show DifferentiableOn ℂ (fun z => q.eval (f z)) U from q.differentiable.comp_differentiableOn hf), hp, hq]
  | monomial n c =>
    have hpow : holomorphicEval A U (fun z => f z ^ n) = holomorphicEval A U f ^ n := by
      induction n with
      | zero => simpa only [pow_zero, map_one] using holomorphicEval_const A hU hKU (1 : ℂ)
      | succ n ih =>
        simp_rw [pow_succ]
        rw [holomorphicEval_mul A hU hKU (f := fun z => f z^n) (hf.pow n) hf, ih]
    simp only [Polynomial.eval_monomial, Polynomial.aeval_monomial]
    rw [holomorphicEval_smul A hU hKU (f := fun z => f z^n) (hf.pow n), hpow, Algebra.smul_def]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.FunctionalComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Functional Composition. -/

noncomputable section

open Set Filter Metric Topology Complex MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

lemma intertwines_aeval {B : Type*} [Ring B] [Algebra ℂ B]
    (S T D : B) (h : S * T = D * S) (p : Polynomial ℂ) :
    S * Polynomial.aeval T p = Polynomial.aeval D p * S := by
  have hp (n : ℕ) : S * T^n = D^n * S := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hq hr => simp only [map_add, mul_add, add_mul, hq, hr]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial]
    rw [← mul_assoc, (Algebra.commutes c S).symm, mul_assoc, hp, ← mul_assoc]

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

lemma holomorphicEval_comp_intertwines (A D S : Operator H) (hN : ‖D‖ ≤ 1)
    {U V : Set ℂ} (hU : IsOpen U) (hKU : numericalClosure A ⊆ U)
    (hV : IsOpen V) (hKV : closedBall (0 : ℂ) 1 ⊆ V)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g V)
    (hfU : MapsTo f U V) (hfK : MapsTo f (numericalClosure A) (closedBall 0 1))
    (hI : S * holomorphicEval A U f = D * S) :
    S * holomorphicEval A U (g ∘ f) = holomorphicEval D V g * S := by
  let K : Set ℂ := closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hDK : numericalClosure D ⊆ K :=
    (numericalClosure_subset_closedBall D).trans (closedBall_subset_closedBall hN)
  obtain ⟨ε,hε,hεV⟩ := hK.exists_cthickening_subset_open hV hKV
  let L := cthickening ε K
  have hKL : K ⊆ interior L :=
    (self_subset_thickening hε _).trans (thickening_subset_interior_cthickening _ _)
  let W := U ∩ f ⁻¹' interior L
  have hW : IsOpen W := hf.continuousOn.isOpen_inter_preimage hU isOpen_interior
  have hAW : numericalClosure A ⊆ W := fun z hz => ⟨hKU hz,hKL (hfK hz)⟩
  have hfW : DifferentiableOn ℂ f W := hf.mono inter_subset_left
  have hAWL : MapsTo f W L := fun z hz => interior_subset hz.2
  have hWL : W ⊆ U := inter_subset_left
  have hgf := hg.comp hf hfU
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hW hAW
  obtain ⟨Δ₀⟩ := exists_calculusContour (isCompact_numericalClosure D)
    (convex_numericalClosure D) (numericalClosure_nonempty D) isOpen_interior (hDK.trans hKL)
  let Δ : CalculusContour (numericalClosure D) V := {
    toSmoothContour := Δ₀.toSmoothContour
    avoids := fun t ht => ⟨hεV (interior_subset (Δ₀.avoids t ht).1), (Δ₀.avoids t ht).2⟩
    index_inside := Δ₀.index_inside
    index_outside := fun z hz => Δ₀.index_outside z (fun he => hz (hεV (interior_subset he))) }
  have hΔL : Δ.toSmoothContour.trace ⊆ L := by
    rintro z ⟨t,ht,rfl⟩
    exact interior_subset (Δ₀.avoids t ht).1
  have hΓW : Γ.toSmoothContour.trace ⊆ W := by
    rintro z ⟨t,ht,rfl⟩
    exact (Γ.avoids t ht).1
  obtain ⟨p,hp⟩ := exists_polynomial_tendstoUniformlyOn hK.cthickening (hKc.cthickening ε) hV hεV hg
  have hpd := tendsto_contourEval D Δ (fun n => (p n).continuous.continuousOn) (hp.mono hΔL)
  simp_rw [contourEval_polynomial, ← holomorphicEval_eq_contourEval D hV hg Δ] at hpd
  have hpa : Tendsto (fun n => Polynomial.aeval (holomorphicEval A U f) (p n)) atTop
      (𝓝 (holomorphicEval A U (g ∘ f))) := by
    have hp' : TendstoUniformlyOn (fun n z => (p n).eval (f z)) (g ∘ f) atTop Γ.toSmoothContour.trace := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro δ hδ
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hp δ hδ] with n hn z hz
      exact hn (f z) (hAWL (hΓW hz))
    have hh := tendsto_contourEval A Γ
      (fun n => (p n).continuous.comp_continuousOn (hf.continuousOn.mono (hΓW.trans hWL))) hp'
    have he (n : ℕ) : contourEval A Γ.toSmoothContour (fun z => (p n).eval (f z)) =
        Polynomial.aeval (holomorphicEval A U f) (p n) := by
      calc
        _ = holomorphicEval A W (fun z => (p n).eval (f z)) :=
          (holomorphicEval_eq_contourEval A hW ((p n).differentiable.comp_differentiableOn hfW) Γ).symm
        _ = Polynomial.aeval (holomorphicEval A W f) (p n) :=
          holomorphicEval_polynomial_comp A hW hAW hfW (p n)
        _ = _ := by rw [holomorphicEval_restrict A hW hU hAW hWL hf]
    change Tendsto (fun n => contourEval A Γ.toSmoothContour (fun z => (p n).eval (f z))) atTop
      (𝓝 (contourEval A Γ.toSmoothContour (g ∘ f))) at hh
    simp_rw [he, ← holomorphicEval_eq_contourEval A hW (hgf.mono hWL) Γ,
      holomorphicEval_restrict A hW hU hAW hWL hgf] at hh
    exact hh
  have hh := (tendsto_const_nhds (x := S)).mul hpa
  have he (n : ℕ) : S * Polynomial.aeval (holomorphicEval A U f) (p n) =
      Polynomial.aeval D (p n) * S := intertwines_aeval S _ D hI (p n)
  simp_rw [he] at hh
  exact (tendsto_nhds_unique hh (hpd.mul tendsto_const_nhds))

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Density. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physicalDensityOperatorRealNormedSpace
lemma integral_operatorDensity_pullback (D : Operator H) (hD : spectralRadius ℂ D < 1)
    (hU : IsOpen U) (hc : Convex ℝ U) {m : ℕ} (F : C(CircleSpace, Coeff m)) :
    (∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.interiorAngle R t)) ∂circleMeasure) =
      ∫ t, tensorOperator (Disk.phi D t) (F t) ∂circleMeasure := by
  let V : C(CircleSpace, Operator (Amplification H m)) :=
    ⟨fun t => tensorOperator (Disk.phi D t) (F t),
      ((tensorBilinearCLM m).continuous.comp (Disk.continuous_phi D hD)).clm_apply F.continuous⟩
  have he (t : CircleSpace) : tensorOperator (C.operatorDensity R D hD t) (F (C.interiorAngle R t)) =
      C.angularJacobian R t • V (C.interiorAngle R t) := by
    change tensorOperator (C.angularJacobian R t • Disk.phi D (C.interiorAngle R t)) _ = _
    exact (tensorOperatorCLM _).map_smul _ _
  simp_rw [he]
  exact C.integral_angularChange R hU hc V

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Calculus. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

lemma isOpen_pullbackDomain {V : Set ℂ} (hV : IsOpen V) : IsOpen (R.pullbackDomain V) :=
  R.analytic_h.continuousOn.isOpen_inter_preimage isOpen_ball hV

lemma closedDisk_subset_pullbackDomain {V : Set ℂ} (hUV : closure U ⊆ V) :
    closedBall (0 : ℂ) 1 ⊆ R.pullbackDomain V := fun _ hz =>
  ⟨R.closedDisk_subset hz,hUV (R.closed_h.mapsTo hz)⟩

lemma differentiableOn_pullback {V : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V) :
    DifferentiableOn ℂ (f ∘ R.h) (R.pullbackDomain V) :=
  hf.comp (R.analytic_h.differentiableOn.mono inter_subset_left) (fun _ hz => hz.2)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

lemma holomorphic_intertwines (A D S : Operator H) (hKU : numericalClosure A ⊆ U)
    (hN : ‖D‖ ≤ 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g V) :
    S * holomorphicEval A V g =
      holomorphicEval D (R.pullbackDomain V) (g ∘ R.h) * S := by
  let W := R.domain ∩ R.f ⁻¹' R.pullbackDomain V
  have hW : IsOpen W := R.analytic_f.continuousOn.isOpen_inter_preimage R.isOpen_domain
    (R.isOpen_pullbackDomain hV)
  have hAW : numericalClosure A ⊆ W := fun z hz =>
    ⟨R.closure_subset_domain (subset_closure (hKU hz)),
      R.closedDisk_subset_pullbackDomain hUV (R.closed_f.mapsTo (subset_closure (hKU hz)))⟩
  have hWV : W ⊆ V := fun z hz => by
    have hh := hz.2.2
    change R.h (R.f z) ∈ V at hh
    rwa [R.inverse.1 hz.1] at hh
  have hfW := R.analytic_f.differentiableOn.mono (show W ⊆ R.domain from inter_subset_left)
  have hgW : DifferentiableOn ℂ ((g ∘ R.h) ∘ R.f) W :=
    (R.differentiableOn_pullback hg).comp hfW (fun z hz => hz.2)
  have hid : holomorphicEval A W ((g ∘ R.h) ∘ R.f) = holomorphicEval A V g := by
    rw [holomorphicEval_congr A hW hAW hgW (hg.mono hWV)
      (fun z hz => congrArg g (R.inverse.1 hz.1)),
      holomorphicEval_restrict A hW hV hAW hWV hg]
  have hiW : S * holomorphicEval A W R.f = D * S := by
    rw [holomorphicEval_restrict A hW R.isOpen_domain hAW inter_subset_left R.analytic_f.differentiableOn]
    exact hI
  have hh := holomorphicEval_comp_intertwines A D S hN hW hAW
    (R.isOpen_pullbackDomain hV) (R.closedDisk_subset_pullbackDomain hUV)
    hfW (R.differentiableOn_pullback hg) (fun z hz => hz.2)
    (fun z hz => R.closed_f.mapsTo (subset_closure (hKU hz))) hiW
  rw [hid] at hh
  exact hh

lemma matrixHolomorphic_intertwines (A D S : Operator H) (hKU : numericalClosure A ⊆ U)
    (hN : ‖D‖ ≤ 1) (hI : S * holomorphicEval A R.domain R.f = D * S)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    tensorOperator S (1 : Coeff m) * matrixHolomorphicEval A V F =
      matrixHolomorphicEval D (R.pullbackDomain V) (F ∘ R.h) * tensorOperator S (1 : Coeff m) := by
  unfold matrixHolomorphicEval
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← tensorOperator_mul, ← tensorOperator_mul, one_mul, mul_one]
  exact congrArg (fun T => tensorOperator T (Matrix.single i j 1))
    (R.holomorphic_intertwines A D S hKU hN hI hV hUV (hF i j))

end Conformal.InteriorCollar

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma h_interiorAngle (t : CircleSpace) :
    R.h (circleCoordinate (C.interiorAngle R t)) = C.boundaryMap t := by
  rw [C.circleCoordinate_interiorAngle]
  exact R.inverse.1 (R.closure_subset_domain (C.boundaryMap_mem_frontier t).1)

attribute [local instance] OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physicalCalculusOperatorRealNormedSpace
lemma integral_operatorDensity_holomorphic (hU : IsOpen U) (hc : Convex ℝ U)
    (D : Operator H) (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    (∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.boundaryMap t)) ∂circleMeasure) =
      matrixHolomorphicEval D (R.pullbackDomain V) (F ∘ R.h) := by
  let F₀ := R.diskTrace hUV F hF.continuousOn
  have he (t : CircleSpace) : F (C.boundaryMap t) = F₀ (C.interiorAngle R t) := by
    change _ = F (R.h (circleCoordinate (C.interiorAngle R t)))
    rw [C.h_interiorAngle R]
  simp_rw [he]
  rw [C.integral_operatorDensity_pullback R D hD hU hc]
  exact Disk.integral_matrixHolomorphic D hN hD (F := F ∘ R.h)
    (R.isOpen_pullbackDomain hV) (R.closedDisk_subset_pullbackDomain hUV)
    (fun i j => R.differentiableOn_pullback (hF i j))

variable [Nontrivial H]

lemma physical_intertwines_oai (hU : IsOpen U) (hc : Convex ℝ U)
    (A D S : Operator H) (hKU : numericalClosure A ⊆ U)
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    tensorOperator S (1 : Coeff m) * matrixHolomorphicEval A V F =
      (∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.boundaryMap t)) ∂circleMeasure) *
        tensorOperator S (1 : Coeff m) := by
  rw [C.integral_operatorDensity_holomorphic R hU hc D hN hD hV hUV hF]
  exact R.matrixHolomorphic_intertwines A D S hKU hN hI hV hUV hF

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_intertwines_oai.{u_1} := @OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_intertwines_oai.{u_1}
