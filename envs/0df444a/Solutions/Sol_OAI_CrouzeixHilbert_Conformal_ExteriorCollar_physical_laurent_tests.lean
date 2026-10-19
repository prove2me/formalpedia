-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_laurent_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:49:52.416323+00:00
-- url     : https://prove2.me/submissions/bbdfee75-bfe4-436b-bda1-c98c06a503ff

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_ExteriorCollar_physical_channel_intertwines
import Theorems.Thm_OAI_CrouzeixHilbert_sum_integral_eq_zero_of_null_homology

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Forms. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

section L2Multipliers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : ℕ}

theorem lpStar_apply_ae (u : Lp (HS k) 2 μ) :
    lpStar u =ᵐ[μ] fun t => toHS (ofHS (u t))ᴴ :=
  (hsStar k).toContinuousLinearMap.coeFn_compLpL u

@[simp] theorem lpStar_lpStar (u : Lp (HS k) 2 μ) : lpStar (lpStar u) = u := by
  apply Lp.ext
  filter_upwards [lpStar_apply_ae u, lpStar_apply_ae (lpStar u)] with t hu hsu
  simp only [hsu, hu, ofHS_toHS, Matrix.conjTranspose_conjTranspose, toHS_ofHS]

end L2Multipliers

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace lp Classical Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

attribute [local instance] OAI.CrouzeixHilbert.Boundary.instFactLtRealOfNat_solutions
lemma matrixFourierBasis_repr {k : ℕ} (u : BoundaryL2 k) (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr u a = fourierCoeff (lpEntry a.2 u) a.1 := by
  rw [HilbertBasis.repr_apply_apply, matrixFourierBasis_apply, inner_matrixFourier,
    ← coe_fourierBasis, ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

end CrouzeixHilbert.Boundary

end

end OAI
end

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

theorem contourEval_sub [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {f g : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hg : ContinuousOn g Γ.toSmoothContour.trace) :
    contourEval A Γ.toSmoothContour (f - g) =
      contourEval A Γ.toSmoothContour f - contourEval A Γ.toSmoothContour g := by
  simp only [contourEval_eq_kernel, Pi.sub_apply, sub_smul]
  rw [intervalIntegral.integral_sub (intervalIntegrable_contourIntegrand A Γ hf)
    (intervalIntegrable_contourIntegrand A Γ hg), smul_sub]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.MatrixContours
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix Contours. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance matrixContourOperatorRealNormedSpace_r2fa2f0_1 (m : ℕ) :
    NormedSpace ℝ (Operator (Amplification H m)) :=
  NormedSpace.restrictScalars ℝ ℂ _
theorem sum_tensorOperator_entries (A : Operator H) {m : ℕ} (B : Coeff m) :
    (∑ i, ∑ j, tensorOperator (B i j • A) (Matrix.single i j 1)) = tensorOperator A B := by
  have hsum : (∑ i, ∑ j, B i j • Matrix.single i j (1 : ℂ)) = B := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using (Matrix.matrix_eq_sum_single B).symm
  calc
    _ = ∑ i, ∑ j, B i j • tensorCoefficientCLM A m (Matrix.single i j 1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact map_smul (tensorOperatorCLM (Matrix.single i j 1)) (B i j) A
    _ = tensorCoefficientCLM A m (∑ i, ∑ j, B i j • Matrix.single i j 1) := by
      simp only [map_sum, map_smul]
    _ = tensorOperator A B := by rw [hsum]; rfl

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

theorem contourEval_const_mul (A : Operator H) (Γ : SmoothContour) (c : ℂ) (f : ℂ → ℂ) :
    contourEval A Γ (fun z => c * f z) = c • contourEval A Γ f := by
  simp only [contourEval_eq_kernel, mul_smul, intervalIntegral.integral_smul]
  exact smul_comm _ _ _

theorem contourEval_congr (A : Operator H) (Γ : SmoothContour) {f g : ℂ → ℂ}
    (hfg : EqOn f g Γ.trace) : contourEval A Γ f = contourEval A Γ g := by
  unfold contourEval
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hfg (show Γ.path t ∈ Γ.trace from
    mem_image_of_mem _ (by simpa using ht))]

theorem contourEval_mul_sub_of_integral_eq_zero [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) (a : ℂ) {f : ℂ → ℂ}
    (hf : ContinuousOn f Γ.toSmoothContour.trace)
    (hzero : (∫ t in (0 : ℝ)..1, deriv Γ.path t * f (Γ.path t)) = 0) :
    contourEval A Γ.toSmoothContour (fun z => (z - a) * f z) =
      (A - algebraMap ℂ (Operator H) a) * contourEval A Γ.toSmoothContour f := by
  have he : (fun z => (z - a) * f z) = (fun z => z * f z) - (fun z => a * f z) := by
    ext z
    exact sub_mul _ _ _
  rw [he, contourEval_sub A Γ (f := fun z => z * f z) (g := fun z => a * f z)
    (continuousOn_id.mul hf) (continuousOn_const.mul hf),
    contourEval_mul_id_of_integral_eq_zero A Γ hf hzero, contourEval_const_mul]
  rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem SmoothContour.integral_deriv_div_eq_zero (Γ : SmoothContour) {a : ℂ}
    (ha : Γ.index a = 0) :
    (∫ t in (0 : ℝ)..1, deriv Γ.path t / (Γ.path t - a)) = 0 := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact (mul_eq_zero.mp ha).resolve_left hc

theorem contourEval_inv_sub [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {a : ℂ} (ha : a ∉ U) :
    contourEval A Γ.toSmoothContour (fun z => (z - a)⁻¹) =
      Ring.inverse (A - algebraMap ℂ (Operator H) a) := by
  have hatrace (z : ℂ) (hz : z ∈ Γ.toSmoothContour.trace) : z - a ≠ 0 := by
    obtain ⟨t, ht, rfl⟩ := hz
    intro he
    exact ha (sub_eq_zero.mp he ▸ (Γ.avoids t ht).1)
  have hf : ContinuousOn (fun z : ℂ => (z - a)⁻¹) Γ.toSmoothContour.trace :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ hatrace
  have hzero : (∫ t in (0 : ℝ)..1, deriv Γ.path t * (Γ.path t - a)⁻¹) = 0 := by
    simpa only [div_eq_mul_inv] using
      Γ.toSmoothContour.integral_deriv_div_eq_zero (Γ.index_outside a ha)
  have he := contourEval_mul_sub_of_integral_eq_zero A Γ a hf hzero
  have hcongr : contourEval A Γ.toSmoothContour (fun z => (z - a) * (z - a)⁻¹) = 1 := by
    calc
      _ = contourEval A Γ.toSmoothContour (fun _ => 1) :=
        contourEval_congr A Γ.toSmoothContour (fun z hz => mul_inv_cancel₀ (hatrace z hz))
      _ = 1 := contourEval_one A Γ
  have haK : a ∉ numericalClosure A := by
    intro h
    exact one_ne_zero ((Γ.index_inside a h).symm.trans (Γ.index_outside a ha))
  have hu : IsUnit (A - algebraMap ℂ (Operator H) a) := by
    have hu0 : IsUnit (algebraMap ℂ (Operator H) a - A) := by
      change a ∈ resolventSet ℂ A
      by_contra h
      exact haK (spectrum_subset_numericalClosure A h)
    simpa only [neg_sub] using hu0.neg
  have h := (Ring.inverse_mul_eq_iff_eq_mul (A - algebraMap ℂ (Operator H) a)
    1 (contourEval A Γ.toSmoothContour (fun z => (z - a)⁻¹)) hu).mpr
      (hcongr.symm.trans he)
  simpa only [mul_one] using h.symm

end CrouzeixHilbert

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
variable [CompleteSpace H]

theorem tensorOperator_star (A : Operator H) {m : ℕ} (B : Coeff m) :
    tensorOperator (star A) (star B) = star (tensorOperator A B) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((tensorOperator (star A) (star B)).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro a
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (tensorOperator A B).continuous)) ?_
  intro b
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.inner_coe, map_star]
  induction a using TensorProduct.induction_on with
  | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
  | tmul x u =>
    induction b using TensorProduct.induction_on with
    | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
    | tmul y v => simp [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    | add b c hb hc => simp only [inner_add_right, map_add, hb, hc]
  | add a c ha hc => simp only [inner_add_left, map_add, ha, hc]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CauchyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cauchy Projection. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Boundary

theorem boundaryField_apply_ae {n : ℕ} (U : C(CircleSpace, Coeff n)) :
    boundaryField U =ᵐ[circleMeasure] fun t => toHS (U t) :=
  ContinuousMap.coeFn_toLp _ _

theorem integrable_tensor_field {n : ℕ} (E U : C(CircleSpace, Coeff n)) :
    Integrable (fun t => tensorOperator (matrixOperatorMap n (E t)) (U t)) circleMeasure := by
  have hc : Continuous (fun t => tensorOperator (matrixOperatorMap n (E t)) (U t)) :=
    ((tensorBilinearCLM n).continuous.comp
      ((matrixOperatorMap n).continuous.comp E.continuous)).clm_apply U.continuous
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem toHS_single {n : ℕ} (i j : Fin n) :
    toHS (Matrix.single i j (1 : ℂ)) = EuclideanSpace.single (i,j) (1 : ℂ) := by
  ext ⟨a,b⟩
  change (Matrix.single i j (1 : ℂ)) a b = _
  simp only [Matrix.single_apply, PiLp.single_apply]
  by_cases hai : a = i <;> by_cases hbj : b = j <;> simp [hai, hbj, Prod.ext_iff, eq_comm]

@[simp] theorem boundaryField_matrixLaurentMonomial {n : ℕ}
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    boundaryField (matrixLaurentMonomial a c) = c • matrixFourier a := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (matrixLaurentMonomial a c),
    matrixFourier_apply_ae a, Lp.coeFn_smul c (matrixFourier a)] with t hu hf hs
  rw [hu, hs, Pi.smul_apply, hf]
  change toHS ((c * fourier a.1 t) • Matrix.single a.2.1 a.2.2 (1 : ℂ)) = _
  rw [← toHSCLM_apply, map_smul, toHSCLM_apply, toHS_single, mul_smul]

end Boundary

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
-- module Solutions.OAIQW_CrouzeixHilbert.CircleAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle Analytic. -/

noncomputable section

open Set Metric Filter Topology Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Boundary

attribute [local instance] OAI.CrouzeixHilbert.Boundary.circleAnalyticFactZeroLtOne
lemma fourierCoeff_inverse_holomorphic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) (n : ℕ) :
    fourierCoeff (fun t : CircleSpace => f (circleCoordinate t)⁻¹) (n : ℤ) =
      if n = 0 then f 0 else 0 := by
  change (∫ t : CircleSpace, fourier (-(n : ℤ)) t • f (circleCoordinate t)⁻¹ ∂circleMeasure) = _
  simp_rw [← circleCoordinate_inverse_pow]
  rw [integral_holomorphic_inverse_circleCoordinate (f := fun u => u^n • f u)
    ((differentiableOn_id.pow n).smul hf)]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, zero_pow hn]

lemma repr_boundaryField {k : ℕ} (F : C(CircleSpace, Coeff k))
    (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr (boundaryField F) a =
      fourierCoeff (fun t => F t a.2.1 a.2.2) a.1 := by
  rw [matrixFourierBasis_repr]
  apply congrFun (fourierCoeff_congr_ae ?_) a.1
  filter_upwards [lpEntry_apply_ae a.2 (boundaryField F), boundaryField_apply_ae F] with t he hf
  rw [he, hf]
  rfl

lemma fourierProj_boundaryField_inverse_zero {k : ℕ} (F : C(CircleSpace, Coeff k))
    {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic (closedBall 0 1) f) (h0 : f 0 = 0)
    (hF : ∀ t, F t = f (circleCoordinate t)⁻¹) :
    fourierProjC k 0 (boundaryField F) = 0 ∧ fourierProjC k 1 (boundaryField F) = 0 := by
  classical
  have hr (a : ℤ × (Fin k × Fin k)) (ha : 0 ≤ a.1) :
      (matrixFourierBasis k).repr (boundaryField F) a = 0 := by
    rcases a with ⟨n,i,j⟩
    obtain ⟨m,rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [repr_boundaryField]
    simp_rw [hF]
    rw [fourierCoeff_inverse_holomorphic (hf i j)]
    split_ifs <;> simp [h0]
  constructor
  · apply (matrixFourierBasis k).repr.injective
    ext a
    rw [repr_fourierProjC, map_zero]
    change (if frequencyPart 0 a.1 then _ else 0) = 0
    split_ifs with ha
    · exact hr a (le_of_eq ((frequencyPart_zero a.1).mp ha).symm)
    · rfl
  · apply (matrixFourierBasis k).repr.injective
    ext a
    rw [repr_fourierProjC, map_zero]
    change (if frequencyPart 1 a.1 then _ else 0) = 0
    split_ifs with ha
    · exact hr a ((frequencyPart_pos a.1).mp ha).le
    · rfl

lemma fourierProj_boundaryField_inverse_neg {k : ℕ} (F : C(CircleSpace, Coeff k))
    {f : ℂ → Coeff k} (hf : EntrywiseHolomorphic (closedBall 0 1) f) (h0 : f 0 = 0)
    (hF : ∀ t, F t = f (circleCoordinate t)⁻¹) :
    fourierProjC k 2 (boundaryField F) = boundaryField F := by
  have hh := congrArg (fun L : BoundaryL2 k →L[ℂ] BoundaryL2 k => L (boundaryField F))
    (fourierProjC_total k)
  have hz := fourierProj_boundaryField_inverse_zero F hf h0 hF
  simpa only [add_apply, hz.1, hz.2, zero_add,
    ContinuousLinearMap.id_apply] using hh

open scoped Classical in

lemma fourierProj_matrixFourier {k : ℕ} (i : Fin 3) (a : ℤ × (Fin k × Fin k)) :
    fourierProjC k i (matrixFourier a) = if frequencyPart i a.1 then matrixFourier a else 0 := by
  classical
  apply (matrixFourierBasis k).repr.injective
  ext b
  rw [repr_fourierProjC]
  by_cases hba : b = a
  · subst b
    split_ifs <;> simp only [map_zero, lp.coeFn_zero, Pi.zero_apply]
  · have hz : (matrixFourierBasis k).repr (matrixFourier a) b = 0 := by
      rw [← matrixFourierBasis_apply, HilbertBasis.repr_self]
      simp [hba]
    split_ifs <;> simp only [hz, map_zero, lp.coeFn_zero, Pi.zero_apply]

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.AngularRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Radius. -/

noncomputable section

open Set Filter Metric Topology Function Complex MeasureTheory

namespace CrouzeixHilbert.Boundary

lemma integral_scaled_circleCoordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (R : ℝ) :
    (∫ t, f ((R : ℂ) * circleCoordinate t) ∂circleMeasure) = Real.circleAverage f 0 R := by
  rw [integral_circleCoordinate_eq_circleAverage (fun z => f ((R : ℂ) * z))]
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [circleMap, zero_add, ofReal_one, one_mul]

lemma integral_scaled_coordinate_cauchy {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) {R : ℝ} (hR : 0 < R) :
    (∫ t, ((R : ℂ) * circleCoordinate t) • f ((R : ℂ) * circleCoordinate t)
        ∂circleMeasure) =
      (2 * (Real.pi : ℂ) * I)⁻¹ • (∮ z in C(0, R), f z) := by
  rw [integral_scaled_circleCoordinate (fun z => z • f z) R,
    Real.circleAverage_eq_circleIntegral hR.ne']
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro z hz
  have hn : z ≠ 0 := norm_pos_iff.mp (by rw [mem_sphere_zero_iff_norm.mp hz]; exact hR)
  simp only [sub_zero, smul_smul, inv_mul_cancel₀ hn, one_smul]

lemma integral_scaled_deform {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {f : ℂ → E}
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : DifferentiableOn ℂ f (ball 0 R \ closedBall 0 r)) :
    (∫ t, ((R : ℂ) * circleCoordinate t) • f ((R : ℂ) * circleCoordinate t)
      ∂circleMeasure) =
    ∫ t, ((r : ℂ) * circleCoordinate t) • f ((r : ℂ) * circleCoordinate t)
      ∂circleMeasure := by
  rw [integral_scaled_coordinate_cauchy f (hr.trans_le hrR),
    integral_scaled_coordinate_cauchy f hr]
  congr 1
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR countable_empty hc
  intro z hz
  exact (hd z hz.1).differentiableAt ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hz.1)

lemma integral_laurent_deform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {f : ℂ → E}
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : DifferentiableOn ℂ f (ball 0 R \ closedBall 0 r)) (j : ℤ) :
    (∫ t, (((R : ℂ) * circleCoordinate t)^j) • f ((R : ℂ) * circleCoordinate t)
      ∂circleMeasure) =
    ∫ t, (((r : ℂ) * circleCoordinate t)^j) • f ((r : ℂ) * circleCoordinate t)
      ∂circleMeasure := by
  have hn {z : ℂ} (hz : z ∈ closedBall 0 R \ ball 0 r) : z ≠ 0 := by
    have hle : r ≤ ‖z‖ := not_lt.mp (mt mem_ball_zero_iff.mpr hz.2)
    exact norm_pos_iff.mp (hr.trans_le hle)
  have hh := integral_scaled_deform hr hrR
    (f := fun z => z^(j-1) • f z)
    ((continuousOn_id.zpow₀ (j-1) (fun z hz => Or.inl (hn hz))).smul hc)
    ((((differentiableOn_id (𝕜 := ℂ)).zpow (Or.inl (fun z hz => hn ⟨ball_subset_closedBall hz.1,
      fun h => hz.2 (ball_subset_closedBall h)⟩)))).smul hd)
  have hs {z : ℂ} (hz : z ≠ 0) : z * z^(j-1) = z^j := by
    rw [← zpow_one_add₀ hz]
    congr 1
    omega
  have hRz (t : CircleSpace) : (R : ℂ) * circleCoordinate t ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr (hr.trans_le hrR).ne') (circleCoordinate_ne_zero t)
  have hrz (t : CircleSpace) : (r : ℂ) * circleCoordinate t ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (circleCoordinate_ne_zero t)
  simpa only [smul_smul, hs (hRz _), hs (hrz _)] using hh

end CrouzeixHilbert.Boundary

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

section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

variable (A : Operator H)

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

lemma holomorphicEval_smul {U : Set ℂ} (hU : IsOpen U)
    (hKU : numericalClosure A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (c : ℂ) :
    holomorphicEval A U (fun z => c * f z) = c • holomorphicEval A U f := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  rw [holomorphicEval_eq_contourEval A hU (hf.const_mul c) Γ,
    holomorphicEval_eq_contourEval A hU hf Γ, contourEval_const_mul]

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

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Faber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Faber. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma physicalCoefficient_inside (hU : IsOpen U) (j : ℤ) {z : ℂ} (hz : z ∈ U) :
    C.physicalCoefficient j z =
      ∫ t, (circleCoordinate t)^j * (C.boundaryNormal t /
        (C.boundaryMap t - z)) ∂circleMeasure := by
  have hsub : closedBall (0 : ℂ) 2 \ ball 0 1 ⊆ {t | C.radius < ‖t‖} := by
    intro t ht
    exact C.radius_lt_one.trans_le (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2))
  have hn : ∀ t ∈ closedBall (0 : ℂ) 2 \ ball 0 1, C.G t - z ≠ 0 := by
    intro t ht
    exact sub_ne_zero.mpr (fun he => C.exterior_value_not_mem hU
      (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2)) (he ▸ hz))
  have hs : ball (0 : ℂ) 2 \ closedBall 0 1 ⊆ closedBall (0 : ℂ) 2 \ ball 0 1 :=
    fun t ht => ⟨ball_subset_closedBall ht.1, fun he => ht.2 (ball_subset_closedBall he)⟩
  have he := integral_laurent_deform (f := fun t => t * deriv C.G t / (C.G t - z))
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)
    ((continuousOn_id.mul (C.analytic.deriv.continuousOn.mono hsub)).div
      ((C.analytic.continuousOn.mono hsub).sub continuousOn_const) hn)
    ((differentiableOn_id.mul (C.analytic.deriv.differentiableOn.mono (hs.trans hsub))).div
      ((C.analytic.differentiableOn.mono (hs.trans hsub)).sub_const z)
      (fun t ht => hn t (hs ht))) j
  simpa only [ofReal_ofNat, ofReal_one, one_mul, smul_eq_mul, physicalCoefficient,
    boundaryNormal, boundaryMap, ContinuousMap.coe_mk] using he

lemma physicalCoefficient_inside_neg (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    {n : ℕ} (hn : n ≠ 0) : C.physicalCoefficient (-(n : ℤ)) z = 0 := by
  rw [C.physicalCoefficient_inside hU _ hz]
  simp_rw [← C.reciprocalCauchy_boundary hU hz, zpow_neg, zpow_natCast, ← inv_pow]
  rw [integral_holomorphic_inverse_circleCoordinate (f := fun u => u^n * C.reciprocalCauchy z u)
    ((differentiableOn_id.pow n).mul (C.differentiableOn_reciprocalCauchy hU hz))]
  simp [zero_pow hn]

lemma physicalCoefficient_inside_zero (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    C.physicalCoefficient 0 z = 1 := by
  rw [C.physicalCoefficient_inside hU _ hz]
  simp_rw [zpow_zero, one_mul, ← C.reciprocalCauchy_boundary hU hz]
  rw [integral_holomorphic_inverse_circleCoordinate (C.differentiableOn_reciprocalCauchy hU hz)]
  simp [reciprocalCauchy, reciprocalDenominator, C.leading_ne_zero]

lemma physicalCoefficient_closed_neg (hU : IsOpen U) {z : ℂ} (hz : z ∈ closure U)
    {n : ℕ} (hn : n ≠ 0) : C.physicalCoefficient (-(n : ℤ)) z = 0 := by
  exact (Set.EqOn.of_subset_closure
    (fun _ hy => C.physicalCoefficient_inside_neg hU hy hn)
    ((C.differentiableOn_physicalCoefficient _).continuousOn.mono C.closure_subset_outerDomain)
    continuousOn_const subset_closure (Subset.refl _)) hz

lemma physicalCoefficient_closed_zero (hU : IsOpen U) {z : ℂ} (hz : z ∈ closure U) :
    C.physicalCoefficient 0 z = 1 := by
  exact (Set.EqOn.of_subset_closure
    (fun _ hy => C.physicalCoefficient_inside_zero hU hy)
    ((C.differentiableOn_physicalCoefficient _).continuousOn.mono C.closure_subset_outerDomain)
    continuousOn_const subset_closure (Subset.refl _)) hz

lemma correctionMoment_outer (j : ℕ) {v : ℂ} (hv : v ∈ C.reciprocalDisk) :
    (∫ t, (2 * circleCoordinate t)^j *
      C.correction (2 * circleCoordinate t)⁻¹ v ∂circleMeasure) = C.correctionMoment j v := by
  have hs : closedBall (0 : ℂ) 2 \ ball 0 1 ⊆ {t | C.radius < ‖t‖} := by
    intro t ht
    exact C.radius_lt_one.trans_le (not_lt.mp (mt mem_ball_zero_iff.mpr ht.2))
  have hn : ∀ t ∈ closedBall (0 : ℂ) 2 \ ball 0 1, t ≠ 0 := fun t ht =>
    norm_pos_iff.mp (C.radius_pos.trans (hs ht))
  have hi : MapsTo (fun t : ℂ => t⁻¹) (closedBall 0 2 \ ball 0 1) C.reciprocalDisk :=
    fun t ht => C.inverse_mem_reciprocalDisk (hs ht)
  have hd : DifferentiableOn ℂ (fun t : ℂ => C.correction t⁻¹ v) (closedBall 0 2 \ ball 0 1) :=
    (C.differentiableOn_correction_left hv).comp (differentiableOn_id.inv hn) hi
  have he := integral_laurent_deform (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) ≤ 2) hd.continuousOn
    (hd.mono (fun t ht => ⟨ball_subset_closedBall ht.1, fun he => ht.2 (ball_subset_closedBall he)⟩)) (j : ℤ)
  simpa only [smul_eq_mul, ofReal_ofNat, ofReal_one, one_mul, zpow_natCast, correctionMoment] using he

lemma circle_model_moment (j : ℕ) {w : ℂ} (hw : ‖w‖ < 2) :
    (∫ t, (2 * circleCoordinate t)^j *
      (2 * circleCoordinate t / (2 * circleCoordinate t - w)) ∂circleMeasure) = w^j := by
  have hc := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (f := fun z : ℂ => z^j) countable_empty (mem_ball_zero_iff.mpr hw)
    (continuous_id.pow j).continuousOn
    (fun z _ => (differentiableAt_id.pow j))
  have he := integral_scaled_coordinate_cauchy (fun z : ℂ => (z-w)⁻¹ • z^j)
    (by norm_num : (0 : ℝ) < 2)
  rw [hc] at he
  convert he using 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [ofReal_ofNat, smul_eq_mul, div_eq_mul_inv]
  ring

lemma physicalCoefficient_boundary (j : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    C.physicalCoefficient (j : ℤ) (C.G w) = w^j + C.correctionMoment j w⁻¹ := by
  have hwC : C.radius < ‖w‖ := hw.symm ▸ C.radius_lt_one
  have hdiff (t : CircleSpace) : 2 * circleCoordinate t ≠ w := by
    intro he
    have hnorm := congrArg norm he
    rw [norm_mul, norm_ofNat, norm_circleCoordinate, mul_one, hw] at hnorm
    norm_num at hnorm
  have hsplit (t : CircleSpace) :
      (2 * circleCoordinate t)^j *
        ((2 * circleCoordinate t * deriv C.G (2 * circleCoordinate t)) /
          (C.G (2 * circleCoordinate t) - C.G w)) =
      (2 * circleCoordinate t)^j * (2 * circleCoordinate t / (2 * circleCoordinate t - w)) +
      (2 * circleCoordinate t)^j * C.correction (2 * circleCoordinate t)⁻¹ w⁻¹ := by
    rw [C.correction_eq (C.twice_coordinate_mem t) hwC (hdiff t)]
    ring
  have hc1 : Continuous (fun t : CircleSpace =>
      (2 * circleCoordinate t)^j * (2 * circleCoordinate t / (2 * circleCoordinate t - w))) :=
    ((continuous_const.mul circleCoordinate.continuous).pow j).mul
      ((continuous_const.mul circleCoordinate.continuous).div
        ((continuous_const.mul circleCoordinate.continuous).sub continuous_const)
        (fun t => sub_ne_zero.mpr (hdiff t)))
  have hc2 : Continuous (fun t : CircleSpace =>
      (2 * circleCoordinate t)^j * C.correction (2 * circleCoordinate t)⁻¹ w⁻¹) :=
    ((continuous_const.mul circleCoordinate.continuous).pow j).mul
      (C.continuousOn_correction.comp_continuous
        (((continuous_const.mul circleCoordinate.continuous).inv₀
          (fun t => mul_ne_zero (by norm_num) (circleCoordinate_ne_zero t))).prodMk continuous_const)
        (fun t => ⟨C.inverse_mem_reciprocalDisk (C.twice_coordinate_mem t), C.inverse_mem_reciprocalDisk hwC⟩))
  simp only [physicalCoefficient, zpow_natCast, hsplit]
  rw [integral_add (hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    circle_model_moment j (by rw [hw]; norm_num), C.correctionMoment_outer j (C.inverse_mem_reciprocalDisk hwC)]

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Fourier. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Boundary

lemma kernelLp_complex_smul {k : ℕ} (m : CircleKernel) (c : ℂ) (u : BoundaryL2 k) :
    kernelLp m (c • u) = c • kernelLp m u := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae m (c • u), kernelLp_apply_ae m u,
    Lp.coeFn_smul c (kernelLp m u)] with x hcu hu hsmul
  simp only [hcu, hsmul, Pi.smul_apply, hu, kernelApply]
  calc
    _ = ∫ y, c • (m (x,y) • u y) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c u] with y hy
      rw [hy]
      exact smul_comm (m (x,y)) c (u y)
    _ = _ := integral_smul c _

@[simp] lemma boundaryField_add {k : ℕ} (F G : C(CircleSpace, Coeff k)) :
    boundaryField (F+G) = boundaryField F + boundaryField G := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (F+G), boundaryField_apply_ae F, boundaryField_apply_ae G,
    Lp.coeFn_add (boundaryField F) (boundaryField G)] with t hfg hf hg hsum
  simp only [hfg, hsum, Pi.add_apply, hf, hg, ContinuousMap.add_apply]
  exact (toHSCLM k).map_add _ _

@[simp] lemma boundaryField_smul {k : ℕ} (c : ℂ) (F : C(CircleSpace, Coeff k)) :
    boundaryField (c • F) = c • boundaryField F := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (c • F), boundaryField_apply_ae F,
    Lp.coeFn_smul c (boundaryField F)] with t hcf hf hs
  simp only [hcf, hs, Pi.smul_apply, hf, ContinuousMap.smul_apply]
  exact (toHSCLM k).map_smul _ _

@[simp] lemma boundaryField_zero {k : ℕ} : boundaryField (0 : C(CircleSpace, Coeff k)) = 0 := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (0 : C(CircleSpace, Coeff k)), Lp.coeFn_zero (E := HS k) (p := 2) circleMeasure] with t he hz
  rw [he, hz]
  exact (toHSCLM k).map_zero

end Boundary

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

lemma boundaryKernel_complex (w t : CircleSpace) :
    (C.boundaryKernel (w,t) : ℂ) = 1 + C.boundaryCorrection (w,t) + conj (C.boundaryCorrection (w,t)) := by
  change (((1 : ℝ) + 2 * (C.boundaryCorrection (w,t)).re : ℝ) : ℂ) = _
  apply Complex.ext <;> simp [add_re, add_im, mul_re, mul_im]
  ring

lemma boundaryKernel_moment {j : ℕ} (hj : j ≠ 0) (w : CircleSpace) :
    (∫ t, (C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j ∂circleMeasure) =
      C.correctionMoment j (circleCoordinate w)⁻¹ := by
  have hb : Continuous (fun t => C.boundaryCorrection (w,t)) :=
    C.boundaryCorrection.continuous.comp (continuous_const.prodMk continuous_id)
  have hp := circleCoordinate.continuous.pow j
  have hi1 : Integrable (fun t => (circleCoordinate t)^j) circleMeasure :=
    hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun t => (circleCoordinate t)^j * C.boundaryCorrection (w,t)) circleMeasure :=
    (hp.mul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi3 : Integrable (fun t => conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j) circleMeasure :=
    ((continuous_conj.comp hb).mul hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : (∫ t : CircleSpace, ((circleCoordinate t)⁻¹)^j * C.boundaryCorrection (w,t)
      ∂circleMeasure) = 0 := by
    change (∫ t, ((circleCoordinate t)⁻¹)^j *
      C.correction (circleCoordinate t)⁻¹ (circleCoordinate w)⁻¹ ∂circleMeasure) = 0
    rw [integral_holomorphic_inverse_circleCoordinate
      (f := fun v => v^j * C.correction v (circleCoordinate w)⁻¹)
      ((differentiableOn_id.pow j).mul
        ((C.differentiableOn_correction_left (C.circle_inverse_mem w)).mono C.closed_unit_subset_reciprocalDisk))]
    simp
  have h3 : (∫ t, conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j ∂circleMeasure) = 0 := by
    have he := congrArg conj hz
    rw [← integral_conj] at he
    simp only [map_zero] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    rw [map_mul, map_pow, Complex.inv_eq_conj (norm_circleCoordinate t), conj_conj]
    ring
  have h1 : (∫ t : CircleSpace, (circleCoordinate t)^j ∂circleMeasure) = 0 := by
    rw [integral_holomorphic_circleCoordinate (f := fun z => z^j) (differentiableOn_id.pow j)]
    exact zero_pow hj
  have he (t : CircleSpace) : (C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j =
      (circleCoordinate t)^j + (circleCoordinate t)^j * C.boundaryCorrection (w,t) +
        conj (C.boundaryCorrection (w,t)) * (circleCoordinate t)^j := by
    rw [C.boundaryKernel_complex]; ring
  simp_rw [he]
  have hi12 : Integrable (fun t => (circleCoordinate t)^j + (circleCoordinate t)^j *
      C.boundaryCorrection (w,t)) circleMeasure := hi1.add hi2
  rw [integral_add hi12 hi3, integral_add hi1 hi2, h1, h3, zero_add, add_zero]
  rfl

lemma boundaryCauchy_complex_smul (hc : Convex ℝ U) {k : ℕ} (c : ℂ) (u : BoundaryL2 k) :
    boundaryCauchy (C.boundaryOperator hc k) (c • u) =
      c • boundaryCauchy (C.boundaryOperator hc k) u := by
  change fourierProjC k 0 (c • u) + fourierProjC k 1 (c • u) +
    fourierProjC k 2 (kernelLp C.boundaryKernel (fourierProjC k 1 (c • u))) =
    c • (fourierProjC k 0 u + fourierProjC k 1 u +
      fourierProjC k 2 (kernelLp C.boundaryKernel (fourierProjC k 1 u)))
  simp only [map_smul, kernelLp_complex_smul, smul_add]

lemma kernelLp_fourier_pos (hc : Convex ℝ U) {k : ℕ} (j : ℕ) (hj : j ≠ 0) (i l : Fin k) :
    C.boundaryOperator hc k (matrixFourier ((j : ℤ),i,l)) =
      boundaryField (C.correctionChannel (j,i,l)) := by
  apply Lp.ext
  filter_upwards [kernelLp_apply_ae C.boundaryKernel (matrixFourier ((j : ℤ),i,l)),
    boundaryField_apply_ae (C.correctionChannel (j,i,l))] with w hw hv
  change kernelLp C.boundaryKernel _ w = _
  rw [hw, hv]
  change (∫ t, C.boundaryKernel (w,t) • matrixFourier ((j : ℤ),i,l) t ∂circleMeasure) =
    toHS (C.correctionMoment j (circleCoordinate w)⁻¹ • Matrix.single i l (1 : ℂ))
  rw [← toHSCLM_apply, map_smul, toHSCLM_apply, toHS_single]
  calc
    _ = ∫ t, ((C.boundaryKernel (w,t) : ℂ) * (circleCoordinate t)^j) •
        EuclideanSpace.single (i,l) (1 : ℂ) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [matrixFourier_apply_ae ((j : ℤ),i,l)] with t ht
      rw [ht, circleCoordinate_pow, mul_smul]
      rfl
    _ = _ := by rw [integral_smul_const, C.boundaryKernel_moment hj]

lemma correctionChannel_negative {k : ℕ} (a : ℕ × (Fin k × Fin k)) :
    fourierProjC k 2 (boundaryField (C.correctionChannel a)) =
      boundaryField (C.correctionChannel a) := by
  apply fourierProj_boundaryField_inverse_neg (f := fun v =>
    C.correctionMoment a.1 v • Matrix.single a.2.1 a.2.2 (1 : ℂ))
  · intro i l
    exact ((C.differentiableOn_correctionMoment a.1).mono
      C.closed_unit_subset_reciprocalDisk).mul_const _
  · simp
  · exact fun _ => rfl

lemma boundaryCauchy_matrixFourier (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (a : ℤ × (Fin k × Fin k)) :
    boundaryCauchy (C.boundaryOperator hc k) (matrixFourier a) =
      boundaryField (C.physicalChannel a) := by
  classical
  change fourierProjC k 0 (matrixFourier a) + fourierProjC k 1 (matrixFourier a) +
    fourierProjC k 2 (C.boundaryOperator hc k (fourierProjC k 1 (matrixFourier a))) = _
  simp only [fourierProj_matrixFourier, frequencyPart_zero, frequencyPart_pos]
  rcases a with ⟨j,i,l⟩
  rcases lt_trichotomy j 0 with hj|hj|hj
  · simp only [ne_of_lt hj, not_lt_of_gt hj, ↓reduceIte, map_zero, zero_add]
    have he : C.physicalChannel (j,i,l) = 0 := by
      ext t a b
      obtain ⟨n,hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hj.le)
      have hjn : j = -(n : ℤ) := by omega
      have hn0 : n ≠ 0 := by omega
      change C.physicalCoefficient j (C.boundaryMap t) * _ = _
      rw [hjn, C.physicalCoefficient_closed_neg hU (C.boundaryMap_mem_frontier t).1 hn0]
      simp
    rw [he, boundaryField_zero]
  · subst j
    simp only [lt_self_iff_false, ↓reduceIte, map_zero, add_zero]
    have he : C.physicalChannel (0,i,l) = matrixLaurentMonomial (0,i,l) 1 := by
      ext t a b
      change C.physicalCoefficient 0 (C.boundaryMap t) * _ = _
      rw [C.physicalCoefficient_closed_zero hU (C.boundaryMap_mem_frontier t).1]
      simp [matrixLaurentMonomial]
    rw [he, boundaryField_matrixLaurentMonomial, one_smul]
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hj.le
    have hn : n ≠ 0 := by omega
    simp only [ne_of_gt hj, hj, ↓reduceIte, zero_add]
    rw [C.kernelLp_fourier_pos hc n hn, C.correctionChannel_negative]
    have he : C.physicalChannel ((n : ℤ),i,l) =
        matrixLaurentMonomial ((n : ℤ),i,l) 1 + C.correctionChannel (n,i,l) := by
      ext t a b
      change C.physicalCoefficient (n : ℤ) (C.G (circleCoordinate t)) * _ = _
      rw [C.physicalCoefficient_boundary n (norm_circleCoordinate t)]
      simp only [ContinuousMap.add_apply, matrixLaurentMonomial, correctionChannel,
        scalarChannel, ContinuousMap.coe_mk, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, one_mul, circleCoordinate_pow, add_mul]
    rw [he, boundaryField_add, boundaryField_matrixLaurentMonomial, one_smul]

lemma boundaryCauchy_matrixLaurentMonomial (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (a : ℤ × (Fin k × Fin k)) (c : ℂ) :
    boundaryCauchy (C.boundaryOperator hc k) (boundaryField (matrixLaurentMonomial a c)) =
      boundaryField (c • C.physicalChannel a) := by
  rw [boundaryField_matrixLaurentMonomial, C.boundaryCauchy_complex_smul,
    C.boundaryCauchy_matrixFourier hU hc, boundaryField_smul]

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.SimilarityRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Similarity Representation. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

section OperatorIntegral

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem integral_operator_adjoint (T : α → V →L[ℂ] V) :
    (∫ t, T t ∂μ).adjoint = ∫ t, (T t).adjoint ∂μ := by
  simpa only [starL'_apply, ContinuousLinearMap.star_eq_adjoint] using
    ((starL' ℝ : (V →L[ℂ] V) ≃L[ℝ] (V →L[ℂ] V)).integral_comp_comm T).symm

end OperatorIntegral

namespace Boundary

@[simp] theorem boundaryField_star {n : ℕ} (U : C(CircleSpace, Coeff n)) :
    boundaryField (boundaryStar U) = lpStar (boundaryField U) := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (boundaryStar U),
    boundaryField_apply_ae U, lpStar_apply_ae (boundaryField U)] with t hs hu hl
  rw [hs, hl, hu, ofHS_toHS]
  rfl

end Boundary

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.ResolventMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Resolvent Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma contourEval_circleIntegral (A : Operator H) {V : Set ℂ}
    (Γ : CalculusContour (numericalClosure A) V) (f : CircleSpace → ℂ → ℂ)
    (hf : ContinuousOn (fun p : ℝ × CircleSpace => f p.2 (Γ.path p.1)) (Icc 0 1 ×ˢ univ)) :
    contourEval A Γ.toSmoothContour (fun z => ∫ t, f t z ∂circleMeasure) =
      ∫ t, contourEval A Γ.toSmoothContour (f t) ∂circleMeasure := by
  let k (s : ℝ) (t : CircleSpace) := f t (Γ.path s) • contourKernel A Γ.toSmoothContour s
  have hc : ContinuousOn (uncurry k) (Icc 0 1 ×ˢ univ) :=
    hf.smul ((continuousOn_contourKernel A Γ).comp continuous_fst.continuousOn (fun p hp => hp.1))
  have hi := (hc.integrableOn_compact (μ := volume.prod circleMeasure)
    (isCompact_Icc.prod isCompact_univ)).mono_set (prod_mono Ioc_subset_Icc_self (Subset.refl univ))
  have hi' : Integrable (uncurry k) ((volume.restrict (uIoc 0 1)).prod circleMeasure) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ,
      uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hi
  simp only [contourEval_eq_kernel]
  simp_rw [← integral_smul_const]
  rw [intervalIntegral_integral_swap hi', integral_smul]

lemma ringInverse_neg {R : Type*} [Ring R] (a : R) : Ring.inverse (-a) = -Ring.inverse a := by
  rw [← neg_one_mul a, Ring.inverse_mul (Or.inl isUnit_one.neg)]
  have h : Ring.inverse (-1 : R) = (-1 : R) := by
    rw [show (-1 : R) = ((-1 : Rˣ) : R) from rfl, Ring.inverse_unit]
    simp
  rw [h, mul_neg_one]

lemma contourEval_sub_inv (A : Operator H) {V : Set ℂ}
    (Γ : CalculusContour (numericalClosure A) V) {a : ℂ} (ha : a ∉ V) :
    contourEval A Γ.toSmoothContour (fun z => (a - z)⁻¹) =
      Ring.inverse (algebraMap ℂ (Operator H) a - A) := by
  have hfun : (fun z : ℂ => (a-z)⁻¹) = (fun z => (-1 : ℂ) * (z-a)⁻¹) := by
    ext z
    rw [← neg_sub z a, inv_neg, neg_one_mul]
  rw [hfun, contourEval_const_mul, contourEval_inv_sub A Γ ha, neg_one_smul,
    ← ringInverse_neg, neg_sub]

end

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma boundary_difference_ne_zero (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (t : CircleSpace) :
    C.boundaryMap t - z ≠ 0 := fun he => C.boundaryMap_not_mem hU t (sub_eq_zero.mp he ▸ hz)

variable [Nontrivial H]

lemma integral_operatorResolvent_moment (A : Operator H) (hKU : numericalClosure A ⊆ U)
    (hU : IsOpen U) (j : ℤ) :
    (∫ t, (circleCoordinate t)^j • C.operatorResolvent A hKU hU t ∂circleMeasure) =
      holomorphicEval A C.outerDomain (C.physicalCoefficient j) := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  have hsub : U ⊆ C.outerDomain := subset_closure.trans C.closure_subset_outerDomain
  rw [← holomorphicEval_restrict A hU C.isOpen_outerDomain hKU hsub
    (C.differentiableOn_physicalCoefficient j), holomorphicEval_eq_contourEval A hU
      ((C.differentiableOn_physicalCoefficient j).mono hsub) Γ]
  have he : contourEval A Γ.toSmoothContour (C.physicalCoefficient j) =
      contourEval A Γ.toSmoothContour (fun z => ∫ t, (circleCoordinate t)^j *
        (C.boundaryNormal t / (C.boundaryMap t-z)) ∂circleMeasure) := by
    apply contourEval_congr
    rintro z ⟨s,hs,rfl⟩
    exact C.physicalCoefficient_inside hU j (Γ.avoids s hs).1
  rw [he]
  have hcont : ContinuousOn (fun p : ℝ × CircleSpace => (circleCoordinate p.2)^j *
      (C.boundaryNormal p.2 / (C.boundaryMap p.2 - Γ.path p.1))) (Icc 0 1 ×ˢ univ) := by
    exact ((circleCoordinate.continuous.zpow₀ j (fun t => Or.inl (circleCoordinate_ne_zero t))).comp continuous_snd).continuousOn.mul
      ((C.boundaryNormal.continuous.comp continuous_snd).continuousOn.div
        ((C.boundaryMap.continuous.comp continuous_snd).sub (Γ.smooth.continuous.comp continuous_fst)).continuousOn
        (fun p hp => C.boundary_difference_ne_zero hU (Γ.avoids p.1 hp.1).1 p.2))
  rw [contourEval_circleIntegral A Γ _ hcont]
  apply integral_congr_ae
  filter_upwards [] with t
  have heq : (fun z => (circleCoordinate t)^j * (C.boundaryNormal t / (C.boundaryMap t-z))) =
      (fun z => ((circleCoordinate t)^j * C.boundaryNormal t) * (C.boundaryMap t-z)⁻¹) := by
    ext z; simp only [div_eq_mul_inv, mul_assoc]
  rw [heq, contourEval_const_mul, contourEval_sub_inv A Γ (C.boundaryMap_not_mem hU t), mul_smul]
  rfl

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

lemma tensorOperator_smul_exchange
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator H) {m : ℕ} (c : ℂ) (B : Coeff m) :
    tensorOperator A (c • B) = tensorOperator (c • A) B := by
  exact ((tensorCoefficientCLM A m).map_smul c B).trans
    ((tensorOperatorCLM B).map_smul c A).symm

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]

lemma matrixHolomorphicEval_scalar (A : Operator H) {V : Set ℂ} (hV : IsOpen V)
    (hKV : numericalClosure A ⊆ V) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    {m : ℕ} (B : Coeff m) :
    matrixHolomorphicEval A V (fun z => f z • B) = tensorOperator (holomorphicEval A V f) B := by
  unfold matrixHolomorphicEval
  convert sum_tensorOperator_entries (holomorphicEval A V f) B using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Matrix.smul_apply, smul_eq_mul]
  simpa only [mul_comm] using holomorphicEval_smul A hV hKV hf (B i j)

end

namespace Boundary

lemma circleCoordinate_zpow (j : ℤ) (t : CircleSpace) :
    (circleCoordinate t)^j = fourier j t := by
  cases j with
  | ofNat k => exact circleCoordinate_pow k t
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow, circleCoordinate_inverse_pow]
    rfl

lemma boundaryStar_matrixLaurentMonomial {n : ℕ} (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    boundaryStar (matrixLaurentMonomial a c) =
      matrixLaurentMonomial (-a.1, a.2.2, a.2.1) (star c) := by
  ext t i j
  simp only [boundaryStar_apply, matrixLaurentMonomial, ContinuousMap.coe_mk,
    Matrix.conjTranspose_smul, star_mul, Matrix.conjTranspose_single, star_one,
    fourier_neg, Complex.star_def, mul_comm]

lemma tensorOperator_matrixLaurentMonomial
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : Operator H) {n : ℕ} (a : ℤ × (Fin n × Fin n)) (c : ℂ) (t : CircleSpace) :
    tensorOperator T (matrixLaurentMonomial a c t) =
      tensorOperatorCLM (Matrix.single a.2.1 a.2.2 1)
        (c • (circleCoordinate t)^a.1 • T) := by
  simpa only [matrixLaurentMonomial, ContinuousMap.coe_mk, tensorOperatorCLM_apply,
    mul_smul, circleCoordinate_zpow] using
    tensorOperator_smul_exchange T (c * fourier a.1 t) (Matrix.single a.2.1 a.2.2 1)

lemma integral_tensor_star {n : ℕ} (Q : C(CircleSpace, Coeff n)) (F : C(CircleSpace, Coeff n)) :
    (∫ t, tensorOperator (matrixOperatorMap n ((Q t)ᴴ)) (F t) ∂circleMeasure) =
      (tensorIntegral Q (boundaryStar F)).adjoint := by
  rw [tensorIntegral, integral_operator_adjoint]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [← ContinuousLinearMap.star_eq_adjoint, ← tensorOperator_star]
    simp only [boundaryStar_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, matrixOperatorMap_apply]
    congr 1
    exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).map_star' (Q t)

lemma tensorIntegral_add_left {n : ℕ} (P Q F : C(CircleSpace, Coeff n)) :
    tensorIntegral (P+Q) F = tensorIntegral P F + tensorIntegral Q F := by
  simp only [tensorIntegral, ContinuousMap.add_apply, map_add,
    ← tensorOperatorCLM_apply]
  exact integral_add (integrable_tensor_field P F) (integrable_tensor_field Q F)

end Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {n : ℕ} (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U)

variable [Nonempty (Fin n)]

include hKU in
lemma matrixHolomorphicEval_physicalRepresentative (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) =
      tensorOperator (c • holomorphicEval A C.outerDomain (C.physicalCoefficient a.1))
        (Matrix.single a.2.1 a.2.2 1) := by
  rw [show C.physicalRepresentative a c =
      (fun z => (c * C.physicalCoefficient a.1 z) • Matrix.single a.2.1 a.2.2 1) from rfl,
    matrixHolomorphicEval_scalar A C.isOpen_outerDomain
      (hKU.trans (subset_closure.trans C.closure_subset_outerDomain))
      ((C.differentiableOn_physicalCoefficient a.1).const_mul c),
    holomorphicEval_smul A C.isOpen_outerDomain
      (hKU.trans (subset_closure.trans C.closure_subset_outerDomain))
      (C.differentiableOn_physicalCoefficient a.1)]

lemma tensorIntegral_matrixResolvent_moment (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    tensorIntegral (C.matrixResolvent A hKU hU) (matrixLaurentMonomial a c) =
      matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) := by
  let : ContinuousSMul ℂ (EuclideanSpace ℂ (Fin n)) := IsBoundedSMul.continuousSMul
  let : CompleteSpace (Operator (EuclideanSpace ℂ (Fin n))) :=
    ContinuousLinearMap.instCompleteSpace
  rw [C.matrixHolomorphicEval_physicalRepresentative A hKU a c]
  simp only [tensorIntegral, C.matrixResolvent_operator,
    tensorOperator_matrixLaurentMonomial]
  have hi : Integrable (fun t => (circleCoordinate t)^a.1 • C.operatorResolvent A hKU hU t)
      circleMeasure :=
    ((circleCoordinate.continuous.zpow₀ a.1 (fun t => Or.inl (circleCoordinate_ne_zero t))).smul
      (C.operatorResolvent A hKU hU).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  refine ((tensorOperatorCLM (H := EuclideanSpace ℂ (Fin n))
    (Matrix.single a.2.1 a.2.2 1)).integral_comp_comm (hi.smul c)).trans ?_
  simp only [Pi.smul_apply, integral_smul, C.integral_operatorResolvent_moment A hKU hU,
    tensorOperatorCLM_apply]

lemma tensorIntegral_matrixResolventDensity (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    tensorIntegral (C.matrixResolventDensity A hKU hU) (matrixLaurentMonomial a c) =
      matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) +
      (matrixHolomorphicEval A C.outerDomain
        (C.physicalRepresentative (-a.1,a.2.2,a.2.1) (star c))).adjoint := by
  rw [matrixResolventDensity, tensorIntegral_add_left,
    C.tensorIntegral_matrixResolvent_moment A hKU hU]
  congr 1
  change (∫ t, tensorOperator (matrixOperatorMap n
    ((C.matrixResolvent A hKU hU t)ᴴ)) (matrixLaurentMonomial a c t) ∂circleMeasure) = _
  rw [integral_tensor_star, boundaryStar_matrixLaurentMonomial,
    C.tensorIntegral_matrixResolvent_moment A hKU hU]

variable (R : InteriorCollar U)

lemma physical_laurent_tests_oai (hc : Convex ℝ U)
    (D S : Operator (EuclideanSpace ℂ (Fin n)))
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    ∃ (V W : C(CircleSpace, Coeff n))
      (B L : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)),
      boundaryCauchy (C.boundaryOperator hc n) (boundaryField (matrixLaurentMonomial a c)) = boundaryField V ∧
      boundaryCauchy (C.boundaryOperator hc n) (lpStar (boundaryField (matrixLaurentMonomial a c))) = boundaryField W ∧
      tensorIntegral (C.matrixResolventDensity A hKU hU) (matrixLaurentMonomial a c) = B + L.adjoint ∧
      tensorOperator S (1 : Coeff n) * B =
        tensorIntegral (C.matrixDensity R D hD) V * tensorOperator S (1 : Coeff n) ∧
      tensorOperator S (1 : Coeff n) * L =
        tensorIntegral (C.matrixDensity R D hD) W * tensorOperator S (1 : Coeff n) := by
  refine ⟨c • C.physicalChannel a, star c • C.physicalChannel (-a.1,a.2.2,a.2.1),
    matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c),
    matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative (-a.1,a.2.2,a.2.1) (star c)),
    C.boundaryCauchy_matrixLaurentMonomial hU hc a c, ?_,
    C.tensorIntegral_matrixResolventDensity A hKU hU a c,
    C.physical_channel_intertwines A hKU hU R hc D S hN hD hI a c,
    C.physical_channel_intertwines A hKU hU R hc D S hN hD hI _ _⟩
  rw [← boundaryField_star, boundaryStar_matrixLaurentMonomial]
  exact C.boundaryCauchy_matrixLaurentMonomial hU hc _ _

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
end

theorem solution : type_of% @OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_laurent_tests_oai := @OAI.CrouzeixHilbert.Conformal.ExteriorCollar.physical_laurent_tests_oai
