-- Prove2me | solution 1 for LeblSCV.Pseudoconvex.hartogs_pseudoconvex_tfae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T13:01:40.894727+00:00
-- url     : https://prove2.me/submissions/94acbeb3-22d9-4ba8-ad3c-4f6fb4deb3e0

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsPlurisubharmonicOn
import Definitions.Def_LeblSCV_Pseudoconvex_IsHartogsPseudoconvex
import Definitions.Def_LeblSCV_Pseudoconvex_IsConvexWrt
import Definitions.Def_LeblSCV_Pseudoconvex_SatisfiesContinuityPrinciple
import Definitions.Def_LeblSCV_Pseudoconvex_hull
import Definitions.Def_LeblSCV_Pseudoconvex_IsClosedAnalyticDisc

set_option autoImplicit false

section P_ps13
open InnerProductSpace in
/-- The bundle's `IsHarmonicOn` on a ball plus continuity on the closed ball gives Mathlib's
`HarmonicContOnCl`. -/
theorem p0f0c_harmonicContOnCl {g : ℂ → ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (Metric.closedBall c r))
    (hh : LeblSCV.Pseudoconvex.IsHarmonicOn g (Metric.ball c r)) :
    HarmonicContOnCl g (Metric.ball c r) := by
  refine ⟨fun x hx => ⟨hh.1.contDiffAt (Metric.isOpen_ball.mem_nhds hx), ?_⟩, ?_⟩
  · exact Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun y hy => hh.2 y hy)
  · rw [closure_ball c hr.ne']; exact hg

open InnerProductSpace in
/-- Minimum principle for harmonic functions on a disc, via the Poisson formula. -/
theorem p0f0c_min_principle {G : ℂ → ℝ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : HarmonicContOnCl G (Metric.ball c r)) (m : ℝ)
    (hm : ∀ x ∈ Metric.sphere c r, m ≤ G x) :
    ∀ x ∈ Metric.ball c r, m ≤ G x := by
  intro w hw
  have hP := (hG.sub_const m).circleAverage_poissonKernel_smul hw
  have hnn : 0 ≤ Real.circleAverage (poissonKernel c w • (G - fun _ => m)) c r := by
    apply Real.circleAverage_nonneg_of_nonneg
    intro z hz
    rw [abs_of_pos hr] at hz
    have hzc : ‖z - c‖ = r := by rw [← dist_eq_norm]; exact hz
    have hwc : ‖w - c‖ < r := by rw [← dist_eq_norm]; exact hw
    have hk : 0 ≤ poissonKernel c w z := by
      rw [poissonKernel_def, hzc]
      apply div_nonneg _ (sq_nonneg _)
      nlinarith [norm_nonneg (w - c)]
    have hgz : 0 ≤ (G - fun _ : ℂ => m) z := by
      show 0 ≤ G z - m
      linarith [hm z hz]
    exact mul_nonneg hk hgz
  rw [hP] at hnn
  simp only [Pi.sub_apply] at hnn
  linarith

/-- Expansion of `‖a + ξ b‖²` around `ξ = c`. -/
theorem p0f0c_normSq_expand {n : ℕ} (a b : EuclideanSpace ℂ (Fin n)) (c ξ : ℂ) :
    ‖a + ξ • b‖ ^ 2 = (((‖a + c • b‖ ^ 2 : ℝ) : ℂ) +
        2 * ((ξ - c) * inner ℂ (a + c • b) b)).re + ‖ξ - c‖ ^ 2 * ‖b‖ ^ 2 := by
  have h1 : a + ξ • b = (a + c • b) + (ξ - c) • b := by
    rw [sub_smul]; abel
  rw [h1, @norm_add_sq ℂ, inner_smul_right, norm_smul, mul_pow, Complex.add_re,
    Complex.ofReal_re, RCLike.re_to_complex]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
  ring

open InnerProductSpace in
/-- PS-3 on one complex line: `ξ ↦ ‖a + ξ b‖²` is subharmonic on any set. -/
theorem p0f0c_normSq_line_subharmonic {n : ℕ} (a b : EuclideanSpace ℂ (Fin n)) (V : Set ℂ) :
    LeblSCV.Pseudoconvex.IsSubharmonicOn (fun ξ : ℂ => ((‖a + ξ • b‖ ^ 2 : ℝ) : EReal)) V := by
  have hcont : Continuous (fun ξ : ℂ => ((‖a + ξ • b‖ ^ 2 : ℝ) : EReal)) := by
    refine continuous_coe_real_ereal.comp ?_
    fun_prop
  refine ⟨hcont.continuousOn.upperSemicontinuousOn, fun _ _ => EReal.coe_ne_top _, ?_⟩
  intro c r hr _ g hg hgh hle x hx
  set β : ℂ := inner ℂ (a + c • b) b
  set K : ℝ := ‖a + c • b‖ ^ 2
  let H : ℂ → ℝ := fun ξ => (((K : ℝ) : ℂ) + 2 * ((ξ - c) * β)).re
  have hHan : ∀ ξ, HarmonicAt H ξ := by
    intro ξ
    have : AnalyticAt ℂ (fun ξ : ℂ => ((K : ℝ) : ℂ) + 2 * ((ξ - c) * β)) ξ := by fun_prop
    exact this.harmonicAt_re
  have hHc : HarmonicContOnCl H (Metric.ball c r) :=
    HarmonicOnNhd.harmonicContOnCl (fun ξ _ => hHan ξ)
  have hG := (p0f0c_harmonicContOnCl hr hg hgh).sub hHc
  have hexp : ∀ ξ, ‖a + ξ • b‖ ^ 2 = H ξ + ‖ξ - c‖ ^ 2 * ‖b‖ ^ 2 :=
    fun ξ => p0f0c_normSq_expand a b c ξ
  have hmin := p0f0c_min_principle hr hG (r ^ 2 * ‖b‖ ^ 2) (by
    intro y hy
    have h1 := EReal.coe_le_coe_iff.mp (hle y hy)
    have hyc : ‖y - c‖ = r := by rw [← dist_eq_norm]; exact hy
    rw [hexp y, hyc] at h1
    simp only [Pi.sub_apply]
    linarith) x hx
  have hxc : ‖x - c‖ < r := by rw [← dist_eq_norm]; exact hx
  have hsq : ‖x - c‖ ^ 2 * ‖b‖ ^ 2 ≤ r ^ 2 * ‖b‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) hxc.le 2
  simp only [Pi.sub_apply] at hmin
  refine EReal.coe_le_coe_iff.mpr ?_
  rw [hexp x]
  linarith

open LeblSCV.Pseudoconvex in
/-- PS-3: `‖z‖²` is plurisubharmonic on any set. -/
theorem p0f0c_normSq_psh {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) :
    IsPlurisubharmonicOn (fun z => ((‖z‖ ^ 2 : ℝ) : EReal)) U := by
  have hcont : Continuous (fun z : EuclideanSpace ℂ (Fin n) => ((‖z‖ ^ 2 : ℝ) : EReal)) := by
    refine continuous_coe_real_ereal.comp ?_
    fun_prop
  exact ⟨hcont.continuousOn.upperSemicontinuousOn, fun _ _ => EReal.coe_ne_top _,
    fun a b => p0f0c_normSq_line_subharmonic a b _⟩

open LeblSCV.Pseudoconvex in
/-- PS-1 (i) ⇒ (ii): `max (-log ρ) ‖z‖²` is a continuous psh exhaustion. -/
theorem p0f0c_hartogs_of_neg_log_dist_psh {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUo : IsOpen U) (hUc : IsConnected U) (hne : U ≠ Set.univ)
    (h : IsPlurisubharmonicOn
      (fun z => ((-Real.log (Metric.infDist z (frontier U)) : ℝ) : EReal)) U) :
    IsHartogsPseudoconvex U := by
  have hfr : (frontier U).Nonempty := nonempty_frontier_iff.mpr ⟨hUc.nonempty, hne⟩
  have hpos : ∀ z ∈ U, 0 < Metric.infDist z (frontier U) := fun z hz =>
    (isClosed_frontier.notMem_iff_infDist_pos hfr).mp
      (fun h => (hUo.frontier_eq ▸ h).2 hz)
  have hlogc : ContinuousOn (fun z => -Real.log (Metric.infDist z (frontier U))) U :=
    ContinuousOn.neg (ContinuousOn.log (Metric.continuous_infDist_pt _).continuousOn
      (fun z hz => (hpos z hz).ne'))
  let F : EuclideanSpace ℂ (Fin n) → ℝ :=
    fun z => max (-Real.log (Metric.infDist z (frontier U))) (‖z‖ ^ 2)
  have hFc : ContinuousOn F U := hlogc.sup (by fun_prop)
  refine ⟨hUo, hUc, F, hFc, ?_, ?_⟩
  · refine ⟨(continuous_coe_real_ereal.comp_continuousOn hFc).upperSemicontinuousOn,
      fun _ _ => EReal.coe_ne_top _, fun a b => ?_⟩
    have hA := h.2.2 a b
    have hB := p0f0c_normSq_line_subharmonic a b {ξ : ℂ | a + ξ • b ∈ U}
    have hlc : ContinuousOn (fun ξ : ℂ => ((F (a + ξ • b) : ℝ) : EReal))
        {ξ : ℂ | a + ξ • b ∈ U} :=
      continuous_coe_real_ereal.comp_continuousOn
        (hFc.comp (by fun_prop : Continuous fun ξ : ℂ => a + ξ • b).continuousOn
          (fun ξ hξ => hξ))
    refine ⟨hlc.upperSemicontinuousOn, fun _ _ => EReal.coe_ne_top _, ?_⟩
    intro c r hr hsub g hg hgh hle x hx
    have h1 := hA.2.2 c r hr hsub g hg hgh (fun y hy => le_trans
      (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) (hle y hy)) x hx
    have h2 := hB.2.2 c r hr hsub g hg hgh (fun y hy => le_trans
      (EReal.coe_le_coe_iff.mpr (le_max_right _ _)) (hle y hy)) x hx
    exact EReal.coe_le_coe_iff.mpr
      (max_le (EReal.coe_le_coe_iff.mp h1) (EReal.coe_le_coe_iff.mp h2))
  · intro r
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      Metric.closedBall 0 (|r| + 1) ∩
        ({z | Real.exp (-r) ≤ Metric.infDist z (frontier U)} ∩ closure U)
    have hKc : IsClosed K :=
      Metric.isClosed_closedBall.inter
        ((isClosed_le continuous_const (Metric.continuous_infDist_pt _)).inter isClosed_closure)
    have hsub : {z | z ∈ U ∧ F z < r} ⊆ K := by
      rintro z ⟨hzU, hzr⟩
      have ha : -Real.log (Metric.infDist z (frontier U)) < r :=
        lt_of_le_of_lt (le_max_left _ _) hzr
      have hb : ‖z‖ ^ 2 < r := lt_of_le_of_lt (le_max_right _ _) hzr
      refine ⟨?_, ?_, subset_closure hzU⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        nlinarith [norm_nonneg z, abs_nonneg r, le_abs_self r]
      · have : -r < Real.log (Metric.infDist z (frontier U)) := by linarith
        exact ((Real.lt_log_iff_exp_lt (hpos z hzU)).mp this).le
    have hKU : K ⊆ U := by
      rintro z ⟨-, hz1, hz2⟩
      have hzf : z ∉ frontier U := by
        intro hzf
        have := Metric.infDist_zero_of_mem hzf
        have := Real.exp_pos (-r)
        simp only [Set.mem_ofPred_eq] at hz1
        linarith
      rw [frontier, hUo.interior_eq] at hzf
      by_contra hzU
      exact hzf ⟨hz2, hzU⟩
    have hclK : closure {z | z ∈ U ∧ F z < r} ⊆ K := closure_minimal hsub hKc
    refine ⟨?_, hclK.trans hKU⟩
    exact (isCompact_closedBall 0 (|r| + 1)).of_isClosed_subset isClosed_closure
      (hclK.trans Set.inter_subset_left)

end P_ps13

section P_ps2
open LeblSCV.Pseudoconvex in
/-- PS-2 (ii)⇒(iii): a continuous psh exhaustion bounds every hull. -/
theorem ps2_convexWrt_psh_of_hartogs {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (h : IsHartogsPseudoconvex U) :
    IsConvexWrt U {f | IsPlurisubharmonicOn f U} := by
  obtain ⟨-, -, f, hfc, hfpsh, hfex⟩ := h
  intro K ⟨hKc, hKU⟩
  obtain ⟨M, hM⟩ := hKc.bddAbove_image (hfc.mono hKU)
  have hsub : hull U {f | IsPlurisubharmonicOn f U} K ⊆ {z | z ∈ U ∧ f z < M + 1} := by
    intro x ⟨hxU, hx⟩
    refine ⟨hxU, ?_⟩
    have h1 := hx (fun z => (f z : EReal)) hfpsh
    have h2 : (⨆ y ∈ K, (f y : EReal)) ≤ (M : EReal) := by
      refine iSup₂_le fun y hy => ?_
      exact EReal.coe_le_coe_iff.mpr (hM ⟨y, subset_closure hy, rfl⟩)
    have h3 : (f x : EReal) ≤ (M : EReal) := h1.trans h2
    have := EReal.coe_le_coe_iff.mp h3
    linarith
  obtain ⟨hSc, hSU⟩ := hfex (M + 1)
  exact ⟨hSc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hSU⟩

end P_ps2

section P_ps4
/-- PS-4 step A: by upper semicontinuity, `u < g + ε` on a sphere slightly inside. -/
theorem p0f0c_radius {V : Set ℂ} {u : ℂ → EReal} (husc : UpperSemicontinuousOn u V)
    {a : ℂ} {r : ℝ} (hsub : Metric.closedBall a r ⊆ V) {g : ℂ → ℝ}
    (hg : ContinuousOn g (Metric.closedBall a r))
    (hle : ∀ y ∈ Metric.sphere a r, u y ≤ (g y : EReal)) {x : ℂ} (hx : x ∈ Metric.ball a r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ, dist x a < ρ ∧ ρ < r ∧ ∀ y ∈ Metric.sphere a ρ, u y < ((g y + ε : ℝ) : EReal) := by
  set A : Set ℂ := {z | z ∈ Metric.closedBall a r → u z < ((g z + ε : ℝ) : EReal)} with hAdef
  have hnhds : ∀ y ∈ Metric.sphere a r, A ∈ nhds y := by
    intro y hy
    have hyB : y ∈ Metric.closedBall a r := Metric.sphere_subset_closedBall hy
    have h1 : ∀ᶠ z in nhdsWithin y V, u z < ((g y + ε / 2 : ℝ) : EReal) :=
      husc y (hsub hyB) _ (lt_of_le_of_lt (hle y hy) (EReal.coe_lt_coe_iff.mpr (by linarith)))
    have h1' : ∀ᶠ z in nhdsWithin y (Metric.closedBall a r),
        u z < ((g y + ε / 2 : ℝ) : EReal) :=
      h1.filter_mono (nhdsWithin_mono y hsub)
    have h2 : ∀ᶠ z in nhdsWithin y (Metric.closedBall a r), dist (g z) (g y) < ε / 2 :=
      Metric.tendsto_nhds.mp (hg y hyB) (ε / 2) (half_pos hε)
    have h3 : ∀ᶠ z in nhdsWithin y (Metric.closedBall a r),
        u z < ((g z + ε : ℝ) : EReal) := by
      filter_upwards [h1', h2] with z hz1 hz2
      refine lt_of_lt_of_le hz1 (EReal.coe_le_coe_iff.mpr ?_)
      rw [Real.dist_eq] at hz2
      linarith [(abs_lt.mp hz2).1]
    exact eventually_nhdsWithin_iff.mp h3
  have hsubI : Metric.sphere a r ⊆ interior A :=
    fun y hy => mem_interior_iff_mem_nhds.mpr (hnhds y hy)
  obtain ⟨δ, hδ, hth⟩ :=
    (isCompact_sphere a r).exists_thickening_subset_open isOpen_interior hsubI
  have hxa : dist x a < r := hx
  have hd0 : 0 ≤ dist x a := dist_nonneg
  refine ⟨max ((dist x a + r) / 2) (r - δ / 2), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · exact max_lt (by linarith) (by linarith)
  · intro y hy
    set ρ := max ((dist x a + r) / 2) (r - δ / 2) with hρdef
    have hρ1 : (dist x a + r) / 2 ≤ ρ := le_max_left _ _
    have hρ2 : r - δ / 2 ≤ ρ := le_max_right _ _
    have hρr : ρ < r := max_lt (by linarith) (by linarith)
    have hρpos : 0 < ρ := by linarith
    have hya : ‖y - a‖ = ρ := by rw [← dist_eq_norm]; exact hy
    have hmem : y ∈ Metric.thickening δ (Metric.sphere a r) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨a + ((r / ρ : ℝ) : ℂ) * (y - a), ?_, ?_⟩
      · rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (div_pos (by linarith) hρpos), hya]
        field_simp
      · rw [dist_eq_norm]
        have he : y - (a + ((r / ρ : ℝ) : ℂ) * (y - a)) = ((1 - r / ρ : ℝ) : ℂ) * (y - a) := by
          push_cast; ring
        have hle1 : 1 - r / ρ ≤ 0 := by
          rw [sub_nonpos, le_div_iff₀ hρpos]; linarith
        rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, hya, abs_of_nonpos hle1]
        have he2 : -(1 - r / ρ) * ρ = r - ρ := by field_simp; ring
        rw [he2]; linarith
    have hyA : y ∈ A := interior_subset (hth hmem)
    exact hyA (Metric.mem_closedBall.mpr (by rw [dist_eq_norm, hya]; exact hρr.le))

/-- PS-4 step B: a harmonic function is uniformly approximated on a smaller closed disc by the
real part of a polynomial (truncated Taylor series of a holomorphic primitive). -/
theorem p0f0c_poly_approx {g : ℂ → ℝ} {a : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hh : InnerProductSpace.HarmonicOnNhd g (Metric.ball a r)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ y ∈ Metric.closedBall a ρ, |(P.eval y).re - g y| < ε := by
  obtain ⟨F, hFa, hFre⟩ := hh.exists_analyticOnNhd_ball_re_eq
  have hs2 : 0 < ρ + 2 * (r - ρ) / 3 := by linarith
  have hs1 : 0 ≤ ρ + (r - ρ) / 3 := by linarith
  let R2 : NNReal := ⟨ρ + 2 * (r - ρ) / 3, hs2.le⟩
  let R1 : NNReal := ⟨ρ + (r - ρ) / 3, hs1⟩
  have hdiff : DifferentiableOn ℂ F (Metric.closedBall a R2) := by
    intro y hy
    refine (hFa y ?_).differentiableAt.differentiableWithinAt
    rw [Metric.mem_ball]
    have : dist y a ≤ ρ + 2 * (r - ρ) / 3 := hy
    linarith
  have hR2 : (0 : NNReal) < R2 := by
    show (0 : ℝ) < ρ + 2 * (r - ρ) / 3
    exact hs2
  have hps := hdiff.hasFPowerSeriesOnBall hR2
  have hR12 : (R1 : ENNReal) < R2 := by
    rw [ENNReal.coe_lt_coe]
    show ρ + (r - ρ) / 3 < ρ + 2 * (r - ρ) / 3
    linarith
  have hU := hps.tendstoUniformlyOn' hR12
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hU ε hε)
  set p := cauchyPowerSeries F a R2
  refine ⟨∑ k ∈ Finset.range N,
    Polynomial.C (p.coeff k) * (Polynomial.X - Polynomial.C a) ^ k, ?_⟩
  intro y hy
  have hyρ : dist y a ≤ ρ := hy
  have hy1 : y ∈ Metric.ball a (R1 : ℝ) := by
    show dist y a < ρ + (r - ρ) / 3
    linarith
  have hd := hN N le_rfl y hy1
  have heval : (∑ k ∈ Finset.range N,
      Polynomial.C (p.coeff k) * (Polynomial.X - Polynomial.C a) ^ k).eval y =
      p.partialSum N (y - a) := by
    simp [Polynomial.eval_finset_sum, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, mul_comm]
  have hyr : y ∈ Metric.ball a r := by
    rw [Metric.mem_ball]; linarith
  rw [heval, ← hFre hyr]
  calc |(p.partialSum N (y - a)).re - (F y).re|
      = |(p.partialSum N (y - a) - F y).re| := by rw [Complex.sub_re]
    _ ≤ ‖p.partialSum N (y - a) - F y‖ := Complex.abs_re_le_norm _
    _ = dist (F y) (p.partialSum N (y - a)) := by rw [dist_comm, dist_eq_norm]
    _ < ε := hd

open LeblSCV.Pseudoconvex in
/-- PS-4: the polynomial test characterizes subharmonicity. -/
theorem p0f0c_subharmonic_of_poly_test (V : Set ℂ) (u : ℂ → EReal)
    (husc : UpperSemicontinuousOn u V) (hne : ∀ z ∈ V, u z ≠ ⊤)
    (htest : ∀ (a : ℂ) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ V →
      ∀ P : Polynomial ℂ, (∀ x ∈ Metric.sphere a r, u x ≤ ((P.eval x).re : EReal)) →
        ∀ x ∈ Metric.ball a r, u x ≤ ((P.eval x).re : EReal)) :
    IsSubharmonicOn u V := by
  refine ⟨husc, hne, ?_⟩
  intro a r hr hsub g hg hgh hle x hx
  have hH : InnerProductSpace.HarmonicOnNhd g (Metric.ball a r) :=
    (p0f0c_harmonicContOnCl hr hg hgh).harmonicOnNhd
  have key : ∀ ε > 0, u x ≤ ((g x + 3 * ε : ℝ) : EReal) := by
    intro ε hε
    obtain ⟨ρ, hxρ, hρr, hρu⟩ := p0f0c_radius husc hsub hg hle hx hε
    have hρ : 0 < ρ := lt_of_le_of_lt dist_nonneg hxρ
    obtain ⟨P, hP⟩ := p0f0c_poly_approx hρ hρr hH hε
    have hcb : Metric.closedBall a ρ ⊆ V :=
      (Metric.closedBall_subset_closedBall hρr.le).trans hsub
    have h := htest a ρ hρ hcb (P + Polynomial.C ((2 * ε : ℝ) : ℂ)) (by
      intro y hy
      have h1 := hρu y hy
      have h2 := hP y (Metric.sphere_subset_closedBall hy)
      refine (le_of_lt h1).trans (EReal.coe_le_coe_iff.mpr ?_)
      simp only [Polynomial.eval_add, Polynomial.eval_C, Complex.add_re, Complex.ofReal_re]
      linarith [(abs_lt.mp h2).1]) x hxρ
    refine h.trans (EReal.coe_le_coe_iff.mpr ?_)
    have h2 := hP x (Metric.mem_closedBall.mpr hxρ.le)
    simp only [Polynomial.eval_add, Polynomial.eval_C, Complex.add_re, Complex.ofReal_re]
    linarith [(abs_lt.mp h2).2]
  have hxV : x ∈ V := hsub (Metric.ball_subset_closedBall hx)
  by_cases hb : u x = ⊥
  · rw [hb]; exact bot_le
  have hux : u x = ((u x).toReal : EReal) := (EReal.coe_toReal (hne x hxV) hb).symm
  rw [hux]
  refine EReal.coe_le_coe_iff.mpr (le_of_forall_pos_le_add fun ε hε => ?_)
  have h3 := key (ε / 3) (by positivity)
  rw [hux] at h3
  have h4 := EReal.coe_le_coe_iff.mp h3
  linarith

end P_ps4

section P_ps5
/-- The open ball of radius `ρ(z)` about `z ∈ U` lies in `U`. -/
theorem p0f0c_mem_of_dist_lt {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hUo : IsOpen U)
    {z y : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U)
    (hy : dist y z < Metric.infDist z (frontier U)) : y ∈ U := by
  have hball : Metric.ball z (Metric.infDist z (frontier U)) ⊆ U := by
    refine (convex_ball z _).isPreconnected.subset_left_of_subset_union hUo
      isClosed_closure.isOpen_compl (Set.disjoint_compl_right_iff_subset.mpr subset_closure)
      ?_ ⟨z, Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hy), hz⟩
    intro p hp
    by_cases hpU : p ∈ U
    · exact Or.inl hpU
    · right
      intro hpc
      have hpf : p ∈ frontier U := by
        rw [frontier, hUo.interior_eq]; exact ⟨hpc, hpU⟩
      have h1 := Metric.infDist_le_dist_of_mem hpf (x := z)
      rw [Metric.mem_ball, dist_comm] at hp
      linarith
  exact hball hy

/-- A ball of radius `s` about `z` inside `U` gives `s ≤ ρ(z)`. -/
theorem p0f0c_le_infDist {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hUo : IsOpen U)
    (hfr : (frontier U).Nonempty) {z : EuclideanSpace ℂ (Fin n)} {s : ℝ}
    (h : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ < s → z + v ∈ U) :
    s ≤ Metric.infDist z (frontier U) := by
  rw [Metric.le_infDist hfr]
  intro y hy
  by_contra hlt
  push_neg at hlt
  have h1 := h (y - z) (by rw [← dist_eq_norm, dist_comm]; exact hlt)
  have e : z + (y - z) = y := by abel
  rw [e] at h1
  rw [frontier, hUo.interior_eq] at hy
  exact hy.2 h1

open LeblSCV.Pseudoconvex in
/-- PS-5 (core of (iv) ⇒ (i), Lebl's disc argument): under the continuity principle,
`-log ρ(a + ξ b) ≤ Re P(ξ)` on a circle implies it on the disc. -/
theorem p0f0c_neg_log_dist_poly_bound {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUo : IsOpen U) (hUc : IsConnected U) (hne : U ≠ Set.univ)
    (hcp : SatisfiesContinuityPrinciple U) (a b : EuclideanSpace ℂ (Fin n)) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hdisc : ∀ ξ ∈ Metric.closedBall c r, a + ξ • b ∈ U)
    (P : Polynomial ℂ)
    (hP : ∀ ξ ∈ Metric.sphere c r,
      -Real.log (Metric.infDist (a + ξ • b) (frontier U)) ≤ (P.eval ξ).re) :
    ∀ ξ ∈ Metric.ball c r,
      -Real.log (Metric.infDist (a + ξ • b) (frontier U)) ≤ (P.eval ξ).re := by
  intro ξ0 hξ0
  let E : ℂ → ℂ := fun ξ => Complex.exp (-(P.eval ξ))
  have hEn : ∀ ξ, ‖E ξ‖ = Real.exp (-(P.eval ξ).re) := by
    intro ξ; simp [E, Complex.norm_exp]
  have hEd : Differentiable ℂ E := (P.differentiable.neg).cexp
  have hEc : Continuous E := hEd.continuous
  have hfr : (frontier U).Nonempty := nonempty_frontier_iff.mpr ⟨hUc.nonempty, hne⟩
  have hpos : ∀ z ∈ U, 0 < Metric.infDist z (frontier U) := fun z hz =>
    (isClosed_frontier.notMem_iff_infDist_pos hfr).mp
      (fun h => (hUo.frontier_eq ▸ h).2 hz)
  have hbd : ∀ ξ ∈ Metric.sphere c r,
      ‖E ξ‖ ≤ Metric.infDist (a + ξ • b) (frontier U) := by
    intro ξ hξ
    have hz := hdisc ξ (Metric.sphere_subset_closedBall hξ)
    have h1 := hP ξ hξ
    rw [hEn]
    have h2 : -(P.eval ξ).re ≤ Real.log (Metric.infDist (a + ξ • b) (frontier U)) := by
      linarith
    calc Real.exp (-(P.eval ξ).re)
        ≤ Real.exp (Real.log (Metric.infDist (a + ξ • b) (frontier U))) :=
          Real.exp_le_exp.mpr h2
      _ = _ := Real.exp_log (hpos _ hz)
  have hsph : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, c + (r : ℂ) * ζ ∈ Metric.sphere c r := by
    intro ζ hζ
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, hζ, mul_one]
  have hcb : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, c + (r : ℂ) * ζ ∈ Metric.closedBall c r := by
    intro ζ hζ
    rw [mem_closedBall_zero_iff] at hζ
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have claim : ∀ w : EuclideanSpace ℂ (Fin n), ‖w‖ < 1 → a + ξ0 • b + E ξ0 • w ∈ U := by
    intro w hw
    let Φ : ℝ → ℂ → EuclideanSpace ℂ (Fin n) :=
      fun t ζ => a + (c + (r : ℂ) * ζ) • b + ((t : ℂ) * E (c + (r : ℂ) * ζ)) • w
    have hΦc : Continuous (fun p : ℝ × ℂ => Φ p.1 p.2) := by
      simp only [Φ]; fun_prop
    have hΦd : ∀ t, Differentiable ℂ (Φ t) := by
      intro t; simp only [Φ]; fun_prop
    have hΦt : ∀ ζ, Continuous (fun t : ℝ => Φ t ζ) := by
      intro ζ; simp only [Φ]; fun_prop
    set K := (fun p : ℝ × ℂ => Φ p.1 p.2) '' (Set.Icc (0 : ℝ) 1 ×ˢ Metric.sphere (0 : ℂ) 1)
      with hKdef
    have hKc : IsCompact K := (isCompact_Icc.prod (isCompact_sphere 0 1)).image hΦc
    have hKU : K ⊆ U := by
      rintro _ ⟨⟨t, ζ⟩, ⟨ht, hζ⟩, rfl⟩
      have hξ := hsph ζ hζ
      have hz := hdisc _ (Metric.sphere_subset_closedBall hξ)
      have hb := hbd _ hξ
      apply p0f0c_mem_of_dist_lt hUo hz
      show dist (a + (c + (r : ℂ) * ζ) • b + ((t : ℂ) * E (c + (r : ℂ) * ζ)) • w)
        (a + (c + (r : ℂ) * ζ) • b) < _
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
      have hE0 : 0 < ‖E (c + (r : ℂ) * ζ)‖ := by rw [hEn]; exact Real.exp_pos _
      calc t * ‖E (c + (r : ℂ) * ζ)‖ * ‖w‖ ≤ 1 * ‖E (c + (r : ℂ) * ζ)‖ * ‖w‖ := by
            gcongr; exact ht.2
        _ < ‖E (c + (r : ℂ) * ζ)‖ := by nlinarith [norm_nonneg w]
        _ ≤ _ := hb
    set A : Set ℝ :=
      {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, Φ t ζ ∈ U} with hAdef
    have h0A : (0 : ℝ) ∈ A := by
      refine ⟨⟨le_rfl, zero_le_one⟩, fun ζ hζ => ?_⟩
      have := hdisc _ (hcb ζ hζ)
      simpa [Φ] using this
    have hAbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
    set S : Set (ℂ → EuclideanSpace ℂ (Fin n)) :=
      {φ | ∃ t ∈ A, φ = Φ t ∧ IsClosedAnalyticDisc φ} with hSdef
    have hS : ∀ φ ∈ S, IsClosedAnalyticDisc φ ∧ φ '' Metric.ball (0 : ℂ) 1 ⊆ U := by
      rintro φ ⟨t, htA, rfl, hφ⟩
      exact ⟨hφ, by rintro _ ⟨ζ, hζ, rfl⟩; exact htA.2 ζ (Metric.ball_subset_closedBall hζ)⟩
    have hSb : (⋃ φ ∈ S, φ '' Metric.sphere (0 : ℂ) 1) ⊆ K := by
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨φ, ⟨t, htA, rfl, -⟩, ζ, hζ, rfl⟩ := hy
      exact ⟨(t, ζ), ⟨htA.1, hζ⟩, rfl⟩
    have hrel : IsRelCompactIn (⋃ φ ∈ S, φ '' Metric.sphere (0 : ℂ) 1) U := by
      have hcl := closure_minimal hSb hKc.isClosed
      exact ⟨hKc.of_isClosed_subset isClosed_closure hcl, hcl.trans hKU⟩
    obtain ⟨hLc, hLU⟩ := hcp S hS hrel
    set L := closure (⋃ φ ∈ S, φ '' Metric.ball (0 : ℂ) 1) with hLdef
    have hMc : IsCompact (L ∪ K) := hLc.union hKc
    have hMU : L ∪ K ⊆ U := Set.union_subset hLU hKU
    have hAM : ∀ t ∈ A, ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, Φ t ζ ∈ L ∪ K := by
      intro t htA ζ hζ
      by_cases hζs : ζ ∈ Metric.sphere (0 : ℂ) 1
      · exact Or.inr ⟨(t, ζ), ⟨htA.1, hζs⟩, rfl⟩
      have hζb : ζ ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball]
        rw [Metric.mem_closedBall] at hζ
        rw [Metric.mem_sphere] at hζs
        exact lt_of_le_of_ne hζ hζs
      by_cases hnc : ∃ ξ ∈ Metric.ball (0 : ℂ) 1, ∃ η ∈ Metric.ball (0 : ℂ) 1, Φ t ξ ≠ Φ t η
      · left
        apply subset_closure
        simp only [Set.mem_iUnion]
        exact ⟨Φ t, ⟨t, htA, rfl, (hΦd t).continuous.continuousOn,
          (hΦd t).differentiableOn, hnc⟩, ζ, hζb, rfl⟩
      · right
        push_neg at hnc
        have h1 : (1 : ℂ) ∈ closure (Metric.ball (0 : ℂ) 1) := by
          rw [closure_ball 0 one_ne_zero]; simp
        have hmap : Set.MapsTo (Φ t) (Metric.ball (0 : ℂ) 1) {Φ t ζ} :=
          fun η hη => hnc η hη ζ hζb
        have h2 := map_mem_closure (hΦd t).continuous h1 hmap
        rw [closure_singleton, Set.mem_singleton_iff] at h2
        rw [← h2]
        exact ⟨(t, 1), ⟨htA.1, by simp⟩, rfl⟩
    have hsA_cl : sSup A ∈ closure A := csSup_mem_closure ⟨0, h0A⟩ hAbdd
    have hs0 : 0 ≤ sSup A := le_csSup hAbdd h0A
    have hs1 : sSup A ≤ 1 := csSup_le ⟨0, h0A⟩ (fun t ht => ht.1.2)
    have hsM : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, Φ (sSup A) ζ ∈ L ∪ K := by
      intro ζ hζ
      have := map_mem_closure (hΦt ζ) hsA_cl (fun t ht => hAM t ht ζ hζ)
      rwa [hMc.isClosed.closure_eq] at this
    have hs_eq : sSup A = 1 := by
      by_contra hne1
      have hlt : sSup A < 1 := lt_of_le_of_ne hs1 hne1
      have hQc : IsCompact (Φ (sSup A) '' Metric.closedBall (0 : ℂ) 1) :=
        (isCompact_closedBall 0 1).image (hΦd _).continuous
      have hQU : Φ (sSup A) '' Metric.closedBall (0 : ℂ) 1 ⊆ U := by
        rintro _ ⟨ζ, hζ, rfl⟩; exact hMU (hsM ζ hζ)
      obtain ⟨δ, hδ, hδU⟩ := hQc.exists_thickening_subset_open hUo hQU
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
        (f := fun ζ => E (c + (r : ℂ) * ζ)) (by fun_prop)
      have hC0 : 0 ≤ C :=
        le_trans (norm_nonneg _) (hC 0 (Metric.mem_closedBall_self zero_le_one))
      have hη : 0 < δ / (2 * (C + 1)) := by positivity
      set t := min 1 (sSup A + δ / (2 * (C + 1))) with htdef
      have hts : sSup A < t := lt_min hlt (by linarith)
      have ht1 : t ≤ 1 := min_le_left _ _
      have htd : t - sSup A ≤ δ / (2 * (C + 1)) := by
        have := min_le_right 1 (sSup A + δ / (2 * (C + 1))); linarith
      have htA : t ∈ A := by
        refine ⟨⟨by linarith, ht1⟩, fun ζ hζ => hδU ?_⟩
        rw [Metric.mem_thickening_iff]
        refine ⟨Φ (sSup A) ζ, ⟨ζ, hζ, rfl⟩, ?_⟩
        rw [dist_eq_norm]
        have he : Φ t ζ - Φ (sSup A) ζ =
            (((t - sSup A : ℝ) : ℂ) * E (c + (r : ℂ) * ζ)) • w := by
          simp only [Φ]; push_cast; rw [sub_mul, sub_smul]; abel
        rw [he, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        have hCζ : ‖E (c + (r : ℂ) * ζ)‖ ≤ C := hC ζ hζ
        have hw1 : ‖w‖ ≤ 1 := hw.le
        calc (t - sSup A) * ‖E (c + (r : ℂ) * ζ)‖ * ‖w‖
            ≤ (δ / (2 * (C + 1))) * C * 1 := by gcongr
          _ < δ := by
            rw [mul_one, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith
      have := le_csSup hAbdd htA
      linarith
    have h1A : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, Φ 1 ζ ∈ U := by
      intro ζ hζ; rw [← hs_eq]; exact hMU (hsM ζ hζ)
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hζ0 : (ξ0 - c) / (r : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, div_le_one hr, ← dist_eq_norm]
      exact (Metric.mem_ball.mp hξ0).le
    have hξ : c + (r : ℂ) * ((ξ0 - c) / (r : ℂ)) = ξ0 := by field_simp; ring
    have h1 := h1A _ hζ0
    have hΦ1 : Φ 1 ((ξ0 - c) / (r : ℂ)) = a + ξ0 • b + E ξ0 • w := by
      simp only [Φ, hξ, Complex.ofReal_one, one_mul]
    rwa [hΦ1] at h1
  have hz0 := hdisc ξ0 (Metric.ball_subset_closedBall hξ0)
  have hlow : Real.exp (-(P.eval ξ0).re) ≤ Metric.infDist (a + ξ0 • b) (frontier U) := by
    apply p0f0c_le_infDist hUo hfr
    intro v hv
    have hw : ‖Complex.exp (P.eval ξ0) • v‖ < 1 := by
      rw [norm_smul, Complex.norm_exp]
      calc Real.exp (P.eval ξ0).re * ‖v‖
          < Real.exp (P.eval ξ0).re * Real.exp (-(P.eval ξ0).re) :=
            mul_lt_mul_of_pos_left hv (Real.exp_pos _)
        _ = 1 := by rw [← Real.exp_add]; simp
    have h1 := claim _ hw
    have he : E ξ0 • Complex.exp (P.eval ξ0) • v = v := by
      rw [smul_smul]
      simp only [E]
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
    rwa [he] at h1
  have := Real.log_le_log (Real.exp_pos _) hlow
  rw [Real.log_exp] at this
  linarith

end P_ps5

section P_asm
open LeblSCV.Pseudoconvex in
/-- (iv) ⇒ (i) from PS-4 and PS-5, plus continuity of `-log ρ` on `U`. -/
theorem asm_iv_to_i {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUo : IsOpen U) (hUc : IsConnected U) (hne : U ≠ Set.univ)
    (PS4 : ∀ (V : Set ℂ), IsOpen V → ∀ (u : ℂ → EReal),
      UpperSemicontinuousOn u V → (∀ z ∈ V, u z ≠ ⊤) →
      (∀ (a : ℂ) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ V →
        ∀ P : Polynomial ℂ, (∀ x ∈ Metric.sphere a r, u x ≤ ((P.eval x).re : EReal)) →
          ∀ x ∈ Metric.ball a r, u x ≤ ((P.eval x).re : EReal)) →
      IsSubharmonicOn u V)
    (PS5 : SatisfiesContinuityPrinciple U → ∀ (a b : EuclideanSpace ℂ (Fin n)) (c : ℂ) (r : ℝ),
      0 < r → (∀ ξ ∈ Metric.closedBall c r, a + ξ • b ∈ U) → ∀ (P : Polynomial ℂ),
      (∀ ξ ∈ Metric.sphere c r,
        -Real.log (Metric.infDist (a + ξ • b) (frontier U)) ≤ (P.eval ξ).re) →
      ∀ ξ ∈ Metric.ball c r,
        -Real.log (Metric.infDist (a + ξ • b) (frontier U)) ≤ (P.eval ξ).re)
    (hcp : SatisfiesContinuityPrinciple U) :
    IsPlurisubharmonicOn (fun z => ((-Real.log (Metric.infDist z (frontier U)) : ℝ) : EReal)) U := by
  have hfr : (frontier U).Nonempty := nonempty_frontier_iff.mpr ⟨hUc.nonempty, hne⟩
  have hpos : ∀ z ∈ U, 0 < Metric.infDist z (frontier U) := fun z hz =>
    (isClosed_frontier.notMem_iff_infDist_pos hfr).mp
      (fun h => (hUo.frontier_eq ▸ h).2 hz)
  have hcont : ContinuousOn (fun z => ((-Real.log (Metric.infDist z (frontier U)) : ℝ) : EReal)) U := by
    refine continuous_coe_real_ereal.comp_continuousOn ?_
    refine ContinuousOn.neg ?_
    exact ContinuousOn.log (Metric.continuous_infDist_pt _).continuousOn
      (fun z hz => (hpos z hz).ne')
  refine ⟨hcont.upperSemicontinuousOn, fun z _ => EReal.coe_ne_top _, fun a b => ?_⟩
  have hVo : IsOpen {ξ : ℂ | a + ξ • b ∈ U} :=
    hUo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hline : ContinuousOn (fun ξ : ℂ =>
      ((-Real.log (Metric.infDist (a + ξ • b) (frontier U)) : ℝ) : EReal))
      {ξ : ℂ | a + ξ • b ∈ U} :=
    hcont.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (fun ξ hξ => hξ)
  refine PS4 _ hVo _ hline.upperSemicontinuousOn (fun z _ => EReal.coe_ne_top _) ?_
  intro c r hr hball P hP x hx
  have := PS5 hcp a b c r hr (fun ξ hξ => hball hξ) P
    (fun ξ hξ => EReal.coe_le_coe_iff.mp (hP ξ hξ)) x hx
  exact EReal.coe_le_coe_iff.mpr this

open LeblSCV.Pseudoconvex in
/-- Reduction of Theorem 2.5.6 to its children. -/
theorem hartogs_tfae_reduction {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUo : IsOpen U) (hUc : IsConnected U) (hne : U ≠ Set.univ)
    (PS1 : IsPlurisubharmonicOn (fun z => ((-Real.log (Metric.infDist z (frontier U)) : ℝ) : EReal)) U →
      IsHartogsPseudoconvex U)
    (PS2 : IsHartogsPseudoconvex U → IsConvexWrt U {f | IsPlurisubharmonicOn f U})
    (KS : IsConvexWrt U {f | IsPlurisubharmonicOn f U} → SatisfiesContinuityPrinciple U)
    (PS4 : ∀ (V : Set ℂ), IsOpen V → ∀ (u : ℂ → EReal),
      UpperSemicontinuousOn u V → (∀ z ∈ V, u z ≠ ⊤) →
      (∀ (a : ℂ) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ V →
        ∀ P : Polynomial ℂ, (∀ x ∈ Metric.sphere a r, u x ≤ ((P.eval x).re : EReal)) →
          ∀ x ∈ Metric.ball a r, u x ≤ ((P.eval x).re : EReal)) →
      IsSubharmonicOn u V)
    (PS5 : SatisfiesContinuityPrinciple U → ∀ (a b : EuclideanSpace ℂ (Fin n)) (c : ℂ) (r : ℝ),
      0 < r → (∀ ξ ∈ Metric.closedBall c r, a + ξ • b ∈ U) → ∀ (P : Polynomial ℂ),
      (∀ ξ ∈ Metric.sphere c r,
        -Real.log (Metric.infDist (a + ξ • b) (frontier U)) ≤ (P.eval ξ).re) →
      ∀ ξ ∈ Metric.ball c r,
        -Real.log (Metric.infDist (a + ξ • b) (frontier U)) ≤ (P.eval ξ).re) :
    List.TFAE
      [IsPlurisubharmonicOn (fun z => ((-Real.log (Metric.infDist z (frontier U)) : ℝ) : EReal)) U,
       IsHartogsPseudoconvex U,
       IsConvexWrt U {f | IsPlurisubharmonicOn f U},
       SatisfiesContinuityPrinciple U] := by
  tfae_have 1 → 2 := PS1
  tfae_have 2 → 3 := PS2
  tfae_have 3 → 4 := KS
  tfae_have 4 → 1 := asm_iv_to_i U hUo hUc hne PS4 PS5
  tfae_finish

end P_asm

section P_ks
open LeblSCV.Pseudoconvex in
/-- A constant is subharmonic on any set (minimum principle for the harmonic majorant). -/
theorem p0f0c_const_subharmonic (V : Set ℂ) (m : ℝ) :
    IsSubharmonicOn (fun _ : ℂ => (m : EReal)) V := by
  refine ⟨continuousOn_const.upperSemicontinuousOn, fun _ _ => EReal.coe_ne_top _, ?_⟩
  intro a r hr _ g hg hgh hle x hx
  exact EReal.coe_le_coe_iff.mpr (p0f0c_min_principle hr (p0f0c_harmonicContOnCl hr hg hgh) m
    (fun y hy => EReal.coe_le_coe_iff.mp (hle y hy)) x hx)

open LeblSCV.Pseudoconvex in
/-- Truncation from below keeps plurisubharmonicity. -/
theorem p0f0c_max_const_psh {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → EReal} (hf : IsPlurisubharmonicOn f U) (m : ℝ) :
    IsPlurisubharmonicOn (fun z => max (f z) (m : EReal)) U := by
  obtain ⟨husc, hne, hline⟩ := hf
  refine ⟨?_, fun z hz => ?_, fun a b => ?_⟩
  · intro x hx y hy
    have h1 : f x < y := lt_of_le_of_lt (le_max_left _ _) hy
    have h2 : (m : EReal) < y := lt_of_le_of_lt (le_max_right _ _) hy
    filter_upwards [husc x hx y h1] with z hz
    exact max_lt hz h2
  · exact (max_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr (hne z hz), EReal.coe_lt_top m⟩).ne
  · obtain ⟨hu1, hu2, hu3⟩ := hline a b
    refine ⟨?_, fun z hz => ?_, ?_⟩
    · intro x hx y hy
      have h1 : f (a + x • b) < y := lt_of_le_of_lt (le_max_left _ _) hy
      have h2 : (m : EReal) < y := lt_of_le_of_lt (le_max_right _ _) hy
      filter_upwards [hu1 x hx y h1] with z hz
      exact max_lt hz h2
    · exact (max_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr (hu2 z hz), EReal.coe_lt_top m⟩).ne
    · intro c r hr hsub g hg hgh hle x hx
      have hc := (p0f0c_const_subharmonic {ξ : ℂ | a + ξ • b ∈ U} m).2.2 c r hr hsub g hg hgh
        (fun y hy => le_trans (le_max_right _ _) (hle y hy)) x hx
      have hu := hu3 c r hr hsub g hg hgh
        (fun y hy => le_trans (le_max_left _ _) (hle y hy)) x hx
      exact max_le hu hc

/-- COMP for all psh functions follows from COMP for psh functions bounded below. -/
theorem p0f0c_comp_of_bdd {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (COMPb : ∀ f : EuclideanSpace ℂ (Fin n) → EReal,
      LeblSCV.Pseudoconvex.IsPlurisubharmonicOn f U → (∃ m : ℝ, ∀ z, (m : EReal) ≤ f z) →
      ∀ φ : ℂ → EuclideanSpace ℂ (Fin n), LeblSCV.Pseudoconvex.IsClosedAnalyticDisc φ →
        φ '' Metric.closedBall (0 : ℂ) 1 ⊆ U →
        ∀ ζ ∈ Metric.ball (0 : ℂ) 1, f (φ ζ) ≤ ⨆ η ∈ Metric.sphere (0 : ℂ) 1, f (φ η))
    (f : EuclideanSpace ℂ (Fin n) → EReal) (hf : LeblSCV.Pseudoconvex.IsPlurisubharmonicOn f U)
    (φ : ℂ → EuclideanSpace ℂ (Fin n)) (hφ : LeblSCV.Pseudoconvex.IsClosedAnalyticDisc φ)
    (hφU : φ '' Metric.closedBall (0 : ℂ) 1 ⊆ U) :
    ∀ ζ ∈ Metric.ball (0 : ℂ) 1, f (φ ζ) ≤ ⨆ η ∈ Metric.sphere (0 : ℂ) 1, f (φ η) := by
  intro ζ hζ
  set M := ⨆ η ∈ Metric.sphere (0 : ℂ) 1, f (φ η)
  have key : ∀ m : ℝ, f (φ ζ) ≤ max M (m : EReal) := by
    intro m
    have h := COMPb (fun z => max (f z) (m : EReal)) (p0f0c_max_const_psh hf m)
      ⟨m, fun z => le_max_right _ _⟩ φ hφ hφU ζ hζ
    refine le_trans (le_max_left _ _) (h.trans ?_)
    refine iSup₂_le fun η hη => max_le_max (le_iSup₂ (f := fun η _ => f (φ η)) η hη) le_rfl
  by_contra hlt
  push Not at hlt
  -- M < f (φ ζ): pick a real strictly between
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  exact absurd (lt_of_le_of_lt (key q) (max_lt hlt hq2)) (lt_irrefl _)

open LeblSCV.Pseudoconvex in
/-- KS from COMP: discs lie in the psh hull of their boundaries. -/
theorem p0f0c_ks_of_comp {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hconv : IsConvexWrt U {f | IsPlurisubharmonicOn f U})
    (COMP : ∀ f : EuclideanSpace ℂ (Fin n) → EReal, IsPlurisubharmonicOn f U →
      ∀ φ : ℂ → EuclideanSpace ℂ (Fin n), IsClosedAnalyticDisc φ →
        φ '' Metric.closedBall (0 : ℂ) 1 ⊆ U →
        ∀ ζ ∈ Metric.ball (0 : ℂ) 1, f (φ ζ) ≤ ⨆ η ∈ Metric.sphere (0 : ℂ) 1, f (φ η)) :
    SatisfiesContinuityPrinciple U := by
  intro S hS hrel
  set K := ⋃ φ ∈ S, φ '' Metric.sphere (0 : ℂ) 1
  obtain ⟨hHc, hHU⟩ := hconv K hrel
  have hsub : (⋃ φ ∈ S, φ '' Metric.ball (0 : ℂ) 1) ⊆ hull U {f | IsPlurisubharmonicOn f U} K := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨φ, hφS, ζ, hζ, rfl⟩ := hy
    obtain ⟨hφ, hφb⟩ := hS φ hφS
    have hφK : ∀ η ∈ Metric.sphere (0 : ℂ) 1, φ η ∈ K := fun η hη => by
      simp only [K, Set.mem_iUnion]; exact ⟨φ, hφS, η, hη, rfl⟩
    have hφU : φ '' Metric.closedBall (0 : ℂ) 1 ⊆ U := by
      rintro _ ⟨η, hη, rfl⟩
      by_cases hηs : η ∈ Metric.sphere (0 : ℂ) 1
      · exact hrel.2 (subset_closure (hφK η hηs))
      · apply hφb
        refine ⟨η, ?_, rfl⟩
        rw [Metric.mem_ball]
        rw [Metric.mem_closedBall] at hη
        rw [Metric.mem_sphere] at hηs
        exact lt_of_le_of_ne hη hηs
    refine ⟨hφb ⟨ζ, hζ, rfl⟩, fun f hf => ?_⟩
    refine (COMP f hf φ hφ hφU ζ hζ).trans ?_
    exact iSup₂_le fun η hη => le_iSup₂ (f := fun x _ => f x) (φ η) (hφK η hη)
  exact ⟨hHc.of_isClosed_subset isClosed_closure (closure_mono hsub),
    (closure_mono hsub).trans hHU⟩

end P_ks

section P_c1
open InnerProductSpace

/-! C1a: the Dirichlet problem on a disc via the Poisson integral (center 0 first). -/

theorem p0f0c_pk_nonneg {R : ℝ} {w ζ : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R)
    (hζ : ζ ∈ Metric.sphere (0 : ℂ) R) : 0 ≤ poissonKernel 0 w ζ := by
  rw [poissonKernel_def]
  apply div_nonneg _ (sq_nonneg _)
  rw [mem_sphere_zero_iff_norm] at hζ
  rw [mem_ball_zero_iff] at hw
  simp only [sub_zero]
  rw [hζ]
  nlinarith [norm_nonneg w]

theorem p0f0c_pk_avg {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R) :
    Real.circleAverage (poissonKernel 0 w) 0 R = 1 := by
  have h := (harmonicContOnCl_const (c := (1 : ℝ)) (s := Metric.ball (0 : ℂ) R)).circleAverage_poissonKernel_smul hw
  have e : (poissonKernel 0 w • fun _ : ℂ => (1 : ℝ)) = poissonKernel 0 w := by
    funext ζ; simp
  rw [e] at h
  exact h

theorem p0f0c_pk_far {R d : ℝ} {w ζ : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R)
    (hζ : ζ ∈ Metric.sphere (0 : ℂ) R) (hd : 0 < d) (hdist : d ≤ ‖ζ - w‖) :
    poissonKernel 0 w ζ ≤ (R ^ 2 - ‖w‖ ^ 2) / d ^ 2 := by
  rw [poissonKernel_def]
  rw [mem_sphere_zero_iff_norm] at hζ
  rw [mem_ball_zero_iff] at hw
  simp only [sub_zero]
  rw [hζ]
  apply div_le_div_of_nonneg_left _ (by positivity)
  · exact pow_le_pow_left₀ hd.le hdist 2
  · nlinarith [norm_nonneg w]

theorem p0f0c_pk_cont {R : ℝ} {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) R) :
    ContinuousOn (poissonKernel 0 w) (Metric.sphere (0 : ℂ) R) := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg w) (mem_ball_zero_iff.mp hw)
  have h := continuousOn_herglotzRieszKernel_sphere (c := 0) hw
  rw [abs_of_pos hR] at h
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact Complex.continuous_re.comp_continuousOn h

/-- Boundary behaviour of the Poisson integral. -/
theorem p0f0c_PI_boundary {h : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hh : ContinuousOn h (Metric.sphere (0 : ℂ) R)) {z0 : ℂ}
    (hz0 : z0 ∈ Metric.sphere (0 : ℂ) R) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ w ∈ Metric.ball (0 : ℂ) R, dist w z0 < ρ →
      |Real.circleAverage (poissonKernel 0 w • h) 0 R - h z0| < ε := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hh
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB z0 hz0)
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuousWithinAt_iff.mp (hh z0 hz0) (ε / 2) (half_pos hε)
  set K : ℝ := 16 * B * R / δ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨min (δ / 2) (ε / (2 * (K + 1))), by positivity, ?_⟩
  intro w hw hwd
  have hwd1 : dist w z0 < δ / 2 := lt_of_lt_of_le hwd (min_le_left _ _)
  have hwd2 : dist w z0 < ε / (2 * (K + 1)) := lt_of_lt_of_le hwd (min_le_right _ _)
  have hz0n : ‖z0‖ = R := mem_sphere_zero_iff_norm.mp hz0
  have hwn : ‖w‖ < R := mem_ball_zero_iff.mp hw
  have hPc := p0f0c_pk_cont hw
  have hint1 : CircleIntegrable (poissonKernel 0 w • h) 0 R :=
    (hPc.mul hh).circleIntegrable hR.le
  have hint2 : CircleIntegrable (poissonKernel 0 w • fun _ : ℂ => h z0) 0 R :=
    (hPc.mul continuousOn_const).circleIntegrable hR.le
  have e1 : Real.circleAverage (poissonKernel 0 w • fun _ : ℂ => h z0) 0 R = h z0 := by
    have : (poissonKernel 0 w • fun _ : ℂ => h z0) = h z0 • poissonKernel 0 w := by
      funext ζ; simp [mul_comm]
    rw [this, Real.circleAverage_smul, p0f0c_pk_avg hw, smul_eq_mul, mul_one]
  have hid : Real.circleAverage (poissonKernel 0 w • h) 0 R - h z0 =
      Real.circleAverage (poissonKernel 0 w • h - poissonKernel 0 w • fun _ : ℂ => h z0) 0 R := by
    rw [Real.circleAverage_sub hint1 hint2, e1]
  rw [hid]
  -- pointwise bound on the sphere
  have hRw : R ^ 2 - ‖w‖ ^ 2 ≤ 2 * R * dist w z0 := by
    have h1 : R - ‖w‖ ≤ dist w z0 := by
      rw [dist_comm, dist_eq_norm, ← hz0n]
      have := norm_sub_norm_le z0 w
      linarith
    nlinarith [norm_nonneg w]
  have hpt : ∀ ζ ∈ Metric.sphere (0 : ℂ) |R|,
      |(poissonKernel 0 w • h - poissonKernel 0 w • fun _ : ℂ => h z0) ζ| ≤
        (ε / 2) * poissonKernel 0 w ζ + K * dist w z0 := by
    intro ζ hζ
    rw [abs_of_pos hR] at hζ
    have hP0 := p0f0c_pk_nonneg hw hζ
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_nonneg hP0]
    by_cases hnear : dist ζ z0 < δ
    · have h1 := hδh hζ hnear
      rw [Real.dist_eq] at h1
      have : poissonKernel 0 w ζ * |h ζ - h z0| ≤ poissonKernel 0 w ζ * (ε / 2) :=
        mul_le_mul_of_nonneg_left h1.le hP0
      nlinarith [mul_nonneg hK0 (dist_nonneg (x := w) (y := z0))]
    · push Not at hnear
      have hfar : δ / 2 ≤ ‖ζ - w‖ := by
        have := dist_triangle ζ w z0
        rw [← dist_eq_norm]
        linarith
      have hPb := p0f0c_pk_far hw hζ (by positivity) hfar
      have hhb : |h ζ - h z0| ≤ 2 * B := by
        have h1 := hB ζ hζ
        have h2 := hB z0 hz0
        rw [Real.norm_eq_abs] at h1 h2
        calc |h ζ - h z0| ≤ |h ζ| + |h z0| := abs_sub _ _
          _ ≤ 2 * B := by linarith
      have h3 : poissonKernel 0 w ζ ≤ 2 * R * dist w z0 / (δ / 2) ^ 2 :=
        hPb.trans (div_le_div_of_nonneg_right hRw (by positivity))
      have h4 : poissonKernel 0 w ζ * |h ζ - h z0| ≤
          (2 * R * dist w z0 / (δ / 2) ^ 2) * (2 * B) :=
        mul_le_mul h3 hhb (abs_nonneg _) (by positivity)
      have h5 : (2 * R * dist w z0 / (δ / 2) ^ 2) * (2 * B) = K * dist w z0 := by
        rw [hK]; field_simp; ring
      nlinarith [mul_nonneg (half_pos hε).le hP0]
  have hbound : Real.circleAverage
      (fun ζ => (ε / 2) * poissonKernel 0 w ζ + K * dist w z0) 0 R =
      ε / 2 + K * dist w z0 := by
    have e : (fun ζ => (ε / 2) * poissonKernel 0 w ζ + K * dist w z0) =
        (ε / 2) • poissonKernel 0 w + fun _ => K * dist w z0 := by
      funext ζ; simp
    rw [e, Real.circleAverage_add ((hPc.const_smul (ε / 2)).circleIntegrable hR.le)
      (continuousOn_const.circleIntegrable hR.le), Real.circleAverage_smul, p0f0c_pk_avg hw,
      Real.circleAverage_const, smul_eq_mul, mul_one]
  calc |Real.circleAverage (poissonKernel 0 w • h - poissonKernel 0 w • fun _ : ℂ => h z0) 0 R|
      ≤ Real.circleAverage
          |poissonKernel 0 w • h - poissonKernel 0 w • fun _ : ℂ => h z0| 0 R :=
        Real.abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun ζ => (ε / 2) * poissonKernel 0 w ζ + K * dist w z0) 0 R := by
        apply Real.circleAverage_mono
        · exact (hint1.sub hint2).abs
        · exact ((hPc.const_smul (ε / 2)).add continuousOn_const).circleIntegrable hR.le
        · intro ζ hζ; exact hpt ζ hζ
    _ = ε / 2 + K * dist w z0 := hbound
    _ < ε := by
        have : K * dist w z0 ≤ K * (ε / (2 * (K + 1))) :=
          mul_le_mul_of_nonneg_left hwd2.le hK0
        have h6 : K * (ε / (2 * (K + 1))) < ε / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

/-- C1a: the Dirichlet problem on a disc with continuous boundary data. -/
theorem p0f0c_dirichlet {h : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hh : ContinuousOn h (Metric.sphere c R)) :
    ∃ g : ℂ → ℝ, ContinuousOn g (Metric.closedBall c R) ∧ HarmonicOnNhd g (Metric.ball c R) ∧
      (∀ x ∈ Metric.sphere c R, g x = h x) ∧ g c = Real.circleAverage h c R := by
  classical
  set h' : ℂ → ℝ := fun ζ => h (c + ζ) with hh'def
  have hh' : ContinuousOn h' (Metric.sphere (0 : ℂ) R) := by
    refine hh.comp (by fun_prop) (fun ζ hζ => ?_)
    rw [mem_sphere_zero_iff_norm] at hζ
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, hζ]
  have hint : CircleIntegrable h' 0 R := hh'.circleIntegrable hR.le
  set PI : ℂ → ℝ := fun w' => Real.circleAverage (poissonKernel 0 w' • h') 0 R with hPIdef
  set F : ℂ → ℂ := fun w' =>
    Real.circleAverage (fun ζ ↦ herglotzRieszKernel 0 w' ζ • ((h' ζ : ℝ) : ℂ)) 0 R with hFdef
  have hFa : AnalyticOnNhd ℂ F (Metric.ball 0 R) := by
    have hint' : CircleIntegrable (fun ζ => ((h' ζ : ℝ) : ℂ)) 0 R :=
      (Complex.continuous_ofReal.comp_continuousOn hh').circleIntegrable hR.le
    exact analyticOnNhd_circleAverage_herglotzRieszKernel_smul hint'
  have hPIF : ∀ w' ∈ Metric.ball (0 : ℂ) R, PI w' = (F w').re := by
    intro w' hw'
    simp only [hPIdef, hFdef]
    rw [re_circleAverage_herglotzRieszKernel_smul hint hw', poissonKernel_eq_re_herglotzRieszKernel]
  set g : ℂ → ℝ := fun w => if w ∈ Metric.ball c R then PI (w - c) else h w with hgdef
  have hball' : ∀ w ∈ Metric.ball c R, w - c ∈ Metric.ball (0 : ℂ) R := by
    intro w hw; rw [mem_ball_zero_iff, ← dist_eq_norm]; exact hw
  have hharm : HarmonicOnNhd g (Metric.ball c R) := by
    intro z hz
    have hev : g =ᶠ[nhds z] fun w => (F (w - c)).re := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      simp only [hgdef, if_pos hw]
      exact hPIF _ (hball' w hw)
    rw [harmonicAt_congr_nhds hev]
    have h2 : AnalyticAt ℂ (fun w : ℂ => w - c) z := analyticAt_id.sub analyticAt_const
    have : AnalyticAt ℂ (fun w => F (w - c)) z :=
      AnalyticAt.comp (g := F) (f := fun w : ℂ => w - c) (x := z) (hFa _ (hball' z hz)) h2
    exact this.harmonicAt_re
  refine ⟨g, ?_, hharm, ?_, ?_⟩
  · intro z hz
    by_cases hzb : z ∈ Metric.ball c R
    · exact (hharm z hzb).1.continuousAt.continuousWithinAt
    · have hzs : z ∈ Metric.sphere c R := by
        rw [Metric.mem_sphere]
        rw [Metric.mem_ball] at hzb
        rw [Metric.mem_closedBall] at hz
        linarith
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have hz0' : z - c ∈ Metric.sphere (0 : ℂ) R := by
        rw [mem_sphere_zero_iff_norm, ← dist_eq_norm]; exact hzs
      obtain ⟨ρ1, hρ1, hP⟩ := p0f0c_PI_boundary hR hh' hz0' hε
      obtain ⟨ρ2, hρ2, hc⟩ := Metric.continuousWithinAt_iff.mp (hh z hzs) ε hε
      refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun {w} hw hwd => ?_⟩
      have hgz : g z = h z := by simp only [hgdef, if_neg hzb]
      rw [hgz]
      by_cases hwb : w ∈ Metric.ball c R
      · simp only [hgdef, if_pos hwb]
        have hdist : dist (w - c) (z - c) < ρ1 := by
          rw [dist_sub_right]; exact lt_of_lt_of_le hwd (min_le_left _ _)
        have := hP (w - c) (hball' w hwb) hdist
        have e : h' (z - c) = h z := by simp [hh'def]
        rw [e] at this
        rw [Real.dist_eq]; exact this
      · simp only [hgdef, if_neg hwb]
        have hws : w ∈ Metric.sphere c R := by
          rw [Metric.mem_sphere]
          rw [Metric.mem_ball] at hwb
          rw [Metric.mem_closedBall] at hw
          linarith
        exact hc hws (lt_of_lt_of_le hwd (min_le_right _ _))
  · intro x hx
    have hxb : x ∉ Metric.ball c R := by
      rw [Metric.mem_ball]; rw [Metric.mem_sphere] at hx; linarith
    simp only [hgdef, if_neg hxb]
  · have hcb : c ∈ Metric.ball c R := Metric.mem_ball_self hR
    simp only [hgdef, if_pos hcb, sub_self, hPIdef]
    have e1 : Real.circleAverage (poissonKernel 0 0 • h') 0 R = Real.circleAverage h' 0 R := by
      apply Real.circleAverage_congr_sphere
      intro ζ hζ
      rw [abs_of_pos hR, mem_sphere_zero_iff_norm] at hζ
      show poissonKernel 0 0 ζ * h' ζ = h' ζ
      rw [poissonKernel_def]
      simp [hζ, hR.ne']
    rw [e1]
    unfold Real.circleAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [hh'def, circleMap]

/-- Averages of a bounded-below usc function on a circle are limits of averages of continuous
majorants (Lipschitz envelopes + dominated convergence). -/
theorem p0f0c_usc_avg_le {v : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hv : UpperSemicontinuousOn v (Metric.sphere c R)) {m : ℝ}
    (hm : ∀ x ∈ Metric.sphere c R, m ≤ v x) {a : ℝ}
    (H : ∀ h : ℂ → ℝ, Continuous h → (∀ x ∈ Metric.sphere c R, v x ≤ h x) →
      a ≤ Real.circleAverage h c R) :
    a ≤ Real.circleAverage v c R := by
  set S := Metric.sphere c R with hSdef
  have hSne : S.Nonempty := ⟨c + R, by simp [S, abs_of_pos hR]⟩
  obtain ⟨x0, hx0, hmax⟩ := hv.exists_isMaxOn hSne (isCompact_sphere c R)
  set B := v x0
  have hB : ∀ x ∈ S, v x ≤ B := fun x hx => hmax hx
  let hk : ℕ → ℂ → ℝ := fun k x => sSup ((fun y => v y - (k : ℝ) * dist x y) '' S)
  have hbdd : ∀ (k : ℕ) (x : ℂ), BddAbove ((fun y => v y - (k : ℝ) * dist x y) '' S) := by
    intro k x
    refine ⟨B, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := hB y hy
    have : 0 ≤ (k : ℝ) * dist x y := by positivity
    linarith
  have hne : ∀ (k : ℕ) (x : ℂ), ((fun y => v y - (k : ℝ) * dist x y) '' S).Nonempty :=
    fun k x => hSne.image _
  have hle : ∀ k, ∀ x ∈ S, v x ≤ hk k x := by
    intro k x hx
    exact le_csSup (hbdd k x) ⟨x, hx, by simp⟩
  have hub : ∀ k x, hk k x ≤ B := by
    intro k x
    refine csSup_le (hne k x) ?_
    rintro _ ⟨y, hy, rfl⟩
    have := hB y hy
    have : 0 ≤ (k : ℝ) * dist x y := by positivity
    linarith
  have hlip : ∀ k x x', hk k x ≤ hk k x' + (k : ℝ) * dist x x' := by
    intro k x x'
    refine csSup_le (hne k x) ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : v y - (k : ℝ) * dist x' y ≤ hk k x' := le_csSup (hbdd k x') ⟨y, hy, rfl⟩
    have h2 : dist x' y ≤ dist x' x + dist x y := dist_triangle _ _ _
    have h3 : (k : ℝ) * dist x' y ≤ (k : ℝ) * dist x' x + (k : ℝ) * dist x y := by
      have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) k)
      linarith
    rw [dist_comm x' x] at h3
    linarith
  have hcont : ∀ k, Continuous (hk k) := fun k =>
    (LipschitzWith.of_le_add_mul' (k : ℝ) (hlip k)).continuous
  have hlim : ∀ x ∈ S, Filter.Tendsto (fun k => hk k x) Filter.atTop (nhds (v x)) := by
    intro x hx
    rw [tendsto_order]
    refine ⟨fun a' ha' => Filter.Eventually.of_forall fun k => lt_of_lt_of_le ha' (hle k x hx),
      fun a' ha' => ?_⟩
    have hε : 0 < a' - v x := by linarith
    have hu := hv x hx (v x + (a' - v x) / 2) (by linarith)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.mp hu
    obtain ⟨N, hN⟩ := exists_nat_ge ((B - m) / δ)
    refine Filter.eventually_atTop.mpr ⟨N, fun k hk' => ?_⟩
    have hkN : (N : ℝ) ≤ k := by exact_mod_cast hk'
    have hsup : hk k x ≤ v x + (a' - v x) / 2 := by
      refine csSup_le (hne k x) ?_
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyd : dist y x < δ
      · have := hδs ⟨hyd, hy⟩
        simp only [Set.mem_setOf_eq] at this
        have : 0 ≤ (k : ℝ) * dist x y := by positivity
        linarith
      · push Not at hyd
        have h1 : (B - m) ≤ (k : ℝ) * δ := by
          have := (div_le_iff₀ hδ).mp hN
          nlinarith
        have h2 : (k : ℝ) * δ ≤ (k : ℝ) * dist x y := by
          rw [dist_comm]; exact mul_le_mul_of_nonneg_left hyd (Nat.cast_nonneg k)
        have := hB y hy
        have := hm x hx
        linarith
    linarith
  -- dominated convergence for the averages
  have hmem : ∀ θ : ℝ, circleMap c R θ ∈ S := fun θ => circleMap_mem_sphere c hR.le θ
  have htend : Filter.Tendsto (fun k => Real.circleAverage (hk k) c R) Filter.atTop
      (nhds (Real.circleAverage v c R)) := by
    unfold Real.circleAverage
    refine Filter.Tendsto.const_smul ?_ _
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => |B| + |m|) ?_ ?_ intervalIntegrable_const ?_
    · exact Filter.Eventually.of_forall fun k =>
        ((hcont k).comp (continuous_circleMap c R)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun k => Filter.Eventually.of_forall fun θ _ => ?_
      have h1 := hle k _ (hmem θ)
      have h2 := hub k (circleMap c R θ)
      have h3 := hm _ (hmem θ)
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := neg_abs_le m; have := abs_nonneg B; linarith
      · have := le_abs_self B; have := abs_nonneg m; linarith
    · exact Filter.Eventually.of_forall fun θ _ => hlim _ (hmem θ)
  exact ge_of_tendsto' htend fun k => H (hk k) (hcont k) (hle k)

open LeblSCV.Pseudoconvex in
/-- C1: sub-mean value property of a bounded-below subharmonic function. -/
theorem p0f0c_sub_mean {u : ℂ → EReal} {V : Set ℂ} (hu : IsSubharmonicOn u V) {m : ℝ}
    (hm : ∀ z ∈ V, (m : EReal) ≤ u z) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hcb : Metric.closedBall c R ⊆ V) :
    (u c).toReal ≤ Real.circleAverage (fun ξ => (u ξ).toReal) c R := by
  set v : ℂ → ℝ := fun ξ => (u ξ).toReal with hvdef
  have hcoe : ∀ z ∈ V, u z = (v z : EReal) := by
    intro z hz
    have hbot : u z ≠ ⊥ := by
      intro h; have := hm z hz; rw [h] at this; exact absurd this (by simp)
    exact (EReal.coe_toReal (hu.2.1 z hz) hbot).symm
  have hSV : Metric.sphere c R ⊆ V := Metric.sphere_subset_closedBall.trans hcb
  have hvusc : UpperSemicontinuousOn v (Metric.sphere c R) := by
    intro x hx y hy
    have h1 : u x < (y : EReal) := by rw [hcoe x (hSV hx)]; exact_mod_cast hy
    have h2 := (hu.1 x (hSV hx) y h1).filter_mono (nhdsWithin_mono x hSV)
    filter_upwards [h2, self_mem_nhdsWithin] with z hz hzS
    rw [hcoe z (hSV hzS)] at hz
    exact_mod_cast hz
  refine p0f0c_usc_avg_le hR hvusc (m := m)
    (fun x hx => by have := hm x (hSV hx); rw [hcoe x (hSV hx)] at this; exact_mod_cast this) ?_
  intro h hh hvh
  obtain ⟨g, hgc, hgH, hgb, hgc0⟩ := p0f0c_dirichlet hR hh.continuousOn
  have hgI : IsHarmonicOn g (Metric.ball c R) :=
    ⟨hgH.contDiffOn, fun z hz => (hgH z hz).2.eq_of_nhds⟩
  have := hu.2.2 c R hR hcb g hgc hgI (fun x hx => by
    rw [hcoe x (hSV hx), hgb x hx]; exact_mod_cast hvh x hx) c (Metric.mem_ball_self hR)
  rw [hcoe c (hcb (Metric.mem_closedBall_self hR.le)), hgc0] at this
  exact_mod_cast this

end P_c1

section P_c3
/-- A function that changes sign under the rotation `τ ↦ τ e^{iθ₀}` has zero circle average. -/
theorem p0f0c_avg_rot_zero {h : ℂ → ℝ} {s : ℝ} (θ0 : ℝ)
    (hh : ∀ τ, h (τ * Complex.exp (θ0 * Complex.I)) = - h τ) :
    Real.circleAverage h 0 s = 0 := by
  have h1 := Real.circleAverage_eq_integral_add (f := h) (c := 0) (R := s) θ0
  have h2 : ∀ θ : ℝ, h (circleMap 0 s (θ + θ0)) = - h (circleMap 0 s θ) := by
    intro θ
    rw [← hh]
    congr 1
    simp only [circleMap, zero_add, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  simp only [h2, intervalIntegral.integral_neg, smul_neg] at h1
  rw [← Real.circleAverage_def] at h1
  linarith

/-- Second-order expansion of a holomorphic map at a point. -/
theorem p0f0c_disc_taylor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {φ : ℂ → F} {ζ0 : ℂ} (h : AnalyticAt ℂ φ ζ0) :
    ∃ a q : F, ∃ K > 0, ∃ s1 > 0, ∀ τ : ℂ, ‖τ‖ < s1 →
      ‖φ (ζ0 + τ) - (φ ζ0 + τ • a + τ ^ 2 • q)‖ ≤ K * ‖τ‖ ^ 3 := by
  obtain ⟨pφ, hp⟩ := h
  obtain ⟨c, hc, hw⟩ := (hp.isBigO_sub_partialSum_pow 3).exists_pos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hw.bound
  refine ⟨pφ.coeff 1, pφ.coeff 2, c, hc, ε, hε, fun τ hτ => ?_⟩
  have hτ' : dist τ 0 < ε := by simpa using hτ
  have := hball hτ'
  have hps : pφ.partialSum 3 τ = φ ζ0 + τ • pφ.coeff 1 + τ ^ 2 • pφ.coeff 2 := by
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add]
    rw [hp.coeff_zero, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, pow_one]
  rw [hps] at this
  simpa [norm_pow] using this

/-- Second-order control of a `C²` function near a point, uniformly on small balls. -/
theorem p0f0c_G_taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : E → ℝ} (hG : ContDiff ℝ 2 G) (p : E) :
    ∃ L ≥ (0 : ℝ), ∃ ρ > 0, ∀ r ≤ ρ, ∀ x ∈ Metric.closedBall p r, ∀ y ∈ Metric.closedBall p r,
      ‖G y - G x - fderiv ℝ G p (y - x)‖ ≤ L * r * ‖y - x‖ := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.contDiffAt.exists_lipschitzOnWith (x := p)
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨K, K.2, ε / 2, by linarith, fun r hr x hx y hy => ?_⟩
  have hsub : Metric.closedBall p r ⊆ t := fun z hz =>
    hεt (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by linarith)))
  have hpt : p ∈ t := hεt (Metric.mem_ball_self hε)
  have hdiff : ∀ z ∈ Metric.closedBall p r, DifferentiableAt ℝ G z :=
    fun z _ => (hG.differentiable (by norm_num)) z
  have hbound : ∀ z ∈ Metric.closedBall p r, ‖fderiv ℝ G z - fderiv ℝ G p‖ ≤ K * r := by
    intro z hz
    rw [← dist_eq_norm]
    calc dist (fderiv ℝ G z) (fderiv ℝ G p) ≤ K * dist z p := hK.dist_le_mul z (hsub hz) p hpt
      _ ≤ K * r := mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hz) K.2
  have := (convex_closedBall p r).norm_image_sub_le_of_norm_fderiv_le' hdiff hbound hx hy
  simpa using this

/-- Taylor bound for `G ∘ φ` at a point: `G(φ(ζ0+τ)) = G(p + τa) + DG(p)(τ²q) + O(|τ|³)`. -/
theorem p0f0c_comp_taylor {n : ℕ} {G : EuclideanSpace ℂ (Fin n) → ℝ} (hG : ContDiff ℝ 2 G)
    {φ : ℂ → EuclideanSpace ℂ (Fin n)} {ζ0 : ℂ} (hφ : AnalyticAt ℂ φ ζ0) :
    ∃ a q : EuclideanSpace ℂ (Fin n), ∃ C ≥ (0 : ℝ), ∃ s0 > (0 : ℝ), ∀ τ : ℂ, ‖τ‖ < s0 →
      |G (φ (ζ0 + τ)) - G (φ ζ0 + τ • a) - fderiv ℝ G (φ ζ0) (τ ^ 2 • q)| ≤ C * ‖τ‖ ^ 3 := by
  obtain ⟨a, q, K, hK, s1, hs1, hT⟩ := p0f0c_disc_taylor hφ
  obtain ⟨L, hL, ρ, hρ, hG2⟩ := p0f0c_G_taylor hG (φ ζ0)
  set p := φ ζ0
  set D := fderiv ℝ G p
  set κ := ‖a‖ + ‖q‖ + K
  have hκ : 0 ≤ κ := by positivity
  refine ⟨a, q, L * κ * (‖q‖ + K) + ‖D‖ * K, by positivity,
    min s1 (min 1 (ρ / (κ + 1))), by positivity, fun τ hτ => ?_⟩
  have hτ1 : ‖τ‖ < s1 := lt_of_lt_of_le hτ (min_le_left _ _)
  have hτ2 : ‖τ‖ < 1 := lt_of_lt_of_le hτ ((min_le_right _ _).trans (min_le_left _ _))
  have hτ3 : ‖τ‖ < ρ / (κ + 1) := lt_of_lt_of_le hτ ((min_le_right _ _).trans (min_le_right _ _))
  have he' : ‖φ (ζ0 + τ) - (p + τ • a + τ ^ 2 • q)‖ ≤ K * ‖τ‖ ^ 3 := hT τ hτ1
  set e := φ (ζ0 + τ) - (p + τ • a + τ ^ 2 • q) with he
  set t := ‖τ‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hy : φ (ζ0 + τ) = p + τ • a + τ ^ 2 • q + e := by rw [he]; abel
  have hna : ‖τ • a‖ = t * ‖a‖ := norm_smul _ _
  have hnq : ‖τ ^ 2 • q‖ = t ^ 2 * ‖q‖ := by rw [norm_smul, norm_pow]
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have ht3 : t ^ 3 ≤ t ^ 2 := by nlinarith
  have hr : κ * t ≤ ρ := by
    have : t * (κ + 1) < ρ := (lt_div_iff₀ (by positivity)).mp hτ3
    nlinarith
  have hx : p + τ • a ∈ Metric.closedBall p (κ * t) := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hna]
    nlinarith [norm_nonneg q, norm_nonneg a]
  have hyb : φ (ζ0 + τ) ∈ Metric.closedBall p (κ * t) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hy]
    have : p + τ • a + τ ^ 2 • q + e - p = τ • a + τ ^ 2 • q + e := by abel
    rw [this]
    calc ‖τ • a + τ ^ 2 • q + e‖ ≤ ‖τ • a‖ + ‖τ ^ 2 • q‖ + ‖e‖ := norm_add₃_le
      _ ≤ κ * t := by
        rw [hna, hnq]
        nlinarith [norm_nonneg a, norm_nonneg q, mul_le_mul_of_nonneg_left ht2 (norm_nonneg q),
          mul_le_mul_of_nonneg_left (ht3.trans ht2) hK.le]
  have hyx : φ (ζ0 + τ) - (p + τ • a) = τ ^ 2 • q + e := by rw [hy]; abel
  have hyxn : ‖φ (ζ0 + τ) - (p + τ • a)‖ ≤ (‖q‖ + K) * t ^ 2 := by
    rw [hyx]
    calc ‖τ ^ 2 • q + e‖ ≤ ‖τ ^ 2 • q‖ + ‖e‖ := norm_add_le _ _
      _ ≤ (‖q‖ + K) * t ^ 2 := by
        rw [hnq]; nlinarith [mul_le_mul_of_nonneg_left ht3 hK.le]
  have hmain := hG2 (κ * t) hr _ hx _ hyb
  rw [Real.norm_eq_abs] at hmain
  have hDe : |D e| ≤ ‖D‖ * (K * t ^ 3) := by
    calc |D e| = ‖D e‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖D‖ * ‖e‖ := D.le_opNorm e
      _ ≤ _ := mul_le_mul_of_nonneg_left he' (norm_nonneg _)
  have hsplit : G (φ (ζ0 + τ)) - G (p + τ • a) - D (τ ^ 2 • q) =
      (G (φ (ζ0 + τ)) - G (p + τ • a) - D (φ (ζ0 + τ) - (p + τ • a))) + D e := by
    rw [hyx, map_add]; ring
  rw [hsplit]
  calc _ ≤ |G (φ (ζ0 + τ)) - G (p + τ • a) - D (φ (ζ0 + τ) - (p + τ • a))| + |D e| :=
        abs_add_le _ _
    _ ≤ L * (κ * t) * ((‖q‖ + K) * t ^ 2) + ‖D‖ * (K * t ^ 3) :=
        add_le_add (hmain.trans (mul_le_mul_of_nonneg_left hyxn (by positivity))) hDe
    _ = _ := by ring

/-- C3: a `C²` function with the sub-mean property on complex lines satisfies the maximum
principle along holomorphic discs. -/
theorem p0f0c_C3 {n : ℕ} {G : EuclideanSpace ℂ (Fin n) → ℝ} (hG : ContDiff ℝ 2 G)
    {W : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W)
    (hsm : ∀ z ∈ W, ∀ b : EuclideanSpace ℂ (Fin n), ∀ r > (0 : ℝ),
      (∀ τ ∈ Metric.closedBall (0 : ℂ) r, z + τ • b ∈ W) →
      G z ≤ Real.circleAverage (fun τ => G (z + τ • b)) 0 r)
    {φ : ℂ → EuclideanSpace ℂ (Fin n)} (hc : ContinuousOn φ (Metric.closedBall 0 1))
    (hd : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφW : φ '' Metric.closedBall 0 1 ⊆ W)
    {M : ℝ} (hM : ∀ η ∈ Metric.sphere (0 : ℂ) 1, G (φ η) ≤ M) :
    ∀ ζ ∈ Metric.ball (0 : ℂ) 1, G (φ ζ) ≤ M := by
  intro ζ1 hζ1
  by_contra hlt
  have hlt' : M < G (φ ζ1) := not_le.mp hlt
  set η := (G (φ ζ1) - M) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  set w : ℂ → ℝ := fun ζ => G (φ ζ) + η * ‖ζ‖ ^ 2 with hwdef
  have hwc : ContinuousOn w (Metric.closedBall 0 1) :=
    (hG.continuous.comp_continuousOn hc).add
      (by fun_prop : Continuous fun ζ : ℂ => η * ‖ζ‖ ^ 2).continuousOn
  obtain ⟨ζ0, hζ0, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hwc
  have hmax' : ∀ x ∈ Metric.closedBall (0 : ℂ) 1, w x ≤ w ζ0 := isMaxOn_iff.mp hmax
  have hw1 : w ζ1 ≤ w ζ0 := hmax' ζ1 (Metric.ball_subset_closedBall hζ1)
  have hζ0n : ‖ζ0‖ < 1 := by
    by_contra hnb
    have h1 : ‖ζ0‖ = 1 := le_antisymm (by simpa using hζ0) (not_lt.mp hnb)
    have hs : ζ0 ∈ Metric.sphere (0 : ℂ) 1 := by simpa using h1
    have := hM ζ0 hs
    have h2 : 0 ≤ η * ‖ζ1‖ ^ 2 := by positivity
    have hw1' : G (φ ζ1) + η * ‖ζ1‖ ^ 2 ≤ G (φ ζ0) + η * ‖ζ0‖ ^ 2 := hw1
    rw [h1] at hw1'
    linarith
  have hζ0b : ζ0 ∈ Metric.ball (0 : ℂ) 1 := by simpa using hζ0n
  have hAn := hd.analyticAt (Metric.isOpen_ball.mem_nhds hζ0b)
  obtain ⟨a, q, C, hC, s0, hs0, hT⟩ := p0f0c_comp_taylor hG hAn
  set p := φ ζ0 with hpdef
  have hpW : p ∈ W := hφW ⟨ζ0, hζ0, rfl⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW p hpW
  have hd1 : 0 < 1 - ‖ζ0‖ := by linarith
  have ha1 : 0 < ‖a‖ + 1 := by positivity
  have hC1 : 0 < C + 1 := by linarith
  set s := min (min (s0 / 2) ((1 - ‖ζ0‖) / 2)) (min (ε / (‖a‖ + 1) / 2) (η / (C + 1) / 2)) with hsdef
  have hspos : 0 < s := lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by positivity) (by positivity))
  have hss0 : s < s0 := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hs1 : s < 1 - ‖ζ0‖ :=
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  have hsε : s < ε / (‖a‖ + 1) :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith [div_pos hε ha1])
  have hsη : s < η / (C + 1) :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith [div_pos hη hC1])
  clear_value s
  have hsph : ∀ τ ∈ Metric.sphere (0 : ℂ) |s|, ‖τ‖ = s := by
    intro τ hτ; simpa [abs_of_pos hspos] using hτ
  have hin : ∀ τ : ℂ, ‖τ‖ ≤ s → ζ0 + τ ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro τ hτ
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖ζ0 + τ‖ ≤ ‖ζ0‖ + ‖τ‖ := norm_add_le _ _
      _ ≤ 1 := by linarith
  have hlineW : ∀ τ ∈ Metric.closedBall (0 : ℂ) s, p + τ • a ∈ W := by
    intro τ hτ
    apply hεW
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ‖τ‖ ≤ s := by simpa using hτ
    have h' : s * (‖a‖ + 1) < ε := (lt_div_iff₀ ha1).mp hsε
    nlinarith [norm_nonneg a, norm_nonneg τ]
  have hsub := hsm p hpW a s hspos hlineW
  have hwint : CircleIntegrable (fun τ => w (ζ0 + τ)) 0 s := by
    apply ContinuousOn.circleIntegrable'
    refine hwc.comp (by fun_prop : Continuous fun τ : ℂ => ζ0 + τ).continuousOn ?_
    intro τ hτ; exact hin τ (hsph τ hτ).le
  have hup : Real.circleAverage (fun τ => w (ζ0 + τ)) 0 s ≤ w ζ0 :=
    Real.circleAverage_mono_on_of_le_circle hwint (fun τ hτ => hmax' _ (hin τ (hsph τ hτ).le))
  set D := fderiv ℝ G p with hDdef
  set f1 : ℂ → ℝ := fun τ => G (p + τ • a) with hf1def
  set f2 : ℂ → ℝ := fun τ => D (τ ^ 2 • q) with hf2def
  set f4 : ℂ → ℝ := fun τ => η * (2 * (ζ0 * (starRingEnd ℂ) τ).re) with hf4def
  set c0 : ℝ := η * (‖ζ0‖ ^ 2 + s ^ 2) - C * s ^ 3 with hc0def
  have hlow : ∀ τ ∈ Metric.sphere (0 : ℂ) |s|, f1 τ + f2 τ + f4 τ + c0 ≤ w (ζ0 + τ) := by
    intro τ hτ
    have hn := hsph τ hτ
    have hTτ := hT τ (by rw [hn]; exact hss0)
    rw [hn] at hTτ
    have hsq : ‖ζ0 + τ‖ ^ 2 = ‖ζ0‖ ^ 2 + s ^ 2 + 2 * (ζ0 * (starRingEnd ℂ) τ).re := by
      rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm, ← Complex.sq_norm, hn]
    show G (p + τ • a) + D (τ ^ 2 • q) + η * (2 * (ζ0 * (starRingEnd ℂ) τ).re) +
      (η * (‖ζ0‖ ^ 2 + s ^ 2) - C * s ^ 3) ≤ G (φ (ζ0 + τ)) + η * ‖ζ0 + τ‖ ^ 2
    rw [hsq]
    have := (abs_le.mp hTτ).1
    linarith
  have hf2 : Real.circleAverage f2 0 s = 0 := by
    apply p0f0c_avg_rot_zero (Real.pi / 2)
    intro τ
    have h2 : (τ * Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) ^ 2 = -τ ^ 2 := by
      rw [mul_pow, ← Complex.exp_nat_mul]
      have : ((2 : ℕ) : ℂ) * (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
        push_cast; ring
      rw [this, Complex.exp_pi_mul_I]; ring
    simp only [hf2def]
    rw [h2, neg_smul, map_neg]
  have hf4 : Real.circleAverage f4 0 s = 0 := by
    apply p0f0c_avg_rot_zero Real.pi
    intro τ
    simp only [hf4def]
    rw [Complex.exp_pi_mul_I]
    simp only [mul_neg, mul_one, map_neg, Complex.neg_re]
  have hcont1 : Continuous f1 := hG.continuous.comp (by fun_prop)
  have hcont2 : Continuous f2 := D.continuous.comp (by fun_prop)
  have hcont4 : Continuous f4 := continuous_const.mul (continuous_const.mul
    (Complex.continuous_re.comp (continuous_const.mul Complex.continuous_conj)))
  have hint : ∀ g : ℂ → ℝ, Continuous g → CircleIntegrable g 0 s :=
    fun g hg => hg.continuousOn.circleIntegrable'
  have havg : Real.circleAverage (fun τ => f1 τ + f2 τ + f4 τ + c0) 0 s =
      Real.circleAverage f1 0 s + c0 := by
    rw [Real.circleAverage_fun_add (hint (fun τ => f1 τ + f2 τ + f4 τ)
        ((hcont1.add hcont2).add hcont4)) (hint _ continuous_const),
      Real.circleAverage_fun_add (hint (fun τ => f1 τ + f2 τ) (hcont1.add hcont2)) (hint _ hcont4),
      Real.circleAverage_fun_add (hint _ hcont1) (hint _ hcont2), hf2, hf4,
      Real.circleAverage_const]
    ring
  have hmono : Real.circleAverage (fun τ => f1 τ + f2 τ + f4 τ + c0) 0 s ≤
      Real.circleAverage (fun τ => w (ζ0 + τ)) 0 s :=
    Real.circleAverage_mono (hint _ (((hcont1.add hcont2).add hcont4).add continuous_const))
      hwint hlow
  have hw0 : w ζ0 = G p + η * ‖ζ0‖ ^ 2 := rfl
  have hkey : η * s ^ 2 ≤ C * s ^ 3 := by
    have := hsub.trans (le_of_eq_of_le rfl (by linarith [havg, hmono, hup] :
      Real.circleAverage f1 0 s ≤ w ζ0 - c0))
    rw [hw0, hc0def] at this
    linarith
  have hCs : C * s < η := by
    have : s * (C + 1) < η := (lt_div_iff₀ hC1).mp hsη
    nlinarith
  have hs2 : 0 < s ^ 2 := by positivity
  nlinarith

end P_c3

section P_c2
open MeasureTheory

/-- A radial mollifier on `ℂⁿ` supported in the open ball of radius `ε`. -/
theorem p0f0c_mollifier {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : EuclideanSpace ℂ (Fin n) → ℝ, ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧ (∀ t, 0 ≤ ψ t) ∧
      (∀ t, ψ t ≠ 0 → ‖t‖ < ε) ∧ ∫ t, ψ t = 1 ∧
      (∀ (u : ℂ) t, ‖u‖ = 1 → ψ (u • t) = ψ t) := by
  set ψ0 : EuclideanSpace ℂ (Fin n) → ℝ := fun t => Real.smoothTransition (1 - ‖t‖ ^ 2 / ε ^ 2)
    with hψ0
  have hc0 : ContDiff ℝ 2 ψ0 :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))
  have hsupp : ∀ t, ψ0 t ≠ 0 → ‖t‖ < ε := by
    intro t ht
    by_contra h
    push Not at h
    apply ht
    apply Real.smoothTransition.zero_of_nonpos
    have h1 : ε ^ 2 ≤ ‖t‖ ^ 2 := by nlinarith
    rw [sub_nonpos, le_div_iff₀ (by positivity)]
    linarith
  have hnn : ∀ t, 0 ≤ ψ0 t := fun t => Real.smoothTransition.nonneg _
  have hcs : HasCompactSupport ψ0 := HasCompactSupport.intro
    (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) ε) (fun t ht => by
      by_contra h
      exact ht (by rw [mem_closedBall_zero_iff]; exact (hsupp t h).le))
  have h00 : ψ0 0 ≠ 0 := by simp [hψ0]
  have hpos : 0 < ∫ t, ψ0 t :=
    hc0.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun t => hnn t) h00
  refine ⟨fun t => ψ0 t / ∫ s, ψ0 s, hc0.div_const _, ?_, fun t => div_nonneg (hnn t) hpos.le,
    fun t ht => hsupp t (fun h => ht (by simp [h])), ?_, fun u t hu => ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) ε)
      (fun t ht => ?_)
    have : ψ0 t = 0 := by
      by_contra h
      exact ht (by rw [mem_closedBall_zero_iff]; exact (hsupp t h).le)
    simp [this]
  · rw [integral_div, div_self hpos.ne']
  · simp only [hψ0, norm_smul, hu, one_mul]

/-- Rotations `t ↦ u • t` (`|u| = 1`) preserve Lebesgue integrals on `ℂⁿ`. -/
theorem p0f0c_integral_rot {n : ℕ} (u : ℂ) (hu : ‖u‖ = 1) (g : EuclideanSpace ℂ (Fin n) → ℝ) :
    ∫ t, g (u • t) = ∫ t, g t := by
  let L : EuclideanSpace ℂ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
    { toFun := fun t => u • t
      map_add' := fun x y => smul_add u x y
      map_smul' := fun r x => by simp only [RingHom.id_apply]; exact smul_comm u r x
      norm_map' := fun x => by simp [norm_smul, hu] }
  let e := L.toLinearIsometryEquiv rfl
  exact e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding g

/-- Fubini for a compactly supported weight against a bounded jointly measurable family of
circle integrands. -/
theorem p0f0c_swap {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {H : EuclideanSpace ℂ (Fin n) → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) {B : ℝ} (hB : ∀ t θ, |H t θ| ≤ B) :
    ∫ t, ψ t * (∫ θ in (0 : ℝ)..2 * Real.pi, H t θ) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ t, ψ t * H t θ := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  simp only [intervalIntegral.integral_of_le h2π]
  simp_rw [← integral_const_mul]
  apply integral_integral_swap
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hdom : Integrable (fun z : EuclideanSpace ℂ (Fin n) × ℝ => |ψ z.1| * B)
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :=
    (hψi.abs.mul_const B).comp_fst _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact ((hψc.measurable.comp measurable_fst).mul hH).aestronglyMeasurable
  · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB _ _) (abs_nonneg _)

/-- Integrability companion of `p0f0c_swap`. -/
theorem p0f0c_swap_int {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {H : EuclideanSpace ℂ (Fin n) → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) {B : ℝ} (hB : ∀ t θ, |H t θ| ≤ B) :
    Integrable (fun t => ψ t * (∫ θ in (0 : ℝ)..2 * Real.pi, H t θ)) := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hdom : Integrable (fun z : EuclideanSpace ℂ (Fin n) × ℝ => |ψ z.1| * B)
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :=
    (hψi.abs.mul_const B).comp_fst _
  have hprod : Integrable (Function.uncurry fun t θ => ψ t * H t θ)
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact ((hψc.measurable.comp measurable_fst).mul hH).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB _ _) (abs_nonneg _)
  refine hprod.integral_prod_left.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.uncurry, intervalIntegral.integral_of_le h2π]
  exact integral_const_mul _ _

/-- The mollified function is `C²`. -/
theorem p0f0c_Feps_smooth {n : ℕ} {ψ F : EuclideanSpace ℂ (Fin n) → ℝ} (hψd : ContDiff ℝ 2 ψ)
    (hψs : HasCompactSupport ψ) (hFm : Measurable F) {B : ℝ} (hB : ∀ z, |F z| ≤ B) :
    ContDiff ℝ 2 (fun x => ∫ t, ψ t * F (x - t)) := by
  have hloc : LocallyIntegrable F volume := fun x =>
    ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos,
      Measure.integrableOn_of_bounded measure_ball_lt_top.ne hFm.aestronglyMeasurable (M := B)
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hB z)⟩
  have := hψs.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (n := 2) hψd hloc
  have heq : (fun x => ∫ t, ψ t * F (x - t)) =
      convolution ψ F (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [heq]
  exact_mod_cast this

theorem p0f0c_int_mul {n : ℕ} {ψ F : EuclideanSpace ℂ (Fin n) → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hFm : Measurable F) {B : ℝ} (hB : ∀ z, |F z| ≤ B)
    (x : EuclideanSpace ℂ (Fin n)) : Integrable (fun t => ψ t * F (x - t)) :=
  (hψc.integrable_of_hasCompactSupport hψs).mul_bdd
    (hFm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hB _)

/-- Upper bound for the mollified function. -/
theorem p0f0c_Feps_le {n : ℕ} {ψ F : EuclideanSpace ℂ (Fin n) → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψn : ∀ t, 0 ≤ ψ t) (hψ1 : ∫ t, ψ t = 1)
    (hFm : Measurable F) {B : ℝ} (hB : ∀ z, |F z| ≤ B) {x : EuclideanSpace ℂ (Fin n)} {M' : ℝ}
    (h : ∀ t, ψ t ≠ 0 → F (x - t) ≤ M') : ∫ t, ψ t * F (x - t) ≤ M' := by
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  calc ∫ t, ψ t * F (x - t) ≤ ∫ t, ψ t * M' :=
        integral_mono (p0f0c_int_mul hψc hψs hFm hB x) (hψi.mul_const _) (fun t => by
          by_cases h0 : ψ t = 0
          · simp [h0]
          · exact mul_le_mul_of_nonneg_left (h t h0) (hψn t))
    _ = M' := by rw [integral_mul_const, hψ1, one_mul]

/-- Line sub-mean property of the mollified function. -/
theorem p0f0c_Feps_submean {n : ℕ} {ψ F : EuclideanSpace ℂ (Fin n) → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψn : ∀ t, 0 ≤ ψ t)
    (hFm : Measurable F) {B : ℝ} (hB : ∀ z, |F z| ≤ B) {z b : EuclideanSpace ℂ (Fin n)} {r : ℝ}
    (hloc : ∀ t, ψ t ≠ 0 → F (z - t) ≤ Real.circleAverage (fun τ => F (z - t + τ • b)) 0 r) :
    ∫ t, ψ t * F (z - t) ≤ Real.circleAverage (fun τ => ∫ t, ψ t * F (z + τ • b - t)) 0 r := by
  set H : EuclideanSpace ℂ (Fin n) → ℝ → ℝ := fun t θ => F (z - t + circleMap 0 r θ • b) with hHdef
  have hH : Measurable (Function.uncurry H) :=
    hFm.comp (by
      apply Continuous.measurable
      exact (continuous_const.sub continuous_fst).add
        (((continuous_circleMap 0 r).comp continuous_snd).smul continuous_const))
  have hHB : ∀ t θ, |H t θ| ≤ B := fun _ _ => hB _
  have hswap := p0f0c_swap hψc hψs hH hHB
  have hint := p0f0c_swap_int hψc hψs hH hHB
  have hR : Real.circleAverage (fun τ => ∫ t, ψ t * F (z + τ • b - t)) 0 r =
      ∫ t, (2 * Real.pi)⁻¹ * (ψ t * ∫ θ in (0 : ℝ)..2 * Real.pi, H t θ) := by
    rw [integral_const_mul, hswap, Real.circleAverage_def, smul_eq_mul]
    congr 1
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [hHdef, add_sub_right_comm]
  rw [hR]
  refine integral_mono (p0f0c_int_mul hψc hψs hFm hB z) (hint.const_mul _) (fun t => ?_)
  by_cases h0 : ψ t = 0
  · simp [h0]
  · have := hloc t h0
    rw [Real.circleAverage_def, smul_eq_mul] at this
    calc ψ t * F (z - t) ≤ ψ t * ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, H t θ) :=
          mul_le_mul_of_nonneg_left this (hψn t)
      _ = _ := by ring

/-- The mollified function dominates the function (radial weight + rotation invariance). -/
theorem p0f0c_le_Feps {n : ℕ} {ψ F : EuclideanSpace ℂ (Fin n) → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψn : ∀ t, 0 ≤ ψ t) (hψ1 : ∫ t, ψ t = 1)
    (hψrot : ∀ (u : ℂ) t, ‖u‖ = 1 → ψ (u • t) = ψ t)
    (hFm : Measurable F) {B : ℝ} (hB : ∀ z, |F z| ≤ B) {p : EuclideanSpace ℂ (Fin n)}
    (hloc : ∀ t, ψ t ≠ 0 → F p ≤ Real.circleAverage (fun τ => F (p + τ • (-t))) 0 1) :
    F p ≤ ∫ t, ψ t * F (p - t) := by
  set H : EuclideanSpace ℂ (Fin n) → ℝ → ℝ := fun t θ => F (p + circleMap 0 1 θ • (-t))
    with hHdef
  have hH : Measurable (Function.uncurry H) :=
    hFm.comp (by
      apply Continuous.measurable
      exact continuous_const.add
        (((continuous_circleMap 0 1).comp continuous_snd).smul continuous_fst.neg))
  have hHB : ∀ t θ, |H t θ| ≤ B := fun _ _ => hB _
  have hswap := p0f0c_swap hψc hψs hH hHB
  have hint := p0f0c_swap_int hψc hψs hH hHB
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hrot : ∀ θ : ℝ, ∫ t, ψ t * F (p - t) = ∫ t, ψ t * H t θ := by
    intro θ
    have hu : ‖circleMap (0 : ℂ) 1 θ‖ = 1 := by simp [circleMap]
    rw [← p0f0c_integral_rot (circleMap 0 1 θ) hu (fun t => ψ t * F (p - t))]
    congr 1
    funext t
    simp only [hHdef]
    rw [hψrot _ _ hu, smul_neg, sub_eq_add_neg]
  have hconst : ∫ t, ψ t * F (p - t) =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ t, ψ t * H t θ := by
    rw [intervalIntegral.integral_congr (g := fun _ => ∫ t, ψ t * F (p - t))
      (fun θ _ => (hrot θ).symm), intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  rw [hconst, ← hswap, ← integral_const_mul]
  calc F p = ∫ t, ψ t * F p := by rw [integral_mul_const, hψ1, one_mul]
    _ ≤ _ := integral_mono (hψi.mul_const _) (hint.const_mul _) (fun t => by
        by_cases h0 : ψ t = 0
        · simp [h0]
        · have := hloc t h0
          rw [Real.circleAverage_def, smul_eq_mul] at this
          calc ψ t * F p ≤ ψ t * ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, H t θ) :=
                mul_le_mul_of_nonneg_left this (hψn t)
            _ = _ := by ring)

end P_c2

section P_c4
open LeblSCV.Pseudoconvex in
theorem p0f0c_coe {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → EReal} (hf : IsPlurisubharmonicOn f U) {m : ℝ}
    (hm : ∀ z, (m : EReal) ≤ f z) : ∀ z ∈ U, f z = ((f z).toReal : EReal) := fun z hz =>
  (EReal.coe_toReal (hf.2.1 z hz) (fun h => by
    have := hm z; rw [h] at this; exact absurd this (by simp))).symm

open LeblSCV.Pseudoconvex Classical in
theorem p0f0c_F_usc {n : ℕ} {U Kc : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → EReal} (hf : IsPlurisubharmonicOn f U) (hU : IsOpen U) {m : ℝ}
    (hm : ∀ z, (m : EReal) ≤ f z) (hKc : IsClosed Kc) (hKcU : Kc ⊆ U)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ∀ z, F z = if z ∈ Kc then (f z).toReal else m) :
    UpperSemicontinuous F := by
  have hcoe := p0f0c_coe hf hm
  intro x y hy
  by_cases hx : x ∈ Kc
  · rw [hF x, if_pos hx] at hy
    have hxU := hKcU hx
    have hfx : f x < (y : EReal) := by rw [hcoe x hxU]; exact EReal.coe_lt_coe_iff.mpr hy
    have h1 : ∀ᶠ z in nhds x, f z < (y : EReal) := by
      have := hf.1 x hxU (y : EReal) hfx
      rwa [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hxU)] at this
    have hmx : m < y := by
      have h2 := hm x
      rw [hcoe x hxU] at h2
      exact lt_of_le_of_lt (EReal.coe_le_coe_iff.mp h2) hy
    filter_upwards [h1] with z hz
    rw [hF z]
    split_ifs with hzK
    · rw [hcoe z (hKcU hzK)] at hz; exact EReal.coe_lt_coe_iff.mp hz
    · exact hmx
  · rw [hF x, if_neg hx] at hy
    filter_upwards [hKc.isOpen_compl.mem_nhds hx] with z hz
    rw [hF z, if_neg hz]; exact hy

open LeblSCV.Pseudoconvex Classical in
theorem p0f0c_F_bdd {n : ℕ} {U Kc : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → EReal} (hf : IsPlurisubharmonicOn f U) {m : ℝ}
    (hm : ∀ z, (m : EReal) ≤ f z) (hKc : IsCompact Kc) (hKcU : Kc ⊆ U)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ∀ z, F z = if z ∈ Kc then (f z).toReal else m) :
    ∃ B, ∀ z, |F z| ≤ B := by
  have hcoe := p0f0c_coe hf hm
  by_cases hne : Kc.Nonempty
  · obtain ⟨a, ha, hmax⟩ := (hf.1.mono hKcU).exists_isMaxOn hne hKc
    refine ⟨|(f a).toReal| + |m|, fun z => ?_⟩
    rw [hF z]
    split_ifs with hz
    · have h1 : f z ≤ f a := isMaxOn_iff.mp hmax z hz
      have h2 := hm z
      rw [hcoe z (hKcU hz), hcoe a (hKcU ha)] at h1
      rw [hcoe z (hKcU hz)] at h2
      have h1' := EReal.coe_le_coe_iff.mp h1
      have h2' := EReal.coe_le_coe_iff.mp h2
      rw [abs_le]
      constructor <;> linarith [neg_abs_le m, le_abs_self (f a).toReal, abs_nonneg (f a).toReal,
        abs_nonneg m]
    · linarith [abs_nonneg (f a).toReal]
  · refine ⟨|m|, fun z => ?_⟩
    have hz : z ∉ Kc := fun h => hne ⟨z, h⟩
    rw [hF z, if_neg hz]

open LeblSCV.Pseudoconvex Classical in
theorem p0f0c_F_submean {n : ℕ} {U Kc : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → EReal} (hf : IsPlurisubharmonicOn f U) {m : ℝ}
    (hm : ∀ z, (m : EReal) ≤ f z) (hKcU : Kc ⊆ U)
    {F : EuclideanSpace ℂ (Fin n) → ℝ} (hF : ∀ z, F z = if z ∈ Kc then (f z).toReal else m)
    {a b : EuclideanSpace ℂ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hab : ∀ τ ∈ Metric.closedBall (0 : ℂ) r, a + τ • b ∈ Kc) :
    F a ≤ Real.circleAverage (fun τ => F (a + τ • b)) 0 r := by
  have hV : Metric.closedBall (0 : ℂ) r ⊆ {ξ : ℂ | a + ξ • b ∈ U} := fun τ hτ => hKcU (hab τ hτ)
  have h := p0f0c_sub_mean (hf.2.2 a b) (fun z _ => hm _) hr hV
  simp only [zero_smul, add_zero] at h
  have ha : a ∈ Kc := by simpa using hab 0 (Metric.mem_closedBall_self hr.le)
  rw [hF a, if_pos ha]
  refine h.trans (le_of_eq (Real.circleAverage_congr_sphere fun τ hτ => ?_))
  have hτ' : τ ∈ Metric.closedBall (0 : ℂ) r := by
    rw [abs_of_pos hr] at hτ; exact Metric.sphere_subset_closedBall hτ
  show (f (a + τ • b)).toReal = F (a + τ • b)
  rw [hF, if_pos (hab τ hτ')]

open LeblSCV.Pseudoconvex Classical in
/-- COMPb: maximum principle for bounded-below psh functions along closed analytic discs. -/
theorem p0f0c_COMPb {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EReal) (hf : IsPlurisubharmonicOn f U)
    (hbdd : ∃ m : ℝ, ∀ z, (m : EReal) ≤ f z)
    (φ : ℂ → EuclideanSpace ℂ (Fin n)) (hφ : IsClosedAnalyticDisc φ)
    (hφU : φ '' Metric.closedBall (0 : ℂ) 1 ⊆ U) :
    ∀ ζ ∈ Metric.ball (0 : ℂ) 1, f (φ ζ) ≤ ⨆ η ∈ Metric.sphere (0 : ℂ) 1, f (φ η) := by
  obtain ⟨m, hm⟩ := hbdd
  intro ζ hζ
  have hcoe := p0f0c_coe hf hm
  suffices key : ∀ M' : ℝ, (⨆ η ∈ Metric.sphere (0 : ℂ) 1, f (φ η)) < (M' : EReal) →
      f (φ ζ) ≤ M' by
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    exact absurd (key q hq1) (not_le.mpr hq2)
  intro M' hM'
  have hK : IsCompact (φ '' Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn hφ.1
  obtain ⟨δ0, hδ0, hδ0U⟩ := hK.exists_cthickening_subset_open hU hφU
  have hKcc : IsCompact (Metric.cthickening δ0 (φ '' Metric.closedBall 0 1)) := hK.cthickening
  have hO : IsOpen {y | y ∈ U ∧ f y < M'} := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyU, hy⟩
    have h1 := hf.1 y hyU (M' : EReal) hy
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hyU)] at h1
    filter_upwards [h1, hU.mem_nhds hyU] with z hz hzU using ⟨hzU, hz⟩
  have hsph : φ '' Metric.sphere 0 1 ⊆ {y | y ∈ U ∧ f y < M'} := by
    rintro _ ⟨η, hη, rfl⟩
    exact ⟨hφU ⟨η, Metric.sphere_subset_closedBall hη, rfl⟩,
      lt_of_le_of_lt (le_iSup₂ (f := fun η _ => f (φ η)) η hη) hM'⟩
  have hKs : IsCompact (φ '' Metric.sphere 0 1) :=
    (isCompact_sphere 0 1).image_of_continuousOn (hφ.1.mono Metric.sphere_subset_closedBall)
  obtain ⟨ε1, hε1, hε1O⟩ := hKs.exists_thickening_subset_open hO hsph
  have hε : 0 < min (δ0 / 2) ε1 := lt_min (by positivity) hε1
  obtain ⟨ψ, hψd, hψs, hψn, hψsupp, hψ1, hψrot⟩ := p0f0c_mollifier (n := n) hε
  have hψc := hψd.continuous
  set Kc := Metric.cthickening δ0 (φ '' Metric.closedBall 0 1) with hKcdef
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => if z ∈ Kc then (f z).toReal else m with hFdef
  have hF : ∀ z, F z = if z ∈ Kc then (f z).toReal else m := fun z => rfl
  have hFm : Measurable F := (p0f0c_F_usc hf hU hm hKcc.isClosed hδ0U hF).measurable
  obtain ⟨B, hB⟩ := p0f0c_F_bdd hf hm hKcc hδ0U hF
  set W := Metric.thickening (δ0 / 2) (φ '' Metric.closedBall 0 1) with hWdef
  have hG : ContDiff ℝ 2 (fun x => ∫ t, ψ t * F (x - t)) := p0f0c_Feps_smooth hψd hψs hFm hB
  have hgeo : ∀ z ∈ W, ∀ t : EuclideanSpace ℂ (Fin n), ‖t‖ < min (δ0 / 2) ε1 → z - t ∈ Kc := by
    intro z hz t ht
    obtain ⟨k, hk, hzk⟩ := Metric.mem_thickening_iff.mp hz
    apply Metric.mem_cthickening_of_dist_le (z - t) k δ0 _ hk
    have h1 : dist (z - t) z = ‖t‖ := by rw [dist_eq_norm]; simp
    have h2 := min_le_left (δ0 / 2) ε1
    calc dist (z - t) k ≤ dist (z - t) z + dist z k := dist_triangle _ _ _
      _ ≤ δ0 := by rw [h1]; linarith
  have hsm : ∀ z ∈ W, ∀ b : EuclideanSpace ℂ (Fin n), ∀ r > (0 : ℝ),
      (∀ τ ∈ Metric.closedBall (0 : ℂ) r, z + τ • b ∈ W) →
      (fun x => ∫ t, ψ t * F (x - t)) z ≤
        Real.circleAverage (fun τ => (fun x => ∫ t, ψ t * F (x - t)) (z + τ • b)) 0 r := by
    intro z hz b r hr hline
    apply p0f0c_Feps_submean hψc hψs hψn hFm hB
    intro t ht
    apply p0f0c_F_submean hf hm hδ0U hF hr
    intro τ hτ
    have := hgeo _ (hline τ hτ) t (hψsupp t ht)
    rwa [add_sub_right_comm] at this
  have hKW : φ '' Metric.closedBall 0 1 ⊆ W := Metric.self_subset_thickening (by positivity) _
  have hM : ∀ η ∈ Metric.sphere (0 : ℂ) 1, (fun x => ∫ t, ψ t * F (x - t)) (φ η) ≤ M' := by
    intro η hη
    apply p0f0c_Feps_le hψc hψs hψn hψ1 hFm hB
    intro t ht
    have hy : φ η - t ∈ {y | y ∈ U ∧ f y < M'} := hε1O (Metric.mem_thickening_iff.mpr
      ⟨φ η, ⟨η, hη, rfl⟩, by
        rw [dist_eq_norm]; simp only [sub_sub_cancel_left, norm_neg]
        exact lt_of_lt_of_le (hψsupp t ht) (min_le_right _ _)⟩)
    rw [hF]
    split_ifs with hK'
    · have := hy.2; rw [hcoe _ hy.1] at this; exact (EReal.coe_lt_coe_iff.mp this).le
    · have h1 : (m : EReal) ≤ f (φ η) := hm _
      have h2 : f (φ η) ≤ ⨆ η ∈ Metric.sphere (0 : ℂ) 1, f (φ η) :=
        le_iSup₂ (f := fun η _ => f (φ η)) η hη
      exact EReal.coe_le_coe_iff.mp (h1.trans (h2.trans hM'.le))
  have hC3 := p0f0c_C3 hG Metric.isOpen_thickening hsm hφ.1 hφ.2.1 hKW hM ζ hζ
  have hpK : φ ζ ∈ Kc :=
    Metric.self_subset_cthickening _ ⟨ζ, Metric.ball_subset_closedBall hζ, rfl⟩
  have hle : F (φ ζ) ≤ (fun x => ∫ t, ψ t * F (x - t)) (φ ζ) := by
    apply p0f0c_le_Feps hψc hψs hψn hψ1 hψrot hFm hB
    intro t ht
    apply p0f0c_F_submean hf hm hδ0U hF one_pos
    intro τ hτ
    have hτ1 : ‖τ‖ ≤ 1 := by simpa using hτ
    have h1 : ‖τ • t‖ < min (δ0 / 2) ε1 := by
      rw [norm_smul]
      have := hψsupp t ht
      nlinarith [norm_nonneg t, norm_nonneg τ]
    have := hgeo (φ ζ) (hKW ⟨ζ, Metric.ball_subset_closedBall hζ, rfl⟩) (τ • t) h1
    rwa [smul_neg, ← sub_eq_add_neg]
  have hFζ : F (φ ζ) = (f (φ ζ)).toReal := by rw [hF, if_pos hpK]
  rw [hcoe _ (hδ0U hpK)]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

end P_c4

open LeblSCV.Pseudoconvex in
theorem solution {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUo : IsOpen U) (hUc : IsConnected U) (hne : U ≠ Set.univ) :
    List.TFAE
      [IsPlurisubharmonicOn (fun z => ((-Real.log (Metric.infDist z (frontier U)) : ℝ) : EReal)) U,
       IsHartogsPseudoconvex U,
       IsConvexWrt U {f | IsPlurisubharmonicOn f U},
       SatisfiesContinuityPrinciple U] := by
  exact hartogs_tfae_reduction U hUo hUc hne (p0f0c_hartogs_of_neg_log_dist_psh U hUo hUc hne)
    (ps2_convexWrt_psh_of_hartogs U)
    (fun hconv => p0f0c_ks_of_comp U hconv (p0f0c_comp_of_bdd (p0f0c_COMPb hUo)))
    (fun V _ => p0f0c_subharmonic_of_poly_test V)
    (fun hcp => p0f0c_neg_log_dist_poly_bound U hUo hUc hne hcp)
