-- Prove2me | solution 1 for NonsmoothLojasiewicz.Traj.thm4_5_finite_length
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T00:42:55.269717+00:00
-- url     : https://prove2.me/submissions/11542f0e-b7a1-4b4e-9eda-dc47147532d3

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory
import Definitions.Def_NonsmoothLojasiewicz_Traj_Subanalytic
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_NonsmoothLojasiewicz_Continuous_LojIneqAt
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit
import Theorems.Thm_NonsmoothLojasiewicz_Traj_cor4_1_iii_maximal_extension
import Theorems.Thm_NonsmoothLojasiewicz_Traj_cor4_1_i_chain_rule
import Theorems.Thm_NonsmoothLojasiewicz_Traj_trajectory_value_absolutelyContinuous
import Theorems.Thm_NonsmoothLojasiewicz_Continuous_lojasiewicz_continuous_subanalytic
import Theorems.Thm_NonsmoothLojasiewicz_Convex_theorem33_lojasiewicz_convex
import Theorems.Thm_NonsmoothLojasiewicz_Convex_eq5_subdiff_eq_convex

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace

namespace Thm45Aux

/-- Lojasiewicz integration on `[s,t]`: if `r ≥ 0` is antitone with `r' = -g²` a.e. and
`r^θ ≤ C g` a.e., then `∫⁻ g ≤ C/(1-θ) (r s^{1-θ} - r t^{1-θ})`. -/
theorem lint_bound {r g : ℝ → ℝ} {s t θ C : ℝ} (hst : s ≤ t) (hθ1 : θ < 1)
    (hC : 0 < C) (hr0 : ∀ u ∈ Icc s t, 0 ≤ r u) (hanti : AntitoneOn r (Icc s t))
    (hder : ∀ᵐ u, u ∈ Ioo s t →
      HasDerivAt r (-(g u ^ 2)) u ∧ 0 ≤ g u ∧ r u ^ θ ≤ C * g u) :
    ∫⁻ u in Ioc s t, ENNReal.ofReal (g u) ≤
      ENNReal.ofReal (C / (1 - θ) * (r s ^ (1 - θ) - r t ^ (1 - θ))) := by
  set p := 1 - θ with hp
  have hp0 : 0 < p := by linarith
  set φ : ℝ → ℝ := fun u => -(r u ^ p) with hφ
  have hmonoI : MonotoneOn φ (Icc s t) := by
    intro a ha b hb hab
    simp only [hφ, neg_le_neg_iff]
    exact Real.rpow_le_rpow (hr0 b hb) (hanti ha hb hab) hp0.le
  have hmono : MonotoneOn φ (uIcc s t) := by rw [uIcc_of_le hst]; exact hmonoI
  have hint := hmono.intervalIntegrable_deriv
  have hmem := hmono.intervalIntegral_deriv_mem_uIcc
  have h1 : φ s ≤ φ t := hmonoI (left_mem_Icc.2 hst) (right_mem_Icc.2 hst) hst
  have hle : ∫ u in s..t, deriv φ u ≤ φ t - φ s := by
    rw [uIcc_of_le (by linarith)] at hmem
    exact hmem.2
  have hnn : ∀ u ∈ Ioo s t, 0 ≤ deriv φ u := by
    intro u hu
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
    exact hmonoI.derivWithin_nonneg
  have hpt : ∀ᵐ u, u ∈ Ioo s t → ENNReal.ofReal (g u) ≤ ENNReal.ofReal (C / p * deriv φ u) := by
    filter_upwards [hder] with u hu humem
    obtain ⟨hd, hg0, hloj⟩ := hu humem
    have humem' : u ∈ Icc s t := Ioo_subset_Icc_self humem
    rcases (hr0 u humem').eq_or_lt with h0 | hpos
    · have hmin : IsLocalMin r u := by
        filter_upwards [Icc_mem_nhds humem.1 humem.2] with v hv
        rw [← h0]; exact hr0 v hv
      have hz := hmin.hasDerivAt_eq_zero hd
      have hg : g u = 0 := by nlinarith [sq_nonneg (g u)]
      rw [hg, ENNReal.ofReal_zero]; exact bot_le
    · have hdφ : HasDerivAt φ (-(-(g u ^ 2) * p * r u ^ (p - 1))) u :=
        (hd.rpow_const (p := p) (Or.inl hpos.ne')).neg
      rw [hdφ.deriv]
      apply ENNReal.ofReal_le_ofReal
      have hrp : r u ^ (p - 1) = (r u ^ θ)⁻¹ := by
        rw [hp, show 1 - θ - 1 = -θ by ring, Real.rpow_neg hpos.le]
      have hrθ : 0 < r u ^ θ := Real.rpow_pos_of_pos hpos θ
      have heq : C / p * (-(-(g u ^ 2) * p * r u ^ (p - 1))) = C * g u ^ 2 / r u ^ θ := by
        rw [hrp]; field_simp
      rw [heq, le_div_iff₀ hrθ]
      nlinarith
  have hIoo : ∫⁻ u in Ioc s t, ENNReal.ofReal (g u) = ∫⁻ u in Ioo s t, ENNReal.ofReal (g u) :=
    setLIntegral_congr Ioo_ae_eq_Ioc.symm
  have hintIoo : IntegrableOn (fun u => C / p * deriv φ u) (Ioo s t) :=
    ((hint.1).mono_set Ioo_subset_Ioc_self).const_mul _
  calc ∫⁻ u in Ioc s t, ENNReal.ofReal (g u)
      = ∫⁻ u in Ioo s t, ENNReal.ofReal (g u) := hIoo
    _ ≤ ∫⁻ u in Ioo s t, ENNReal.ofReal (C / p * deriv φ u) := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff' measurableSet_Ioo]
        exact hpt
    _ = ENNReal.ofReal (∫ u in Ioo s t, C / p * deriv φ u) := by
        rw [ofReal_integral_eq_lintegral_ofReal hintIoo]
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
        exact Eventually.of_forall (fun u hu =>
          mul_nonneg (div_nonneg hC.le hp0.le) (hnn u hu))
    _ ≤ ENNReal.ofReal (C / (1 - θ) * (r s ^ (1 - θ) - r t ^ (1 - θ))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hst]
        have : φ t - φ s = r s ^ p - r t ^ p := by simp only [hφ]; ring
        rw [← hp, ← this]
        exact mul_le_mul_of_nonneg_left hle (div_nonneg hC.le hp0.le)

/-- Trapping: a curve whose length on any stretch inside `ball a ε` is bounded by `K r(s)^p`
with `r → 0`, and which comes back near `a` at arbitrarily late times, has finite length on
`(0, ∞)` and converges to `a`. -/
theorem trap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℝ → E} {r : ℝ → ℝ} {a : E} {ε K p : ℝ} (hε : 0 < ε) (hp : 0 < p) (hK : 0 ≤ K)
    (hcont : ContinuousOn x (Ici 0)) (hr0 : ∀ t, 0 ≤ t → 0 ≤ r t)
    (hr : Tendsto r atTop (𝓝 0))
    (hloc : ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, x u ∈ Metric.ball a ε) →
      ∫⁻ u in Ioc s t, ‖deriv x u‖ₑ ≤ ENNReal.ofReal (K * r s ^ p))
    (hlen : ∀ s t, 0 ≤ s → s ≤ t → ENNReal.ofReal ‖x t - x s‖ ≤ ∫⁻ u in Ioc s t, ‖deriv x u‖ₑ)
    (hclus : ∀ N δ : ℝ, 0 < δ → ∃ t, N ≤ t ∧ ‖x t - a‖ < δ)
    (hfin0 : ∀ t, 0 ≤ t → ∫⁻ u in Ioc 0 t, ‖deriv x u‖ₑ < ⊤) :
    ∫⁻ u in Ioi 0, ‖deriv x u‖ₑ < ⊤ ∧ Tendsto x atTop (𝓝 a) := by
  have hrp : Tendsto (fun t => K * r t ^ p) atTop (𝓝 0) := by
    have := (hr.rpow_const (p := p) (Or.inr hp.le)).const_mul K
    rwa [Real.zero_rpow hp.ne', mul_zero] at this
  -- small tail bound eventually
  have hev : ∀ δ : ℝ, 0 < δ → ∃ N, 0 ≤ N ∧ ∀ t, N ≤ t → K * r t ^ p < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hrp.eventually (gt_mem_nhds hδ))
    exact ⟨max N 0, le_max_right _ _, fun t ht => hN t (le_trans (le_max_left _ _) ht)⟩
  -- the bound turns into a distance bound
  have hdist : ∀ s t, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, x u ∈ Metric.ball a ε) →
      ‖x t - x s‖ ≤ K * r s ^ p := by
    intro s t hs hst hin
    have h1 := (hlen s t hs hst).trans (hloc s t hs hst hin)
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (Real.rpow_nonneg (hr0 s hs) p))).1 h1
  obtain ⟨N0, hN0, hN0'⟩ := hev (ε / 3) (by linarith)
  obtain ⟨t0, ht0N, ht0a⟩ := hclus N0 (ε / 3) (by linarith)
  have ht0 : 0 ≤ t0 := hN0.trans ht0N
  have hsmall : K * r t0 ^ p < ε / 3 := hN0' t0 ht0N
  -- stays in the ball after t0
  have hstay : ∀ t, t0 ≤ t → ‖x t - a‖ < ε := by
    by_contra hcon
    push Not at hcon
    set S := {t | t0 ≤ t ∧ ε ≤ ‖x t - a‖} with hS
    have hSne : S.Nonempty := by
      obtain ⟨t, ht, hta⟩ := hcon; exact ⟨t, ht, hta⟩
    have hSbdd : BddBelow S := ⟨t0, fun t ht => ht.1⟩
    have hScl : IsClosed S := by
      have hc : ContinuousOn (fun t => ‖x t - a‖) (Ici t0) :=
        ((hcont.mono (Ici_subset_Ici.2 ht0)).sub continuousOn_const).norm
      have := hc.preimage_isClosed_of_isClosed isClosed_Ici
        (isClosed_le continuous_const continuous_id : IsClosed {y : ℝ | ε ≤ y})
      exact this
    set τ := sInf S with hτ
    have hτS : τ ∈ S := hScl.csInf_mem hSne hSbdd
    have hτ0 : t0 < τ := by
      rcases hτS.1.eq_or_lt with h | h
      · exfalso; have := hτS.2; rw [← h] at this; linarith
      · exact h
    have hbefore : ∀ u, t0 ≤ u → u < τ → ‖x u - a‖ < ε := by
      intro u hu1 hu2
      by_contra h; push Not at h
      exact absurd (csInf_le hSbdd ⟨hu1, h⟩) (not_le.2 hu2)
    have hbound : ∀ u ∈ Ico t0 τ, ‖x u - x t0‖ ≤ ε / 3 := by
      intro u hu
      refine (hdist t0 u ht0 hu.1 ?_).trans hsmall.le
      intro v hv
      rw [Metric.mem_ball, dist_eq_norm]
      exact hbefore v hv.1 (lt_of_le_of_lt hv.2 hu.2)
    have hcl : τ ∈ closure (Ico t0 τ) := by
      rw [closure_Ico hτ0.ne]; exact right_mem_Icc.2 hτ0.le
    have hcont' : ContinuousOn (fun u => ‖x u - x t0‖) (closure (Ico t0 τ)) := by
      rw [closure_Ico hτ0.ne]
      exact ((hcont.mono (fun u hu => le_trans ht0 hu.1)).sub continuousOn_const).norm
    have hτb : ‖x τ - x t0‖ ≤ ε / 3 :=
      le_on_closure hbound hcont' continuousOn_const hcl
    have : ‖x τ - a‖ ≤ ‖x τ - x t0‖ + ‖x t0 - a‖ := by
      calc ‖x τ - a‖ = ‖(x τ - x t0) + (x t0 - a)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith [hτS.2]
  have hin : ∀ s t, t0 ≤ s → ∀ u ∈ Icc s t, x u ∈ Metric.ball a ε := by
    intro s t hs u hu
    rw [Metric.mem_ball, dist_eq_norm]; exact hstay u (hs.trans hu.1)
  refine ⟨?_, ?_⟩
  · -- finite length
    have htail : ∫⁻ u in Ioi t0, ‖deriv x u‖ₑ ≤ ENNReal.ofReal (K * r t0 ^ p) := by
      have hU : Ioi t0 = ⋃ k : ℕ, Ioc t0 (t0 + k) := by
        ext u; simp only [mem_Ioi, mem_iUnion, mem_Ioc]
        constructor
        · intro hu
          obtain ⟨k, hk⟩ := exists_nat_ge (u - t0)
          exact ⟨k, hu, by linarith⟩
        · rintro ⟨k, hk, _⟩; exact hk
      rw [hU, setLIntegral_iUnion_of_directed _
        (Monotone.directed_le (fun i j hij => Ioc_subset_Ioc_right (by
          simp only [add_le_add_iff_left, Nat.cast_le]; exact hij)))]
      exact iSup_le (fun k => hloc t0 (t0 + k) ht0 (by simp) (hin t0 _ le_rfl))
    have hsplit : Ioi (0 : ℝ) = Ioc 0 t0 ∪ Ioi t0 := (Ioc_union_Ioi_eq_Ioi ht0).symm
    rw [hsplit]
    refine lt_of_le_of_lt (lintegral_union_le _ _ _) ?_
    exact ENNReal.add_lt_top.2 ⟨hfin0 t0 ht0, htail.trans_lt ENNReal.ofReal_lt_top⟩
  · -- convergence
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N1, hN1, hN1'⟩ := hev (δ / 2) (by linarith)
    obtain ⟨t2, ht2, ht2a⟩ := hclus (max N1 t0) (δ / 2) (by linarith)
    refine ⟨t2, fun t ht => ?_⟩
    have h2 := hdist t2 t (ht0.trans ((le_max_right _ _).trans ht2)) ht
      (hin t2 t ((le_max_right _ _).trans ht2))
    have h3 := hN1' t2 ((le_max_left _ _).trans ht2)
    rw [dist_eq_norm]
    calc ‖x t - a‖ = ‖(x t - x t2) + (x t2 - a)‖ := by congr 1; abel
      _ ≤ ‖x t - x t2‖ + ‖x t2 - a‖ := norm_add_le _ _
      _ < δ := by linarith

end Thm45Aux

namespace Thm45Aux

open NonconvexSplitting.Shared in
/-- Closedness of the limiting subdifferential along sequences with converging finite values. -/
theorem limiting_closed {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) {a w : X} {ys ws : ℕ → X} {c : ℕ → ℝ} {c0 : ℝ}
    (hfa : f a = (c0 : EReal)) (hfy : ∀ k, f (ys k) = (c k : EReal))
    (hy : Tendsto ys atTop (𝓝 a)) (hc : Tendsto c atTop (𝓝 c0))
    (hw : Tendsto ws atTop (𝓝 w)) (hmem : ∀ k, ws k ∈ LimitingSubdiff f (ys k)) :
    w ∈ LimitingSubdiff f a := by
  have hex : ∀ k : ℕ, ∃ z u : X, dist z (ys k) < 1 / ((k : ℝ) + 1) ∧
      dist u (ws k) < 1 / ((k : ℝ) + 1) ∧
      f z ∈ Ioo ((c k - 1 / ((k : ℝ) + 1) : ℝ) : EReal) ((c k + 1 / ((k : ℝ) + 1) : ℝ) : EReal) ∧
      IsRegularSubgrad f z u := by
    intro k
    obtain ⟨_, xs, vs, hxs, hfxs, hvs, hreg⟩ := hmem k
    have hδ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have e1 := (Metric.tendsto_nhds.1 hxs) _ hδ
    have e2 := (Metric.tendsto_nhds.1 hvs) _ hδ
    have e3 : ∀ᶠ j in atTop, f (xs j) ∈
        Ioo ((c k - 1 / ((k : ℝ) + 1) : ℝ) : EReal) ((c k + 1 / ((k : ℝ) + 1) : ℝ) : EReal) := by
      apply hfxs
      rw [hfy k]
      exact Ioo_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith))
        (EReal.coe_lt_coe_iff.2 (by linarith))
    obtain ⟨j, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
    exact ⟨xs j, vs j, h1, h2, h3, hreg j⟩
  choose X V hX hV hF hR using hex
  have hδ0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨by rw [hfa]; exact EReal.coe_ne_top _, X, V, ?_, ?_, ?_, hR⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    have hya := (tendsto_iff_dist_tendsto_zero.1 hy)
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) (by simpa only [add_zero] using hδ0.add hya)
    have := dist_triangle (X k) (ys k) a; have := hX k; linarith
  · have hreal : ∀ k, f (X k) = (((f (X k)).toReal : ℝ) : EReal) := by
      intro k
      have h1 := (hF k).1
      have h2 := (hF k).2
      exact (EReal.coe_toReal (ne_top_of_lt h2) (ne_bot_of_gt h1)).symm
    have hd : ∀ k, |(f (X k)).toReal - c k| < 1 / ((k : ℝ) + 1) := by
      intro k
      have h1 := (hF k).1
      have h2 := (hF k).2
      rw [hreal k] at h1 h2
      rw [EReal.coe_lt_coe_iff] at h1 h2
      rw [abs_lt]; constructor <;> linarith
    have hconv : Tendsto (fun k => (f (X k)).toReal) atTop (𝓝 c0) := by
      have h0 : Tendsto (fun k => (f (X k)).toReal - c k) atTop (𝓝 0) :=
        squeeze_zero_norm (fun k => (hd k).le) hδ0
      simpa using h0.add hc
    rw [hfa]
    exact ((continuous_coe_real_ereal.tendsto c0).comp hconv).congr (fun k => (hreal k).symm)
  · rw [tendsto_iff_dist_tendsto_zero]
    have hwa := (tendsto_iff_dist_tendsto_zero.1 hw)
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) (by simpa only [add_zero] using hδ0.add hwa)
    have := dist_triangle (V k) (ws k) w; have := hV k; linarith

open NonsmoothLojasiewicz.Traj in
/-- A finite lower-`C²` function is continuous (local max of a jointly continuous family over a
compact index space). -/
theorem lowerC2_continuous {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hl : IsLowerC2 f)
    (hfin : ∀ y, f y ≠ ⊤) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨U, hU, hx0U, S, _, _, F, DF, D2F, hF, hmax, -, -, -⟩ := hl x0 (hfin x0)
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun y => sSup (F y '' univ) with hG
  have hF' : Continuous (Function.uncurry (fun (y : U) (s : S) => F y.1 s)) := by
    have : Continuous (fun p : U × S => ((p.1 : EuclideanSpace ℝ (Fin n)), p.2)) := by fun_prop
    exact hF.comp_continuous this (fun p => ⟨p.1.2, mem_univ _⟩)
  have hGc : Continuous (fun y : U => G y) := isCompact_univ.continuous_sSup hF'
  have hGon : ContinuousOn G U := continuousOn_iff_continuous_domRestrict.2 hGc
  have heq : ∀ y ∈ U, f y = (G y : EReal) := by
    intro y hy
    obtain ⟨s, hs, hsmax⟩ := hmax y hy
    have : G y = F y s := by
      apply IsGreatest.csSup_eq
      exact ⟨⟨s, mem_univ _, rfl⟩, by rintro _ ⟨s', -, rfl⟩; exact hsmax s'⟩
    rw [hs, this]
  have hc : ContinuousAt (fun y => (G y : EReal)) x0 :=
    continuous_coe_real_ereal.continuousAt.comp (hGon.continuousAt (hU.mem_nhds hx0U))
  refine hc.congr ?_
  filter_upwards [hU.mem_nhds hx0U] with y hy
  exact (heq y hy).symm

end Thm45Aux

namespace Thm45Aux

theorem enorm_le_one_add_sq (e : ℝ≥0∞) : e ≤ 1 + e ^ 2 := by
  rcases le_total e 1 with h | h
  · exact h.trans le_self_add
  · calc e = e * 1 := (mul_one e).symm
      _ ≤ e * e := by gcongr
      _ = e ^ 2 := (sq e).symm
      _ ≤ 1 + e ^ 2 := le_add_self

theorem ac_inner {n : ℕ} {x : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ}
    (e : EuclideanSpace ℝ (Fin n)) (h : AbsolutelyContinuousOnInterval x a b) :
    AbsolutelyContinuousOnInterval (fun u => ⟪e, x u⟫_ℝ) a b := by
  unfold AbsolutelyContinuousOnInterval at h ⊢
  have h2 := h.const_mul ‖e‖
  rw [mul_zero] at h2
  refine squeeze_zero (fun E => Finset.sum_nonneg (fun i _ => dist_nonneg)) (fun E => ?_) h2
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Real.dist_eq, ← inner_sub_right, dist_eq_norm]
  exact abs_real_inner_le_norm _ _

theorem norm_sub_le_integral' {n : ℕ} {x : ℝ → EuclideanSpace ℝ (Fin n)} {t b : ℝ} (htb : t ≤ b)
    (hac : AbsolutelyContinuousOnInterval x t b)
    (hdiff : ∀ᵐ u, t < u → DifferentiableAt ℝ x u)
    (hint : IntervalIntegrable (fun u => ‖deriv x u‖) volume t b) :
    ‖x b - x t‖ ≤ ∫ u in t..b, ‖deriv x u‖ := by
  set e := x b - x t with he
  have hg := ac_inner e hac
  have hftc := hg.integral_deriv_eq_sub
  have hee : ⟪e, x b⟫_ℝ - ⟪e, x t⟫_ℝ = ‖e‖ ^ 2 := by
    rw [← inner_sub_right, ← he, real_inner_self_eq_norm_sq]
  rw [hee] at hftc
  have hint2 : IntervalIntegrable (fun u => ‖e‖ * ‖deriv x u‖) volume t b := hint.const_mul _
  have hmono : ∫ u in t..b, deriv (fun u => ⟪e, x u⟫_ℝ) u ≤ ∫ u in t..b, ‖e‖ * ‖deriv x u‖ := by
    apply intervalIntegral.integral_mono_ae_restrict htb hg.intervalIntegrable_deriv hint2
    rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hdiff] with u hu hmem
    have hd := hu hmem.1
    have hD : HasDerivAt (fun u => ⟪e, x u⟫_ℝ) ⟪e, deriv x u⟫_ℝ u := by
      exact ((innerSL ℝ e).hasFDerivAt).comp_hasDerivAt u hd.hasDerivAt
    rw [hD.deriv]
    exact real_inner_le_norm _ _
  rw [hftc, intervalIntegral.integral_const_mul] at hmono
  have hI : 0 ≤ ∫ u in t..b, ‖deriv x u‖ :=
    intervalIntegral.integral_nonneg htb (fun u _ => norm_nonneg _)
  rcases (norm_nonneg e).eq_or_lt with h0 | hpos
  · rw [← h0]; exact hI
  · have : ‖e‖ * ‖e‖ ≤ ‖e‖ * ∫ u in t..b, ‖deriv x u‖ := by nlinarith
    exact le_of_mul_le_mul_left this hpos

open NonsmoothLojasiewicz.Traj in
theorem stage1 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EReal}
    {x : ℝ → EuclideanSpace ℝ (Fin n)} {T : ℝ≥0∞}
    (hx : IsMaximalTrajectory f x T)
    (hext : ∃ xhat : ℝ → EuclideanSpace ℝ (Fin n), (∀ t ∈ timeDom T, xhat t = x t) ∧
      IsMaximalTrajectory f xhat ⊤ ∧ ∫⁻ t in Ioi (0 : ℝ), ‖deriv xhat t‖ₑ ^ 2 < ⊤) :
    T = ⊤ ∧ ∫⁻ t in Ioi (0 : ℝ), ‖deriv x t‖ₑ ^ 2 < ⊤ := by
  obtain ⟨xhat, hagree, hmax, hL2⟩ := hext
  have hT : T = ⊤ := by
    by_contra hT
    exact hx.2 ⟨⊤, lt_top_iff_ne_top.2 hT, xhat, hagree, hmax.1⟩
  subst hT
  refine ⟨rfl, ?_⟩
  have hderiv_eq : ∀ u ∈ Ioi (0 : ℝ), ‖deriv xhat u‖ₑ ^ 2 = ‖deriv x u‖ₑ ^ 2 := by
    intro u hu
    have : deriv xhat u = deriv x u := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact hagree v ⟨le_of_lt hv, ENNReal.ofReal_lt_top⟩
    rw [this]
  rwa [setLIntegral_congr_fun measurableSet_Ioi hderiv_eq] at hL2

open NonsmoothLojasiewicz.Traj NonconvexSplitting.Shared MoreauProx.Characterization in
theorem core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : IsTrajectory f x ⊤)
    (hbdd : Bornology.IsBounded (x '' timeDom ⊤))
    (hL2 : ∫⁻ t in Ioi (0 : ℝ), ‖deriv x t‖ₑ ^ 2 < ⊤)
    (hchain : ∀ᵐ t : ℝ, 0 < t → ENNReal.ofReal t < ⊤ →
      HasDerivAt x (deriv x t) t ∧
      ∀ v ∈ LimitingSubdiff f (x t),
        HasDerivAt (fun s => (f (x s)).toReal) ⟪deriv x t, v⟫_ℝ t)
    (hACh : ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b < ⊤ →
      AbsolutelyContinuousOnInterval (fun t => (f (x t)).toReal) 0 b)
    (hLojC : (∀ y, f y ≠ ⊥) → IsClosed {y | f y ≠ ⊤} → ContinuousOn f {y | f y ≠ ⊤} →
      ∀ a ∈ NonsmoothLojasiewicz.Continuous.crit f,
        ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ NonsmoothLojasiewicz.Continuous.LojIneqAt f a θ)
    (hLojV : GammaZero f → (NonsmoothLojasiewicz.Convex.crit f).Nonempty →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded K →
        ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∃ C : ℝ, ∀ y ∈ K, ∀ v ∈ LimitingSubdiff f y,
          |(f y).toReal - (⨅ y, f y).toReal| ^ θ ≤ C * ‖v‖)
    (hEq5 : GammaZero f → ∀ y, LimitingSubdiff f y = {v | IsRegularSubgrad f y v} ∧
      {v | IsRegularSubgrad f y v} = subgrad f y) :
    ∫⁻ t in Ioi (0 : ℝ), ‖deriv x t‖ₑ < ⊤ ∧
      ∃ a ∈ NonsmoothLojasiewicz.Continuous.crit f, Tendsto x atTop (𝓝 a) := by
  obtain ⟨-, hAC, hae, hne⟩ := hx
  obtain ⟨⟨y0, hy0⟩, m, hm⟩ := hH2
  set h : ℝ → ℝ := fun u => (f (x u)).toReal with hh
  have hbot : ∀ y, f y ≠ ⊥ := fun y => ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hm y)
  have hfin : ∀ u, 0 ≤ u → f (x u) = (h u : EReal) := by
    intro u hu
    obtain ⟨v, hv⟩ := hne u hu ENNReal.ofReal_lt_top
    exact (EReal.coe_toReal hv.1 (hbot _)).symm
  have hmh : ∀ u, 0 ≤ u → m ≤ h u := by
    intro u hu
    have := hm (x u)
    rw [hfin u hu] at this
    exact EReal.coe_le_coe_iff.1 this
  have hgood : ∀ᵐ u, 0 < u → HasDerivAt x (deriv x u) u ∧
      -deriv x u ∈ LimitingSubdiff f (x u) ∧ HasDerivAt h (-(‖deriv x u‖ ^ 2)) u := by
    filter_upwards [hae, hchain] with u h1 h2 hu
    obtain ⟨v, hv, hvs⟩ := h1 hu ENNReal.ofReal_lt_top
    obtain ⟨hd, hcr⟩ := h2 hu ENNReal.ofReal_lt_top
    have hvd : v = deriv x u := hv.deriv.symm
    subst hvd
    refine ⟨hd, hvs, ?_⟩
    have := hcr _ hvs
    rwa [inner_neg_right, real_inner_self_eq_norm_sq] at this
  have hanti : ∀ s t, 0 ≤ s → s ≤ t → h t ≤ h s := by
    intro s t hs hst
    have hac : AbsolutelyContinuousOnInterval h s t :=
      (hACh t (hs.trans hst) ENNReal.ofReal_lt_top).mono (by
        rw [uIcc_of_le hst, uIcc_of_le (hs.trans hst)]; exact Icc_subset_Icc_left hs)
    have hftc := hac.integral_deriv_eq_sub
    have hnn : 0 ≤ ∫ u in s..t, -deriv h u := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hst
      rw [Filter.EventuallyLE, ← restrict_Ioo_eq_restrict_Icc, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hgood] with u hu hmem
      rw [(hu (lt_of_le_of_lt hs hmem.1)).2.2.deriv]
      simp only [Pi.zero_apply, neg_neg]
      positivity
    rw [intervalIntegral.integral_neg, hftc] at hnn
    linarith
  set h' : ℝ → ℝ := fun u => h (max u 0) with hh'
  have h'anti : Antitone h' := fun u v huv =>
    hanti _ _ (le_max_right _ _) (max_le_max huv le_rfl)
  have h'bdd : BddBelow (range h') := ⟨m, by rintro _ ⟨u, rfl⟩; exact hmh _ (le_max_right _ _)⟩
  set β := ⨅ u, h' u with hβ
  have hlim : Tendsto h atTop (𝓝 β) := by
    refine (tendsto_atTop_ciInf h'anti h'bdd).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with u hu
    simp only [hh', max_eq_left hu]
  have hβle : ∀ u, 0 ≤ u → β ≤ h u := by
    intro u hu
    have := ciInf_le h'bdd u
    simp only [hh', max_eq_left hu] at this
    exact this
  have hsmall : ∀ N : ℕ, ∃ s : ℝ, (N : ℝ) < s ∧ -deriv x s ∈ LimitingSubdiff f (x s) ∧
      ‖deriv x s‖ < 1 / ((N : ℝ) + 1) := by
    intro N
    by_contra hcon
    push Not at hcon
    have hae2 : ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ENNReal.ofReal (1 / ((N : ℝ) + 1)) ^ 2 ≤ ‖deriv x u‖ₑ ^ 2 := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards [hgood] with u hu hmem
      have hpos : 0 < u := lt_of_le_of_lt (Nat.cast_nonneg N) hmem
      have h1 := hcon u hmem (hu hpos).2.1
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal h1
    have htop : ∫⁻ u in Ioi (N : ℝ), ‖deriv x u‖ₑ ^ 2 = ⊤ := by
      apply eq_top_iff.2
      calc (⊤ : ℝ≥0∞) = ∫⁻ u in Ioi (N : ℝ), ENNReal.ofReal (1 / ((N : ℝ) + 1)) ^ 2 := by
            rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top]
            apply pow_ne_zero
            rw [Ne, ENNReal.ofReal_eq_zero, not_le]
            positivity
        _ ≤ _ := lintegral_mono_ae hae2
    have hsub : ∫⁻ u in Ioi (N : ℝ), ‖deriv x u‖ₑ ^ 2 ≤ ∫⁻ u in Ioi (0 : ℝ), ‖deriv x u‖ₑ ^ 2 :=
      lintegral_mono_set (Ioi_subset_Ioi (Nat.cast_nonneg N))
    rw [htop, top_le_iff] at hsub
    rw [hsub] at hL2
    exact lt_irrefl _ hL2
  choose s hsN hsm hsv using hsmall
  have hsin : ∀ k, x (s k) ∈ x '' timeDom ⊤ := fun k =>
    ⟨s k, ⟨le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg k) (hsN k)), ENNReal.ofReal_lt_top⟩, rfl⟩
  obtain ⟨a, -, φ, hφ, hxa⟩ := tendsto_subseq_of_bounded hbdd hsin
  have hφk : ∀ k : ℕ, (k : ℝ) ≤ s (φ k) := fun k =>
    le_trans (Nat.cast_le.2 (hφ.id_le k)) (hsN (φ k)).le
  have hsφ : Tendsto (fun k => s (φ k)) atTop atTop :=
    tendsto_atTop_mono hφk tendsto_natCast_atTop_atTop
  have hs0 : ∀ k : ℕ, 0 ≤ s (φ k) := fun k => (Nat.cast_nonneg k).trans (hφk k)
  have hhs : Tendsto (fun k => h (s (φ k))) atTop (𝓝 β) := hlim.comp hsφ
  have hws : Tendsto (fun k => -deriv x (s (φ k))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_neg]
    refine (hsv (φ k)).le.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have := hφ.id_le k
    have : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast this
    linarith
  have hxa' : Tendsto (fun k => x (s (φ k))) atTop (𝓝 a) := hxa
  have hfs : Tendsto (fun k => f (x (s (φ k)))) atTop (𝓝 (β : EReal)) := by
    refine ((continuous_coe_real_ereal.tendsto β).comp hhs).congr (fun k => ?_)
    simp only [Function.comp]
    exact (hfin _ (hs0 k)).symm
  have hpkg : f a = (β : EReal) ∧ a ∈ NonsmoothLojasiewicz.Continuous.crit f ∧
      ∃ θ C ε : ℝ, 0 ≤ θ ∧ θ < 1 ∧ 0 < C ∧ 0 < ε ∧
        ∀ y ∈ Metric.ball a ε, ∀ v ∈ LimitingSubdiff f y, |(f y).toReal - β| ^ θ ≤ C * ‖v‖ := by
    rcases hH1 with ⟨hlsc, hconv⟩ | ⟨hlc2, hfinf⟩
    · have hG : GammaZero f := ⟨hbot, ⟨y0, hy0⟩, hconv, hlsc⟩
      have hge : ∀ z, (β : EReal) ≤ f z := by
        intro z
        have hsg : ∀ k, ((h (s (φ k)) + ⟪z - x (s (φ k)), -deriv x (s (φ k))⟫_ℝ : ℝ) : EReal)
            ≤ f z := by
          intro k
          have hmem := hsm (φ k)
          rw [(hEq5 hG _).1, (hEq5 hG _).2] at hmem
          have := hmem.2.2 z
          rwa [hfin _ (hs0 k), ← EReal.coe_add] at this
        have hconvk : Tendsto (fun k => h (s (φ k)) + ⟪z - x (s (φ k)), -deriv x (s (φ k))⟫_ℝ)
            atTop (𝓝 β) := by
          have h1 : Tendsto (fun k => ⟪z - x (s (φ k)), -deriv x (s (φ k))⟫_ℝ) atTop
              (𝓝 ⟪z - a, (0 : EuclideanSpace ℝ (Fin n))⟫_ℝ) :=
            (tendsto_const_nhds.sub hxa').inner hws
          rw [inner_zero_right] at h1
          simpa using hhs.add h1
        exact le_of_tendsto' ((continuous_coe_real_ereal.tendsto β).comp hconvk) hsg
      have hle : f a ≤ (β : EReal) := by
        by_contra hlt
        push Not at hlt
        obtain ⟨y', hy1, hy2⟩ := exists_between hlt
        have e1 := hlsc a y' hy2
        have e2 : ∀ᶠ k in atTop, f (x (s (φ k))) < y' := hfs.eventually (gt_mem_nhds hy1)
        obtain ⟨k, hk1, hk2⟩ := ((hxa'.eventually e1).and e2).exists
        exact lt_asymm hk1 hk2
      have hfa : f a = (β : EReal) := le_antisymm hle (hge a)
      have hcrit : a ∈ NonsmoothLojasiewicz.Continuous.crit f := by
        have hreg : IsRegularSubgrad f a 0 := by
          refine ⟨by rw [hfa]; exact EReal.coe_ne_top _, fun ε hε => Eventually.of_forall (fun z => ?_)⟩
          rw [inner_zero_left, zero_sub, hfa]
          calc (β : EReal) + ((-(ε * ‖z - a‖) : ℝ) : EReal) ≤ (β : EReal) := by
                rw [← EReal.coe_add]
                exact EReal.coe_le_coe_iff.2 (by nlinarith [norm_nonneg (z - a)])
            _ ≤ f z := hge z
        exact ⟨hreg.1, fun _ => a, fun _ => 0, tendsto_const_nhds, tendsto_const_nhds,
          tendsto_const_nhds, fun _ => hreg⟩
      obtain ⟨θ, hθ0, hθ1, C, hC⟩ := hLojV hG ⟨a, hcrit⟩ (Metric.ball a 1) Metric.isBounded_ball
      have hinf : (⨅ y, f y) = (β : EReal) :=
        le_antisymm (hfa ▸ iInf_le f a) (le_iInf hge)
      refine ⟨hfa, hcrit, θ, max C 1, 1, hθ0, hθ1, lt_of_lt_of_le one_pos (le_max_right _ _),
        one_pos, fun y hy v hv => ?_⟩
      have := hC y hy v hv
      rw [hinf, EReal.toReal_coe] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · have hcont : Continuous f := lowerC2_continuous f hlc2 hfinf
      have hfa : f a = (β : EReal) :=
        tendsto_nhds_unique ((hcont.tendsto a).comp hxa') hfs
      have hcrit : a ∈ NonsmoothLojasiewicz.Continuous.crit f :=
        limiting_closed f hfa (fun k => hfin _ (hs0 k)) hxa' hhs hws (fun k => hsm (φ k))
      have hdomc : IsClosed {y | f y ≠ ⊤} := by
        have : {y | f y ≠ ⊤} = univ := eq_univ_of_forall hfinf
        rw [this]; exact isClosed_univ
      obtain ⟨θ, hθ0, hθ1, C, U, hU, hCU⟩ := hLojC hbot hdomc hcont.continuousOn a hcrit
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
      refine ⟨hfa, hcrit, θ, max C 1, ε, hθ0, hθ1, lt_of_lt_of_le one_pos (le_max_right _ _),
        hε, fun y hy v hv => ?_⟩
      have := hCU y (hball hy) v hv
      rw [hfa, EReal.toReal_coe] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨hfa, hcrit, θ, C, ε, hθ0, hθ1, hC, hε, hloj⟩ := hpkg
  set r : ℝ → ℝ := fun u => h u - β with hr
  have hr0 : ∀ u, 0 ≤ u → 0 ≤ r u := fun u hu => sub_nonneg.2 (hβle u hu)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have := hlim.sub_const β
    rwa [sub_self] at this
  have hp : 0 < 1 - θ := by linarith
  have hcontx : ContinuousOn x (Ici 0) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    have hc := (hAC (t + 1) (by linarith) ENNReal.ofReal_lt_top).continuousOn
    rw [uIcc_of_le (by linarith)] at hc
    have := hc t ⟨ht0, by linarith⟩
    apply this.mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin]
    exact ⟨Iio (t + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
  have hloc : ∀ s1 t1, 0 ≤ s1 → s1 ≤ t1 → (∀ u ∈ Icc s1 t1, x u ∈ Metric.ball a ε) →
      ∫⁻ u in Ioc s1 t1, ‖deriv x u‖ₑ ≤ ENNReal.ofReal (C / (1 - θ) * r s1 ^ (1 - θ)) := by
    intro s1 t1 hs1 hst hin
    have hb := lint_bound (r := r) (g := fun u => ‖deriv x u‖) hst hθ1 hC
      (fun u hu => hr0 u (hs1.trans hu.1))
      (fun u hu v hv huv => by
        show h v - β ≤ h u - β
        linarith [hanti u v (hs1.trans hu.1) huv])
      (by
        filter_upwards [hgood] with u hu hmem
        have hpos : 0 < u := lt_of_le_of_lt hs1 hmem.1
        obtain ⟨-, hsub, hd⟩ := hu hpos
        refine ⟨hd.sub_const β, norm_nonneg _, ?_⟩
        have := hloj (x u) (hin u (Ioo_subset_Icc_self hmem)) _ hsub
        rw [norm_neg, hfin u hpos.le, EReal.toReal_coe,
          abs_of_nonneg (sub_nonneg.2 (hβle u hpos.le))] at this
        exact this)
    simp only [ofReal_norm] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 0 ≤ r t1 ^ (1 - θ) := Real.rpow_nonneg (hr0 t1 (hs1.trans hst)) _
    have h2 : 0 ≤ C / (1 - θ) := div_nonneg hC.le hp.le
    nlinarith
  have hlen : ∀ s1 t1, 0 ≤ s1 → s1 ≤ t1 →
      ENNReal.ofReal ‖x t1 - x s1‖ ≤ ∫⁻ u in Ioc s1 t1, ‖deriv x u‖ₑ := by
    intro s1 t1 hs1 hst
    by_cases hfinI : ∫⁻ u in Ioc s1 t1, ‖deriv x u‖ₑ = ⊤
    · rw [hfinI]; exact le_top
    have hmeas : AEStronglyMeasurable (fun u => ‖deriv x u‖) (volume.restrict (Ioc s1 t1)) :=
      (measurable_deriv x).norm.aestronglyMeasurable
    have hintg : IntegrableOn (fun u => ‖deriv x u‖) (Ioc s1 t1) := by
      refine ⟨hmeas, ?_⟩
      simp only [HasFiniteIntegral, enorm_norm]
      exact lt_top_iff_ne_top.2 hfinI
    have hac : AbsolutelyContinuousOnInterval x s1 t1 :=
      (hAC t1 (hs1.trans hst) ENNReal.ofReal_lt_top).mono (by
        rw [uIcc_of_le hst, uIcc_of_le (hs1.trans hst)]; exact Icc_subset_Icc_left hs1)
    have hII : IntervalIntegrable (fun u => ‖deriv x u‖) volume s1 t1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 hintg
    have key := norm_sub_le_integral' hst hac (by
        filter_upwards [hgood] with u hu hmem
        exact (hu (lt_of_le_of_lt hs1 hmem)).1.differentiableAt) hII
    rw [intervalIntegral.integral_of_le hst] at key
    calc ENNReal.ofReal ‖x t1 - x s1‖ ≤ ENNReal.ofReal (∫ u in Ioc s1 t1, ‖deriv x u‖) :=
          ENNReal.ofReal_le_ofReal key
      _ = ∫⁻ u in Ioc s1 t1, ‖deriv x u‖ₑ := by
          rw [ofReal_integral_eq_lintegral_ofReal hintg
            (Eventually.of_forall (fun u => norm_nonneg _))]
          simp only [ofReal_norm]
  have hclus : ∀ N δ : ℝ, 0 < δ → ∃ t, N ≤ t ∧ ‖x t - a‖ < δ := by
    intro N δ hδ
    have e1 := hsφ.eventually (eventually_ge_atTop N)
    have e2 := (Metric.tendsto_nhds.1 hxa') δ hδ
    obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
    exact ⟨s (φ k), hk1, by rwa [dist_eq_norm] at hk2⟩
  have hfin0 : ∀ t1, 0 ≤ t1 → ∫⁻ u in Ioc 0 t1, ‖deriv x u‖ₑ < ⊤ := by
    intro t1 ht1
    calc ∫⁻ u in Ioc 0 t1, ‖deriv x u‖ₑ ≤ ∫⁻ u in Ioc 0 t1, (1 + ‖deriv x u‖ₑ ^ 2) :=
          lintegral_mono (fun u => enorm_le_one_add_sq _)
      _ = volume (Ioc 0 t1) + ∫⁻ u in Ioc 0 t1, ‖deriv x u‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
      _ < ⊤ := by
          refine ENNReal.add_lt_top.2 ⟨by simp, ?_⟩
          exact lt_of_le_of_lt (lintegral_mono_set Ioc_subset_Ioi_self) hL2
  obtain ⟨hlenfin, htend⟩ := trap (K := C / (1 - θ)) (p := 1 - θ) hε hp
    (div_nonneg hC.le hp.le) hcontx hr0 hrlim hloc hlen hclus hfin0
  exact ⟨hlenfin, a, hcrit, htend⟩

end Thm45Aux

open NonsmoothLojasiewicz.Traj in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (hH3 : IsSubanalyticFn f)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsMaximalTrajectory f x T)
    (hbdd : Bornology.IsBounded (x '' timeDom T)) :
    T = ⊤ ∧ ∫⁻ t in Set.Ioi (0 : ℝ), ‖deriv x t‖ₑ < ⊤ ∧
      ∃ a ∈ NonsmoothLojasiewicz.Continuous.crit f, Tendsto x atTop (𝓝 a) := by
  obtain ⟨hT, hL2⟩ := Thm45Aux.stage1 hx (cor4_1_iii_maximal_extension f hH1 hH2 x T hx.1)
  subst hT
  have hc := Thm45Aux.core f hH1 hH2 x hx.1 hbdd hL2 (cor4_1_i_chain_rule f hH1 hH2 x ⊤ hx.1)
    (fun b hb hbT => trajectory_value_absolutelyContinuous f hH1 hH2 x ⊤ hx.1 b hb hbT)
    (fun hbot hdom hcont a ha =>
      NonsmoothLojasiewicz.Continuous.lojasiewicz_continuous_subanalytic f hbot hdom hcont hH3 a ha)
    (fun hG hcr K hK => NonsmoothLojasiewicz.Convex.theorem33_lojasiewicz_convex f hG hH3 hcr K hK)
    (fun hG y => NonsmoothLojasiewicz.Convex.eq5_subdiff_eq_convex f hG y)
  exact ⟨rfl, hc⟩
