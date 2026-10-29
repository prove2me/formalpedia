-- Prove2me | solution 1 for NonsmoothLojasiewicz.Traj.tail_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T00:54:01.414997+00:00
-- url     : https://prove2.me/submissions/d7ff5eb4-aad9-43c7-82c5-90cf4af608a5

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Traj_LowerC2
import Definitions.Def_NonsmoothLojasiewicz_Traj_Slope
import Definitions.Def_NonsmoothLojasiewicz_Traj_Trajectory
import Definitions.Def_NonsmoothLojasiewicz_Traj_Subanalytic
import Theorems.Thm_NonsmoothLojasiewicz_Traj_cor4_1_iii_maximal_extension
import Theorems.Thm_NonsmoothLojasiewicz_Traj_cor4_1_i_chain_rule
import Theorems.Thm_NonsmoothLojasiewicz_Traj_trajectory_value_absolutelyContinuous

set_option autoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace

namespace TailAux

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

open NonsmoothLojasiewicz.Traj NonconvexSplitting.Shared in
/-- The tail-length estimate for a trajectory defined on `[0, ∞)`, given the chain rule and the
absolute continuity of `t ↦ f (x t)`. -/
theorem core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hlsc : LowerSemicontinuous f)
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : IsTrajectory f x ⊤)
    (hchain : ∀ᵐ t : ℝ, 0 < t → ENNReal.ofReal t < ⊤ →
      HasDerivAt x (deriv x t) t ∧
      ∀ v ∈ LimitingSubdiff f (x t),
        HasDerivAt (fun s => (f (x s)).toReal) ⟪deriv x t, v⟫_ℝ t)
    (hACh : ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b < ⊤ →
      AbsolutelyContinuousOnInterval (fun t => (f (x t)).toReal) 0 b)
    (a : EuclideanSpace ℝ (Fin n)) (hxa : Tendsto x atTop (𝓝 a))
    (c θ ε : ℝ) (hc : 0 < c) (hθ1 : θ < 1)
    (h20 : ∀ y ∈ Metric.ball a ε, ∀ v ∈ LimitingSubdiff f y,
      |(f y).toReal - (f a).toReal| ^ θ ≤ c * ‖v‖) (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      ∫⁻ s in Ioi t, ‖deriv x s‖ₑ ≤
        ENNReal.ofReal (c / (1 - θ) * ((f (x t)).toReal - (f a).toReal) ^ (1 - θ)) := by
  obtain ⟨-, -, hae, hne⟩ := hx
  obtain ⟨-, m, hm⟩ := hH2
  set h : ℝ → ℝ := fun u => (f (x u)).toReal with hh
  have hbot : ∀ y, f y ≠ ⊥ := fun y => ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hm y)
  have hfin : ∀ u, 0 ≤ u → f (x u) = (h u : EReal) := by
    intro u hu
    obtain ⟨v, hv⟩ := hne u hu ENNReal.ofReal_lt_top
    exact (EReal.coe_toReal hv.1 (hbot _)).symm
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
  -- `f a` is below every value along the trajectory (lower semicontinuity at the limit).
  have hfa_le : ∀ u, 0 ≤ u → f a ≤ (h u : EReal) := by
    intro u hu
    by_contra hlt
    push Not at hlt
    have e1 := hlsc a (h u) hlt
    have e2 : ∀ᶠ w in atTop, (h u : EReal) < f (x w) := hxa.eventually e1
    obtain ⟨w, hw1, hw2⟩ := (e2.and (eventually_ge_atTop u)).exists
    rw [hfin w (hu.trans hw2), EReal.coe_lt_coe_iff] at hw1
    linarith [hanti u w hu hw2]
  have hfa_top : f a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hfa_le 0 le_rfl)
  set fa : ℝ := (f a).toReal with hfadef
  have hfa_eq : f a = (fa : EReal) := (EReal.coe_toReal hfa_top (hbot a)).symm
  have hfa_le' : ∀ u, 0 ≤ u → fa ≤ h u := by
    intro u hu
    have := hfa_le u hu
    rwa [hfa_eq, EReal.coe_le_coe_iff] at this
  set r : ℝ → ℝ := fun u => h u - fa with hr
  have hr0 : ∀ u, 0 ≤ u → 0 ≤ r u := fun u hu => sub_nonneg.2 (hfa_le' u hu)
  have hp : 0 < 1 - θ := by linarith
  obtain ⟨T1, hT1⟩ := eventually_atTop.1 (hxa.eventually (Metric.ball_mem_nhds a hε))
  refine ⟨max 0 T1, le_max_left _ _, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have htT : T1 ≤ t := (le_max_right _ _).trans ht
  have hloc : ∀ k : ℕ, ∫⁻ u in Ioc t (t + k), ‖deriv x u‖ₑ ≤
      ENNReal.ofReal (c / (1 - θ) * r t ^ (1 - θ)) := by
    intro k
    have hst : t ≤ t + k := by simp
    have hb := lint_bound (r := r) (g := fun u => ‖deriv x u‖) hst hθ1 hc
      (fun u hu => hr0 u (ht0.trans hu.1))
      (fun u hu v hv huv => by
        show h v - fa ≤ h u - fa
        linarith [hanti u v (ht0.trans hu.1) huv])
      (by
        filter_upwards [hgood] with u hu hmem
        have hpos : 0 < u := lt_of_le_of_lt ht0 hmem.1
        obtain ⟨-, hsub, hd⟩ := hu hpos
        refine ⟨hd.sub_const fa, norm_nonneg _, ?_⟩
        have := h20 (x u) (hT1 u (htT.trans hmem.1.le)) _ hsub
        have hr' : |(f (x u)).toReal - fa| = r u := abs_of_nonneg (hr0 u hpos.le)
        rw [norm_neg, hr'] at this
        exact this)
    simp only [ofReal_norm] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 0 ≤ r (t + k) ^ (1 - θ) := Real.rpow_nonneg (hr0 _ (ht0.trans hst)) _
    have h2 : 0 ≤ c / (1 - θ) := div_nonneg hc.le hp.le
    nlinarith
  have hU : Ioi t = ⋃ k : ℕ, Ioc t (t + k) := by
    ext u; simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro hu
      obtain ⟨k, hk⟩ := exists_nat_ge (u - t)
      exact ⟨k, hu, by linarith⟩
    · rintro ⟨k, hk, _⟩; exact hk
  rw [hU, setLIntegral_iUnion_of_directed _
    (Monotone.directed_le (fun i j hij => Ioc_subset_Ioc_right (by
      simp only [add_le_add_iff_left, Nat.cast_le]; exact hij)))]
  exact iSup_le hloc

end TailAux

open NonsmoothLojasiewicz.Traj NonconvexSplitting.Shared in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hH1 : (LowerSemicontinuous f ∧ MoreauProx.Characterization.EConvex f) ∨
      (IsLowerC2 f ∧ ∀ y, f y ≠ ⊤))
    (hH2 : (∃ y, f y ≠ ⊤) ∧ ∃ m : ℝ, ∀ y, (m : EReal) ≤ f y)
    (hH3 : IsSubanalyticFn f)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ≥0∞) (hx : IsMaximalTrajectory f x T)
    (a : EuclideanSpace ℝ (Fin n)) (hxa : Tendsto x atTop (𝓝 a))
    (c θ ε : ℝ) (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (h20 : ∀ y ∈ Metric.ball a ε, ∀ v ∈ LimitingSubdiff f y,
      |(f y).toReal - (f a).toReal| ^ θ ≤ c * ‖v‖) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      ∫⁻ s in Set.Ioi t, ‖deriv x s‖ₑ ≤
        ENNReal.ofReal (c / (1 - θ) * ((f (x t)).toReal - (f a).toReal) ^ (1 - θ)) := by
  obtain ⟨hT, -⟩ := TailAux.stage1 hx (cor4_1_iii_maximal_extension f hH1 hH2 x T hx.1)
  subst hT
  have hlsc : LowerSemicontinuous f := by
    rcases hH1 with ⟨hl, -⟩ | ⟨hlc2, hfinf⟩
    · exact hl
    · exact (TailAux.lowerC2_continuous f hlc2 hfinf).lowerSemicontinuous
  exact TailAux.core f hlsc hH2 x hx.1 (cor4_1_i_chain_rule f hH1 hH2 x ⊤ hx.1)
    (fun b hb hbT => trajectory_value_absolutelyContinuous f hH1 hH2 x ⊤ hx.1 b hb hbT)
    a hxa c θ ε hc hθ1 h20 hε
