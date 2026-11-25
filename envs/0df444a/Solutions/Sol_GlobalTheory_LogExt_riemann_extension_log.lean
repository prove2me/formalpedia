-- Prove2me | solution 1 for GlobalTheory.LogExt.riemann_extension_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:16.245078+00:00
-- url     : https://prove2.me/submissions/4ac97296-0f8e-4754-8e1f-37a578124140

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionOfLogGrowth
import Theorems.Thm_GlobalTheory_differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace GlobalTheory.LogExt
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
open Filter Topology Asymptotics Metric Set Complex in
open scoped Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] in
private theorem exists_differentiableOn_of_locally_extends {U S : Set V} (hU : IsOpen U) (hS : S ⊆ U)
    (hd : U ⊆ closure S) (u : V → ℂ)
    (hloc : ∀ b₀ ∈ U, ∃ N ∈ 𝓝 b₀, ∃ G : V → ℂ, DifferentiableOn ℂ G N ∧ EqOn G u (N ∩ S)) :
    ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ EqOn u' u S := by
  have key : ∀ b ∈ U, ∀ N ∈ 𝓝 b, ∀ G : V → ℂ, DifferentiableOn ℂ G N → EqOn G u (N ∩ S) →
      limUnder (𝓝[S] b) u = G b := by
    intro b hbU N hN G hG hGu
    haveI : (𝓝[S] b).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hd hbU)
    apply Tendsto.limUnder_eq
    have hc : ContinuousAt G b := (hG.differentiableAt hN).continuousAt
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with x hxN hxS
    exact hGu ⟨hxN, hxS⟩
  refine ⟨fun b => limUnder (𝓝[S] b) u, ?_, ?_⟩
  · intro b₀ hb₀
    obtain ⟨N, hN, G, hG, hGu⟩ := hloc b₀ hb₀
    have h : (fun b => limUnder (𝓝[S] b) u) =ᶠ[𝓝 b₀] G := by
      filter_upwards [hU.mem_nhds hb₀, eventually_mem_nhds_iff.mpr hN] with b hbU hbN
      exact key b hbU N hbN G hG hGu
    exact ((hG.differentiableAt hN).congr_of_eventuallyEq h).differentiableWithinAt
  · intro b hb
    obtain ⟨N, hN, G, hG, hGu⟩ := hloc b (hS hb)
    show limUnder (𝓝[S] b) u = u b
    rw [key b (hS hb) N hN G hG hGu]
    exact hGu ⟨mem_of_mem_nhds hN, hb⟩
open Filter Topology Asymptotics Metric Set Complex in
open scoped Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] in
private theorem isLittleO_sub_inv_sub_of_log_bound {ψ h : ℂ → ℂ} {s₀ : ℂ} (hψ : AnalyticAt ℂ ψ s₀)
    (hz : ψ s₀ = 0) (hne : ∀ᶠ s in 𝓝[≠] s₀, ψ s ≠ 0) {C : ℝ} {k : ℕ}
    (hb : ∀ᶠ s in 𝓝 s₀, ψ s ≠ 0 → ‖h s‖ ≤ C * (1 + |Real.log ‖ψ s‖|) ^ k) :
    (fun s => h s - h s₀) =o[𝓝[≠] s₀] fun s => (s - s₀)⁻¹ := by
  have hnz : ¬ ∀ᶠ z in 𝓝 s₀, ψ z = 0 := by
    intro h0
    have h0' : ∀ᶠ z in 𝓝[≠] s₀, ψ z = 0 := nhdsWithin_le_nhds h0
    obtain ⟨s, hs1, hs2⟩ := (h0'.and hne).exists
    exact hs2 hs1
  obtain ⟨n, g, hg, hg0, hfg⟩ := hψ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  set A := |Real.log ‖g s₀‖| + 1 with hA
  have hA0 : 0 ≤ A := by positivity
  have hglog : ∀ᶠ s in 𝓝 s₀, |Real.log ‖g s‖| ≤ A :=
    ((hg.continuousAt.norm.log (norm_ne_zero_iff.mpr hg0)).abs).eventually
      (ge_mem_nhds (lt_add_one _))
  have hdist : Tendsto (fun s => ‖s - s₀‖) (𝓝 s₀) (𝓝 0) := by
    simpa using ((continuous_id.sub continuous_const).norm.tendsto s₀ : Tendsto
      (fun s : ℂ => ‖s - s₀‖) (𝓝 s₀) (𝓝 ‖s₀ - s₀‖))
  have hsmall : ∀ᶠ s in 𝓝 s₀, ‖s - s₀‖ < Real.exp (-1) :=
    hdist.eventually (gt_mem_nhds (Real.exp_pos _))
  have hbound : ∀ᶠ s in 𝓝[≠] s₀, ‖h s * (s - s₀)‖ ≤
      |C| * (1 + A + n) ^ k * (|Real.log ‖s - s₀‖| ^ k * ‖s - s₀‖) := by
    filter_upwards [nhdsWithin_le_nhds (hb.and (hfg.and (hglog.and hsmall))), hne,
      self_mem_nhdsWithin] with s ⟨hbs, hfs, hgs, hxs⟩ hψs hss
    have hx : 0 < ‖s - s₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hss)
    have hgs0 : g s ≠ 0 := by
      intro h0
      apply hψs
      rw [hfs, h0, smul_zero]
    have hlogx : 1 ≤ |Real.log ‖s - s₀‖| := by
      have : Real.log ‖s - s₀‖ < -1 := (Real.log_lt_iff_lt_exp hx).mpr hxs
      rw [abs_of_neg (by linarith)]
      linarith
    have hlogψ : |Real.log ‖ψ s‖| ≤ n * |Real.log ‖s - s₀‖| + A := by
      rw [hfs, norm_smul, norm_pow, Real.log_mul (pow_ne_zero _ hx.ne')
        (norm_ne_zero_iff.mpr hgs0), Real.log_pow]
      calc |n * Real.log ‖s - s₀‖ + Real.log ‖g s‖|
          ≤ |n * Real.log ‖s - s₀‖| + |Real.log ‖g s‖| := abs_add_le _ _
        _ ≤ n * |Real.log ‖s - s₀‖| + A := by
          rw [abs_mul, Nat.abs_cast]
          linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 1 + |Real.log ‖ψ s‖| ≤ (1 + A + n) * |Real.log ‖s - s₀‖| := by nlinarith
    have h2 : ‖h s‖ ≤ |C| * ((1 + A + n) * |Real.log ‖s - s₀‖|) ^ k := by
      calc ‖h s‖ ≤ C * (1 + |Real.log ‖ψ s‖|) ^ k := hbs hψs
        _ ≤ |C| * (1 + |Real.log ‖ψ s‖|) ^ k :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * ((1 + A + n) * |Real.log ‖s - s₀‖|) ^ k := by gcongr
    rw [norm_mul]
    calc ‖h s‖ * ‖s - s₀‖
        ≤ |C| * ((1 + A + n) * |Real.log ‖s - s₀‖|) ^ k * ‖s - s₀‖ := by gcongr
      _ = |C| * (1 + A + n) ^ k * (|Real.log ‖s - s₀‖| ^ k * ‖s - s₀‖) := by
        rw [mul_pow]
        ring
  have hreal : Tendsto (fun x : ℝ => |Real.log x| ^ k * x) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (Real.isLittleO_pow_log_id_atTop (n := k)).tendsto_div_nhds_zero
    have h2 := (h1.comp tendsto_inv_nhdsGT_zero).norm
    rw [norm_zero] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    simp [Real.log_inv, abs_pow, abs_of_pos hx0, div_inv_eq_mul]
  have hx : Tendsto (fun s => ‖s - s₀‖) (𝓝[≠] s₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hdist.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs using norm_pos_iff.mpr (sub_ne_zero.mpr hs)
  have hlim : Tendsto (fun s => |C| * (1 + A + n) ^ k * (|Real.log ‖s - s₀‖| ^ k * ‖s - s₀‖))
      (𝓝[≠] s₀) (𝓝 0) := by
    simpa using (hreal.comp hx).const_mul (|C| * (1 + A + n) ^ k)
  have hmain : Tendsto (fun s => h s * (s - s₀)) (𝓝[≠] s₀) (𝓝 0) := squeeze_zero_norm' hbound hlim
  have hlin : Tendsto (fun s => h s₀ * (s - s₀)) (𝓝[≠] s₀) (𝓝 0) := by
    have : Tendsto (fun s => h s₀ * (s - s₀)) (𝓝 s₀) (𝓝 (h s₀ * (s₀ - s₀))) :=
      (continuous_const.mul (continuous_id.sub continuous_const)).tendsto s₀
    simpa using this.mono_left nhdsWithin_le_nhds
  rw [isLittleO_iff_tendsto']
  · have := hmain.sub hlin
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun s => ?_)
    simp [div_inv_eq_mul, sub_mul]
  · filter_upwards [self_mem_nhdsWithin] with s hs h0
    exact absurd h0 (inv_ne_zero (sub_ne_zero.mpr hs))
open Filter Topology Asymptotics Metric Set Complex in
open scoped Real in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] in
private theorem exists_differentiableOn_ball_of_log_bound {ψ h : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hψ : DifferentiableOn ℂ ψ (ball 0 ρ)) (h0 : ψ 0 ≠ 0)
    (hh : DifferentiableOn ℂ h {s ∈ ball (0 : ℂ) ρ | ψ s ≠ 0})
    (hb : ∀ s₀ ∈ ball (0 : ℂ) ρ, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ s in 𝓝 s₀, ψ s ≠ 0 → ‖h s‖ ≤ C * (1 + |Real.log ‖ψ s‖|) ^ k) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 ρ) ∧ EqOn H h {s ∈ ball (0 : ℂ) ρ | ψ s ≠ 0} := by
  have han : AnalyticOnNhd ℂ ψ (ball 0 ρ) := hψ.analyticOnNhd isOpen_ball
  have hiso : ∀ s₀ ∈ ball (0 : ℂ) ρ, ∀ᶠ s in 𝓝[≠] s₀, ψ s ≠ 0 := by
    intro s₀ hs₀
    rcases (han s₀ hs₀).eventually_eq_zero_or_eventually_ne_zero with hz | hz
    · exfalso
      have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 ρ).isPreconnected
        hs₀ hz (mem_ball_self hρ)
      exact h0 (by simpa using this)
    · exact hz
  refine exists_differentiableOn_of_locally_extends isOpen_ball (fun s hs => hs.1) ?_ h ?_
  · intro s₀ hs₀
    rw [mem_closure_iff_frequently]
    have hev : ∀ᶠ s in 𝓝[≠] s₀, s ∈ {s ∈ ball (0 : ℂ) ρ | ψ s ≠ 0} :=
      ((hiso s₀ hs₀).and (nhdsWithin_le_nhds (isOpen_ball.mem_nhds hs₀))).mono
        fun s hs => ⟨hs.2, hs.1⟩
    exact hev.frequently.filter_mono nhdsWithin_le_nhds
  · intro s₀ hs₀
    by_cases hz : ψ s₀ ≠ 0
    · exact ⟨_, (hψ.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).mem_nhds
        ⟨hs₀, hz⟩, h, hh, fun x _ => rfl⟩
    push_neg at hz
    obtain ⟨C, k, hCk⟩ := hb s₀ hs₀
    have hN : {s | s ∈ ball (0 : ℂ) ρ ∧ (s ≠ s₀ → ψ s ≠ 0)} ∈ 𝓝 s₀ := by
      have := eventually_nhdsWithin_iff.mp (hiso s₀ hs₀)
      filter_upwards [this, isOpen_ball.mem_nhds hs₀] with s h1 h2 using ⟨h2, h1⟩
    refine ⟨_, hN, Function.update h s₀ (limUnder (𝓝[≠] s₀) h), ?_, ?_⟩
    · apply differentiableOn_update_limUnder_of_isLittleO hN
      · exact hh.mono fun s hs => ⟨hs.1.1, hs.1.2 hs.2⟩
      · exact isLittleO_sub_inv_sub_of_log_bound (han s₀ hs₀) hz (hiso s₀ hs₀) hCk
    · intro s hs
      have hne : s ≠ s₀ := fun h' => hs.2.2 (by rw [h']; exact hz)
      simp [Function.update_of_ne hne]
end GlobalTheory.LogExt
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LogExt
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
open Filter Topology Asymptotics Metric Set Complex
open scoped Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.LogExt
namespace _root_.GlobalTheory.LogExt
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (U : Set V) (φ u : V → ℂ) (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hu : DifferentiableOn ℂ u {b ∈ U | φ b ≠ 0})
    (hd : U ⊆ closure {b ∈ U | φ b ≠ 0})
    (hb : ∀ b₀ ∈ U, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ b in 𝓝 b₀, φ b ≠ 0 → ‖u b‖ ≤ C * (1 + |Real.log ‖φ b‖|) ^ k) :
    ∃ u' : V → ℂ, DifferentiableOn ℂ u' U ∧ Set.EqOn u' u {b ∈ U | φ b ≠ 0} := by
  have hSo : IsOpen {b ∈ U | φ b ≠ 0} :=
    hφ.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  refine exists_differentiableOn_of_locally_extends hU (fun b hb => hb.1) hd u ?_
  intro b₀ hb₀
  by_cases h0 : φ b₀ ≠ 0
  · exact ⟨_, hSo.mem_nhds ⟨hb₀, h0⟩, u, hu, fun x hx => rfl⟩
  push_neg at h0
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU b₀ hb₀
  obtain ⟨b₁, hb₁S, hb₁⟩ := Metric.mem_closure_iff.mp (hd hb₀) ε hε
  set v := b₁ - b₀ with hv
  have hv0 : v ≠ 0 := by
    intro h
    apply hb₁S.2
    rw [show b₁ = b₀ from sub_eq_zero.mp h]
    exact h0
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hvε : ‖v‖ < ε := by rw [hv, ← dist_eq_norm, dist_comm]; exact hb₁
  set R := ε / ‖v‖ with hRdef
  have hR1 : 1 < R := (one_lt_div hvpos).mpr hvε
  have hRv : R * ‖v‖ = ε := div_mul_cancel₀ _ hvpos.ne'
  have hline : ∀ t : ℂ, ‖t‖ < R → b₀ + t • v ∈ U := by
    intro t ht
    apply hεU
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖v‖ < R * ‖v‖ := by gcongr
      _ = ε := hRv
  have hgd : DifferentiableOn ℂ (fun t : ℂ => φ (b₀ + t • v)) (ball 0 R) :=
    hφ.comp (by fun_prop) (fun t ht => hline t (by simpa using ht))
  have hg1 : (fun t : ℂ => φ (b₀ + t • v)) 1 ≠ 0 := by simpa [hv] using hb₁S.2
  have hgiso : ∀ᶠ t in 𝓝[≠] (0 : ℂ), φ (b₀ + t • v) ≠ 0 := by
    have han := hgd.analyticOnNhd isOpen_ball
    rcases (han 0 (mem_ball_self (by linarith))).eventually_eq_zero_or_eventually_ne_zero with
      hz | hz
    · exact absurd (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball 0 R).isPreconnected (mem_ball_self (by linarith)) hz
        (by simpa using hR1)) hg1
    · exact hz
  obtain ⟨r₀, hr₀, hr₀g⟩ : ∃ r₀ > 0, ∀ t : ℂ, t ∈ ball (0 : ℂ) r₀ → t ≠ 0 →
      φ (b₀ + t • v) ≠ 0 := by
    rcases Metric.mem_nhdsWithin_iff.mp hgiso with ⟨r₀, hr₀, h⟩
    exact ⟨r₀, hr₀, fun t ht ht0 => h ⟨ht, ht0⟩⟩
  set r := min r₀ R / 2 with hrdef
  have hr : 0 < r := by have := lt_min hr₀ (by linarith : (0 : ℝ) < R); positivity
  have hrr₀ : r < r₀ := by have := min_le_left r₀ R; linarith
  have hrR : r ≤ R / 2 := by have := min_le_right r₀ R; linarith
  have hKS : (fun t : ℂ => b₀ + t • v) '' sphere 0 r ⊆ {b ∈ U | φ b ≠ 0} := by
    rintro _ ⟨t, ht, rfl⟩
    have htn : ‖t‖ = r := by simpa using ht
    refine ⟨hline t (by linarith), hr₀g t (by rw [mem_ball_zero_iff]; linarith) ?_⟩
    rintro rfl
    simp at htn
    linarith
  have hK : IsCompact ((fun t : ℂ => b₀ + t • v) '' sphere 0 r) :=
    (isCompact_sphere 0 r).image (by fun_prop)
  obtain ⟨δ₁, hδ₁, hthick⟩ := hK.exists_thickening_subset_open hSo hKS
  set δ := min δ₁ (ε / 4) with hδdef
  have hδ : 0 < δ := lt_min hδ₁ (by linarith)
  have hcirc : ∀ b ∈ ball b₀ δ, ∀ t : ℂ, ‖t‖ = r → b + t • v ∈ {x ∈ U | φ x ≠ 0} := by
    intro b hb t ht
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨b₀ + t • v, ⟨t, by simpa using ht, rfl⟩, ?_⟩
    rw [dist_eq_norm, show b + t • v - (b₀ + t • v) = b - b₀ by abel, ← dist_eq_norm]
    exact lt_of_lt_of_le hb (min_le_left _ _)
  have hdisc : ∀ b ∈ ball b₀ δ, ∀ t : ℂ, ‖t‖ < 3 / 2 * r → b + t • v ∈ U := by
    intro b hb t ht
    apply hεU
    rw [mem_ball, dist_eq_norm, show b + t • v - b₀ = (b - b₀) + t • v by abel]
    have h1 : ‖b - b₀‖ < ε / 4 := by
      rw [← dist_eq_norm]; exact lt_of_lt_of_le hb (min_le_right _ _)
    have h2 : ‖t • v‖ ≤ 3 / 4 * ε := by
      rw [norm_smul]
      calc ‖t‖ * ‖v‖ ≤ (3 / 2 * r) * ‖v‖ := by gcongr
        _ ≤ (3 / 2 * (R / 2)) * ‖v‖ := by gcongr
        _ = 3 / 4 * ε := by rw [← hRv]; ring
    calc ‖(b - b₀) + t • v‖ ≤ ‖b - b₀‖ + ‖t • v‖ := norm_add_le _ _
      _ < ε := by linarith
  refine ⟨ball b₀ δ, ball_mem_nhds b₀ hδ,
    fun b => (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v), ?_, ?_⟩
  · have hI := (_root_.GlobalTheory.differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
      (F := fun θ b => u (b + circleMap 0 r θ • v)) (U := ball b₀ δ) isOpen_ball
      (a := 0) (b := 2 * π) ?_ ?_).1
    · exact (differentiableOn_const _).mul hI
    · have hc : Continuous fun p : ℝ × V => p.2 + circleMap 0 r p.1 • v :=
        continuous_snd.add (((continuous_circleMap 0 r).comp continuous_fst).smul continuous_const)
      refine hu.continuousOn.comp hc.continuousOn ?_
      rintro ⟨θ, b⟩ ⟨_, hb⟩
      exact hcirc b hb _ (by simp [abs_of_pos hr])
    · intro θ _
      refine hu.comp (differentiable_id.add_const _).differentiableOn ?_
      intro b hb
      exact hcirc b hb _ (by simp [abs_of_pos hr])
  · rintro b ⟨hbδ, hbS⟩
    obtain ⟨H, hHd, hHe⟩ := exists_differentiableOn_ball_of_log_bound (ψ := fun s => φ (b + s • v))
      (h := fun s => u (b + s • v)) (ρ := 3 / 2 * r) (by positivity)
      (hφ.comp (by fun_prop) (fun s hs => hdisc b hbδ s (by simpa using hs)))
      (by simpa using hbS.2)
      (hu.comp (by fun_prop) (fun s hs => ⟨hdisc b hbδ s (by simpa using hs.1), hs.2⟩))
      (by
        intro s₀ hs₀
        obtain ⟨C, k, hCk⟩ := hb _ (hdisc b hbδ s₀ (by simpa using hs₀))
        exact ⟨C, k, ((by fun_prop : Continuous fun s : ℂ => b + s • v).tendsto s₀).eventually hCk⟩)
    have hC := (hHd.mono (closedBall_subset_ball (by linarith : r < 3 / 2 * r))).circleIntegral_sub_inv_smul
      (mem_ball_self hr)
    have hH0 : H 0 = u b := by
      have := hHe ⟨mem_ball_self (by positivity), by simpa using hbS.2⟩
      simpa using this
    have hint : ∀ θ : ℝ, deriv (circleMap 0 r) θ • ((circleMap 0 r θ - 0)⁻¹ • H (circleMap 0 r θ))
        = I * u (b + circleMap 0 r θ • v) := by
      intro θ
      have hne : circleMap 0 r θ ≠ 0 := circleMap_ne_center hr.ne'
      have hn : ‖circleMap 0 r θ‖ = r := by simp [abs_of_pos hr]
      have hH : H (circleMap 0 r θ) = u (b + circleMap 0 r θ • v) :=
        hHe ⟨by rw [mem_ball_zero_iff, hn]; linarith, (hcirc b hbδ _ hn).2⟩
      rw [deriv_circleMap, hH, sub_zero, smul_eq_mul, smul_eq_mul]
      field_simp
    rw [circleIntegral, intervalIntegral.integral_congr (fun θ _ => hint θ),
      intervalIntegral.integral_const_mul, hH0] at hC
    show (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v) = u b
    have hI : I ≠ 0 := I_ne_zero
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have : ∫ θ in (0 : ℝ)..2 * π, u (b + circleMap 0 r θ • v) = 2 * π * u b := by
      apply mul_left_cancel₀ hI
      rw [hC, smul_eq_mul]
      ring
    rw [this]
    field_simp
end _root_.GlobalTheory.LogExt
end GlobalTheory.LogExt
