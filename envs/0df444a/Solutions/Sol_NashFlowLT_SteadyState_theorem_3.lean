-- Prove2me | solution 1 for NashFlowLT.SteadyState.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:26:00.472994+00:00
-- url     : https://prove2.me/submissions/6dbe8391-ca21-4ebc-ad91-45506a187161
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model
import Theorems.Thm_NashFlowLT_SteadyState_labels_monotone_ac
import Theorems.Thm_NashFlowLT_SteadyState_queue_identity
import Theorems.Thm_NashFlowLT_SteadyState_lemma_1
import Theorems.Thm_NashFlowLT_SteadyState_theorem_2
import Theorems.Thm_NashFlowLT_SteadyState_uniform_slope
import Theorems.Thm_NashFlowLT_SteadyState_primal_feasible
import Theorems.Thm_NashFlowLT_SteadyState_dual_feasible_phi_le
import Theorems.Thm_NashFlowLT_SteadyState_labels_piecewise_linear
import Theorems.Thm_NashFlowLT_SteadyState_steady_phase_persists

open NashFlowLT.SteadyState MeasureTheory Set Finset Filter Topology

/-- `x ↦ max (D + m x) 0` is affine on a right neighbourhood of `0`. -/
lemma p2m_nflt_max_affine_right (D m : ℝ) :
    ∃ s : ℝ, ∀ᶠ x in 𝓝[≥] (0:ℝ), max (D + m * x) 0 = max D 0 + s * x := by
  have hT : Tendsto (fun x : ℝ => D + m * x) (𝓝 0) (𝓝 D) := by
    exact (by fun_prop : Continuous fun x : ℝ => D + m * x).tendsto' 0 D (by simp)
  rcases lt_trichotomy D 0 with hD | hD | hD
  · refine ⟨0, ?_⟩
    have h1 : ∀ᶠ x in 𝓝 (0:ℝ), D + m * x < 0 := hT.eventually (gt_mem_nhds hD)
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with x hx
    rw [max_eq_right hx.le, max_eq_right hD.le]; ring
  · refine ⟨max m 0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x (hx : (0:ℝ) ≤ x)
    subst hD
    rcases le_total m 0 with hm | hm
    · rw [max_eq_right hm, max_eq_right (by nlinarith), max_self]; ring
    · rw [max_eq_left hm, max_eq_left (by nlinarith), max_self]
  · refine ⟨m, ?_⟩
    have h1 : ∀ᶠ x in 𝓝 (0:ℝ), 0 < D + m * x := hT.eventually (lt_mem_nhds hD)
    filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with x hx
    rw [max_eq_left hx.le, max_eq_left hD.le]

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F)
    (hcut : ∀ S : Finset V, N.s ∈ S → N.t ∉ S → N.u0 ≤ cutCapacity N S) :
    AttainsSteadyState N F := by
  by_contra hns
  obtain ⟨y, hy⟩ := primal_feasible N hN hcut
  have hbound : ∀ θ, 0 ≤ θ → Phi N F θ ≤ ∑ e, N.tau e * y e :=
    fun θ hθ => (dual_feasible_phi_le N hN F hF θ hθ).2 y hy
  obtain ⟨κ, hκ, hslope⟩ := uniform_slope N hN F hF
  have hgood := hslope.and (theorem_2 N hN F hF).2
  have hq := queue_identity N hN F hF
  have hac := (labels_monotone_ac N hN F hF).1
  set G : ℝ → ℝ := fun θ => N.u0 * (ell N F N.t θ - ell N F N.s θ) -
    ∑ e, N.nu e * max (ell N F (N.head e) θ - ell N F (N.tail e) θ - N.tau e) 0 with hGdef
  have hPG : ∀ θ, 0 ≤ θ → Phi N F θ = G θ := by
    intro θ hθ
    simp only [Phi, G]
    congr 1
    exact Finset.sum_congr rfl (fun e _ => hq e θ hθ)
  -- Step 1: on every phase which is not a steady state, `Φ` grows with slope at least `κ`.
  have hloc : ∀ θ, 0 ≤ θ → ∀ᶠ t in 𝓝[>] θ, Phi N F θ + κ * (t - θ) ≤ Phi N F t := by
    intro θ hθ
    obtain ⟨ε, hε, c, hc⟩ := labels_piecewise_linear N hN F hF θ hθ
    have hs : ∀ e, ∃ s : ℝ, ∀ᶠ x in 𝓝[≥] (0:ℝ),
        max ((ell N F (N.head e) θ - ell N F (N.tail e) θ - N.tau e) +
          (c (N.head e) - c (N.tail e)) * x) 0 =
        max (ell N F (N.head e) θ - ell N F (N.tail e) θ - N.tau e) 0 + s * x :=
      fun e => p2m_nflt_max_affine_right _ _
    choose s hs using hs
    have hall := Filter.eventually_all.2 hs
    set σ := N.u0 * (c N.t - c N.s) - ∑ e, N.nu e * s e with hσdef
    have h1 : Tendsto (fun t => t - θ) (𝓝[≥] θ) (𝓝[≥] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun t => t - θ) (𝓝 θ) (𝓝 (θ - θ)) :=
          (continuous_id.sub continuous_const).tendsto θ
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t (ht : θ ≤ t)
        simpa using ht
    have hev : ∀ᶠ t in 𝓝[≥] θ, Phi N F t = Phi N F θ + σ * (t - θ) ∧
        ∀ v, ell N F v t = ell N F v θ + c v * (t - θ) := by
      have h3 : ∀ᶠ t in 𝓝[≥] θ, t ∈ Icc θ (θ + ε) := Icc_mem_nhdsGE (by linarith)
      filter_upwards [h1.eventually hall, h3] with t ht htI
      have hcv := fun v => hc v t htI
      refine ⟨?_, hcv⟩
      rw [hPG t (by linarith [htI.1]), hPG θ hθ]
      simp only [G]
      have hm : ∀ e, max (ell N F (N.head e) t - ell N F (N.tail e) t - N.tau e) 0 =
          max (ell N F (N.head e) θ - ell N F (N.tail e) θ - N.tau e) 0 + s e * (t - θ) := by
        intro e
        rw [hcv (N.head e), hcv (N.tail e), ← ht e]
        congr 1; ring
      simp_rw [hm]
      rw [hcv N.t, hcv N.s]
      have : ∑ e, N.nu e * (max (ell N F (N.head e) θ - ell N F (N.tail e) θ - N.tau e) 0 +
          s e * (t - θ)) = ∑ e, N.nu e * max (ell N F (N.head e) θ - ell N F (N.tail e) θ -
          N.tau e) 0 + (∑ e, N.nu e * s e) * (t - θ) := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intros; ring
      rw [this, hσdef]; ring
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have hu' : θ < u := hu
    -- derivatives on `(θ, u)`
    have hderiv : ∀ t' ∈ Ioo θ u, HasDerivAt (Phi N F) σ t' ∧
        ∀ v, HasDerivAt (ell N F v) (c v) t' := by
      intro t' ht'
      have hnb : Ioo θ u ∈ 𝓝 t' := Ioo_mem_nhds ht'.1 ht'.2
      constructor
      · have hA : HasDerivAt (fun t => Phi N F θ + σ * (t - θ)) σ t' := by
          simpa using (((hasDerivAt_id t').sub_const θ).const_mul σ).const_add (Phi N F θ)
        apply hA.congr_of_eventuallyEq
        filter_upwards [hnb] with t ht
        exact (hsub ⟨ht.1.le, ht.2⟩).1
      · intro v
        have hA : HasDerivAt (fun t => ell N F v θ + c v * (t - θ)) (c v) t' := by
          simpa using (((hasDerivAt_id t').sub_const θ).const_mul (c v)).const_add (ell N F v θ)
        apply hA.congr_of_eventuallyEq
        filter_upwards [hnb] with t ht
        exact (hsub ⟨ht.1.le, ht.2⟩).2 v
    -- pick a good time in `(θ, u)`
    have hgood' : ∀ᵐ t ∂(volume.restrict (Ioo θ u)), _ :=
      ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi hθ)) hgood
    have : (ae (volume.restrict (Ioo θ u))).NeBot := by
      rw [ae_neBot, Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero]
      linarith
    obtain ⟨t', ⟨hP1, hP2⟩, ht'⟩ := (hgood'.and (ae_restrict_mem measurableSet_Ioo)).exists
    obtain ⟨hdΦ, hdl⟩ := hderiv t' ht'
    have hσ : κ ≤ σ := by
      rcases hP1 σ hdΦ with h0 | h0
      · exfalso
        have hc1 : ∀ v, c v = 1 := (hP2 c σ hdl hdΦ).1 h0
        apply hns
        apply (lemma_1 N hN F hF).2
        refine ⟨θ, hθ, ?_⟩
        apply steady_phase_persists N hN F hF θ u hθ hu'
        intro v t ht
        simpa [hc1 v] using (hderiv t ht).2 v
      · exact h0
    have hev' : ∀ᶠ t in 𝓝[>] θ, Phi N F t = Phi N F θ + σ * (t - θ) :=
      (hev.filter_mono (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)).mono fun t ht => ht.1
    filter_upwards [hev', self_mem_nhdsWithin] with t ht (htθ : θ < t)
    rw [ht]
    nlinarith
  -- Step 2: hence `Φ(T) ≥ Φ(0) + κ T` for all `T ≥ 0`.
  have hgrow : ∀ T, 0 ≤ T → Phi N F 0 + κ * T ≤ Phi N F T := by
    intro T hT
    have hcont : ∀ v, ContinuousOn (ell N F v) (Icc 0 T) := by
      intro v
      have := ((hac v).2 T hT).continuousOn
      rwa [uIcc_of_le hT] at this
    have hGc : ContinuousOn G (Icc 0 T) := by
      simp only [G]
      apply ContinuousOn.sub
      · exact continuousOn_const.mul ((hcont _).sub (hcont _))
      · apply continuousOn_finsetSum
        intro e _
        exact continuousOn_const.mul (continuous_max.comp_continuousOn
          ((((hcont _).sub (hcont _)).sub continuousOn_const).prodMk continuousOn_const))
    have hΦc : ContinuousOn (Phi N F) (Icc 0 T) :=
      hGc.congr (fun t ht => hPG t ht.1)
    have hgc : ContinuousOn (fun t => Phi N F t - κ * t) (Icc 0 T) :=
      hΦc.sub (continuousOn_const.mul continuousOn_id)
    set S : Set ℝ := {t | Phi N F 0 ≤ Phi N F t - κ * t} with hS
    have hclosed : IsClosed (S ∩ Icc 0 T) := by
      rw [Set.inter_comm]
      exact hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have h0 : (0:ℝ) ∈ S := by simp [S]
    have hsub := IsClosed.Icc_subset_of_forall_exists_gt hclosed h0 (by
      intro x hx z hz
      have hxz : x < z := hz
      obtain ⟨t, ht1, ht2⟩ := ((hloc x hx.2.1).and (Ioc_mem_nhdsGT hxz)).exists
      refine ⟨t, ?_, ht2⟩
      have hxS : Phi N F 0 ≤ Phi N F x - κ * x := hx.1
      show Phi N F 0 ≤ Phi N F t - κ * t
      linarith)
    have := hsub ⟨hT, le_rfl⟩
    have h' : Phi N F 0 ≤ Phi N F T - κ * T := this
    linarith
  -- Step 3: contradiction with the bound `Φ ≤ α`.
  set T := max 0 ((∑ e, N.tau e * y e - Phi N F 0) / κ) + 1 with hT
  have hT0 : 0 ≤ T := by positivity
  have h1 := hgrow T hT0
  have h2 := hbound T hT0
  have h3 : (∑ e, N.tau e * y e - Phi N F 0) / κ < T := by
    have := le_max_right 0 ((∑ e, N.tau e * y e - Phi N F 0) / κ); linarith
  rw [div_lt_iff₀ hκ] at h3
  nlinarith
