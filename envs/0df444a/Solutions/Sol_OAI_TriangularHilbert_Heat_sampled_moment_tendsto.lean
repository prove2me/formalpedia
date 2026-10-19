-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.sampled_moment_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:25:29.37063+00:00
-- url     : https://prove2.me/submissions/518eff5d-e52b-4ef4-ab6c-1bcf64c9de78

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledMoment

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uκ
open MeasureTheory Filter
open scoped Topology
lemma h43_gp_le {h : ℝ} (hh : 0 < h) (x : ℝ) : gridPoint h x ≤ x := by
  unfold gridPoint gridIndex
  have := Int.floor_le (x/h)
  rw [le_div_iff₀ hh] at this
  linarith

lemma h43_gp_gt {h : ℝ} (hh : 0 < h) (x : ℝ) : x - h < gridPoint h x := by
  unfold gridPoint gridIndex
  have := Int.lt_floor_add_one (x/h)
  rw [div_lt_iff₀ hh] at this
  nlinarith

lemma h43_gp_meas (h : ℝ) : Measurable (gridPoint h) := by
  unfold gridPoint gridIndex
  exact measurable_const.mul (measurable_from_top.comp (Int.measurable_floor.comp (measurable_id.div_const h)))

lemma h43_gp_tendsto {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (ht : Tendsto h atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => gridPoint (h n) x) atTop (𝓝 x) := by
  have h1 : Tendsto (fun n => x - h n) atTop (𝓝 x) := by simpa using (tendsto_const_nhds (x := x)).sub ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
    (fun n => (h43_gp_gt (hh n) x).le) (fun n => h43_gp_le (hh n) x)

theorem h43_skt (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    (K : ℝ → ℝ) (hK : Measurable K) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ)
    (hcont : ∀ᵐ c : ℝ, ContinuousAt K (z.1+z.2+c)) :
    Tendsto (fun n => sampledKernelOutput B C (h n) K z) atTop (𝓝 (cyclicKernelOutput B C K z)) := by
  set S : Set ℝ := Set.Icc (-(M+1)) (M+1) with hS
  have hSm : MeasurableSet S := measurableSet_Icc
  have hSf : volume S ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  unfold sampledKernelOutput cyclicKernelOutput
  refine tendsto_integral_of_dominated_convergence (fun c => S.indicator (fun _ => CB*CC*L) c) ?_ ?_ ?_ ?_
  · intro n
    unfold sampledIntegrand
    have g := h43_gp_meas (h n)
    refine (Measurable.aestronglyMeasurable ?_)
    refine ((hB.measurable.comp (measurable_const.prodMk g)).mul
      (hC.measurable.comp (g.prodMk measurable_const))).mul ?_
    exact Complex.measurable_ofReal.comp (hK.comp (measurable_const.add g))
  · exact (integrableOn_const (C := CB*CC*L) hSf enorm_ne_top).integrable_indicator hSm
  · intro n
    refine Filter.Eventually.of_forall (fun c => ?_)
    unfold sampledIntegrand
    by_cases hz : B (gridPoint (h n) z.2, gridPoint (h n) c) = 0
    · rw [hz, zero_mul, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · obtain ⟨_, h2⟩ := hs _ hz
      have hcS : c ∈ S := by
        have a1 := h43_gp_le (hh n) c
        have a2 := h43_gp_gt (hh n) c
        have := hh1 n
        rw [abs_le] at h2
        exact ⟨by linarith, by linarith⟩
      rw [Set.indicator_of_mem hcS, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hb (gridPoint (h n) z.2, gridPoint (h n) c)
      have := hc (gridPoint (h n) c, gridPoint (h n) z.1)
      have := hk (gridPoint (h n) z.1 + gridPoint (h n) z.2 + gridPoint (h n) c)
      have := norm_nonneg (B (gridPoint (h n) z.2, gridPoint (h n) c))
      have := norm_nonneg (C (gridPoint (h n) c, gridPoint (h n) z.1))
      have := abs_nonneg (K (gridPoint (h n) z.1 + gridPoint (h n) z.2 + gridPoint (h n) c))
      apply mul_le_mul (mul_le_mul ‹_› ‹_› (by positivity) hCB) ‹_› (by positivity) (by positivity)
  · filter_upwards [hcont] with c hcK
    unfold sampledIntegrand
    have t1 := h43_gp_tendsto hh ht z.1
    have t2 := h43_gp_tendsto hh ht z.2
    have t3 := h43_gp_tendsto hh ht c
    refine (((hB.tendsto _).comp (t2.prodMk_nhds t3)).mul ((hC.tendsto _).comp (t3.prodMk_nhds t1))).mul ?_
    exact (Complex.continuous_ofReal.tendsto _).comp (hcK.tendsto.comp ((t1.add t2).add t3))

lemma h43_si_bound (B C : ℝ×ℝ → ℂ) {M CB CC L : ℝ} (hs : BoxSupport B M) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (K : ℝ → ℝ) (hk : ∀ t, |K t| ≤ L) (z : ℝ×ℝ) (c : ℝ) :
    ‖sampledIntegrand B C h K z c‖ ≤ (Set.Icc (-(M+1)) (M+1)).indicator (fun _ => CB*CC*L) c := by
  unfold sampledIntegrand
  by_cases hz : B (gridPoint h z.2, gridPoint h c) = 0
  · rw [hz, zero_mul, zero_mul, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  · obtain ⟨_, h2⟩ := hs _ hz
    have hcS : c ∈ Set.Icc (-(M+1)) (M+1) := by
      have a1 := h43_gp_le hh c
      have a2 := h43_gp_gt hh c
      rw [abs_le] at h2
      exact ⟨by linarith, by linarith⟩
    rw [Set.indicator_of_mem hcS, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := hb (gridPoint h z.2, gridPoint h c)
    have := hc (gridPoint h c, gridPoint h z.1)
    have := hk (gridPoint h z.1 + gridPoint h z.2 + gridPoint h c)
    have := norm_nonneg (B (gridPoint h z.2, gridPoint h c))
    have := norm_nonneg (C (gridPoint h c, gridPoint h z.1))
    apply mul_le_mul (mul_le_mul ‹_› ‹_› (by positivity) hCB) ‹_› (by positivity) (by positivity)

lemma h43_si_zero (B C : ℝ×ℝ → ℂ) {M : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (K : ℝ → ℝ) (z : ℝ×ℝ)
    (hz : z ∉ Set.Icc (-(M+1)) (M+1) ×ˢ Set.Icc (-(M+1)) (M+1)) (c : ℝ) :
    sampledIntegrand B C h K z c = 0 := by
  unfold sampledIntegrand
  by_contra hne
  have hB0 : B (gridPoint h z.2, gridPoint h c) ≠ 0 := fun e => hne (by rw [e]; simp)
  have hC0 : C (gridPoint h c, gridPoint h z.1) ≠ 0 := fun e => hne (by rw [e]; simp)
  have h2 := (hsB _ hB0).1
  have h1 := (hsC _ hC0).2
  simp only at h1 h2
  rw [abs_le] at h1 h2
  apply hz
  have a1 := h43_gp_le hh z.1
  have a2 := h43_gp_gt hh z.1
  have b1 := h43_gp_le hh z.2
  have b2 := h43_gp_gt hh z.2
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma h43_si_meas (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C) (h : ℝ) (K : ℝ → ℝ) (hK : Measurable K) :
    Measurable (fun p : (ℝ×ℝ)×ℝ => sampledIntegrand B C h K p.1 p.2) := by
  unfold sampledIntegrand
  have g := h43_gp_meas h
  have g1 : Measurable (fun p : (ℝ×ℝ)×ℝ => gridPoint h p.1.1) := g.comp (measurable_fst.comp measurable_fst)
  have g2 : Measurable (fun p : (ℝ×ℝ)×ℝ => gridPoint h p.1.2) := g.comp (measurable_snd.comp measurable_fst)
  have g3 : Measurable (fun p : (ℝ×ℝ)×ℝ => gridPoint h p.2) := g.comp measurable_snd
  exact ((hB.measurable.comp (g2.prodMk g3)).mul (hC.measurable.comp (g3.prodMk g1))).mul
    (Complex.measurable_ofReal.comp (hK.comp ((g1.add g2).add g3)))

lemma h43_cm_cont : Continuous complexMoment := by
  unfold complexMoment; fun_prop

theorem solution (B C : ℝ×ℝ → ℂ) (hB : Continuous B) (hC : Continuous C)
    {M CB CC L : ℝ} (hsB : BoxSupport B M) (hsC : BoxSupport C M)
    (hCB : 0 ≤ CB) (hCC : 0 ≤ CC) (hL : 0 ≤ L)
    (hb : ∀ z, ‖B z‖ ≤ CB) (hc : ∀ z, ‖C z‖ ≤ CC)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0))
    {κ : Type uκ} [Fintype κ] [Nonempty κ] (K : κ → ℝ → ℝ)
    (hK : ∀ k, Measurable (K k)) (hk : ∀ k t, |K k t| ≤ L)
    (hcont : ∀ k (z : ℝ×ℝ), ∀ᵐ c : ℝ, ContinuousAt (K k) (z.1+z.2+c)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, finiteMoment (fun k => sampledKernelOutput B C (h n) (K k) z)) atTop
      (𝓝 (∫ z : ℝ×ℝ, finiteMoment (fun k => cyclicKernelOutput B C (K k) z))) := by
  set S2 : Set (ℝ×ℝ) := Set.Icc (-(M+1)) (M+1) ×ˢ Set.Icc (-(M+1)) (M+1) with hS2
  have hS2m : MeasurableSet S2 := measurableSet_Icc.prod measurableSet_Icc
  have hS2f : volume S2 ≠ ⊤ := ((isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne
  have hSm : MeasurableSet (Set.Icc (-(M+1)) (M+1)) := measurableSet_Icc
  have hSf : volume (Set.Icc (-(M+1)) (M+1)) ≠ ⊤ := (isCompact_Icc.measure_lt_top).ne
  set Q := ∫ c : ℝ, (Set.Icc (-(M+1)) (M+1)).indicator (fun _ => CB*CC*L) c with hQ
  have hgi : Integrable (fun c : ℝ => (Set.Icc (-(M+1)) (M+1)).indicator (fun _ => CB*CC*L) c) :=
    (integrableOn_const (C := CB*CC*L) hSf enorm_ne_top).integrable_indicator hSm
  have hQ0 : 0 ≤ Q := integral_nonneg (fun c => Set.indicator_nonneg (fun _ _ => by positivity) _)
  have hout : ∀ n k z, ‖sampledKernelOutput B C (h n) (K k) z‖ ≤ Q := by
    intro n k z
    exact norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall
      (fun c => h43_si_bound B C hsB hCB hCC hL hb hc (hh n) (hh1 n) (K k) (hk k) z c))
  have hzero : ∀ n k z, z ∉ S2 → sampledKernelOutput B C (h n) (K k) z = 0 := by
    intro n k z hz
    unfold sampledKernelOutput
    simp [h43_si_zero B C hsB hsC (hh n) (hh1 n) (K k) z hz]
  have hne : (Finset.univ : Finset κ).Nonempty := Finset.univ_nonempty
  have hfm_nonneg : ∀ f : κ → ℂ, 0 ≤ finiteMoment f := by
    intro f
    obtain ⟨k0⟩ := ‹Nonempty κ›
    exact le_trans (by unfold complexMoment; positivity) (Finset.le_sup' (fun k => complexMoment (f k)) (Finset.mem_univ k0))
  refine tendsto_integral_of_dominated_convergence (fun z => S2.indicator (fun _ => Q * Real.sqrt Q) z) ?_ ?_ ?_ ?_
  · intro n
    refine Measurable.aestronglyMeasurable ?_
    have hm : ∀ k, Measurable (fun z => complexMoment (sampledKernelOutput B C (h n) (K k) z)) := by
      intro k
      refine h43_cm_cont.measurable.comp ?_
      exact (h43_si_meas B C hB hC (h n) (K k) (hK k)).stronglyMeasurable.integral_prod_right'.measurable
    have := Finset.measurable_sup' hne (fun k _ => hm k)
    convert this using 1
    all_goals first | rfl | (funext z; simp [finiteMoment, Finset.sup'_apply])
  · exact (integrableOn_const (C := Q * Real.sqrt Q) hS2f enorm_ne_top).integrable_indicator hS2m
  · intro n
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_of_nonneg (hfm_nonneg _)]
    by_cases hz : z ∈ S2
    · rw [Set.indicator_of_mem hz]
      refine Finset.sup'_le _ _ (fun k _ => ?_)
      unfold complexMoment
      have := hout n k z
      exact mul_le_mul this (Real.sqrt_le_sqrt this) (Real.sqrt_nonneg _) hQ0
    · rw [Set.indicator_of_notMem hz]
      have : (fun k => sampledKernelOutput B C (h n) (K k) z) = fun _ => (0:ℂ) := by
        funext k; exact hzero n k z hz
      rw [this, finiteMoment_zero]
  · refine Filter.Eventually.of_forall (fun z => ?_)
    unfold finiteMoment
    refine Filter.Tendsto.finset_sup'_nhds_apply hne (fun k _ => ?_)
    exact (h43_cm_cont.tendsto _).comp
      (h43_skt B C hB hC hsB hCB hCC hL hb hc hh hh1 ht (K k) (hK k) (hk k) z (hcont k z))

