-- Prove2me | solution 1 for JHolomorphic.exists_subseq_tendstoCInftyLocOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T15:38:08.634574+00:00
-- url     : https://prove2.me/submissions/023b4ab0-74ee-4182-b589-201d06f1ee8f

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
import Theorems.Thm_JHolomorphic_bounded_iteratedFDeriv_of_sobolevNorm_le
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
import Theorems.Thm_JHolomorphic_exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv
import Theorems.Thm_JHolomorphic_contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence



namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity Set
open scoped ContDiff ENNReal NNReal

set_option maxHeartbeats 1000000 in
theorem exists_subseq_tendstoCInftyLocOn_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ 1 (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (C : ℝ)
    (hC : ∀ ν, ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (u ν) z‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → E, ContDiffOn ℝ ∞ v (ball 0 1) ∧
      IsJHolomorphicOn J (ball 0 1) v ∧ Set.MapsTo v (ball 0 1) K₀ ∧
      TendstoCInftyLocOn (fun ν => u (φ ν)) v (ball 0 1) := by
  -- each `u ν` is smooth
  have hsm : ∀ ν, ContDiffOn ℝ ∞ (u ν) (ball 0 1) := by
    intro ν
    refine contDiffOn_of_isWeakJHolomorphicOn 3 (by norm_num) (Jν ν) O (hJν ν) (ball 0 1)
      isOpen_ball (u ν) ?_
    have hcf : ContinuousOn (fderiv ℝ (u ν)) (ball 0 1) :=
      (hu ν).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
    refine ⟨(hu ν).continuousOn, (hmaps ν).mono_right hK₀O, fun z => fderiv ℝ (u ν) z 1,
      fun z => fderiv ℝ (u ν) z Complex.I, HasWeakPartialsOn.of_contDiffOn isOpen_ball (hu ν),
      ?_, ?_⟩
    · intro K hK hKc
      exact ⟨memLp_of_continuousOn_compact hKc ((hu ν).continuousOn.mono hK),
        memLp_of_continuousOn_compact hKc ((hcf.clm_apply continuousOn_const).mono hK),
        memLp_of_continuousOn_compact hKc ((hcf.clm_apply continuousOn_const).mono hK)⟩
    · exact ae_restrict_of_forall_mem measurableSet_ball fun z hz => (hhol ν z hz).2
  -- a uniform `W^{1,3}` bound on the disc
  obtain ⟨R, hR⟩ := hK₀.isBounded.exists_norm_le
  have hμ : (volume.restrict (ball (0 : ℂ) 1)) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top.ne
  set A : ℝ≥0∞ := (volume.restrict (ball (0 : ℂ) 1)) univ ^ (ENNReal.ofReal 3).toReal⁻¹ *
    (ENNReal.ofReal R + ENNReal.ofReal C) with hA_def
  have hA : A ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ) ?_
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hsob : ∀ ν, sobolevNorm 1 (ENNReal.ofReal 3) (ball 0 1) (u ν) ≤ A.toNNReal := by
    intro ν
    rw [ENNReal.coe_toNNReal hA, hA_def, mul_add]
    simp only [sobolevNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    refine add_le_add ?_ ?_
    · refine eLpNorm_le_of_ae_bound (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
      rw [norm_iteratedFDeriv_zero]; exact hR _ (hmaps ν hz)
    · refine eLpNorm_le_of_ae_bound (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
      rw [norm_iteratedFDeriv_one]; exact hC ν z hz
  -- uniform bounds on all derivatives, extraction, identification of the limit
  have hbd : ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ m : ℕ, ∃ M : ℝ, ∀ ν, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (u ν) z‖ ≤ M :=
    bounded_iteratedFDeriv_of_sobolevNorm_le 3 (by norm_num) J Jν O K₀ hJ hJν hconv hK₀ hK₀O u
      hsm hhol hmaps A.toNNReal hsob
  obtain ⟨φ, hφ, g, hg⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv isOpen_ball u hsm hbd
  set v : ℂ → E := fun z => continuousMultilinearCurryFin0 ℝ ℂ E (g 0 z) with hv_def
  have hv : ∀ z ∈ ball (0 : ℂ) 1, Tendsto (fun ν => u (φ ν) z) atTop (𝓝 (v z)) := by
    intro z hz
    have := ((continuousMultilinearCurryFin0 ℝ ℂ E).continuous.tendsto _).comp
      ((hg 0).tendsto_at hz)
    simpa [Function.comp_def, v, continuousMultilinearCurryFin0_apply,
      iteratedFDeriv_zero_apply] using this
  obtain ⟨hvs, hvg⟩ := contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv isOpen_ball
    (fun ν => u (φ ν)) (fun ν => hsm (φ ν)) v hv g hg
  have hvK : Set.MapsTo v (ball 0 1) K₀ := fun z hz =>
    hK₀.isClosed.mem_of_tendsto (hv z hz) (Eventually.of_forall fun ν => hmaps (φ ν) hz)
  refine ⟨φ, hφ, v, hvs, ?_, hvK, ?_⟩
  · intro z hz
    have hdv : DifferentiableAt ℝ v z :=
      (hvs.differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hz)
    refine ⟨hdv, ?_⟩
    have hD1 : Tendsto (fun ν => iteratedFDeriv ℝ 1 (u (φ ν)) z) atTop
        (𝓝 (iteratedFDeriv ℝ 1 v z)) := by
      rw [hvg 1 hz]; exact (hg 1).tendsto_at hz
    have hd : ∀ w : ℂ, Tendsto (fun ν => fderiv ℝ (u (φ ν)) z w) atTop
        (𝓝 (fderiv ℝ v z w)) := by
      intro w
      have := ((continuous_eval_const (fun _ : Fin 1 => w)).tendsto _).comp hD1
      simpa [Function.comp_def, iteratedFDeriv_one_apply] using this
    have hunif : TendstoUniformlyOn (fun ν => Jν (φ ν)) J atTop K₀ := by
      have h0 := hconv K₀ hK₀O hK₀ 0
      rw [Metric.tendstoUniformlyOn_iff] at h0 ⊢
      intro ε hε
      filter_upwards [hφ.tendsto_atTop.eventually (h0 ε hε)] with ν hν x hx
      have := hν x hx
      rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp] at this
      simpa only [Function.comp_apply, LinearIsometryEquiv.dist_map] using this
    have hvz : v z ∈ K₀ := hvK hz
    have hcont : ContinuousWithinAt J K₀ (v z) :=
      ((hJ.2.1.continuousOn).continuousAt (hJ.1.mem_nhds (hK₀O hvz))).continuousWithinAt
    have hin : Tendsto (fun ν => u (φ ν) z) atTop (𝓝[K₀] (v z)) :=
      tendsto_nhdsWithin_iff.2 ⟨hv z hz, Eventually.of_forall fun ν => hmaps (φ ν) hz⟩
    have hJt : Tendsto (fun ν => Jν (φ ν) (u (φ ν) z)) atTop (𝓝 (J (v z))) :=
      hunif.tendsto_comp hcont hin
    have hlim : Tendsto (fun ν => dbarJ (Jν (φ ν)) (u (φ ν)) z) atTop (𝓝 (dbarJ J v z)) :=
      (hd 1).add ((isBoundedBilinearMap_apply.continuous.tendsto _).comp
        (hJt.prodMk_nhds (hd Complex.I)))
    have hzero : ∀ ν, dbarJ (Jν (φ ν)) (u (φ ν)) z = 0 := fun ν => (hhol (φ ν) z hz).2
    simp only [hzero] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  · intro K hK hKc m
    exact (((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1 (hg m)) K hK
      hKc).congr_right (fun z hz => (hvg m (hK hz)).symm)

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ 1 (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (C : ℝ)
    (hC : ∀ ν, ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (u ν) z‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → E, ContDiffOn ℝ ∞ v (ball 0 1) ∧
      IsJHolomorphicOn J (ball 0 1) v ∧ Set.MapsTo v (ball 0 1) K₀ ∧
      TendstoCInftyLocOn (fun ν => u (φ ν)) v (ball 0 1) :=
  exists_subseq_tendstoCInftyLocOn_aux J Jν O K₀ hJ hJν hconv hK₀ hK₀O u hu hhol hmaps C hC
