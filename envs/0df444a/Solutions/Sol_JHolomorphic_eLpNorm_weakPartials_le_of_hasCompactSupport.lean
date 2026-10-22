-- Prove2me | solution 1 for JHolomorphic.eLpNorm_weakPartials_le_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T17:33:12.3975+00:00
-- url     : https://prove2.me/submissions/5b8bdb7d-4061-4278-b867-89e59552c460

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_eLpNorm_fderiv_le_of_contDiff
import Theorems.Thm_JHolomorphic_eLpNorm_normed_convolution_le
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_univ_indicator_tsupport
import Theorems.Thm_JHolomorphic_fderiv_normed_convolution_eq_of_hasWeakPartialsOn



namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

theorem eLpNorm_weakPartials_le_of_hasCompactSupport_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (J₀ : E →L[ℝ] E)
    (hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ U : Set ℂ, IsOpen U → ∀ ξ ξs ξt : ℂ → E, Continuous ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ U → HasWeakPartialsOn U ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict U) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm ξs (ENNReal.ofReal p) (volume.restrict U) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict U) ≤
        ENNReal.ofReal C * eLpNorm (fun z => ξs z + J₀ (ξt z)) (ENNReal.ofReal p)
          (volume.restrict U) := by
  obtain ⟨C, hC⟩ := eLpNorm_fderiv_le_of_contDiff p hp J₀ hJ₀
  refine ⟨2 * max C 0, ?_⟩
  intro U hU ξ ξs ξt hξ hc hsub hW hs ht
  set q := ENNReal.ofReal p with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact ENNReal.one_le_ofReal.2 hp.le
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  set K := tsupport ξ with hK
  have hKm : MeasurableSet K := (isClosed_tsupport ξ).measurableSet
  obtain ⟨hWu, hae⟩ := HasWeakPartialsOn.univ_indicator_tsupport hU hq1 hξ hc hsub hW hs ht
  set gs := K.indicator ξs with hgs
  set gt := K.indicator ξt with hgt
  have hrestr : ∀ {f : ℂ → E}, MemLp f q (volume.restrict U) → MemLp (K.indicator f) q volume :=
    fun hf => (memLp_indicator_iff_restrict hKm).2
      (hf.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hgsL : MemLp gs q volume := hrestr hs
  have hgtL : MemLp gt q volume := hrestr ht
  -- the left-hand side only sees `K`
  have hae' := (ae_restrict_iff' hU.measurableSet).1 hae
  have hLs : eLpNorm ξs q (volume.restrict U) = eLpNorm gs q volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae'] with z hz
    by_cases hzU : z ∈ U
    · rw [Set.indicator_of_mem hzU]; exact (hz hzU).1
    · have hzK : z ∉ K := fun h => hzU (hsub h)
      rw [Set.indicator_of_notMem hzU, hgs, Set.indicator_of_notMem hzK]
  have hLt : eLpNorm ξt q (volume.restrict U) = eLpNorm gt q volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae'] with z hz
    by_cases hzU : z ∈ U
    · rw [Set.indicator_of_mem hzU]; exact (hz hzU).2
    · have hzK : z ∉ K := fun h => hzU (hsub h)
      rw [Set.indicator_of_notMem hzU, hgt, Set.indicator_of_notMem hzK]
  -- the right-hand side
  set H : ℂ → E := fun z => gs z + J₀ (gt z) with hH
  have hHeq : H = K.indicator (fun z => ξs z + J₀ (ξt z)) := by
    funext z
    by_cases hz : z ∈ K
    · simp [hH, hgs, hgt, hz]
    · simp [hH, hgs, hgt, hz]
  have hR : eLpNorm H q volume ≤ eLpNorm (fun z => ξs z + J₀ (ξt z)) q (volume.restrict U) := by
    rw [hHeq, eLpNorm_indicator_eq_eLpNorm_restrict hKm]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)
  have hHm : AEStronglyMeasurable H volume :=
    hgsL.1.add (J₀.continuous.comp_aestronglyMeasurable hgtL.1)
  -- mollifiers
  let ρ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity,
      by gcongr; norm_num⟩
  have hρr : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) := by
    show Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hρK : ∀ᶠ n in atTop, (ρ n).rOut ≤ 2 * (ρ n).rIn := Eventually.of_forall fun n => by
    show 2 / ((n : ℝ) + 2) ≤ 2 * (1 / ((n : ℝ) + 2))
    rw [mul_one_div]
  have hξli : LocallyIntegrable ξ volume := hξ.locallyIntegrable
  have hgsli : LocallyIntegrable gs volume := hgsL.locallyIntegrable hq1
  have hgtli : LocallyIntegrable gt volume := hgtL.locallyIntegrable hq1
  -- linearity of the mollification
  have hlin : ∀ n z, ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] gs) z +
      J₀ (((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] gt) z) =
      ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] H) z := by
    intro n z
    have hw := (ρ n).hasCompactSupport_normed (μ := volume)
    have hwcont := (ρ n).continuous_normed (μ := volume)
    have i1 : Integrable (fun t => lsmul ℝ ℝ ((ρ n).normed volume t) (gs (z - t))) volume :=
      HasCompactSupport.convolutionExists_left (𝕜 := ℝ) (G := ℂ) (μ := volume) (E := ℝ)
        (E' := E) (F := E) (lsmul ℝ ℝ) hw hwcont hgsli z
    have i2 : Integrable (fun t => lsmul ℝ ℝ ((ρ n).normed volume t) (gt (z - t))) volume :=
      HasCompactSupport.convolutionExists_left (𝕜 := ℝ) (G := ℂ) (μ := volume) (E := ℝ)
        (E' := E) (F := E) (lsmul ℝ ℝ) hw hwcont hgtli z
    simp only [convolution_def]
    rw [← J₀.integral_comp_comm i2, ← integral_add i1 (J₀.integrable_comp i2)]
    congr 1
    funext t
    simp [hH, map_smul, smul_add]
  -- the estimate for each mollification
  have hbound : ∀ n, eLpNorm ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] gs) q volume +
      eLpNorm ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] gt) q volume ≤
      ENNReal.ofReal C * eLpNorm H q volume := by
    intro n
    have hwc : HasCompactSupport ((ρ n).normed volume) := (ρ n).hasCompactSupport_normed
    have hcd : ContDiff ℝ 1 ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] ξ) :=
      hwc.contDiff_convolution_left (lsmul ℝ ℝ) (ρ n).contDiff_normed hξli
    have hcc : HasCompactSupport ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] ξ) :=
      hwc.convolution (lsmul ℝ ℝ) hc
    have h1 := hC _ hcd hcc
    have hd := fun z => fderiv_normed_convolution_eq_of_hasWeakPartialsOn (ρ n) hWu hξli z
    simp only [fun z => (hd z).1, fun z => (hd z).2] at h1
    refine h1.trans ?_
    gcongr
    have : (fun z => ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] gs) z +
        J₀ (((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] gt) z)) =
        (ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] H := funext (hlin n)
    rw [this]
    exact eLpNorm_normed_convolution_le (ρ n) hq1 hqt hHm
  -- pass to the limit
  have hlim : ∀ {g : ℂ → E}, LocallyIntegrable g volume →
      (∀ n, eLpNorm ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] g) q volume ≤
        ENNReal.ofReal C * eLpNorm H q volume) →
      eLpNorm g q volume ≤ ENNReal.ofReal C * eLpNorm H q volume := by
    intro g hg hgn
    have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hρr hρK hg
    refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => ?_) g hconv).trans ?_
    · exact ((ρ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
        ((ρ n).contDiff_normed (n := 0)) hg).continuous.aestronglyMeasurable
    · exact liminf_le_of_frequently_le' (Frequently.of_forall hgn)
  have hs' := hlim hgsli fun n => le_trans le_self_add (hbound n)
  have ht' := hlim hgtli fun n => le_trans le_add_self (hbound n)
  rw [hLs, hLt]
  calc eLpNorm gs q volume + eLpNorm gt q volume
      ≤ ENNReal.ofReal C * eLpNorm H q volume + ENNReal.ofReal C * eLpNorm H q volume :=
        add_le_add hs' ht'
    _ = (2 * ENNReal.ofReal C) * eLpNorm H q volume := by ring
    _ ≤ ENNReal.ofReal (2 * max C 0) *
        eLpNorm (fun z => ξs z + J₀ (ξt z)) q (volume.restrict U) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        gcongr
        exact le_max_left _ _

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (J₀ : E →L[ℝ] E)
    (hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ U : Set ℂ, IsOpen U → ∀ ξ ξs ξt : ℂ → E, Continuous ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ U → HasWeakPartialsOn U ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict U) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm ξs (ENNReal.ofReal p) (volume.restrict U) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict U) ≤
        ENNReal.ofReal C * eLpNorm (fun z => ξs z + J₀ (ξt z)) (ENNReal.ofReal p)
          (volume.restrict U) :=
  JHolomorphic.eLpNorm_weakPartials_le_of_hasCompactSupport_aux p hp J₀ hJ₀
