-- Prove2me | solution 1 for OAI.SoftChannel204.thinning_interval_aux
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:53:11.454459+00:00
-- url     : https://prove2.me/submissions/3d0c9c11-5ce7-46c0-82a6-cdab4cb6ab0c

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Thinning.lean:L343-L433
-- (upload_full_project.md Phase 4): solution for node OAI.SoftChannel204.thinning_interval_aux. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
import Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
import Definitions.Def_OAI_InformationTheory_SoftChannel_Thinning
import Theorems.Thm_OAI_SoftChannel204_thinning_derivative_product

-- ---- from OAI.InformationTheory.SoftChannel.Thinning ----
namespace OAI

section

noncomputable section
open Set
namespace SoftChannel204

open MeasureTheory

theorem continuousAt_clipKernel (β : ℝ) {v : ℝ} (hv : 0 < v) :
    ContinuousAt (clipKernel β) v := by
  unfold clipKernel
  exact ((continuousAt_id.sub continuousAt_const).max continuousAt_const).div
    (continuousAt_id.pow 2) (pow_ne_zero _ hv.ne')

theorem intervalIntegrable_clipKernel (β : ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (clipKernel β) volume u v := by
  apply ContinuousOn.intervalIntegrable
  intro w hw
  exact (continuousAt_clipKernel β
    (lt_of_lt_of_le (lt_min hu hv) hw.1)).continuousWithinAt

theorem hasDerivAt_clipPrimitive (β : ℝ) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (clipPrimitive β) (clipKernel β w) w := by
  apply intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_clipKernel β (by norm_num) hw)
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun v hv => continuousAt_clipKernel β hv) w hw
  · exact continuousAt_clipKernel β hw

theorem thinning_interval_aux {x β u z : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hβ1 : β ≤ 1) (hcut : 4 * x / (3 + x) ≤ β)
    (hz0 : 0 ≤ z) (hzg : z < (1 - x) / (1 + x))
    (hulo : 1 - x - (1 + x) * z ≤ u) (huhi : u ≤ 1 - z) :
    (∫ v in u..u+z, clipKernel β v) ≤
      -(3 / 2 : ℝ) * Real.log (1 - ((1 - x) / (1 + x)) * z) := by
  let γ := (1 - x) / (1 + x)
  let a := (2 - u) / (1 + z)
  let U : ℝ → ℝ := fun s => 2 - a * (1 + s)
  let V : ℝ → ℝ := fun s => U s + s
  let f : ℝ → ℝ := fun s => clipPrimitive β (V s) - clipPrimitive β (U s) +
    (3 / 2) * Real.log (1 - γ * s)
  let f' : ℝ → ℝ := fun s =>
    a * clipKernel β (U s) - (a - 1) * clipKernel β (V s) -
      (3 / 2) * γ / (1 - γ * s)
  have hp : 0 < 1 + x := by positivity
  have hσ : 0 < 1 - x := by linarith
  have hγ0 : 0 < γ := div_pos hσ hp
  have hγ1 : γ ≤ 1 := by dsimp [γ]; exact (div_le_one hp).mpr (by linarith)
  have hz1 : z < 1 := hzg.trans_le hγ1
  have ha1 : 1 ≤ a := (le_div_iff₀ (by positivity : 0 < 1 + z)).mpr (by linarith)
  have hap : a ≤ 1 + x := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + z)).mpr
    nlinarith
  have bounds (s : ℝ) (hs : s ∈ Icc 0 z) :
      0 < U s ∧ U s ≤ V s ∧ V s ≤ 1 ∧ 0 < 1 - γ * s := by
    have hsγ : s < γ := hs.2.trans_lt hzg
    have hps := (lt_div_iff₀ hp).mp hsγ
    have ha := mul_le_mul_of_nonneg_right hap (show 0 ≤ 1 + s by linarith [hs.1])
    have hb := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 1 + s by linarith [hs.1])
    have hγs := mul_le_mul_of_nonneg_right hγ1 hs.1
    dsimp [U, V]
    exact ⟨by nlinarith, by linarith [hs.1], by nlinarith,
      by nlinarith [hs.2]⟩
  have hd (s : ℝ) (hs : s ∈ Icc 0 z) : HasDerivAt f (f' s) s := by
    obtain ⟨hu0, huv, hv1, hlog⟩ := bounds s hs
    have hu : HasDerivAt U (-a) s := by
      convert! (((hasDerivAt_id s).const_add 1).const_mul a).const_sub 2 using 1;
        simp
    have hv : HasDerivAt V (1 - a) s := by
      convert! hu.add (hasDerivAt_id s) using 1; ring
    have hl := ((((hasDerivAt_id s).const_mul γ).const_sub 1).log hlog.ne').const_mul
      (3 / 2 : ℝ)
    convert! (((hasDerivAt_clipPrimitive β (hu0.trans_le huv)).comp s hv).sub
      ((hasDerivAt_clipPrimitive β hu0).comp s hu)).add hl using 1;
      simp [f']; ring
  have hnonpos (s : ℝ) (hs : s ∈ Icc 0 z) : f' s ≤ 0 := by
    have hb := thinning_derivative_product hx0 hx1 ha1 hap hs.1
      (hs.2.trans_lt hzg) hβ1 hcut
    change (a * clipKernel β (U s) - (a - 1) * clipKernel β (V s)) *
      ((1 + x) / (1 - x) - s) ≤ 3 / 2 at hb
    have hY : 0 < (1 + x) / (1 - x) - s := by
      have hr : 1 ≤ (1 + x) / (1 - x) := (le_div_iff₀ hσ).mpr (by linarith)
      linarith [hs.2]
    have hid : (3 / 2 : ℝ) * γ / (1 - γ * s) =
        (3 / 2 : ℝ) / ((1 + x) / (1 - x) - s) := by
      dsimp [γ]
      field_simp
    have hb' := (le_div_iff₀ hY).mpr hb
    dsimp [f']
    rw [hid]
    linarith
  have hanti : AntitoneOn f (Icc 0 z) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc _ _)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s ⟨hs.1.le, hs.2.le⟩).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact hnonpos s ⟨hs.1.le, hs.2.le⟩
  have hle := hanti (show (0 : ℝ) ∈ Icc 0 z from ⟨le_rfl, hz0⟩)
    (show z ∈ Icc 0 z from ⟨hz0, le_rfl⟩) hz0
  have hU : U z = u := by
    dsimp [U, a]
    field_simp
    ring
  have hV : V z = u + z := by simp [V, hU]
  have hu0 : 0 < u := hU ▸ (bounds z ⟨hz0, le_rfl⟩).1
  have hv0 : 0 < u + z := by linarith
  have hprim : clipPrimitive β (u + z) - clipPrimitive β u =
      ∫ v in u..u+z, clipKernel β v := by
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_clipKernel β (show (0 : ℝ) < 1 by norm_num) hu0)
      (intervalIntegrable_clipKernel β hu0 hv0)
    dsimp [clipPrimitive]
    linarith
  dsimp [f] at hle
  rw [hU, hV, hprim] at hle
  simp [V] at hle
  linarith

end SoftChannel204
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SoftChannel204
open Set
open MeasureTheory


theorem solution : type_of% @_root_.OAI.SoftChannel204.thinning_interval_aux := @_root_.OAI.SoftChannel204.thinning_interval_aux
