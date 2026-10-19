-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.le_of_deriv_le_on_above_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:36:52.629932+00:00
-- url     : https://prove2.me/submissions/6fe5374e-18f2-4f4f-832b-b1475b5804d4

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Comparison.lean:L70-L91
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.le_of_deriv_le_on_above_of_tendsto. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.Comparison ----
namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem le_add_initial_gap_of_deriv_le_on_above
    {f g f' g' : ℝ → ℝ} {a b δ : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hderiv : ∀ t ∈ Ico a b, g t ≤ f t → f' t ≤ g' t)
    (hδ : 0 ≤ δ) (ha : f a ≤ g a + δ) :
    ∀ t ∈ Icc a b, f t ≤ g t + δ := by
  have hfcont : ContinuousOn f (Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g (Icc a b) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hpert : ∀ t ∈ Icc a b, ∀ ε > 0,
      f t ≤ g t + δ + ε * (t - a) := by
    intro t ht ε hε
    apply image_le_of_deriv_right_lt_deriv_boundary' hfcont
      (fun x hx => (hf x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt)
      (B := fun x => g x + δ + ε * (x - a))
      (B' := fun x => g' x + ε)
    · simpa using ha
    · exact (hgcont.add continuousOn_const).add
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · intro x hx
      convert! (((hg x ⟨hx.1, hx.2.le⟩).add_const δ).add
        (((hasDerivAt_id x).sub_const a).const_mul ε)).hasDerivWithinAt using 1
      simp
    · intro x hx heq
      have hnonneg : 0 ≤ ε * (x - a) := mul_nonneg hε.le (sub_nonneg.mpr hx.1)
      have hgf : g x ≤ f x := by rw [heq]; linarith
      have hd := hderiv x hx hgf
      linarith
    · exact ht
  intro t ht
  have hc : ContinuousWithinAt (fun ε : ℝ => g t + δ + ε * (t - a)) (Ioi 0) 0 := by
    fun_prop
  convert! continuousWithinAt_const.closure_le _ hc (hpert t ht) using 1 <;> simp

theorem le_of_deriv_le_on_above_of_tendsto
    {f g f' g' : ℝ → ℝ} {l : ℝ}
    (hf : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hg : ∀ t, 0 < t → HasDerivAt g (g' t) t)
    (hderiv : ∀ t, 0 < t → g t ≤ f t → f' t ≤ g' t)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 l))
    (hg0 : Tendsto g (𝓝[>] 0) (𝓝 l)) :
    ∀ t, 0 < t → f t ≤ g t := by
  intro t ht
  have hlim : Tendsto (fun a => g t + max (f a - g a) 0) (𝓝[>] 0) (𝓝 (g t)) := by
    convert tendsto_const_nhds.add ((hf0.sub hg0).max tendsto_const_nhds) using 1
    simp
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  apply le_add_initial_gap_of_deriv_le_on_above
    (fun x hx => hf x (ha.1.trans_le hx.1))
    (fun x hx => hg x (ha.1.trans_le hx.1))
    (fun x hx => hderiv x (ha.1.trans_le hx.1))
    (le_max_right (f a - g a) 0)
  · have hgmax := le_max_left (f a - g a) 0
    linarith
  · exact ⟨ha.2.le, le_rfl⟩

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter MeasureTheory
open scoped Topology BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.le_of_deriv_le_on_above_of_tendsto := @_root_.OAI.LeanBlast.CourtadeKumar.le_of_deriv_le_on_above_of_tendsto
