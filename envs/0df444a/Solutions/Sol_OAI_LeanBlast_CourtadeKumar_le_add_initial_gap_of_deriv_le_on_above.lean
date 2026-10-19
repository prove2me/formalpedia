-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.le_add_initial_gap_of_deriv_le_on_above
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:49:48.480153+00:00
-- url     : https://prove2.me/submissions/65373df7-9e8e-4572-b155-d619c4c4f796

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Comparison.lean:L25-L59
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.le_add_initial_gap_of_deriv_le_on_above. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison

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

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter MeasureTheory
open scoped Topology BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.le_add_initial_gap_of_deriv_le_on_above := @_root_.OAI.LeanBlast.CourtadeKumar.le_add_initial_gap_of_deriv_le_on_above
