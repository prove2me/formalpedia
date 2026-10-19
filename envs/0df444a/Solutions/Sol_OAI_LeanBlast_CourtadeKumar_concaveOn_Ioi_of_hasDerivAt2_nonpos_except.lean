-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.concaveOn_Ioi_of_hasDerivAt2_nonpos_except
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:41:43.733279+00:00
-- url     : https://prove2.me/submissions/e55eb1ed-a333-4ec3-ba59-cdbf37f03030

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/ConcavityAcrossJoin.lean:L42-L59
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.concaveOn_Ioi_of_hasDerivAt2_nonpos_except. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.ConcavityAcrossJoin ----
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem antitoneOn_Ioi_of_hasDerivAt_nonpos_except
    (f f' : ℝ → ℝ) (a c : ℝ)
    (hf : ContinuousOn f (Ioi a))
    (hd : ∀ x, a < x → x ≠ c → HasDerivAt f (f' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f' x ≤ 0) :
    AntitoneOn f (Ioi a) := by
  have hsegment (l r : ℝ) (hal : a < l) (hlr : l ≤ r)
      (hc : c ∉ Ioo l r) : f r ≤ f l := by
    have hanti : AntitoneOn f (Icc l r) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc l r)
      · exact hf.mono (fun _ hz => hal.trans_le hz.1)
      · intro z hz
        rw [interior_Icc] at hz
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        exact (hd z (hal.trans hz.1) hzc).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        exact hneg z (hal.trans hz.1) hzc
    exact hanti ⟨le_rfl, hlr⟩ ⟨hlr, le_rfl⟩ hlr
  intro x hx y hy hxy
  by_cases hc : c ∈ Ioo x y
  · exact (hsegment c y (hx.trans hc.1) hc.2.le (by simp)).trans
      (hsegment x c hx hc.1.le (by simp))
  · exact hsegment x y hx hxy hc

theorem concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (f f' f'' : ℝ → ℝ) (a c : ℝ)
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x)
    (hcf' : ContinuousOn f' (Ioi a))
    (hd' : ∀ x, a < x → x ≠ c → HasDerivAt f' (f'' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f'' x ≤ 0) :
    ConcaveOn ℝ (Ioi a) f := by
  have hanti := antitoneOn_Ioi_of_hasDerivAt_nonpos_except f' f'' a c hcf' hd' hneg
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi a)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [interior_Ioi] at hx hy
    rw [(hd x hx).deriv, (hd y hy).deriv]
    exact hanti hx hy hxy

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.concaveOn_Ioi_of_hasDerivAt2_nonpos_except := @_root_.OAI.LeanBlast.CourtadeKumar.concaveOn_Ioi_of_hasDerivAt2_nonpos_except
