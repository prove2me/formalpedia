-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_zero_of_right_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:26:35.236397+00:00
-- url     : https://prove2.me/submissions/a87543fd-9aa6-4b14-9a9a-139feaa9af1e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/KRegularity.lean:L102-L116
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_zero_of_right_derivative. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.InverseScalars ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem K_eq_rGap {s : ℝ} (hs : 0 < s) (hs0 : s ≤ s0) : K s = rGap s := by
  simp [K, not_le.mpr hs, hs0]

theorem s0_pos : 0 < s0 := by
  change 0 < psi (1 / 5)
  rw [← psi_zero]
  exact strictMonoOn_psi (by norm_num) (by norm_num) (by norm_num)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.KRegularity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem K_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : K s = 0 := by simp [K, hs]

theorem K_eq_rGap_nonneg {s : ℝ} (hs : 0 ≤ s) (hsc : s ≤ s0) : K s = rGap s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · exact K_eq_rGap hs hsc

theorem hasDerivAt_K_zero_of_right_derivative
    (hzero : HasDerivWithinAt rGap 0 (Ici 0) 0) : HasDerivAt K 0 0 := by
  have hleft : HasDerivWithinAt K 0 (Iic 0) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
    · intro s hs
      exact K_eq_zero_of_nonpos hs
    · simp
  have hright : HasDerivWithinAt K 0 (Ici 0) 0 := by
    apply hzero.congr_of_eventuallyEq
    · have hnear : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] 0, s < s0 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds s0_pos)
      filter_upwards [self_mem_nhdsWithin, hnear] with s hs hs0
      exact K_eq_rGap_nonneg hs hs0.le
    · simp
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

end LeanBlast.CourtadeKumar

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_zero_of_right_derivative := @_root_.OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_zero_of_right_derivative
