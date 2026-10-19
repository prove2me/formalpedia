-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.exists_reflected_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:46:42.307983+00:00
-- url     : https://prove2.me/submissions/eb986ccb-f5ea-4e86-b137-d0e51b31fe7e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Canonical.lean:L628-L650
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.exists_reflected_entropy. The node keeps its source
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

-- ---- from OAI.InformationTheory.SoftChannel.Canonical ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

lemma exists_reflected_entropy {m d e : ℝ} (_hm : 0 ≤ m) (hd : 0 < d) (hmd : m+d < 1)
    (he : 0 < e) (he0 : e ≤ (1-m)*entropy (d/(1-m))) :
    ∃ r ∈ Ico (d/(1-m)) 1, reflectedEntropy d r = e := by
  have hm0 : 0 < 1-m := by linarith
  have hr0 : 0 < d/(1-m) := div_pos hd hm0
  have hr1 : d/(1-m) < 1 := (div_lt_one hm0).mpr (by linarith)
  have hc : ContinuousOn (reflectedEntropy d) (Icc (d/(1-m)) 1) := by
    intro r hr
    have hnr : r ≠ 0 := by linarith [hr.1]
    unfold reflectedEntropy
    exact ((continuousAt_const.div continuousAt_id hnr).mul continuous_entropy.continuousAt).continuousWithinAt
  have hleft : reflectedEntropy d (d/(1-m)) = (1-m)*entropy (d/(1-m)) := by
    unfold reflectedEntropy
    field_simp
  have hright : reflectedEntropy d 1 = 0 := by simp [reflectedEntropy]
  obtain ⟨r,hr,hre⟩ := intermediate_value_Icc' hr1.le hc
    (show e ∈ Icc (reflectedEntropy d 1) (reflectedEntropy d (d/(1-m))) by
      rw [hleft,hright]; exact ⟨he.le,he0⟩)
  refine ⟨r,⟨hr.1,lt_of_le_of_ne hr.2 ?_⟩,hre⟩
  intro hrEq
  subst r
  rw [hright] at hre
  linarith

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.exists_reflected_entropy := @_root_.OAI.LeanBlast.CourtadeKumar.exists_reflected_entropy
