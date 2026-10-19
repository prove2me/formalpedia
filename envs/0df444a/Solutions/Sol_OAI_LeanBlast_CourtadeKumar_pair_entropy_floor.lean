-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.pair_entropy_floor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:55:18.927259+00:00
-- url     : https://prove2.me/submissions/ebf634aa-07ea-45c2-b71a-33421c2d626f

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Window.lean:L75-L90
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.pair_entropy_floor. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_concaveOn_entropy

-- ---- from OAI.InformationTheory.SoftChannel.Window ----
namespace OAI

section

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

lemma entropy_common_output {a k : ℝ} (ha : a ∈ Icc (-1) 1) (hk : k ∈ Icc (0:ℝ) 1) :
    k*entropy a ≤ entropy (1-k+k*a) := by
  have h := concaveOn_entropy.2 (by norm_num : (1:ℝ) ∈ Icc (-1) 1) ha
    (by linarith [hk.2] : 0 ≤ 1-k) hk.1 (by ring : 1-k+k=1)
  simpa only [smul_eq_mul,mul_one,entropy_one,mul_zero,zero_add] using h

lemma pair_entropy_floor {x d : ℝ} (hx : 0 ≤ x) (hd : 0 ≤ d) (hxd : x+d < 1) :
    (1-x)*entropy (d/(1-x)) ≤ (entropy (x+d)+entropy (x-d))/2 := by
  have hs : 0 < 1-x := by linarith
  have hr : d/(1-x) ∈ Icc (-1) 1 := by
    constructor
    · linarith [div_nonneg hd hs.le]
    · exact (div_le_one hs).mpr (by linarith)
  have hnr : -(d/(1-x)) ∈ Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have hk : 1-x ∈ Icc (0:ℝ) 1 := ⟨hs.le,by linarith⟩
  have h₁ := entropy_common_output hr hk
  have h₂ := entropy_common_output hnr hk
  have he₁ : 1-(1-x)+(1-x)*(d/(1-x)) = x+d := by field_simp; ring
  have he₂ : 1-(1-x)+(1-x)*(-(d/(1-x))) = x-d := by field_simp; ring
  rw [he₁] at h₁
  rw [he₂,entropy_neg] at h₂
  linarith

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set MeasureTheory
open scoped Topology
open SoftChannel204


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.pair_entropy_floor := @_root_.OAI.LeanBlast.CourtadeKumar.pair_entropy_floor
