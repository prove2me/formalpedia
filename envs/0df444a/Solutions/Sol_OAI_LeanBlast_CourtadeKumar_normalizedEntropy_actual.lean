-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.normalizedEntropy_actual
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:44:38.832221+00:00
-- url     : https://prove2.me/submissions/82e1e82b-19b6-46b9-bb31-d405d904e001

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Canonical.lean:L441-L469
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.normalizedEntropy_actual. The node keeps its source
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

lemma bose_pos {z : ℝ} (hz : 0 < z) : 0 < bose z := by
  exact inv_pos.mpr (sub_pos.mpr (Real.one_lt_exp_iff.mpr hz))

lemma entropy_degree {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (s+t) * entropy ((s-t)/(s+t)) =
      (s+t)*Real.log (s+t) - s*Real.log s - t*Real.log t := by
  have hst : s+t ≠ 0 := ne_of_gt (add_pos hs ht)
  rw [entropy_eq_binEntropy]
  rw [show (1+(s-t)/(s+t))/2 = s/(s+t) by field_simp; ring]
  unfold Real.binEntropy
  rw [show 1-s/(s+t)=t/(s+t) by field_simp; ring]
  rw [Real.log_inv, Real.log_inv, Real.log_div hs.ne' hst, Real.log_div ht.ne' hst]
  field_simp
  ring

lemma joiningZ_pos {x y : ℝ} (hy : -1 < y) (hxy : y < x) : 0 < joiningZ x y := by
  apply Real.log_pos
  apply (lt_div_iff₀ (by linarith : 0 < 1+y)).mpr
  linarith

lemma joiningW_pos {x y : ℝ} (hx : x < 1) (hxy : y < x) : 0 < joiningW x y := by
  apply Real.log_pos
  apply (lt_div_iff₀ (by linarith : 0 < 1-x)).mpr
  linarith

lemma bose_joiningZ {x y : ℝ} (hy : -1 < y) (hxy : y < x) :
    bose (joiningZ x y) = (1+y)/(x-y) := by
  have hp : 0 < (1+x)/(1+y) := div_pos (by linarith) (by linarith)
  unfold bose joiningZ
  rw [Real.exp_log hp]
  have hd : 1+y ≠ 0 := by linarith
  rw [show (1+x)/(1+y)-1=(x-y)/(1+y) by field_simp; ring, inv_div]

lemma bose_joiningW {x y : ℝ} (hx : x < 1) (hxy : y < x) :
    bose (joiningW x y) = (1-x)/(x-y) := by
  have hp : 0 < (1-y)/(1-x) := div_pos (by linarith) (by linarith)
  unfold bose joiningW
  rw [Real.exp_log hp]
  have hd : 1-x ≠ 0 := by linarith
  rw [show (1-y)/(1-x)-1=(x-y)/(1-x) by field_simp; ring, inv_div]

lemma normalizedEntropy_actual {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1)
    (hxy : y < x) :
    normalizedEntropy (joiningZ x y) (joiningW x y) = (entropy x + entropy y)/(x-y) := by
  let u := bose (joiningZ x y)
  let v := bose (joiningW x y)
  have hu : 0 < u := bose_pos (joiningZ_pos hy.1 hxy)
  have hv : 0 < v := bose_pos (joiningW_pos hx.2 hxy)
  have hU : u = (1+y)/(x-y) := bose_joiningZ hy.1 hxy
  have hV : v = (1-x)/(x-y) := bose_joiningW hx.2 hxy
  have hd : x-y ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
  have hn : 1+u+v = 2/(x-y) := by rw [hU, hV]; field_simp; ring
  have hn' : 1+u+v ≠ 0 := by linarith
  have hX : (u+1-v)/(u+1+v) = x := by
    rw [hU, hV]
    field_simp
    ring
  have hY : (u-(v+1))/(u+(v+1)) = y := by
    rw [hU, hV]
    field_simp
    ring
  have h₁ := entropy_degree (s := u+1) (t := v) (by linarith) hv
  have h₂ := entropy_degree (s := u) (t := v+1) hu (by linarith)
  rw [hX, show u+1+v=1+u+v by ring] at h₁
  rw [hY, show u+(v+1)=1+u+v by ring] at h₂
  change (1+u+v)*Real.log (1+u+v) -
    ((u+1)*Real.log (u+1)+u*Real.log u+(v+1)*Real.log (v+1)+v*Real.log v)/2 = _
  calc
    _ = (1+u+v)*(entropy x+entropy y)/2 := by nlinarith [h₁,h₂]
    _ = _ := by rw [hn]; field_simp

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.normalizedEntropy_actual := @_root_.OAI.LeanBlast.CourtadeKumar.normalizedEntropy_actual
