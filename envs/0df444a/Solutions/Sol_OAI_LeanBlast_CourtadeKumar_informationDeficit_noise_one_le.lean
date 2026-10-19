-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:47:51.674831+00:00
-- url     : https://prove2.me/submissions/6d84ca81-5f12-4586-b2d5-f54dc9c4ea47

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Attainment.lean:L92-L104
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_one_le. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem psi_nonneg (v : ℝ) : 0 ≤ psi v := by
  have h := Real.binEntropy_le_log_two (p := (1 + v) / 2)
  rw [← entropy_eq_binEntropy] at h
  unfold entropy ell at *
  linarith

theorem entropy_le_ell (v : ℝ) : entropy v ≤ ell := by
  exact sub_le_self _ (psi_nonneg v)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.Attainment ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem informationDeficit_noise_one_le (g : Cube n → ℝ) (hg : IsSignValued g) :
    informationDeficit (noiseOperator 1 g) ≤ psi 1 := by
  have hnoise : noiseOperator 1 g = g := by
    funext x
    exact noiseOperator_one g x
  have he : entropyAverage g = 0 := by
    have hpoint : (fun x => entropy (g x)) = fun _ : Cube n => 0 := by
      funext x
      rcases hg x with h | h <;> simp [h]
    unfold entropyAverage
    rw [hpoint, cubeAverage_const]
  rw [hnoise, informationDeficit, he, sub_zero, psi_one]
  exact entropy_le_ell _

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_one_le := @_root_.OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_one_le
