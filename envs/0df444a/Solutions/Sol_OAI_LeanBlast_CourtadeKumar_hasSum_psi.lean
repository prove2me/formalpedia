-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.hasSum_psi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:07:04.445335+00:00
-- url     : https://prove2.me/submissions/6e2ba94f-6b63-44de-b530-0a8b9ae46669

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/EntropySeries.lean:L54-L73
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.hasSum_psi. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EntropySeries ----
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem hasSum_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.artanh v) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hv).mul_left (1 / 2)
  convert! h using 1
  · ext k
    ring
  · rw [artanh_eq_log_sub (abs_lt.mp hv)]
    ring

theorem psi_eq_mul_artanh_add_log {v : ℝ} (hv : |v| < 1) :
    psi v = v * Real.artanh v + 1 / 2 * Real.log (1 - v ^ 2) := by
  have hp : 1 + v ≠ 0 := by linarith [(abs_lt.mp hv).1]
  have hm : 1 - v ≠ 0 := by linarith [(abs_lt.mp hv).2]
  have hl : Real.log (1 - v ^ 2) = Real.log (1 + v) + Real.log (1 - v) := by
    rw [← Real.log_mul hp hm]
    congr 1
    ring
  rw [artanh_eq_log_sub (abs_lt.mp hv), hl]
  unfold psi
  ring

theorem hasSum_psi {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  have hv2 : |v ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg v)]
    have h1 : 0 < 1 + v := by linarith [(abs_lt.mp hv).1]
    have h2 : 0 < 1 - v := by linarith [(abs_lt.mp hv).2]
    nlinarith [mul_pos h1 h2]
  have h := ((hasSum_artanh hv).mul_left v).add
    ((Real.hasSum_pow_div_log_of_abs_lt_one hv2).mul_left (-(1 / 2)))
  convert! h using 1
  · ext k
    have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
    unfold psiCoeff
    field_simp
    ring
  · rw [psi_eq_mul_artanh_add_log hv]
    ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter Finset
open scoped Topology BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.hasSum_psi := @_root_.OAI.LeanBlast.CourtadeKumar.hasSum_psi
