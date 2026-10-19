-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.lambdaCertificate_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:55:36.579345+00:00
-- url     : https://prove2.me/submissions/56f8fcb5-3347-493e-8f2d-381afaab9f61

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CurvatureCertificates.lean:L137-L151
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.lambdaCertificate_pos. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_bernsteinSum_pos

-- ---- from OAI.InformationTheory.BooleanNoise.CurvatureCertificates ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

private theorem lambdaBernsteinLow_pos (i : Fin 9) : 0 < lambdaBernsteinLow i := by
  fin_cases i <;> norm_num [lambdaBernsteinLow]

private theorem lambdaBernsteinHigh_pos (i : Fin 9) : 0 < lambdaBernsteinHigh i := by
  fin_cases i <;> norm_num [lambdaBernsteinHigh]

theorem lambdaPolynomial_bernstein_low (t : ℝ) :
    lambdaPolynomial ((3 / 4) * t) = bernsteinSum 8 lambdaBernsteinLow t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [lambdaPolynomial, lambdaBernsteinLow, Fin.sum_univ_succ,
    Nat.descFactorial, Nat.factorial]
  ring

theorem lambdaPolynomial_bernstein_high (t : ℝ) :
    lambdaPolynomial (3 / 4 + (1 / 4) * t) = bernsteinSum 8 lambdaBernsteinHigh t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [lambdaPolynomial, lambdaBernsteinHigh, Fin.sum_univ_succ,
    Nat.descFactorial, Nat.factorial]
  ring

theorem lambdaCertificate_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < lambdaPolynomial b := by
  by_cases hb : b ≤ 3 / 4
  · have ht0 : 0 ≤ (4 / 3 : ℝ) * b := by positivity
    have ht1 : (4 / 3 : ℝ) * b ≤ 1 := by linarith
    have h := bernsteinSum_pos 8 lambdaBernsteinLow lambdaBernsteinLow_pos ht0 ht1
    rw [← lambdaPolynomial_bernstein_low] at h
    have he : (3 / 4 : ℝ) * ((4 / 3) * b) = b := by ring
    simpa only [he] using h
  · have ht0 : 0 ≤ 4 * b - 3 := by linarith
    have ht1 : 4 * b - 3 ≤ 1 := by linarith
    have h := bernsteinSum_pos 8 lambdaBernsteinHigh lambdaBernsteinHigh_pos ht0 ht1
    rw [← lambdaPolynomial_bernstein_high] at h
    have he : (3 / 4 : ℝ) + (1 / 4) * (4 * b - 3) = b := by ring
    simpa only [he] using h

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.lambdaCertificate_pos := @_root_.OAI.LeanBlast.CourtadeKumar.lambdaCertificate_pos
