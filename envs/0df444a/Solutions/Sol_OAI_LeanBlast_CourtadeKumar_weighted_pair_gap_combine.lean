-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.weighted_pair_gap_combine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:38:14.772991+00:00
-- url     : https://prove2.me/submissions/5fafabb6-5763-46c1-8595-4aa6012ae7bd

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/JensenGaps.lean:L359-L393
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.weighted_pair_gap_combine. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.PairEntropy ----
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem pair_mean_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a ∈ Set.Ioo (-1) 1 := by
  have ha : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) h
  exact abs_lt.mp ha

theorem pair_denom_add_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 + a := by
  have ha := (pair_mean_mem_Ioo a b h).1
  linarith

theorem pair_denom_sub_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a := by
  have ha := (pair_mean_mem_Ioo a b h).2
  linarith

theorem pair_abs_lt_denom_add (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 + a := by
  linarith [neg_le_abs a]

theorem pair_abs_lt_denom_sub (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 - a := by
  linarith [le_abs_self a]

theorem pair_variance_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a ^ 2 := by
  have hp := mul_pos (pair_denom_add_pos a b h) (pair_denom_sub_pos a b h)
  nlinarith

private theorem weighted_psi_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    s / 2 * psi (b / s) =
      (s + b) / 4 * Real.log (s + b) + (s - b) / 4 * Real.log (s - b) -
        s / 2 * Real.log s := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [psi, hplus, hminus, Real.log_div hp hs0, Real.log_div hm hs0]
  field_simp
  ring

theorem pairEntropyGap_weighted (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b =
      (1 + a) / 2 * psi (b / (1 + a)) + (1 - a) / 2 * psi (b / (1 - a)) := by
  rw [weighted_psi_div (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h),
    weighted_psi_div (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)]
  unfold pairEntropyGap entropy psi
  ring_nf

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.JensenGaps ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace LeanBlast.CourtadeKumar

section Weighted

variable {ι : Type u} [Fintype ι]

private theorem pair_reciprocal_square_identity (a b : ℝ) (h : |a| + |b| < 1) :
    b ^ 2 / (1 + a) + b ^ 2 / (1 - a) = 2 * (b ^ 2 / (1 - a ^ 2)) := by
  have hp := (pair_denom_add_pos a b h).ne'
  have hm := (pair_denom_sub_pos a b h).ne'
  have hv := (pair_variance_pos a b h).ne'
  field_simp
  ring

private theorem weighted_pair_gap_combine (w a b : ι → ℝ) (m k C : ℝ)
    (hdom : ∀ i, |a i| + |b i| < 1) (hcenter : |m| + |k| < 1)
    (hp : ((∑ i, w i * (b i) ^ 2 / (1 + a i)) - k ^ 2 / (1 + m)) * C ≤
      2 * ((∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) -
        (1 + m) * psi (k / (1 + m))))
    (hm : ((∑ i, w i * (b i) ^ 2 / (1 - a i)) - k ^ 2 / (1 - m)) * C ≤
      2 * ((∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) -
        (1 - m) * psi (k / (1 - m)))) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) - k ^ 2 / (1 - m ^ 2)) * C ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) - pairEntropyGap m k) := by
  have hv : (∑ i, w i * (b i) ^ 2 / (1 + a i)) +
      (∑ i, w i * (b i) ^ 2 / (1 - a i)) =
      2 * (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = w i * ((b i) ^ 2 / (1 + a i) + (b i) ^ 2 / (1 - a i)) := by ring
      _ = _ := by rw [pair_reciprocal_square_identity (a i) (b i) (hdom i)]; ring
  have hvc := pair_reciprocal_square_identity m k hcenter
  have he : (∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) +
      (∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) =
      2 * (∑ i, w i * pairEntropyGap (a i) (b i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pairEntropyGap_weighted (a i) (b i) (hdom i)]
    ring
  have hec : (1 + m) * psi (k / (1 + m)) + (1 - m) * psi (k / (1 - m)) =
      2 * pairEntropyGap m k := by
    rw [pairEntropyGap_weighted m k hcenter]
    ring
  have hvC := congrArg (fun z : ℝ => z * C) hv
  have hvcC := congrArg (fun z : ℝ => z * C) hvc
  nlinarith only [hp, hm, hvC, hvcC, he, hec]

end Weighted

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.weighted_pair_gap_combine.{u} := @_root_.OAI.LeanBlast.CourtadeKumar.weighted_pair_gap_combine.{u}
