-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.psi_symmetric_pair_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:31:58.490774+00:00
-- url     : https://prove2.me/submissions/a5273451-be7b-47e9-a21f-3d5428391724

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Rearrangement.lean:L268-L296
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.psi_symmetric_pair_mono. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_concaveOn_entropy

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem convexOn_psi : ConvexOn ℝ (Icc (-1) 1) psi := by
  have h := concaveOn_entropy.neg.add (convexOn_const ell (convex_Icc (-1 : ℝ) 1))
  convert! h using 1
  ext v
  simp [entropy]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.Rearrangement ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem psi_symmetric_pair_mono (a b c : ℝ) (hc : 0 ≤ c)
    (hb : -c ≤ b ∧ b ≤ c)
    (hminus : a - c ∈ Set.Icc (-1 : ℝ) 1)
    (hplus : a + c ∈ Set.Icc (-1 : ℝ) 1) :
    psi (a + b) + psi (a - b) ≤ psi (a + c) + psi (a - c) := by
  by_cases hcz : c = 0
  · have hbz : b = 0 := by rcases hb with ⟨hl, hu⟩; simp only [hcz, neg_zero] at hl hu; linarith
    simp [hcz, hbz]
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
    let t : ℝ := (c + b) / (2 * c)
    let s : ℝ := (c - b) / (2 * c)
    have ht : 0 ≤ t := div_nonneg (by linarith [hb.1]) (by positivity)
    have hs : 0 ≤ s := div_nonneg (by linarith [hb.2]) (by positivity)
    have hts : t + s = 1 := by dsimp [t, s]; field_simp; ring
    have hst : s + t = 1 := by linarith
    have hr1 : t * (a + c) + s * (a - c) = a + b := by
      dsimp [t, s]; field_simp; ring
    have hr2 : s * (a + c) + t * (a - c) = a - b := by
      dsimp [t, s]; field_simp; ring
    have h1 := convexOn_psi.2 hplus hminus ht hs hts
    have h2 := convexOn_psi.2 hplus hminus hs ht hst
    simp only [smul_eq_mul, hr1] at h1
    simp only [smul_eq_mul, hr2] at h2
    calc
      psi (a + b) + psi (a - b) ≤
          (t * psi (a + c) + s * psi (a - c)) +
          (s * psi (a + c) + t * psi (a - c)) := add_le_add h1 h2
      _ = (t + s) * (psi (a + c) + psi (a - c)) := by ring
      _ = psi (a + c) + psi (a - c) := by rw [hts, one_mul]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.psi_symmetric_pair_mono := @_root_.OAI.LeanBlast.CourtadeKumar.psi_symmetric_pair_mono
