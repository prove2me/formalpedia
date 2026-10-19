-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.r_psi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:03:30.834907+00:00
-- url     : https://prove2.me/submissions/630c9772-4acb-473b-a14b-f23202c93251

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/InverseScalars.lean:L142-L154
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.r_psi. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.InverseScalars ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem r_psi_nonneg {u : ℝ} (hu : u ∈ Icc 0 1) :
    r (psi u) = u * Real.artanh u := by rw [r, psiInv_psi hu]

theorem r_psi {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    r (psi u) = u * Real.artanh u := by
  by_cases h0 : 0 ≤ u
  · exact r_psi_nonneg ⟨h0, hu.2.le⟩
  · have hn : -u ∈ Ioo (-1) 1 := by constructor <;> linarith [hu.1, hu.2]
    have hodd : Real.artanh (-u) = -Real.artanh u := by
      rw [artanh_eq_log_sub hn, artanh_eq_log_sub hu]
      simp only [sub_eq_add_neg, neg_neg]
      ring
    calc
      r (psi u) = r (psi (-u)) := by rw [psi_neg]
      _ = (-u) * Real.artanh (-u) := r_psi_nonneg ⟨by linarith, hn.2.le⟩
      _ = u * Real.artanh u := by rw [hodd]; ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.r_psi := @_root_.OAI.LeanBlast.CourtadeKumar.r_psi
