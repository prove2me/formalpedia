-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.artanh_le_cubic_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:13:22.241838+00:00
-- url     : https://prove2.me/submissions/76549d70-0ec9-4855-97d9-05831cad67a9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/SmallCurvatureAux.lean:L7-L34
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.artanh_le_cubic_tail. The node keeps its source
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

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.SmallCurvatureAux ----
namespace OAI

namespace LeanBlast.CourtadeKumar

theorem artanh_le_cubic_tail {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    Real.artanh u ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := by
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := hu.2
  have huabs : |u| < 1 := by rwa [abs_of_nonneg hu0]
  have hu2 : u ^ 2 < 1 := by nlinarith [sq_nonneg (u - 1)]
  have hseries := hasSum_artanh huabs
  have htail : HasSum
      (fun k : ℕ => u ^ (2 * (k + 1) + 1) / (2 * ((k + 1 : ℕ) : ℝ) + 1))
      (Real.artanh u - u) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hseries
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg u) hu2).mul_left (u ^ 3 / 3)
  have hle : Real.artanh u - u ≤ (u ^ 3 / 3) * (1 - u ^ 2)⁻¹ := by
    apply hasSum_le _ htail hgeom
    intro k
    have hpow : u ^ (2 * (k + 1) + 1) = u ^ 3 * (u ^ 2) ^ k := by
      rw [show 2 * (k + 1) + 1 = 3 + 2 * k by omega, pow_add, pow_mul]
    rw [hpow]
    calc
      _ ≤ (u ^ 3 * (u ^ 2) ^ k) / 3 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      _ = _ := by ring
  calc
    Real.artanh u = u + (Real.artanh u - u) := by ring
    _ ≤ u + (u ^ 3 / 3) * (1 - u ^ 2)⁻¹ := by linarith
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end LeanBlast.CourtadeKumar

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.artanh_le_cubic_tail := @_root_.OAI.LeanBlast.CourtadeKumar.artanh_le_cubic_tail
