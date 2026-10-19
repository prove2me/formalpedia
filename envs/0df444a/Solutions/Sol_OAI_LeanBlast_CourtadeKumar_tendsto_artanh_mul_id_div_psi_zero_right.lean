-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.tendsto_artanh_mul_id_div_psi_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:05:02.38026+00:00
-- url     : https://prove2.me/submissions/2ccef8ff-5e45-49af-bb72-5930e4d9adec

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/EndpointLimits.lean:L39-L71
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.tendsto_artanh_mul_id_div_psi_zero_right. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_artanh
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_psi

-- ---- from OAI.InformationTheory.BooleanNoise.EndpointLimits ----
namespace OAI

noncomputable section

open Filter Set
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem tendsto_artanh_div_id_zero_right :
    Tendsto (fun u : ℝ => Real.artanh u / u) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

theorem tendsto_id_div_artanh_zero_right :
    Tendsto (fun u : ℝ => u / Real.artanh u) (𝓝[>] 0) (𝓝 1) := by
  simpa only [inv_div, inv_one] using
    tendsto_artanh_div_id_zero_right.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)

theorem tendsto_entropy_inverse_derivative_zero_right :
    Tendsto (fun u : ℝ => 1 + u / ((1 - u ^ 2) * Real.artanh u))
      (𝓝[>] 0) (𝓝 2) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hden : Tendsto (fun u : ℝ => 1 - u ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hu.pow 2)
  have hquot := tendsto_id_div_artanh_zero_right.div hden (show (1 : ℝ) ≠ 0 by norm_num)
  have hadd :
    Tendsto (fun u : ℝ => 1 + (u / Real.artanh u) / (1 - u ^ 2))
      (𝓝[>] 0) (𝓝 ((1 : ℝ) + 1 / 1)) := tendsto_const_nhds.add hquot
  norm_num [div_div, mul_comm] at hadd ⊢
  exact hadd

theorem tendsto_artanh_mul_id_div_psi_zero_right :
    Tendsto (fun u : ℝ => (u * Real.artanh u) / psi u) (𝓝[>] 0) (𝓝 2) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hda : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  have ha : Tendsto Real.artanh (𝓝[>] 0) (𝓝 0) := by
    simpa using hda.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto psi (𝓝[>] 0) (𝓝 0) := by
    simpa [psi] using
      (hasDerivAt_psi (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have hquot : Tendsto
      (fun u : ℝ => (Real.artanh u + u / (1 - u ^ 2)) / Real.artanh u)
      (𝓝[>] 0) (𝓝 2) := by
    apply tendsto_entropy_inverse_derivative_zero_right.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    have hne : Real.artanh u ≠ 0 := ne_of_gt (Real.artanh_pos hu)
    rw [add_div, div_self hne, div_div]
  apply HasDerivAt.lhopital_zero_right_on_Ioo
    (f' := fun u => Real.artanh u + u / (1 - u ^ 2))
    (g' := Real.artanh) (show (0 : ℝ) < 1 by norm_num)
  · intro u hu
    convert! (hasDerivAt_id u).mul
      (hasDerivAt_artanh (show u ∈ Ioo (-1) 1 from ⟨by linarith [hu.1], hu.2⟩)) using 1
    simp [id_eq, div_eq_mul_inv]
  · intro u hu
    exact hasDerivAt_psi ⟨by linarith [hu.1], hu.2⟩
  · intro u hu
    exact ne_of_gt (Real.artanh_pos hu)
  · simpa using hu.mul ha
  · exact hp
  · exact hquot

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Filter Set
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.tendsto_artanh_mul_id_div_psi_zero_right := @_root_.OAI.LeanBlast.CourtadeKumar.tendsto_artanh_mul_id_div_psi_zero_right
