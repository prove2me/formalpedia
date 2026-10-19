-- Prove2me | solution 1 for OAI.Problem313.unitQuantile_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:44:16.22599+00:00
-- url     : https://prove2.me/submissions/a4693e63-0705-4703-9a9f-4b1ac06eda8a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/Quantile.lean:L42-L56
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.unitQuantile_mem_Ioo. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Quantile

-- ---- from OAI.Combinatorics.SharpThreshold.Quantile ----
namespace OAI

noncomputable section
namespace Problem313

theorem unitQuantile_set_bddBelow (μ : ℝ → ℝ) (a : ℝ) :
    BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} :=
  ⟨0, fun _ hp => hp.1.1⟩

theorem unitQuantile_set_nonempty {μ : ℝ → ℝ} {a : ℝ}
    (h1 : μ 1 = 1) (ha : a ≤ 1) :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p}.Nonempty := by
  refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
  simpa only [h1] using ha

theorem unitQuantile_mem {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h1 : μ 1 = 1) (ha : a ≤ 1) :
    unitQuantile μ a ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ (unitQuantile μ a) := by
  have hc : IsClosed {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ a ≤ μ p} :=
    isClosed_Icc.inter (isClosed_le continuous_const hμ)
  exact hc.csInf_mem (unitQuantile_set_nonempty h1 ha) (unitQuantile_set_bddBelow μ a)

theorem unitQuantile_eq_level {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    μ (unitQuantile μ a) = a := by
  have hq := unitQuantile_mem hμ h1 ha1
  have ha : a ∈ Set.Icc (μ 0) (μ (unitQuantile μ a)) := by
    exact ⟨by simpa only [h0] using ha0, hq.2⟩
  obtain ⟨x, hx, heq⟩ := intermediate_value_Icc hq.1.1 hμ.continuousOn ha
  have hqx : unitQuantile μ a ≤ x := by
    apply csInf_le (unitQuantile_set_bddBelow μ a)
    exact ⟨⟨hx.1, hx.2.trans hq.1.2⟩, heq.ge⟩
  have hxq : x = unitQuantile μ a := le_antisymm hx.2 hqx
  simpa only [hxq] using heq

theorem unitQuantile_mem_Ioo {μ : ℝ → ℝ} {a : ℝ}
    (hμ : Continuous μ) (h0 : μ 0 = 0) (h1 : μ 1 = 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    unitQuantile μ a ∈ Set.Ioo (0 : ℝ) 1 := by
  have hq := (unitQuantile_mem hμ h1 ha1.le).1
  have heq := unitQuantile_eq_level hμ h0 h1 ha0.le ha1.le
  constructor
  · refine lt_of_le_of_ne hq.1 ?_
    intro he
    rw [← he, h0] at heq
    exact ha0.ne heq
  · refine lt_of_le_of_ne hq.2 ?_
    intro he
    rw [he, h1] at heq
    exact ha1.ne heq.symm

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.unitQuantile_mem_Ioo := @_root_.OAI.Problem313.unitQuantile_mem_Ioo
