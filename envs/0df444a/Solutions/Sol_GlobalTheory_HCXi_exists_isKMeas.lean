-- Prove2me | solution 1 for GlobalTheory.HCXi.exists_isKMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:32.297566+00:00
-- url     : https://prove2.me/submissions/b78413fa-05a3-4057-9c32-d8c859fe2e05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupPropertiesStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsCompactHaarMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_compact_group_haar_exists
import Theorems.Thm_GlobalTheory_T_maximal_compact_subgroup_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi
namespace GlobalTheory.HCXi
theorem _root_.solution : ∀ k r : ℕ, ∃ μK : Measure (Mt k r), IsKMeas k r μK := by
  intro k r
  obtain ⟨hcl, hco, -⟩ := GlobalTheory.T.maximal_compact_subgroup_properties k r
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.compact_group_haar_exists k r (Kset k r) hcl hco
  have hfin : μ Set.univ < ∞ := by
    have h1 : μ Set.univ ≤ μ (Kset k r) + μ (Kset k r)ᶜ := measure_univ_le_add_compl _
    have h2 : μ (Kset k r) < ∞ := hμ.finite_compact _ hco
    rw [hμ.conc, add_zero] at h1
    exact h1.trans_lt h2
  have hne : μ Set.univ ≠ 0 := by
    intro h
    exact hμ.ne_zero (Measure.measure_univ_eq_zero.1 h)
  have hone : ((μ Set.univ)⁻¹ • μ) Set.univ = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hfin.ne]
  refine ⟨(μ Set.univ)⁻¹ • μ, ⟨?_, ?_, ?_, ?_, ?_⟩, hone⟩
  · rw [Measure.smul_apply, hμ.conc, smul_zero]
  · intro a ha
    rw [Measure.map_smul, hμ.left a ha]
  · intro a ha
    rw [Measure.map_smul, hμ.right a ha]
  · intro K _
    calc _ ≤ ((μ Set.univ)⁻¹ • μ) Set.univ := measure_mono (Set.subset_univ _)
      _ < ∞ := by rw [hone]; exact ENNReal.one_lt_top
  · intro h
    rw [h] at hone
    simp at hone
end GlobalTheory.HCXi
