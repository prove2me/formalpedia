-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_bound_mulEquivHaarChar_conjCME
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:42.972842+00:00
-- url     : https://prove2.me/submissions/0945d205-a21c-46af-95db-873d5788ddf4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


attribute [local simp] GroundTheory.Automorphic.conjCME_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution {K : Set G} (hK : IsCompact K)
    (hKinv : ∀ k ∈ K, k⁻¹ ∈ K) :
    ∃ B : ℝ≥0, ∀ k ∈ K, mulEquivHaarChar (conjCME k) ≤ B := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set μ : Measure G := Measure.haar
  set C : Set G := (fun p : G × G × G => p.1 * p.2.1 * p.2.2) '' (K ×ˢ V ×ˢ K)
  have hC : IsCompact C := (hK.prod (hVc.prod hK)).image (by fun_prop)
  have hV0 : μ V ≠ 0 := (μ.measure_pos_of_mem_nhds hV1).ne'
  have hCt : μ C ≠ ∞ := hC.measure_lt_top.ne
  refine ⟨(μ C / μ V).toNNReal, fun k hk => ?_⟩
  have hsub : V ⊆ conjCME k ⁻¹' C := fun x hx =>
    ⟨(k, x, k⁻¹), ⟨hk, hx, hKinv k hk⟩, rfl⟩
  have e := mulEquivHaarChar_smul_preimage μ (X := C) (conjCME k)
  have hle : (mulEquivHaarChar (conjCME k) : ℝ≥0∞) * μ V ≤ μ C := by
    rw [← e, ENNReal.smul_def, smul_eq_mul]
    gcongr
  have : (mulEquivHaarChar (conjCME k) : ℝ≥0∞) ≤ μ C / μ V :=
    (ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inr hCt)).2 hle
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ENNReal.div_ne_top hCt hV0)]
  exact this
end GroundTheory.Automorphic
