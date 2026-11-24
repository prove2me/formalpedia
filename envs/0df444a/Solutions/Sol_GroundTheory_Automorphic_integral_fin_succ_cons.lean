-- Prove2me | solution 1 for GroundTheory.Automorphic.integral_fin_succ_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:11.442377+00:00
-- url     : https://prove2.me/submissions/1014c661-2fd5-4e6d-b95c-065982d49b05

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
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
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {F : (Fin (d + 1) → ℝ) → E} (hF : Integrable F) :
    ∫ t, F t = ∫ s, ∫ t', F (Fin.cons s t') := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have h1 := hmp.symm.integral_comp' F
  have hint : Integrable (fun p : ℝ × (Fin d → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [← h1]
  refine (integral_prod _ hint).trans ?_
  congr 1; funext s; congr 1; funext t'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove]
  rfl
end GroundTheory.Automorphic
