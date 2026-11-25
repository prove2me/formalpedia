-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.ord_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:07:05.479636+00:00
-- url     : https://prove2.me/submissions/64e6a21a-4c21-4263-97fb-0989403d978d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_ord_nonneg_of_mem_integers
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_det_mem_integers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    ord (detU k : F) = 0 := by
  obtain ⟨hk1, hk2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have h1 := ord_nonneg_of_mem_integers (detU k).ne_zero (det_mem_integers hk1)
  have h2 := ord_nonneg_of_mem_integers (detU k⁻¹).ne_zero (det_mem_integers hk2)
  have hinv : detU k⁻¹ = (detU k)⁻¹ := map_inv _ k
  rw [hinv, Units.val_inv_eq_inv_val, ord_inv (detU k).ne_zero] at h2
  omega
end GroundTheory.Automorphic.GodementSectionLocal
