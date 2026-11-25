-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.indicator_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:19.896896+00:00
-- url     : https://prove2.me/submissions/d4efc288-3361-4433-a176-e494381602a7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_isLocallyConstant_indicator
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_isCompact_box

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
theorem _root_.solution {S : Set (Fin 2 → F)} (hS : IsClopen S) {n : ℤ}
    (hSn : S ⊆ box F n) {f : (Fin 2 → F) → ℂ} (hf : IsLocallyConstant f) :
    S.indicator f ∈ schwartzBruhat2 F :=
  ⟨isLocallyConstant_indicator hS hf, HasCompactSupport.intro (isCompact_box n) fun _ hx ↦
    Set.indicator_of_notMem (fun h ↦ hx (hSn h)) f⟩
end GroundTheory.Automorphic.GodementSectionLocal
