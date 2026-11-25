-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.borelElt_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:47.38978+00:00
-- url     : https://prove2.me/submissions/67e7f116-7673-4008-985e-602aaa1562ca

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal

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
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution (a d : Fˣ) (x : F) :
    (borelElt a d x : Matrix (Fin 2) (Fin 2) F) = !![(a : F), x; 0, (d : F)] := rfl
end GroundTheory.Automorphic.GodementSectionLocal
