-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.coe_torusPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:46:19.869851+00:00
-- url     : https://prove2.me/submissions/3c682592-97af-47fc-9f3f-41ebda2abbda

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution (l : Fin n → ℤ) :
    ((torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => (GLnLocal.uniformizer F : F) ^ l i := by
  simp [torusPow, Units.val_zpow_eq_zpow_val]
end GroundTheory.Automorphic.Iwasawa
