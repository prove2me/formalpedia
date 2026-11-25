-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.subsingleton_tate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:47:13.543732+00:00
-- url     : https://prove2.me/submissions/730ffe91-77d2-40bb-8da0-854ee595ff3c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_filt_zero
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_filt_complete
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_filt_separated
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_subsingleton_tateZero_gr
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_subsingleton_tateNegOne_gr
import Theorems.Thm_GroundTheory_LocalField_subsingleton_tate_of_complete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
open GroundTheory.LocalField.NormalLatticeData
variable (D : NormalLatticeData K L)
attribute [local instance] action
omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L]
namespace GroundTheory.LocalField.NormalLatticeData
theorem _root_.solution :
    Subsingleton (TateZero Gal(L/K) (D.units 0)) ∧ Subsingleton (TateNegOne Gal(L/K) (D.units 0)) :=
  subsingleton_tate_of_complete D.filt D.filt_zero D.filt_complete D.filt_separated
    D.subsingleton_tateZero_gr D.subsingleton_tateNegOne_gr
end GroundTheory.LocalField.NormalLatticeData
