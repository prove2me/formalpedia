-- Prove2me | solution 1 for GlobalTheory.DerivAtOrigin.isOpen_polydisc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:10.756178+00:00
-- url     : https://prove2.me/submissions/39076f8a-7616-478b-af8e-58f4746e0391

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivFormulaOfSeries
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DerivAtOrigin
namespace GlobalTheory.DerivAtOrigin
theorem _root_.solution (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  have : polydisc I = ⋂ i : I, {z : I → ℂ | ‖z i‖ < 1} := by
    ext z; simp [polydisc]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const
end GlobalTheory.DerivAtOrigin
