-- Prove2me | solution 1 for GlobalTheory.FieldUnitsQuotFG.fg_units_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:34.581595+00:00
-- url     : https://prove2.me/submissions/836119a3-480f-422e-b6af-63f0b0e90f25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsFiniteFieldExt
import Theorems.Thm_GlobalTheory_FieldUnitsQuotFG_fg_quot_ker
import Theorems.Thm_GlobalTheory_FieldUnitsQuotFG_finite_spec
import Theorems.Thm_GlobalTheory_FieldUnitsQuotFG_ker_valHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.FieldUnitsQuotFG
variable (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
  [FiniteDimensional K.E L]
namespace GlobalTheory.FieldUnitsQuotFG
theorem _root_.solution : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L]
    [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  intro K L _ _ _ _ _
  haveI : IsDedekindDomain (integralClosure K.O L) := integralClosure.isDedekindDomain K.O K.E L
  haveI : IsFractionRing (integralClosure K.O L) L := integralClosure.isFractionRing_of_finite_extension K.E L
  haveI := finite_spec K L
  rw [← ker_valHom K L]
  exact fg_quot_ker _
end GlobalTheory.FieldUnitsQuotFG
