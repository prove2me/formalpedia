-- Prove2me | solution 1 for GlobalTheory.BorelUMod.adjJ_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:53.62424+00:00
-- url     : https://prove2.me/submissions/1f661022-7687-49c2-ab76-1e140a0cb68e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open GlobalTheory.LGrp Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod
namespace _root_.GlobalTheory.BorelUMod
theorem _root_.solution (σ : L →+* L) (a : L) (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (a • X) = σ a • _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]
end _root_.GlobalTheory.BorelUMod
end GlobalTheory.BorelUMod
