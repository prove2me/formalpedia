-- Prove2me | solution 1 for GlobalTheory.BorelUMod.adjJ_adjJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:32.395012+00:00
-- url     : https://prove2.me/submissions/9939de16-9f9f-4b95-8ba3-010f4de9600a

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
theorem _root_.solution {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x)
    (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (_root_.GlobalTheory.BorelUMod.adjJ σ X) = X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ, hσ]
end _root_.GlobalTheory.BorelUMod
end GlobalTheory.BorelUMod
