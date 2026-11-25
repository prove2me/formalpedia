-- Prove2me | solution 1 for GlobalTheory.BorelUMod.isOpen_vball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:56:08.832204+00:00
-- url     : https://prove2.me/submissions/e7b0a419-d4d8-4d9e-99e6-c759c25552f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Theorems.Thm_GlobalTheory_BorelUMod_ball_eq_image
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
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod
theorem _root_.solution {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  rw [ball_eq_image hϖ]
  exact (Homeomorph.mulLeft₀ (ϖ ^ k) (zpow_ne_zero k h0)).isOpenMap _ (Valued.isOpen_integer L)
end GlobalTheory.BorelUMod
