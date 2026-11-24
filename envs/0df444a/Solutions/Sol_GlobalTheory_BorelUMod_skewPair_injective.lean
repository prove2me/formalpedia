-- Prove2me | solution 1 for GlobalTheory.BorelUMod.skewPair_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:37.690516+00:00
-- url     : https://prove2.me/submissions/a0c8537c-6304-4b6a-a6f2-73dd11418ff9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
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
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] {n : ℕ}
namespace GlobalTheory.BorelUMod
theorem _root_.solution (σ : L →+* L) (θ : L) {d : L} (hd : d ≠ 0) :
    Function.Injective (skewPair (n := n) σ θ d) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  have h1 : X - θ • (X + adjJ σ X) = 0 := congrArg Prod.fst hX
  have h2 : d • (X + adjJ σ X) = 0 := congrArg Prod.snd hX
  have h3 : X + adjJ σ X = 0 := (smul_eq_zero.1 h2).resolve_left hd
  simpa [h3] using h1
end GlobalTheory.BorelUMod
