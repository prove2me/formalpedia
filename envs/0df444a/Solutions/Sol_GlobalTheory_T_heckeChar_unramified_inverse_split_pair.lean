-- Prove2me | solution 1 for GlobalTheory.T.heckeChar_unramified_inverse_split_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:33.766131+00:00
-- url     : https://prove2.me/submissions/0c6cfd21-ea83-4465-95e7-1ebae34e1de1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPair
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPairStatement
import Theorems.Thm_GlobalTheory_CMVal_Euler_SplitPair_unrAt_and_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E)) (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P → UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by
  first | exact @GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val | exact GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val | (intros; apply GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val <;> assumption)
end _root_.GlobalTheory.T
