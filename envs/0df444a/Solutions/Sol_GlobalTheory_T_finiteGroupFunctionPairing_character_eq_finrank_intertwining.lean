-- Prove2me | solution 1 for GlobalTheory.T.finiteGroupFunctionPairing_character_eq_finrank_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:39.083656+00:00
-- url     : https://prove2.me/submissions/da1350a0-467c-4ebc-891e-736cdfcfda56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingCharacterEqFinrankInte
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingCharacterEqFinrankInteStatement
import Theorems.Thm_GlobalTheory_BI_pair_character_eq_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  first | exact @GlobalTheory.BI.pair_character_eq_finrank | exact GlobalTheory.BI.pair_character_eq_finrank | (intros; apply GlobalTheory.BI.pair_character_eq_finrank <;> assumption)
end _root_.GlobalTheory.T
