-- Prove2me | solution 1 for GlobalTheory.BadShare.ZCalc.op_conv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:12.782607+00:00
-- url     : https://prove2.me/submissions/d6e1b3c5-9f9c-473a-81d0-a58d30138b2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.ZCalc
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.ZCalc
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a b : G → ℂ) :
    op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op, conv, Finset.sum_smul, Finset.sum_mul_sum, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine (Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_).symm
  simp
end GlobalTheory.BadShare.ZCalc
