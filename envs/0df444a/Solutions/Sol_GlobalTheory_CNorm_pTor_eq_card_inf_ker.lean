-- Prove2me | solution 1 for GlobalTheory.CNorm.pTor_eq_card_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:00.517543+00:00
-- url     : https://prove2.me/submissions/1e7358e7-102c-42ce-b809-05e9059334d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p U = Nat.card (U ⊓ (powMonoidHom p : G →* G).ker : Subgroup G) := by
  unfold pTor
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, powMonoidHom_apply])
end GlobalTheory.CNorm
