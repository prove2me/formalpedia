-- Prove2me | solution 1 for GlobalTheory.BlockReorder.leviMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:54.522204+00:00
-- url     : https://prove2.me/submissions/bcfbd98d-25c5-436e-ad5f-2a2f6f2fa57a

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open GlobalTheory GlobalTheory.BlockReorder
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable (R : Type) [CommRing R]
variable {R}
variable (R)
variable {R}
namespace GlobalTheory.BlockReorder
theorem _root_.solution (e : (Σ a, m a) ≃ n) : Function.Surjective (leviMap R e) := by
  intro h
  refine ⟨fun i => Units.map (reindexAlgEquiv R R (blockNum i).symm).toRingEquiv.toMonoidHom (h (neOrder m i).1),
    levi_ext fun i u v => ?_⟩
  rw [leviMap_apply_num]
  simp [reindexAlgEquiv_apply]
end GlobalTheory.BlockReorder
