-- Prove2me | solution 1 for GlobalTheory.FinWeil.index_comap_toSpanSingleton_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:37.017801+00:00
-- url     : https://prove2.me/submissions/7eef39f1-da73-4a86-8a97-e88ff1ff9c21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsAdjacentSelfDualLatticeToward

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) {y : X} (hy : y ∈ B) :
    (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index ≠ 0 := by
  have h1 : (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup =
      A.toAddSubgroup.comap (LinearMap.toSpanSingleton R X y).toAddMonoidHom := rfl
  rw [h1, AddSubgroup.index_comap]
  intro h0
  refine hAB (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨r, rfl⟩
  exact B.smul_mem r hy
end GlobalTheory.FinWeil
