-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertIndex.relIndex_boxLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:53.073611+00:00
-- url     : https://prove2.me/submissions/954358a1-ab42-42bd-a47b-abaa8935e8f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LatticeIndexOfSmith
import Theorems.Thm_GlobalTheory_CompanionTheory_InertIndex_mem_boxLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.BorelUMod.UpLatIndex
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertIndex
theorem _root_.solution (c C : Fin n → ℤ) :
    (boxLat L C).relIndex (boxLat L c) = ∏ i, (ordBall L (C i)).relIndex (ordBall L (c i)) := by
  let f : boxLat L c →+ (∀ i, ordBall L (c i) ⧸ (ordBall L (C i)).addSubgroupOf (ordBall L (c i))) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, mem_boxLat.1 x.2 i⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => by
    refine ⟨⟨fun i => ((y i).out : L), mem_boxLat.2 fun i => (y i).out.2⟩, funext fun i => ?_⟩
    exact (y i).out_eq
  have hc : (boxLat L C).addSubgroupOf (boxLat L c) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, mem_boxLat]
    constructor
    · intro h i
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i)
    · intro h i
      exact AddSubgroup.mem_addSubgroupOf.1
        ((QuotientAddGroup.eq_zero_iff (⟨x.1 i, mem_boxLat.1 x.2 i⟩ : ordBall L (c i))).1 (h i))
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl
end GlobalTheory.CompanionTheory.InertIndex
