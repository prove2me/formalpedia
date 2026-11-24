-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_ker_ratioU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:50.987702+00:00
-- url     : https://prove2.me/submissions/27f39f5c-7918-45ce-b449-b4381dac2db1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_nontrivial_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fixed_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_mem_ker_ratioU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution (h : ResAlg E τ q ε) : Nat.card (ratioU τ).ker = q - 1 := by
  have := nontrivial_of_resAlg h
  rw [← card_fixed_ne h]
  exact Nat.card_congr
    { toFun := fun k => ⟨((k : Eˣ) : E), (mem_ker_ratioU.1 k.2).symm, (k : Eˣ).ne_zero⟩
      invFun := fun x => ⟨(h.fixedUnit x.1 x.2.1 x.2.2).unit, mem_ker_ratioU.2 x.2.1.symm⟩
      left_inv := fun k => Subtype.ext (Units.ext rfl)
      right_inv := fun x => rfl }
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
