-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fixed_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:11:07.373857+00:00
-- url     : https://prove2.me/submissions/a8038c53-9646-456e-a941-32e662b91b6b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_finite_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fixed

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
theorem _root_.solution (h : ResAlg E τ q ε) : Nat.card {x : E // τ x = x ∧ x ≠ 0} = q - 1 := by
  classical
  have := finite_of_resAlg h
  have e1 : Nat.card {x : E // τ x = x ∧ x ≠ 0} =
      Nat.card {y : {x : E // τ x = x} // y ≠ ⟨0, map_zero τ⟩} := Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h0 => x.2.2 (congrArg Subtype.val h0)⟩
      invFun := fun y => ⟨y.1.1, y.1.2, fun h0 => y.2 (Subtype.ext h0)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 := Nat.card_congr (Equiv.optionSubtypeNe (⟨0, map_zero τ⟩ : {x : E // τ x = x}))
  rw [Finite.card_option, card_fixed h] at e2
  rw [e1, ← e2, Nat.add_sub_cancel]
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
