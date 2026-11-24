-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:51:59.804527+00:00
-- url     : https://prove2.me/submissions/27ab3bd3-0caf-448b-8a4a-82c032b9680a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_finite_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_nontrivial_of_resAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_isUnit_of_ne

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
theorem _root_.solution (h : ResAlg E τ q ε) (hf : IsField E) : Nat.card Eˣ = q ^ 2 - 1 := by
  classical
  have := finite_of_resAlg h
  have := nontrivial_of_resAlg h
  have e1 : Nat.card Eˣ = Nat.card {a : E // a ≠ 0} := Nat.card_congr
    { toFun := fun u => ⟨u, u.ne_zero⟩
      invFun := fun a => (isUnit_of_ne hf a.2).unit
      left_inv := fun u => Units.ext rfl
      right_inv := fun a => rfl }
  have e2 := Nat.card_congr (Equiv.optionSubtypeNe (0 : E))
  rw [Finite.card_option, h.card] at e2
  rw [e1, ← e2, Nat.add_sub_cancel]
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
