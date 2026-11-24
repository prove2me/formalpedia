-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BlockIwahoriUML.blockDiag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:34.093306+00:00
-- url     : https://prove2.me/submissions/6faf4b1f-bb62-41b5-848d-33252ea632a5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
namespace GlobalTheory.CompanionTheory.BlockIwahoriUML
theorem _root_.solution {n : ℕ} (β : Fin n → ℕ) {A B : Matrix (Fin n) (Fin n) k}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) (hB : ∀ i j, β i ≠ β j → B i j = 0) :
    ∀ i j, β i ≠ β j → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : β i = β x
  · rw [hB x j (fun e => hij (hx.trans e)), mul_zero]
  · rw [hA i x hx, zero_mul]
end GlobalTheory.CompanionTheory.BlockIwahoriUML
