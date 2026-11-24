-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BlockIwahoriUML.cong_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:35.108122+00:00
-- url     : https://prove2.me/submissions/b279bf2d-1af8-4bbb-b697-288714d926e9

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
theorem _root_.solution (v : Valuation k Γ) {r : Γ} {n : ℕ} {A : Matrix (Fin n) (Fin n) k}
    (hA : Cong v r A) : Cong v r Aᵀ := by
  intro i j
  have h1 : (1 : Matrix (Fin n) (Fin n) k) i j = (1 : Matrix (Fin n) (Fin n) k) j i := by
    simp [Matrix.one_apply, eq_comm]
  rw [h1, Matrix.transpose_apply]
  exact hA j i
end GlobalTheory.CompanionTheory.BlockIwahoriUML
