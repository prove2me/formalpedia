-- Prove2me | solution 1 for GlobalTheory.T.exists_hermitian_congr_to_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:36.062876+00:00
-- url     : https://prove2.me/submissions/82fd090b-34fc-4007-b6f6-3653a2ca538e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOneStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_exists_congr_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det → ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | exact GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_congr_one <;> assumption)
end _root_.GlobalTheory.T
