-- Prove2me | solution 1 for GlobalTheory.T.hermitian_space_anisotropic_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:37.833825+00:00
-- url     : https://prove2.me/submissions/dc98e744-05de-459b-9b00-9829a864f08b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnitStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_exists_unit_norm


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
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nontrivial V → ∃ w : V, IsUnit (B.h w w) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm | exact GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_unit_norm <;> assumption)
end _root_.GlobalTheory.T
