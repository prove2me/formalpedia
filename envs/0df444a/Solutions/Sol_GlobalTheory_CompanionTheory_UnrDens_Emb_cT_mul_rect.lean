-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.Emb.cT_mul_rect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:52:00.761798+00:00
-- url     : https://prove2.me/submissions/8c3d7b68-93c0-48fb-8981-c478551d705d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardOrthonormalFramesHermitianSpaceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsHermitianCongrToOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Emb
variable {E : Type} [CommRing E] {τ : E →+* E}
namespace GlobalTheory.CompanionTheory.UnrDens.Emb
theorem _root_.solution {a b c : ℕ} (x : Matrix (Fin a) (Fin b) E) (y : Matrix (Fin b) (Fin c) E) :
    cT τ (x * y) = cT τ y * cT τ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]
end GlobalTheory.CompanionTheory.UnrDens.Emb
