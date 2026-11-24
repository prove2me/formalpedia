-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.isUnit_det_red_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:58.513811+00:00
-- url     : https://prove2.me/submissions/6c50f624-db08-4f7d-80e2-0aed721dab4a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidueStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardUnimodularHermitianRepsLevelOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution {R : Type} [CommRing R] (ϖ : R) {a : ℕ}
    (x : Matrix (Fin a) (Fin a) R) (hx : IsUnit x.det) : IsUnit (red ϖ 1 x).det := by
  have e : (red ϖ 1 x).det = Ideal.Quotient.mk (lev ϖ 1) x.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact hx.map _
end GlobalTheory.CompanionTheory.UnrDens
