-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.red_mul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:59.576322+00:00
-- url     : https://prove2.me/submissions/23afb128-41e3-4df8-937f-33b7af57d2ed

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
theorem _root_.solution {R : Type} [CommRing R] (ϖ : R) {a b c : ℕ}
    (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ 1 (x * y) = red ϖ 1 x * red ϖ 1 y := by
  simp only [red]
  exact Matrix.map_mul
end GlobalTheory.CompanionTheory.UnrDens
