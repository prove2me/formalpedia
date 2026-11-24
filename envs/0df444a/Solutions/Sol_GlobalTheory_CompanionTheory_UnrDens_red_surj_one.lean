-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.red_surj_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:54:59.039838+00:00
-- url     : https://prove2.me/submissions/3ca109f9-7703-475c-8c1d-8c5dec4311b5

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
theorem _root_.solution {R : Type} [CommRing R] (ϖ : R) {a b : ℕ}
    (y : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ 1)) : ∃ x, red ϖ 1 x = y := by
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  simp only [red, Matrix.map_apply, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec
end GlobalTheory.CompanionTheory.UnrDens
