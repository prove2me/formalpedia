-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.red_cT_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:23.058962+00:00
-- url     : https://prove2.me/submissions/19bb1c4b-bc97-4d8b-a183-284473d28baa

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
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) :
    red ϖ 1 (cT σ x) = cT (barσ σ ϖ h 1) (red ϖ 1 x) := by
  ext i j
  simp only [red, cT, Matrix.map_apply, Matrix.transpose_apply, barσ_mk]
end GlobalTheory.CompanionTheory.UnrDens
