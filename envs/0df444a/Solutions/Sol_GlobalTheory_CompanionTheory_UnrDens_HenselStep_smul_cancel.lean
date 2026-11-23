-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:54.331317+00:00
-- url     : https://prove2.me/submissions/3caf7ad1-9430-4aa7-9577-3d7525378b54

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep
variable {R : Type} [CommRing R] {a b c : ℕ}
namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep
theorem _root_.solution {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) {A B : Matrix (Fin a) (Fin b) R}
    (h : ϖ ^ k • A = ϖ ^ k • B) : A = B := by
  ext i j
  have h1 : ϖ ^ k • A i j = ϖ ^ k • B i j := by
    simpa using congrFun (congrFun h i) j
  exact (hr.pow k) h1
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
