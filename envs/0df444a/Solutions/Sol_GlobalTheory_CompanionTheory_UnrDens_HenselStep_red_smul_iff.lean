-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.red_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:25.390091+00:00
-- url     : https://prove2.me/submissions/c30bc958-6b3d-4715-9724-8c57ef7a61a7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_smul_cancel

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
theorem _root_.solution {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) (A B : Matrix (Fin a) (Fin b) R) :
    red ϖ (k + 1) (ϖ ^ k • A) = red ϖ (k + 1) (ϖ ^ k • B) ↔ red ϖ 1 A = red ϖ 1 B := by
  rw [red_eq_iff, red_eq_iff]
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨D, smul_cancel hr k ?_⟩
    rw [hD, smul_add, smul_smul, pow_one, pow_succ]
  · rintro ⟨D, rfl⟩
    refine ⟨D, ?_⟩
    rw [smul_add, smul_smul, pow_one, pow_succ]
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
