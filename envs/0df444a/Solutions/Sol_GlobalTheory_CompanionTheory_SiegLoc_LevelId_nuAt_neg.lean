-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.LevelId.nuAt_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:37:33.6588+00:00
-- url     : https://prove2.me/submissions/b36f46ac-03b4-4639-a699-e4adc3790c4f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.LevelId
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.LevelId
theorem _root_.solution (ϖ : R) {n k : ℕ} (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :
    nuAt ϖ (-B) = nuAt ϖ B := by
  unfold nuAt
  have hset : (Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x (-B)) =
      Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x B := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) B = Matrix.vecMul x (-B)
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg]
    · rintro ⟨x, rfl⟩
      refine ⟨-x, ?_⟩
      show Matrix.vecMul (-x) (-B) = Matrix.vecMul x B
      rw [Matrix.neg_vecMul, Matrix.vecMul_neg, neg_neg]
  rw [hset]
end GlobalTheory.CompanionTheory.SiegLoc.LevelId
