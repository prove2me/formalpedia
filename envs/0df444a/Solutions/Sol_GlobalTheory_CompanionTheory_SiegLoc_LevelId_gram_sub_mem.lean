-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.LevelId.gram_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:17:01.399923+00:00
-- url     : https://prove2.me/submissions/3f83adc1-f8ee-44f0-b8bb-1f8c7da4856a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_cT_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_cT_cT
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_cT_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_red_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_red_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_red_gram

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
theorem _root_.solution (σ : R →+* R) (ϖ : R) (hinv : ∀ a, σ (σ a) = a) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : cT σ S = S) (hT : cT σ T = T)
    (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    cT (barσ σ ϖ h k) y * red ϖ k S * y - red ϖ k T ∈ hermMod σ ϖ n k := by
  obtain ⟨x, rfl⟩ := red_surj ϖ k y
  unfold hermMod
  refine ⟨cT σ x * S * x - T, ?_, ?_⟩
  · show cT σ (cT σ x * S * x - T) = cT σ x * S * x - T
    rw [cT_sub, cT_mul, cT_mul, cT_cT σ hinv, hS, hT, Matrix.mul_assoc]
  · show red ϖ k (cT σ x * S * x - T) = _
    rw [red_sub, red_gram σ ϖ h]
end GlobalTheory.CompanionTheory.SiegLoc.LevelId
