-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.LevelId.image_sol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:17:02.420802+00:00
-- url     : https://prove2.me/submissions/4bdf6c16-db3f-4796-98ee-7f2422f513c2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion
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
theorem _root_.solution (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ k '' {x : Matrix (Fin m) (Fin n) R | red ϖ k (cT σ x * S * x) = red ϖ k T} =
      {y | cT (barσ σ ϖ h k) y * red ϖ k S * y = red ϖ k T} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show cT (barσ σ ϖ h k) (red ϖ k x) * red ϖ k S * red ϖ k x = red ϖ k T
    rw [← red_gram σ ϖ h]
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := red_surj ϖ k y
    refine ⟨x, ?_, rfl⟩
    show red ϖ k (cT σ x * S * x) = red ϖ k T
    rw [red_gram σ ϖ h]
    exact hy
end GlobalTheory.CompanionTheory.SiegLoc.LevelId
