-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.diagble_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:35.473477+00:00
-- url     : https://prove2.me/submissions/d013f759-d5bf-4edb-87fe-562faf878c70

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_exists_prim
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermDiag
variable {R : Type} [CommRing R]
variable {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HermDiag
theorem _root_.solution (hR : IsUnrQuad R σ ϖ q ε) :
    ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), Hm σ h → Diagble σ h := by
  intro n
  induction n with
  | zero =>
    intro h _
    rw [Subsingleton.elim h 0]
    exact diagble_zero
  | succ n ih =>
    intro h hh
    by_cases h0 : h = 0
    · rw [h0]; exact diagble_zero
    · obtain ⟨a, h', hh', rfl, i, j, hy⟩ := exists_prim hR hh h0
      exact diagble_smul (by simp [hR.fix_ϖ]) (diagble_prim hR ih hh' hy)
end GlobalTheory.CompanionTheory.HermDiag
