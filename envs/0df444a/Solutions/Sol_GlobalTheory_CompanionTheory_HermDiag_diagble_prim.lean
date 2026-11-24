-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.diagble_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:12.11781+00:00
-- url     : https://prove2.me/submissions/fa7ded14-8405-495e-9fa4-bdedf493db98

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_hm_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_of_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_reindex
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_schur
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_exists_pivot

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
theorem _root_.solution (hR : IsUnrQuad R σ ϖ q ε) {n : ℕ}
    (ih : ∀ h : Matrix (Fin n) (Fin n) R, Hm σ h → Diagble σ h)
    {h : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (hh : Hm σ h) {i j : Fin (n + 1)}
    (hy : h i j ∉ lev ϖ 1) : Diagble σ h := by
  obtain ⟨k, p, p', h1, h2, hp⟩ := exists_pivot hR hh hy
  apply diagble_of_congr h1 h2
  have hh2 := hm_congr hR.inv hh p
  have hcard : Fintype.card (Unit ⊕ Fin n) = n + 1 := by simp; omega
  let e0 := Fintype.equivFinOfCardEq hcard
  let e := e0.trans (Equiv.swap (e0 (Sum.inl ())) k)
  have he : e (Sum.inl ()) = k := by simp [e]
  apply diagble_reindex e
  refine diagble_schur hR.inv ih (fun a b => hh2 _ _) ?_
  simp only [Matrix.submatrix_apply, he]
  exact hR.fixLocal _ (hh2 _ _) hp
end GlobalTheory.CompanionTheory.HermDiag
