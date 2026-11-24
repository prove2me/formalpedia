-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.CellSplit.lift_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:36:05.423992+00:00
-- url     : https://prove2.me/submissions/f0bc8a61-6367-42cc-a067-bb7877a8bfac

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_diagCols_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM
namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit
theorem _root_.solution {S E₁ E₂ β : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂) [Fintype β]
    [DecidableEq β] (A : Matrix (β ⊕ β) (β ⊕ β) E₁) (B : Matrix β β E₁)
    (h : A * (diagCols β : Matrix (β ⊕ β) β E₁) = (diagCols β : Matrix (β ⊕ β) β E₁) * B) :
    lift s A * (diagCols β : Matrix (β ⊕ β) β S) = (diagCols β : Matrix (β ⊕ β) β S) * lift s B := by
  apply mat_ext s
  · rw [Matrix.map_mul, Matrix.map_mul, lift_map₁, lift_map₁, diagCols_map, h]
  · rw [Matrix.map_mul, Matrix.map_mul, lift_map₂, lift_map₂, diagCols_map, Matrix.one_mul, Matrix.mul_one]
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
