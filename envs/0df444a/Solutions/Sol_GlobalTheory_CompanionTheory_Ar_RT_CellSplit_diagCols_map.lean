-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.CellSplit.diagCols_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:20:31.610797+00:00
-- url     : https://prove2.me/submissions/0e1d1323-fd16-445f-86e9-1e436c3ebd82

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct

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
theorem _root_.solution {S T β : Type} [CommRing S] [CommRing T] [DecidableEq β] (f : S →+* T) :
    (diagCols β : Matrix (β ⊕ β) β S).map f = diagCols β := by
  ext i j
  rcases i with i | i
  · by_cases h : i = j
    · subst h
      simp [diagCols]
    · simp [diagCols, Matrix.one_apply_ne h]
  · by_cases h : i = j
    · subst h
      simp [diagCols]
    · simp [diagCols, Matrix.one_apply_ne h]
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
