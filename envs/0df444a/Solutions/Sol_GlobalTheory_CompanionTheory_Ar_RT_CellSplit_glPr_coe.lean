-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.CellSplit.glPr_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:20.840413+00:00
-- url     : https://prove2.me/submissions/0b55a98b-e69e-44a9-b672-c79c01f6d710

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
variable {S E₁ E₂ : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂)
variable {n : Type} [DecidableEq n]
variable [Fintype n]
namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit
theorem _root_.solution (x : GL n S) : ((glPr s x : GL n E₁) : Matrix n n E₁) = (x : Matrix n n S).map (pr₁ s) := rfl
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
