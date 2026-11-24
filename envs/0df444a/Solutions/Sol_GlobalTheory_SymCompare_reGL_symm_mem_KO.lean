-- Prove2me | solution 1 for GlobalTheory.SymCompare.reGL_symm_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:20:23.588635+00:00
-- url     : https://prove2.me/submissions/8c36b62e-2ef3-4eb1-b46a-7284a8798e3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution (e : n ≃ m) {g : GL m k} : (reGL e).symm g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => ((TypeDatum.full k n).reindex e).le_KO h, fun h => ((TypeDatum.full k m).reindex e.symm).le_KO
    (show (reGL e.symm).symm ((reGL e).symm g) ∈ KO k m by
      have : (reGL e.symm).symm ((reGL e).symm g) = g := by ext i j; simp [reGL_symm_val]
      rwa [this])⟩
end GlobalTheory.SymCompare
