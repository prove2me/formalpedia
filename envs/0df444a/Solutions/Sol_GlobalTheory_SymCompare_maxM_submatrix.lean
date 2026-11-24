-- Prove2me | solution 1 for GlobalTheory.SymCompare.maxM_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:19:46.801782+00:00
-- url     : https://prove2.me/submissions/f26bf40d-24d2-49f5-9e33-c7d840350c79

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
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m']
namespace GlobalTheory.SymCompare
theorem _root_.solution (e : n ≃ m) (e' : n' ≃ m') (M : Matrix m m' k) : MaxM (M.submatrix e e') ↔ MaxM M :=
  ⟨fun h i j => by simpa using h (e.symm i) (e'.symm j), fun h _ _ => h _ _⟩
end GlobalTheory.SymCompare
