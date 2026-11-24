-- Prove2me | solution 1 for GlobalTheory.SymChain.IterPattern.intM_submatrix_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:37.148148+00:00
-- url     : https://prove2.me/submissions/6edb5793-dbae-4f5a-8932-12d155a54657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.IterPattern
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SymChain.IterPattern
theorem _root_.solution {a b : Type*} (e : a ≃ b) (M : Matrix b b k) :
    IntM (M.submatrix e e) ↔ IntM M := by
  constructor
  · intro h i j
    simpa using h (e.symm i) (e.symm j)
  · intro h i j
    exact h (e i) (e j)
end GlobalTheory.SymChain.IterPattern
