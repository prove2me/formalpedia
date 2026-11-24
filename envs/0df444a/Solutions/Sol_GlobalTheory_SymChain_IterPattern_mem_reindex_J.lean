-- Prove2me | solution 1 for GlobalTheory.SymChain.IterPattern.mem_reindex_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:39:52.427846+00:00
-- url     : https://prove2.me/submissions/db5c7619-53fa-4bef-bd62-95f2001cb23d

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
theorem _root_.solution {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J := Iff.rfl
end GlobalTheory.SymChain.IterPattern
