-- Prove2me | solution 1 for GlobalTheory.FinWeil.idx_congr_of_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:35.686393+00:00
-- url     : https://prove2.me/submissions/e9e4b4c0-4ec8-4a02-b25b-c66665986795

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumCompOfIntermediateLattiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AdjacentSelfDualLatticesIndexSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergSumCompOfAdjacentOfInfEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedIntertwinerCompOfAdjacentLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    {A B C : Submodule R X} (h : A ⊓ C = B ⊓ C) : idx A C = idx B C := by
  unfold idx
  rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup, ← AddSubgroup.inf_relIndex_right B.toAddSubgroup]
  have : A.toAddSubgroup ⊓ C.toAddSubgroup = B.toAddSubgroup ⊓ C.toAddSubgroup := by
    ext x
    have := SetLike.ext_iff.1 h x
    simpa using this
  rw [this]
end GlobalTheory.FinWeil
