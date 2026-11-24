-- Prove2me | solution 1 for GlobalTheory.IrredSB.pair_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:04.615722+00:00
-- url     : https://prove2.me/submissions/d6503bcc-39f4-4bc5-92ba-ae3573440b5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [Fintype Y']
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IrredSB
theorem _root_.solution [DecidableEq Y] [DecidableEq Y'] (r : Y) (q : Y') (c : k) (t : Matrix Y Y' k) :
    pair (Matrix.single r q c) t = c * t r q := by
  unfold pair
  rw [Finset.sum_eq_single r, Finset.sum_eq_single q]
  · simp
  · intro q' _ h
    simp [Matrix.single, h.symm]
  · simp
  · intro r' _ h
    simp [Matrix.single, h.symm]
  · simp
end GlobalTheory.IrredSB
