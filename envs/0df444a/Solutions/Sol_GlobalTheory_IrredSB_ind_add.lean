-- Prove2me | solution 1 for GlobalTheory.IrredSB.ind_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:02.234803+00:00
-- url     : https://prove2.me/submissions/425c5f9a-ef37-4694-a31d-7e558f759fad

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
variable {G : Type} [AddCommGroup G]
namespace GlobalTheory.IrredSB
theorem _root_.solution (K : AddSubgroup G) (t : G) {u : G} (hu : u ∈ K) : ind K (t + u) = ind K t := by
  unfold ind
  by_cases ht : t ∈ K
  · rw [if_pos ht, if_pos (add_mem ht hu)]
  · rw [if_neg ht, if_neg fun h => ht ((add_mem_cancel_right hu).1 h)]
end GlobalTheory.IrredSB
