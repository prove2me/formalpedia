-- Prove2me | solution 1 for GlobalTheory.T.flatColumnSupport_of_oneIndexAt_symPosition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:30.877695+00:00
-- url     : https://prove2.me/submissions/42176306-a55b-4778-83f5-55c7a04d7c50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPosition
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPositionStatement
import Theorems.Thm_GlobalTheory_LocFlat_suppCol_of_oneIndexAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.OneIndexAt t ν → GlobalTheory.LocFlat.SuppCol S t ν := by
  first | exact @GlobalTheory.LocFlat.suppCol_of_oneIndexAt | exact GlobalTheory.LocFlat.suppCol_of_oneIndexAt | (intros; apply GlobalTheory.LocFlat.suppCol_of_oneIndexAt <;> assumption)
end _root_.GlobalTheory.T
