-- Prove2me | solution 1 for GlobalTheory.Proof.TwistSupportPeriodicLevels.mem_KO_of_latOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:56.47702+00:00
-- url     : https://prove2.me/submissions/9304a8b4-0e2a-4afc-ab20-462fe3ee6d6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Theorems.Thm_GlobalTheory_StepData_latOf_le_iff
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
theorem _root_.solution {Y : Type} [Fintype Y] [DecidableEq Y] {g : GL Y k} (h : latOf g = latOf 1) :
    g ∈ KO k Y := by
  have h1 := latOf_le_iff.mp h.le
  have h2 := latOf_le_iff.mp h.ge
  simp only [inv_one, one_mul, mul_one] at h1 h2
  exact mem_KO.mpr ⟨h1, h2⟩
end GlobalTheory.Proof.TwistSupportPeriodicLevels
