-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.q_i
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:38.705161+00:00
-- url     : https://prove2.me/submissions/7917eac7-12ee-4416-9fd1-fe364318d237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_qI_apply
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_i_e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (a : Fin r) (ha : N.j ≤ a.val) : qI N (N.ist a) = N.ist a := by
  rw [GlobalTheory.DegCnt.LiftS.qI_apply, Finset.sum_eq_single a]
  · rw [GlobalTheory.DegCnt.LiftS.i_e N a a ha, if_pos rfl, one_smul]
  · intro b _ hba
    rw [GlobalTheory.DegCnt.LiftS.i_e N a b ha, if_neg hba, zero_smul]
  · intro h
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩) h
end GlobalTheory.DegCnt.LiftS
