-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.q_Ist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:48.048374+00:00
-- url     : https://prove2.me/submissions/59d834c7-43c7-4ef7-9cd1-04e2fb7089dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_q_i

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
theorem _root_.solution {y : V} (hy : y ∈ N.Ist) : qI N y = y := by
  have key : N.Ist ≤ LinearMap.eqLocus (qI N) LinearMap.id := by
    show Submodule.span K (N.ist '' {b | N.j ≤ b.val}) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact LinearMap.mem_eqLocus.2 (by rw [q_i N b hb, LinearMap.id_apply])
  exact LinearMap.mem_eqLocus.1 (key hy)
end GlobalTheory.DegCnt.LiftS
