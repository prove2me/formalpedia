-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.projectionOntoDualIsotropicSpan_frameSpan_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:38:35.137685+00:00
-- url     : https://prove2.me/submissions/cf8ea35f-0a04-4881-ad7e-2346f3289fb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_q_X
import Theorems.Thm_P2M_GlobalTheory_DegCnt_LiftS_q_X__232d051c03ce
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_projectionOntoDualIsotropicSpan_anisotropicVector
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_hermFramePairNormalForm_frameSpan_le_of_generators

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
theorem _root_.solution {y : V} (hy : y ∈ V0 N.F N.F') : qI N y = 0 :=
  LinearMap.mem_ker.1 (hermFramePairNormalForm_frameSpan_le_of_generators N (M := LinearMap.ker (qI N)) (fun _ hx => LinearMap.mem_ker.2 (q_X N hx))
    (fun _ hx => LinearMap.mem_ker.2 (q_X' N hx)) (LinearMap.mem_ker.2 (projectionOntoDualIsotropicSpan_anisotropicVector N)) hy)
end GlobalTheory.DegCnt.LiftS
