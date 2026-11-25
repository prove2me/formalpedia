-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.normalForm_baseLattice_le_dualSpan_sup_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:56:36.781216+00:00
-- url     : https://prove2.me/submissions/db1bc5f4-f1e2-443b-a1be-ae32ec65b1e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_line_le

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution {M : Submodule (𝓞 K) V} (h1 : ∀ a : Fin r, ∀ t ∈ N.aa a, t • N.F.e a.castSucc ∈ M)
    (h2 : ∀ a : Fin r, a.val < N.j → ∀ t ∈ N.aa a, t • N.F'.e a.castSucc ∈ M)
    (h3 : ∀ t ∈ (1 : Submodule (𝓞 K) K), t • N.F.z ∈ M)
    (h4 : ∀ a : Fin r, N.j ≤ a.val → ∀ t ∈ ipow N.𝔡 ((r : ℤ) - a.val), t • N.ist a ∈ M) : N.P0 ≤ M := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le ?_ ?_) (line_le h3)) ?_
  · exact iSup_le fun a => line_le (h1 a)
  · exact iSup_le fun a => iSup_le fun ha => line_le (h2 a ha)
  · exact iSup_le fun a => iSup_le fun ha => line_le (h4 a ha)
end GlobalTheory.DegCnt.LiftS
