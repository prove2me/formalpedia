-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.hermFramePairNormalForm_frameSpan_le_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:09:51.736124+00:00
-- url     : https://prove2.me/submissions/649007e4-2c4f-4dbc-8496-01752fe2be35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_P2M_GlobalTheory_DegCnt_LiftS_z__eq_3b4bb3d0338d
import Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_z__eq_1a1eccca2614


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
theorem _root_.solution {M : Submodule K V} (h1 : N.F.X ≤ M) (h2 : N.F'.X ≤ M) (h3 : N.F.z ∈ M) : V0 N.F N.F' ≤ M := by
  have h4 : N.F'.z ∈ M := by
    rw [z'_eq N]
    exact M.smul_mem _ h3
  exact sup_le (sup_le h1 h2)
    (Submodule.span_le.2 (Set.insert_subset_iff.2 ⟨h3, Set.singleton_subset_iff.2 h4⟩))
end GlobalTheory.DegCnt.LiftS
