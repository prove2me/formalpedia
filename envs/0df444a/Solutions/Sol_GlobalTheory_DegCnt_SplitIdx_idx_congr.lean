-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.idx_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:22.349705+00:00
-- url     : https://prove2.me/submissions/b24bcdcc-c776-4feb-bdf4-b1eedc08b536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_inf_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution {A B C : Submodule R W} (h : A ⊓ B = A ⊓ C) : idx A B = idx A C := by
  rw [← idx_inf_left A B, h, idx_inf_left]
end GlobalTheory.DegCnt.SplitIdx
