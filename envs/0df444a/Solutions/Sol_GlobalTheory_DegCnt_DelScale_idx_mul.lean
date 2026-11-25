-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.idx_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:54.362432+00:00
-- url     : https://prove2.me/submissions/3238dbb0-9489-49af-8f30-fa53a1e793e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_mul


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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DelScale
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace GlobalTheory.DegCnt.DelScale
theorem _root_.solution {A B C : Submodule R W} (h1 : A ≤ B) (h2 : B ≤ C) : idx B A * idx C B = idx C A :=
  idxN_mul h1 h2
end GlobalTheory.DegCnt.DelScale
