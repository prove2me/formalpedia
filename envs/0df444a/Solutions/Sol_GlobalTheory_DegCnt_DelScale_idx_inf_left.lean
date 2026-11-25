-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.idx_inf_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:57.361839+00:00
-- url     : https://prove2.me/submissions/bcc3522e-292d-4fe9-b111-b371cd5f7dae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod

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
theorem _root_.solution (A B : Submodule R W) : idx A (A ⊓ B) = idx A B :=
  AddSubgroup.inf_relIndex_left A.toAddSubgroup B.toAddSubgroup
end GlobalTheory.DegCnt.DelScale
