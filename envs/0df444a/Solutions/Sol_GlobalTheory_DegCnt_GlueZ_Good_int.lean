-- Prove2me | solution 1 for GlobalTheory.DegCnt.GlueZ.Good.int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:00.101166+00:00
-- url     : https://prove2.me/submissions/b14f82b4-f9be-43dd-a0f3-06c26258c959

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardInnerLatticesWithDefiniteTraceLeNorm
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff


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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.GlueZ
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}
namespace GlobalTheory.DegCnt.GlueZ
namespace Good
theorem _root_.solution (h : Good H S z M) {x y : V} (hx : x ∈ M) (hy : y ∈ M) :
    H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
  ((mem_dual_iff H M x).1 (h.1.symm ▸ hx)).2 y hy
end Good
end GlobalTheory.DegCnt.GlueZ
