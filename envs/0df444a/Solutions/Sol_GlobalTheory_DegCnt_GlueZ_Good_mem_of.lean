-- Prove2me | solution 1 for GlobalTheory.DegCnt.GlueZ.Good.mem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:09:24.652909+00:00
-- url     : https://prove2.me/submissions/6989aeca-6ea6-4fed-8901-6ce1d3acb8e6

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
theorem _root_.solution (h : Good H S z M) {x : V} (hx : x ∈ S)
    (hB : ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ M :=
  h.1 ▸ (mem_dual_iff H M x).2 ⟨h.2.1.symm ▸ hx, hB⟩
end Good
end GlobalTheory.DegCnt.GlueZ
