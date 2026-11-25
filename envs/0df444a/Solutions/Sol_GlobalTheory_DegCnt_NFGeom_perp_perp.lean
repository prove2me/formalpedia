-- Prove2me | solution 1 for GlobalTheory.DegCnt.NFGeom.perp_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:41:12.335693+00:00
-- url     : https://prove2.me/submissions/030cec11-69d3-4a86-b808-4be6a921c8c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_mem_perp__b010c7cdb5ee
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_memOfOrthogonalOrthogonal
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff


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
open Formalism.HermitianLatticeCounting.P
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NFGeom
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
omit [NumberField K]
namespace GlobalTheory.DegCnt.NFGeom
theorem _root_.solution [FiniteDimensional K V] (S : Submodule K V) : perp H (perp H S) = S := by
  refine le_antisymm (fun w hw => memOfOrthogonalOrthogonal K V H S w fun v hv => ?_) fun s hs => ?_
  · exact (mem_perp_iff H _ _).1 hw v ((mem_perp' S v).2 hv)
  · exact (mem_perp_iff H _ _).2 fun x hx => (mem_perp' S x).1 hx s hs
end GlobalTheory.DegCnt.NFGeom
