-- Prove2me | solution 1 for GlobalTheory.DegCnt.NFGeom.proj_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:37.454096+00:00
-- url     : https://prove2.me/submissions/339a1c93-7c3b-44f8-85a3-7c2b6889337a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Theorems.Thm_GlobalTheory_DegCnt_NFGeom_proj_apply

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
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r)
namespace GlobalTheory.DegCnt.NFGeom
namespace _root_.GlobalTheory.DegCnt.NFGeom
theorem _root_.solution {y : V}
    (h : ∀ u ∈ N.Ist, H.B y u = 0) : _root_.GlobalTheory.DegCnt.NFGeom.proj N y = 0 := by
  rw [_root_.GlobalTheory.DegCnt.NFGeom.proj_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hu : N.ist b ∈ N.Ist := by
    unfold _root_.GlobalTheory.DegCnt.NF.Ist
    exact Submodule.subset_span ⟨b, (Finset.mem_filter.1 hb).2, rfl⟩
  rw [h _ hu, zero_smul]
end _root_.GlobalTheory.DegCnt.NFGeom
end GlobalTheory.DegCnt.NFGeom
