-- Prove2me | solution 1 for GlobalTheory.DegCnt.NFGeom.Pi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:08:37.918713+00:00
-- url     : https://prove2.me/submissions/258a2071-97eb-491f-9196-6c9446f99cf9

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
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r)
namespace GlobalTheory.DegCnt.NFGeom
namespace _root_.GlobalTheory.DegCnt.NFGeom
theorem _root_.solution [FiniteDimensional K V] :
    N.Pi =
      _root_.Formalism.HermitianLatticeCounting.S6.V0 N.F N.F' ⊔ N.Ist := by
  apply le_antisymm
  · intro w hw
    unfold _root_.GlobalTheory.DegCnt.NF.Pi at hw
    rw [_root_.GlobalTheory.HermLat.mem_perp_iff] at hw
    exact _root_.Formalism.HermitianLatticeCounting.P.memOfOrthogonalOrthogonal K V H _ w fun v hv => hw v (by
      unfold _root_.GlobalTheory.DegCnt.NF.Wt
      exact (_root_.GlobalTheory.DegCnt.NFGeom.mem_perp' _ _).2 hv)
  · intro w hw
    unfold _root_.GlobalTheory.DegCnt.NF.Pi
    rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
    intro u hu
    unfold _root_.GlobalTheory.DegCnt.NF.Wt at hu
    exact (_root_.GlobalTheory.DegCnt.NFGeom.mem_perp' _ _).1 hu w hw
end _root_.GlobalTheory.DegCnt.NFGeom
end GlobalTheory.DegCnt.NFGeom
