-- Prove2me | solution 1 for GlobalTheory.DegCnt.NFGeom.mem_perp_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:17.675121+00:00
-- url     : https://prove2.me/submissions/10850313-cbe3-459e-a188-8ce070a887c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_mem_perp__b010c7cdb5ee
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_sup
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



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
omit [NumberField K]
namespace GlobalTheory.DegCnt.NFGeom
namespace _root_.GlobalTheory.DegCnt.NFGeom
theorem _root_.solution (S T : Submodule K V) (y : V) :
    y ∈ _root_.GlobalTheory.HermLat.perp H (S ⊔ T) ↔
      y ∈ _root_.GlobalTheory.HermLat.perp H S ∧ y ∈ _root_.GlobalTheory.HermLat.perp H T := by
  simp only [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp']
  refine ⟨fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx),
    fun x hx => h x (Submodule.mem_sup_right hx)⟩, fun h => ?_⟩
  intro x hx
  exact _root_.Formalism.HermitianLatticeCounting.P.perp_sup H h.1 h.2 x hx
end _root_.GlobalTheory.DegCnt.NFGeom
end GlobalTheory.DegCnt.NFGeom
