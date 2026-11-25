-- Prove2me | solution 1 for GlobalTheory.DegCnt.NFGeom.sub_proj_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:07.65967+00:00
-- url     : https://prove2.me/submissions/4089a4d0-06df-4cdd-8d30-e5daab071135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Theorems.Thm_GlobalTheory_DegCnt_NFGeom_proj_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
noncomputable section
namespace GlobalTheory.DegCnt.NFGeom
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (N : _root_.GlobalTheory.DegCnt.NF H r) in
private theorem sub_proj_mem_perp_Ist (y : V) :
    y - _root_.GlobalTheory.DegCnt.NFGeom.proj N y ∈ _root_.GlobalTheory.HermLat.perp H N.Ist := by
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
  intro u hu
  have hle : N.Ist ≤
      LinearMap.ker (H.B (y - _root_.GlobalTheory.DegCnt.NFGeom.proj N y)) := by
    unfold _root_.GlobalTheory.DegCnt.NF.Ist
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : N.j ≤ b.val := hb
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply,
      _root_.GlobalTheory.DegCnt.NFGeom.proj_apply, map_sum, LinearMap.sum_apply]
    simp_rw [map_smul, LinearMap.smul_apply, N.ist_e _ _ hb']
    simp [hb']
  exact LinearMap.mem_ker.1 (hle hu)
end GlobalTheory.DegCnt.NFGeom
namespace GlobalTheory.DegCnt
end GlobalTheory.DegCnt
end
end

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
theorem _root_.solution (y : V) :
    y - _root_.GlobalTheory.DegCnt.NFGeom.proj N y ∈ _root_.GlobalTheory.HermLat.perp H N.Ist :=
  sub_proj_mem_perp_Ist N y
end _root_.GlobalTheory.DegCnt.NFGeom
end GlobalTheory.DegCnt.NFGeom
