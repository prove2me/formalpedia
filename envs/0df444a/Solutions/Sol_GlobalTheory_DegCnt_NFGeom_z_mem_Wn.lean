-- Prove2me | solution 1 for GlobalTheory.DegCnt.NFGeom.z_mem_Wn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:37:32.130822+00:00
-- url     : https://prove2.me/submissions/8c5dc3c5-e676-4cd7-85a0-937346bdd974

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Theorems.Thm_GlobalTheory_DegCnt_NFGeom_mem_perp_sup
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_z_X
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
private theorem mem_perp_span_of_forall_B_eq_zero {S : Set V} {y : V} (h : ∀ s ∈ S, H.B y s = 0) :
    y ∈ _root_.GlobalTheory.HermLat.perp H (Submodule.span K S) := by
  rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
  intro u hu
  have hle : Submodule.span K S ≤ LinearMap.ker (H.B y) :=
    Submodule.span_le.2 fun s hs => LinearMap.mem_ker.2 (h s hs)
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
theorem _root_.solution :
    N.F.z ∈ N.Wn := by
  have hc0 : N.c ≠ 0 := left_ne_zero_of_mul_eq_one N.c_norm
  unfold _root_.GlobalTheory.DegCnt.NF.Wn
  rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
    exact fun u hu => _root_.Formalism.HermitianLatticeCounting.P.z_X _ hu
  · rw [_root_.GlobalTheory.HermLat.mem_perp_iff]
    intro u hu
    have h1 := _root_.Formalism.HermitianLatticeCounting.P.z_X N.F' hu
    have hz : N.F'.z = N.c • N.F.z :=
      N.same (Fin.last r) N.j_le
    rw [hz, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  · unfold _root_.GlobalTheory.DegCnt.NF.Ist
    refine mem_perp_span_of_forall_B_eq_zero fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hs
    exact N.normalForm_dual_orthogonal_last b hb
end _root_.GlobalTheory.DegCnt.NFGeom
end GlobalTheory.DegCnt.NFGeom
