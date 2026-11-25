-- Prove2me | solution 1 for GlobalTheory.DegCnt.NFGeom.Wn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:15.173118+00:00
-- url     : https://prove2.me/submissions/8ad35f4f-2543-4ae5-bb33-220bddc31bfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Theorems.Thm_GlobalTheory_DegCnt_NFGeom_mem_perp_sup
import Theorems.Thm_GlobalTheory_DegCnt_NFGeom_z_mem_Wn
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairing_lastVector_lastVector
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
    N.Wn =
      N.Wt ⊔ Submodule.span K {N.F.z} := by
  have hzz : H.B N.F.z N.F.z ≠ 0 := by
    rw [_root_.Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]
    exact neg_ne_zero.2 N.F.hT
  have hz' : N.F'.z = N.c • N.F.z :=
    N.same (Fin.last r) N.j_le
  apply le_antisymm
  · intro v hv
    set t := H.B v N.F.z / H.B N.F.z N.F.z
      with ht
    refine Submodule.mem_sup.2 ⟨v - t • N.F.z, ?_, t • N.F.z,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), sub_add_cancel _ _⟩
    unfold _root_.GlobalTheory.DegCnt.NF.Wn at hv
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hv
    obtain ⟨⟨hX, hX'⟩, hI⟩ := hv
    have hzW := _root_.GlobalTheory.DegCnt.NFGeom.z_mem_Wn N
    unfold _root_.GlobalTheory.DegCnt.NF.Wn at hzW
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hzW
    obtain ⟨⟨zX, zX'⟩, zI⟩ := hzW
    unfold _root_.GlobalTheory.DegCnt.NF.Wt
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
    refine ⟨?_, Submodule.sub_mem _ hI (Submodule.smul_mem _ _ zI)⟩
    unfold _root_.Formalism.HermitianLatticeCounting.S6.V0
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup, _root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
    refine ⟨⟨Submodule.sub_mem _ hX (Submodule.smul_mem _ _ zX),
      Submodule.sub_mem _ hX' (Submodule.smul_mem _ _ zX')⟩, ?_⟩
    have key : H.B (v - t • N.F.z) N.F.z = 0 := by
      rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, ht,
        div_mul_cancel₀ _ hzz, sub_self]
    refine mem_perp_span_of_forall_B_eq_zero fun s hs => ?_
    rcases hs with rfl | hs
    · exact key
    · rw [Set.mem_singleton_iff] at hs
      rw [hs, hz', map_smulₛₗ, key, smul_zero]
  · refine sup_le (fun v hv => ?_)
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 (_root_.GlobalTheory.DegCnt.NFGeom.z_mem_Wn N)))
    unfold _root_.GlobalTheory.DegCnt.NF.Wt at hv
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hv
    obtain ⟨hV, hI⟩ := hv
    unfold _root_.Formalism.HermitianLatticeCounting.S6.V0 at hV
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup] at hV
    unfold _root_.GlobalTheory.DegCnt.NF.Wn
    rw [_root_.GlobalTheory.DegCnt.NFGeom.mem_perp_sup]
    exact ⟨hV.1, hI⟩
end _root_.GlobalTheory.DegCnt.NFGeom
end GlobalTheory.DegCnt.NFGeom
