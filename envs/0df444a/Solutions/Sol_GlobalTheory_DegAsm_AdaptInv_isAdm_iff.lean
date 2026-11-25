-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.isAdm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:38.445752+00:00
-- url     : https://prove2.me/submissions/b682146d-77f6-47f6-a52b-ee804bf99eb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_xa_eq
import Theorems.Thm_Formalism_H_dualEquiv_apply
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


section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem sameGr_e_sub_mem_Xa {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G)
    (a : Fin (r + 1)) : G.e a - F.e a ∈ F.Xa a := by
  unfold _root_.GlobalTheory.DegAsm.SameGr at h
  exact h a
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V] in
private theorem sameGr_sub_smul_e_mem_Xa_iff {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) (a : Fin (r + 1)) (t : K) (x : V) :
    x - t • G.e a ∈ G.Xa a ↔ x - t • F.e a ∈ F.Xa a := by
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h]
  have hd := sameGr_e_sub_mem_Xa h a
  have h3 : x - t • G.e a = (x - t • F.e a) - t • (G.e a - F.e a) := by
    rw [smul_sub]
    abel
  rw [h3, Submodule.sub_mem_iff_left _ (Submodule.smul_mem _ t hd)]
end GlobalTheory.DegAsm.AdaptInv
namespace GlobalTheory.DegAsm
open AdaptInv
end GlobalTheory.DegAsm
end

set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.DegAsm.AdaptInv
namespace _root_.GlobalTheory.DegAsm.AdaptInv
theorem _root_.solution {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (Λ : Submodule R V) (g : R) :
    _root_.GlobalTheory.HermLat.IsAdm G G' Λ g ↔ _root_.GlobalTheory.HermLat.IsAdm F F' Λ g := by
  unfold _root_.GlobalTheory.HermLat.IsAdm
  simp only [sameGr_sub_smul_e_mem_Xa_iff h, sameGr_sub_smul_e_mem_Xa_iff h']
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
