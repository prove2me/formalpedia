-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.sitesCommonSpace_v0_eq_Vp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:30:45.475182+00:00
-- url     : https://prove2.me/submissions/448061c0-43d7-412e-816b-4fdbe370d0be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_sameGr_symm
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_x_eq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicSpan_le_jointSpan_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVector_mem_jointSpan_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVector_mem_jointSpan_right
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
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem sameGr_z_sub_mem_X {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) : G.z - F.z ∈ F.X := by
  have hd := sameGr_e_sub_mem_Xa h (Fin.last r)
  simp only [Fin.val_last] at hd
  exact hd
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem sameGr_V0_le {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') :
    _root_.Formalism.HermitianLatticeCounting.S6.V0 G G' ≤ _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' := by
  show G.X ⊔ G'.X ⊔ Submodule.span K {G.z, G'.z} ≤ _
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.x_eq h, _root_.GlobalTheory.DegAsm.AdaptInv.x_eq h']
  refine sup_le (sup_le (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left F F') (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right F F')) ?_
  rw [Submodule.span_le]
  rintro v (rfl | rfl)
  · have h3 := Submodule.add_mem _ (_root_.Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_left F F')
      (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left F F' (sameGr_z_sub_mem_X h))
    simpa using h3
  · have h3 := Submodule.add_mem _ (_root_.Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_right F F')
      (_root_.Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right F F' (sameGr_z_sub_mem_X h'))
    simpa using h3
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
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
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.AdaptInv
namespace _root_.GlobalTheory.DegAsm.AdaptInv
theorem _root_.solution {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') : _root_.Formalism.HermitianLatticeCounting.S6.V0 G G' = _root_.Formalism.HermitianLatticeCounting.S6.V0 F F' :=
  le_antisymm (sameGr_V0_le h h')
    (sameGr_V0_le (_root_.GlobalTheory.DegAsm.AdaptInv.sameGr_symm h) (_root_.GlobalTheory.DegAsm.AdaptInv.sameGr_symm h'))
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
