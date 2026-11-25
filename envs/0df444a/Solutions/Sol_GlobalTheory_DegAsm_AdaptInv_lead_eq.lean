-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.lead_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:43.823016+00:00
-- url     : https://prove2.me/submissions/9e179c2c-77e1-4a57-b1c3-50e69ebd292c

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
theorem _root_.solution {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    (h : _root_.GlobalTheory.DegAsm.SameGr F G) (Λ : Submodule R V) (a : Fin (r + 1)) :
    _root_.GlobalTheory.HermLat.lead G Λ a = _root_.GlobalTheory.HermLat.lead F Λ a := by
  unfold _root_.GlobalTheory.HermLat.lead
  rw [_root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h]
  ext t
  simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply]
  have hd : t • (G.e a - F.e a) ∈ Λ ⊔ _root_.GlobalTheory.HermLat.rs R (F.Xa a) := by
    apply Submodule.mem_sup_right
    unfold _root_.GlobalTheory.HermLat.rs
    rw [Submodule.restrictScalars_mem]
    exact Submodule.smul_mem _ t (sameGr_e_sub_mem_Xa h a)
  have h3 : t • G.e a = t • F.e a + t • (G.e a - F.e a) := by
    rw [smul_sub]
    abel
  rw [h3, Submodule.add_mem_iff_left _ hd]
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
