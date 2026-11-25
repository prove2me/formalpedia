-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.inN_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:30:51.151883+00:00
-- url     : https://prove2.me/submissions/99316546-f18e-4953-b6d3-eed353207b8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_xa_eq
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_x_eq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
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
private theorem Xa_eq_span_e_castSucc (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (n : ℕ) :
    F.Xa n = Submodule.span K ((fun b : Fin r => F.e b.castSucc) '' {b | b.val < n}) := rfl
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
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.AdaptInv
namespace _root_.GlobalTheory.DegAsm.AdaptInv
theorem _root_.solution {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (s : V →ₗ[K] V) (hs : F.InN s) : G.InN s := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN at hs ⊢
  obtain ⟨hiso, hbij, hflag, hperp⟩ := hs
  refine ⟨hiso, hbij, ?_, ?_⟩
  · have hXa : ∀ n, ∀ x ∈ F.Xa n, s x - x ∈ F.Xa n := by
      intro n x hx
      have hle : Submodule.span K ((fun b : Fin r => F.e b.castSucc) '' {b | b.val < n}) ≤
          (F.Xa n).comap (s - LinearMap.id) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
        exact _root_.Formalism.HermitianLatticeCounting.P.Xa_mono F (le_of_lt hb) (hflag b)
      have h3 := hle (by rwa [← Xa_eq_span_e_castSucc])
      simpa using h3
    intro a
    rw [_root_.GlobalTheory.DegAsm.AdaptInv.xa_eq h]
    have hd := sameGr_e_sub_mem_Xa h a.castSucc
    simp only [Fin.coe_castSucc] at hd
    have h3 := Submodule.add_mem _ (hflag a) (hXa a _ hd)
    convert h3 using 1
    rw [map_sub]
    abel
  · intro y hy
    rw [_root_.GlobalTheory.DegAsm.AdaptInv.x_eq h]
    apply hperp
    intro a
    have hmem : F.e a.castSucc ∈ G.X := by
      rw [_root_.GlobalTheory.DegAsm.AdaptInv.x_eq h]
      exact _root_.Formalism.HermitianLatticeCounting.P.e_mem_X F a
    exact _root_.Formalism.HermitianLatticeCounting.P.perp_X G hy _ hmem
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
