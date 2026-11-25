-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.dl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:11:27.069085+00:00
-- url     : https://prove2.me/submissions/2e51648a-c9bd-4bcd-9d34-25c5561b8d0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_sum_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_swap
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
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem det_of_eq_of_sub_mem_span_lt {l : ℕ} (u u' w : Fin l → V)
    (h : ∀ a, u' a - u a ∈ Submodule.span K (u '' {c | c < a})) :
    (Matrix.of fun a b => H.B (u' a) (w b)).det = (Matrix.of fun a b => H.B (u a) (w b)).det := by
  choose L hLsupp hL using fun a => (Finsupp.mem_span_image_iff_linearCombination K).1 (h a)
  set M : Matrix (Fin l) (Fin l) K := 1 + Matrix.of fun a c => L a c with hM
  have hrow : ∀ a, u' a = ∑ c, M a c • u c := by
    intro a
    have h1 := hL a
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simp only [hM, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, add_smul,
      Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, h1]
    abel
  have hmat : (Matrix.of fun a b => H.B (u' a) (w b)) = M * Matrix.of fun a b => H.B (u a) (w b) := by
    ext a b
    rw [Matrix.of_apply, hrow a, _root_.Formalism.HermitianLatticeCounting.P.B_sum_left, Matrix.mul_apply]
    simp only [Matrix.of_apply]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      have h0 : L a a = 0 := (Finsupp.mem_supported' K (L a)).1 (hLsupp a) a (by simp)
      simp [hM, h0]
    · intro i j hij
      have hij' : i < j := hij
      have h0 : L i j = 0 :=
        (Finsupp.mem_supported' K (L i)).1 (hLsupp i) j (by simpa using hij'.le)
      simp [hM, h0, Matrix.one_apply_ne hij'.ne]
  rw [hmat, Matrix.det_mul, hdet, one_mul]
open NumberField in
open scoped Pointwise ENNReal Classical in
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem sameGr_Dl_left_eq {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G)
    (F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (l : ℕ) (hl : l ≤ r + 1) : _root_.Formalism.HermitianLatticeCounting.S6.Dl G F' l hl = _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl := by
  rw [_root_.Formalism.HermitianLatticeCounting.P.Dl_eq, _root_.Formalism.HermitianLatticeCounting.P.Dl_eq]
  apply det_of_eq_of_sub_mem_span_lt (fun a => F.e (Fin.castLE hl a))
    (fun a => G.e (Fin.castLE hl a))
  intro a
  have hd := sameGr_e_sub_mem_Xa h (Fin.castLE hl a)
  simp only [Fin.coe_castLE] at hd
  refine (show F.Xa a ≤ _ from ?_) hd
  rw [Xa_eq_span_e_castSucc F, Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨b.val, by have := a.isLt; simp only [Set.mem_setOf_eq] at hb; omega⟩, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq] at hb ⊢
    exact Fin.mk_lt_of_lt_val hb
  · simp only
    congr 1
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
theorem _root_.solution {F G F' G' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (h' : _root_.GlobalTheory.DegAsm.SameGr F' G') (l : ℕ) (hl : l ≤ r + 1) :
    _root_.Formalism.HermitianLatticeCounting.S6.Dl G G' l hl = _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl := by
  calc _root_.Formalism.HermitianLatticeCounting.S6.Dl G G' l hl = _root_.Formalism.HermitianLatticeCounting.S6.Dl F G' l hl := sameGr_Dl_left_eq h G' l hl
    _ = star (_root_.Formalism.HermitianLatticeCounting.S6.Dl G' F l hl) := _root_.Formalism.HermitianLatticeCounting.P.Dl_swap G' F l hl
    _ = star (_root_.Formalism.HermitianLatticeCounting.S6.Dl F' F l hl) := by rw [sameGr_Dl_left_eq h' F l hl]
    _ = _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl := (_root_.Formalism.HermitianLatticeCounting.P.Dl_swap F' F l hl).symm
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
