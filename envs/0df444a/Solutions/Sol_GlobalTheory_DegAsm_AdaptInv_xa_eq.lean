-- Prove2me | solution 1 for GlobalTheory.DegAsm.AdaptInv.xa_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:07.119262+00:00
-- url     : https://prove2.me/submissions/6aef243e-9ce8-4235-a8c4-4824b92afd08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa
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
theorem _root_.solution {F G : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} (h : _root_.GlobalTheory.DegAsm.SameGr F G) (n : ℕ) :
    G.Xa n = F.Xa n := by
  have key : ∀ n, F.Xa n ≤ G.Xa n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [Xa_eq_span_e_castSucc F n, Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      have hd := sameGr_e_sub_mem_Xa h b.castSucc
      simp only [Fin.coe_castSucc] at hd
      have h1 : G.e b.castSucc ∈ G.Xa n := _root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa G b hb
      have h2 : G.e b.castSucc - F.e b.castSucc ∈ G.Xa n := _root_.Formalism.HermitianLatticeCounting.P.Xa_mono G (le_of_lt hb) (ih b hb hd)
      have h3 := Submodule.sub_mem _ h1 h2
      simpa using h3
  refine le_antisymm ?_ (key n)
  rw [Xa_eq_span_e_castSucc G n, Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  have hd := sameGr_e_sub_mem_Xa h b.castSucc
  simp only [Fin.coe_castSucc] at hd
  have h1 : F.e b.castSucc ∈ F.Xa n := _root_.Formalism.HermitianLatticeCounting.P.e_mem_Xa F b hb
  have h2 : G.e b.castSucc - F.e b.castSucc ∈ F.Xa n := _root_.Formalism.HermitianLatticeCounting.P.Xa_mono F (le_of_lt hb) hd
  have h3 := Submodule.add_mem _ h1 h2
  simpa using h3
end _root_.GlobalTheory.DegAsm.AdaptInv
end GlobalTheory.DegAsm.AdaptInv
