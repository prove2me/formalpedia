-- Prove2me | solution 1 for GlobalTheory.MainTerm.Adapted.mainVec_level_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:07:14.214713+00:00
-- url     : https://prove2.me/submissions/bb1b80a3-2f3e-40f1-bf49-35a09ef982e2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Theorems.Thm_GlobalTheory_MainTerm_chainMat_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (Data Kn s0)
open Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {G : Cart V d I J} {S : Sys G} {Z : Type} {D : Data C Z I} {a : ZMod d} {i : ℕ}
open Classical
variable {C : Type} [Field C]
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ}
namespace GlobalTheory.MainTerm
namespace _root_.GlobalTheory.MainTerm.Adapted
theorem _root_.solution
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a 1) {c0 : I} (hc : D.lev c0 = 0) (κ : J) :
    _root_.GlobalTheory.MainTerm.mainVec S D c0 κ = -((V.l : C) * S.be c0 1 κ) := by
  obtain ⟨-, hl, hi, -, -⟩ := h
  have hl0 : D.l ≠ 0 := by have := D.l_ge; omega
  unfold _root_.GlobalTheory.MainTerm.mainVec
  rw [hi]
  have hs : _root_.Formalism.BaseCaseIdentities.s0 1 = 0 := rfl
  have hk : _root_.Formalism.BaseCaseIdentities.Kn 1 = 1 := rfl
  rw [hs, hk, Finset.sum_eq_single c0]
  · simp [_root_.GlobalTheory.MainTerm.chainMat_zero, hl]
  · intro b _ hb
    simp [_root_.GlobalTheory.MainTerm.chainMat_zero, hb, zero_pow hl0]
  · intro hc0
    simp [hc] at hc0
end _root_.GlobalTheory.MainTerm.Adapted
end GlobalTheory.MainTerm
