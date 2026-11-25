-- Prove2me | solution 1 for GlobalTheory.MainTerm.Adapted.mainVec_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:04.183442+00:00
-- url     : https://prove2.me/submissions/a3718478-77fd-4b98-aa59-1055ce8533d5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Theorems.Thm_GlobalTheory_MainTerm_two_mul_chainStartIndex_add_one_of_odd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_pure


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
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) (c0 : I) (κ : J)
    (hκ : G.ty (Sum.inr κ) ≠ a + (i : ZMod d)) : _root_.GlobalTheory.MainTerm.mainVec S D c0 κ = 0 := by
  obtain ⟨-, -, hi, -, hty⟩ := h
  unfold _root_.GlobalTheory.MainTerm.mainVec
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun c hc => ?_)
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hlev, hlt⟩ := hc
  have hodd : Odd i := hi ▸ D.i_odd
  have hc' := hty c (by rw [hlev, hi]; rwa [hi] at hlt)
  have h2 : ((i : ℕ) : ZMod d) = ((2 * _root_.Formalism.BaseCaseIdentities.s0 i + 1 : ℕ) : ZMod d) := by
    rw [_root_.GlobalTheory.MainTerm.two_mul_chainStartIndex_add_one_of_odd hodd]
  have hbe : S.be c 1 κ = 0 := by
    unfold _root_.Formalism.L2.FormalSeriesBounds.Sys.be
    apply S.pure c 1 (Sum.inr κ)
    rw [hc', hlev, hi]
    intro heq
    apply hκ
    rw [heq, h2]
    push_cast
    ring
  rw [hbe]
  simp
end _root_.GlobalTheory.MainTerm.Adapted
end GlobalTheory.MainTerm
