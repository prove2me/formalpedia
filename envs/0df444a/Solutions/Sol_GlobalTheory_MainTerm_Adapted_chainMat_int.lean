-- Prove2me | solution 1 for GlobalTheory.MainTerm.Adapted.chainMat_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:03.646135+00:00
-- url     : https://prove2.me/submissions/bf95556e-fb03-4176-855d-82336dff2358

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Theorems.Thm_GlobalTheory_MainTerm_chainMat_zero
import Theorems.Thm_GlobalTheory_MainTerm_chainMat_succ
import Theorems.Thm_GlobalTheory_MainTerm_Adapted_l_mul_al_two_int
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


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
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) (s : ℕ) (e c0 : I) :
    V.Ge 0 (_root_.GlobalTheory.MainTerm.chainMat D s e c0) := by
  induction s generalizing e with
  | zero =>
    rw [_root_.GlobalTheory.MainTerm.chainMat_zero]
    split_ifs
    · exact _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.one
    · exact _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.zero 0
  | succ s ih =>
    rw [_root_.GlobalTheory.MainTerm.chainMat_succ]
    refine _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun c hc => ?_
    rw [Finset.mem_filter] at hc
    have hgood : D.good c := D.pure_good c (by rw [hc.2.1]; exact hc.2.2)
    exact _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int
      (_root_.GlobalTheory.MainTerm.Adapted.l_mul_al_two_int h hgood e) ((ih c).pow _)
end _root_.GlobalTheory.MainTerm.Adapted
end GlobalTheory.MainTerm
