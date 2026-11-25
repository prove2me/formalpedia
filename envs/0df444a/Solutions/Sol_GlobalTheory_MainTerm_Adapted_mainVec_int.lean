-- Prove2me | solution 1 for GlobalTheory.MainTerm.Adapted.mainVec_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:06:32.229383+00:00
-- url     : https://prove2.me/submissions/f607a9a9-5ba8-4374-8be1-a44142044641

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Theorems.Thm_GlobalTheory_MainTerm_l_mul_be_one_int
import Theorems.Thm_GlobalTheory_MainTerm_Adapted_chainMat_int
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) (c0 : I) (κ : J) :
    V.Ge 0 (_root_.GlobalTheory.MainTerm.mainVec S D c0 κ) := by
  unfold _root_.GlobalTheory.MainTerm.mainVec
  refine _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int ((_root_.Formalism.L2.FormalSeriesBounds.VF.Ge.one (V := V)).neg.pow _)
    (_root_.Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun c _ => ?_)
  refine _root_.Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int
    ((_root_.GlobalTheory.MainTerm.Adapted.chainMat_int h _ c c0).pow _) ?_
  rw [h.2.1]
  exact _root_.GlobalTheory.MainTerm.l_mul_be_one_int S c κ
end _root_.GlobalTheory.MainTerm.Adapted
end GlobalTheory.MainTerm
