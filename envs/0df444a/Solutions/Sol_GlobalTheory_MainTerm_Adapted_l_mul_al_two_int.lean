-- Prove2me | solution 1 for GlobalTheory.MainTerm.Adapted.l_mul_al_two_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:37.145105+00:00
-- url     : https://prove2.me/submissions/a0b52c78-79a7-42af-8d00-4ca3df29f3f5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono


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
    (h : _root_.GlobalTheory.MainTerm.Adapted S D a i) {c : I} (hc : D.good c) (e : I) :
    V.Ge 0 ((D.l : C) * D.al c 2 e) := by
  obtain ⟨hv, hl, -, -, -⟩ := h
  have h2 := D.al_good c hc 2 e (by norm_num)
  have hge : V.Ge (-1) (D.al c 2 e) := by
    unfold _root_.Formalism.L2.FormalSeriesBounds.VF.Ge
    rw [← hv]
    refine le_trans (le_of_eq ?_) h2
    norm_num
  rw [hl]
  exact hge.l_mul.mono (by norm_num)
end _root_.GlobalTheory.MainTerm.Adapted
end GlobalTheory.MainTerm
