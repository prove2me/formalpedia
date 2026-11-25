-- Prove2me | solution 1 for GlobalTheory.MainTerm.tan_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:27.51082+00:00
-- url     : https://prove2.me/submissions/87851780-b46d-4cc5-9693-1fe86741f9a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_bound0
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_cur_zero_inl
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_mem


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
namespace _root_.GlobalTheory.MainTerm
theorem _root_.solution (S : _root_.Formalism.L2.FormalSeriesBounds.Sys G) (c x : I) : V.Ge 0 (S.tan c x) := by
  have h := G.bound0 0 (S.cur c) (S.mem c) (Sum.inl x)
  rw [S.cur_zero_inl] at h
  simpa using h
end _root_.GlobalTheory.MainTerm
end GlobalTheory.MainTerm
