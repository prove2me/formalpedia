-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.Tr.aug_up_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:58.325107+00:00
-- url     : https://prove2.me/submissions/0430a121-3906-4bcb-8b23-5c987caba153

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Cx_ex_succ_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_key
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_CoD_ev_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
variable {C D : Type} [Category.{0} C] [Category.{0} D]
open GlobalTheory.CompanionTheory.NerveCoh.Tr
variable (τ : Tr R C D)
namespace GlobalTheory.CompanionTheory.NerveCoh.Tr
theorem _root_.solution [Quiver.IsThin C] [Quiver.IsThin D] (T : C) (k : ℕ) : (τ.up.aug T).Ex k := by
  match k with
  | 0 =>
    refine Cx.ex_zero_iff.2 fun j hj ↦ funext fun p ↦ funext fun U ↦ ?_
    have h := congrFun (congrFun hj (pt U)) ⟨(p.1, U), Prod.mkHom p.2 (𝟙 U)⟩
    exact h
  | 1 =>
    refine Cx.ex_succ_iff.2 fun a ha ↦ ?_
    refine ⟨fun p U ↦ (τ.fibD T).ev (𝟙 U) ((a : MCn (τ.up.fibG T) 0) (pt U)) ⟨p.1, p.2⟩, ?_⟩
    funext c
    refine (τ.fibD T).ev_inj fun U' g ↦ ?_
    rw [(τ.fibD T).key a ha c g]
    refine funext fun p ↦ ?_
    rfl
  | k + 2 => exact Cx.ex_succ_iff.2 fun a ha ↦ (τ.fibD T).exact k a ha
end GlobalTheory.CompanionTheory.NerveCoh.Tr
