-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.cone_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:02.685721+00:00
-- url     : https://prove2.me/submissions/528eb618-ec5c-482c-9b63-4023538f0afa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_SES_ex_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_SES_ex_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_SES_ex_quot
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Tr_aug_up_ex
import Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_Tr_cone_up
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero


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
namespace GlobalTheory.CompanionTheory.NerveCoh
theorem _root_.solution [Quiver.IsThin C] [Quiver.IsThin D] (k : ℕ) :
    ∀ τ : Tr R C D, (∀ T j, (τ.aug T).Ex j) → (cone τ.pull).Ex k := by
  induction k with
  | zero =>
    intro τ h
    exact (τ.coneSES fun T ↦ h T 0).ex_zero (τ.cone_up 0)
  | succ k ih =>
    intro τ h
    have h0 : ∀ T, Function.Injective (τ.fib T) := fun T ↦ h T 0
    refine (τ.coneSES h0).ex_succ τ.cone_up (ih τ.quo fun T j ↦ ?_)
    exact (τ.augSES h0 T).ex_quot (h T) (τ.aug_up_ex T) j
end GlobalTheory.CompanionTheory.NerveCoh
