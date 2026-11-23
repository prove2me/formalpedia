-- Prove2me | solution 1 for GlobalTheory.FlatDescent.isUnit_appTop_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:33.265472+00:00
-- url     : https://prove2.me/submissions/174dda41-57f7-4e03-9493-f6be1056866e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_injective_appTop_of_epi
import Theorems.Thm_GlobalTheory_FlatDescent_exists_appTop_eq_of_effectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_appTop_appTop_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution (p : Y ⟶ X) [EffectiveEpi p] (a : Γ(X, ⊤)) :
    IsUnit (p.appTop a) ↔ IsUnit a := by
  refine ⟨fun ha => ?_, fun ha => ha.map p.appTop.hom⟩
  obtain ⟨t, ht⟩ := ha.exists_right_inv
  have h := IsPullback.of_hasPullback p p
  obtain ⟨b, rfl⟩ := exists_appTop_eq_of_effectiveEpi p h t (by
    have h1 := congrArg (pullback.fst p p).appTop.hom ht
    have h2 := congrArg (pullback.snd p p).appTop.hom ht
    rw [map_mul, map_one] at h1 h2
    rw [appTop_appTop_eq h.w a] at h1
    exact left_inv_eq_right_inv ((mul_comm _ _).trans h1) h2)
  exact IsUnit.of_mul_eq_one b (injective_appTop_of_epi p (by rw [map_mul, ht, map_one]))
end GlobalTheory.FlatDescent
