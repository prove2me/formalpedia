-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cycloChar_toZModPow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:17.268595+00:00
-- url     : https://prove2.me/submissions/a6082594-1434-4cbb-a334-7cef25a27211

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    (cycloChar K σ : ℤ_[p]).toZModPow n = 1 := by
  rw [cycloChar, MonoidHom.comp_apply, cyclotomicCharacter.toZModPow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact @Subsingleton.elim (ZMod 1) _ _ _
  refine (modularCyclotomicCharacter.unique _ _ _ ?_).symm
  intro t ht
  have hp1 : p ^ n ≠ 1 := (Nat.one_lt_pow hn.ne' hp.out.one_lt).ne'
  rw [ZMod.val_one'' hp1, pow_one]
  have ht' : (t : PadicAlgCl p) ^ p ^ n = 1 := by
    have := (mem_rootsOfUnity _ _).1 ht
    simpa using congrArg Units.val this
  exact h _ ht'
end GroundTheory.PAdicHodge
