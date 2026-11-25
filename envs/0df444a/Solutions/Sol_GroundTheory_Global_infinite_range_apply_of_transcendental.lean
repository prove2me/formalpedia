-- Prove2me | solution 1 for GroundTheory.Global.infinite_range_apply_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:57.401038+00:00
-- url     : https://prove2.me/submissions/9506ab21-8320-46bf-9858-04a78b227693

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ExistsRingEquivExtendOfIsTranscendenceBasis
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AutCFixed
import Theorems.Thm_GroundTheory_Global_exists_algEquiv_apply_eq_of_transcendental

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Polynomial IntermediateField
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] {F : Type*} [Field F] [Algebra F Ω]
variable [CharZero Ω]
namespace GroundTheory.Global
theorem _root_.solution {x : Ω} (hx : Transcendental ℚ x) :
    (Set.range fun σ : Ω ≃+* Ω => σ x).Infinite := by
  have hx' : Transcendental ℚ (x + 1) := fun h' =>
    hx (by simpa using (h'.isIntegral.sub isIntegral_one).isAlgebraic)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_transcendental hx hx'
  have hpow : ∀ n : ℕ, (σ ^ n) x = x + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_add, hσ, map_natCast]
      push_cast; ring
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => x + n) ?_ fun n =>
    ⟨(σ ^ n).toRingEquiv, hpow n⟩
  intro m n hmn
  exact_mod_cast add_left_cancel hmn
end GroundTheory.Global
