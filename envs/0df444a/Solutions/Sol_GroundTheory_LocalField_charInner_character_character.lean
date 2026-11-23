-- Prove2me | solution 1 for GroundTheory.LocalField.charInner_character_character
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:59.487744+00:00
-- url     : https://prove2.me/submissions/75ab5322-c131-4554-a933-ddd1fd676fe0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
universe u
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
namespace GroundTheory.LocalField
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    charInner G σ.character ρ.character = finrank ℂ (IntertwiningMap ρ σ) := by
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [charInner_apply]
  exact card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
end GroundTheory.LocalField
