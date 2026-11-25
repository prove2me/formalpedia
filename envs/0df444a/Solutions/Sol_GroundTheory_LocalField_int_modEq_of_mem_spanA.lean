-- Prove2me | solution 1 for GroundTheory.LocalField.int_modEq_of_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:06:44.9118+00:00
-- url     : https://prove2.me/submissions/e7922599-d2de-4a5d-aed1-98d8e2ba5bbf

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_congrData_of_mem_spanA
import Theorems.Thm_GroundTheory_LocalField_CongrData_exists_pow_eq
import Theorems.Thm_GroundTheory_LocalField_exists_int_of_mul_eq_int


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
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
variable {E : Subgroup G → Prop}
namespace GroundTheory.LocalField
theorem _root_.solution (hζ : IsPrimitiveRoot ζ (Nat.card G)) {p k : ℕ} (hp : p.Prime) {b : ℤ}
    (hab : s ^ a * s ^ b = s) (hb : (s ^ b) ^ p ^ k = 1) {f : G → ℂ} (hf : f ∈ spanA E ζ) {u v : ℤ}
    (hu : f s = u) (hv : f (s ^ a) = v) : (u : ZMod p) = v := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr, hrr⟩ := (congrData_of_mem_spanA hζ hab hb hf).exists_pow_eq hp
  rw [hu, hv] at hrr
  have hint := hζ.isIntegral Nat.card_pos
  obtain ⟨z, -, hz⟩ := exists_int_of_mul_eq_int hint hr (d := p) (k := u ^ p ^ k - v ^ p ^ k)
    (Int.natCast_ne_zero.mpr hp.ne_zero) (by push_cast; rw [hrr]; ring)
  have hmod : ((u ^ p ^ k : ℤ) : ZMod p) = ((v ^ p ^ k : ℤ) : ZMod p) := by
    rw [← sub_eq_zero, ← Int.cast_sub, ← hz]
    push_cast
    simp
  push_cast at hmod
  rwa [ZMod.pow_card_pow, ZMod.pow_card_pow] at hmod
end GroundTheory.LocalField
