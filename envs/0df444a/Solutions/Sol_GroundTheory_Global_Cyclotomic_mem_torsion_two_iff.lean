-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.mem_torsion_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:29.416252+00:00
-- url     : https://prove2.me/submissions/af2cf588-7811-4952-a0b7-6c791e031599

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
import Theorems.Thm_GroundTheory_Global_Cyclotomic_mem_torsion_iff
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply



set_option autoImplicit false
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (u : ℤ_[2]ˣ) :
    u ∈ CommGroup.torsion ℤ_[2]ˣ ↔ u = 1 ∨ u = -1 := by
  rw [mem_torsion_iff, torsionExponent, if_pos rfl]
  constructor
  · intro h
    have h1 := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq, mul_self_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (Units.ext h1)
    · exact Or.inr (Units.ext (by rw [h1, Units.val_neg, Units.val_one]))
  · rintro (rfl | rfl) <;> simp
end GroundTheory.Global.Cyclotomic
