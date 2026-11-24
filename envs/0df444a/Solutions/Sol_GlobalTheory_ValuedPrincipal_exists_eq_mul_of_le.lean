-- Prove2me | solution 1 for GlobalTheory.ValuedPrincipal.exists_eq_mul_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:11:40.41889+00:00
-- url     : https://prove2.me/submissions/f17ca663-4b70-4928-9635-51e1b64c3f81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete
import Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_val_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuedPrincipal
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace GlobalTheory.ValuedPrincipal
theorem _root_.solution {t a : F} (ht : t ≠ 0) (h : v t ≤ v a) :
    ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ a = c * t := by
  refine ⟨a * t⁻¹, ?_, (inv_mul_cancel_right₀ ht a).symm⟩
  by_cases ha : a = 0
  · rw [ha, zero_mul, v.map_zero]
    exact le_top
  · obtain ⟨r, hr, hri⟩ := exists_val_eq v ht
    obtain ⟨s, hs, -⟩ := exists_val_eq v ha
    rw [hr, hs] at h
    have hrs : r ≤ s := by exact_mod_cast h
    rw [v.map_mul, hs, hri, ← WithTop.coe_add]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ s + -r)
end GlobalTheory.ValuedPrincipal
