-- Prove2me | solution 1 for GlobalTheory.ValuedPrincipal.exists_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:40.116035+00:00
-- url     : https://prove2.me/submissions/9026410b-ccf1-4230-a3c4-20b4798e8c28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete

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
theorem _root_.solution {x : F} (hx : x ≠ 0) :
    ∃ r : ℚ, v x = (r : WithTop ℚ) ∧ v x⁻¹ = ((-r : ℚ) : WithTop ℚ) := by
  have hit : v x⁻¹ ≠ ⊤ := (v.ne_top_iff).2 (inv_ne_zero hx)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((v.ne_top_iff).2 hx)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hit
  refine ⟨r, hr.symm, ?_⟩
  have hsum : v x + v x⁻¹ = 0 := by
    rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  rw [← hr, ← hs, ← WithTop.coe_add] at hsum
  have h0 : r + s = 0 := by exact_mod_cast hsum
  rw [← hs]
  congr 1
  linarith
end GlobalTheory.ValuedPrincipal
