-- Prove2me | solution 1 for GlobalTheory.ValuedPrincipal.exists_val_eq_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:28.051864+00:00
-- url     : https://prove2.me/submissions/a1cbdc39-ab03-4bdb-827e-cbbdcdf49331

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
theorem _root_.solution {π : F} (hπ : v π = ((1 : ℚ) : WithTop ℚ)) (n : ℤ) :
    ∃ y : F, y ≠ 0 ∧ v y = ((n : ℚ) : WithTop ℚ) := by
  have hπ0 : π ≠ 0 := (v.ne_top_iff).1 (by rw [hπ]; exact WithTop.coe_ne_top)
  obtain ⟨r, hr, hri⟩ := exists_val_eq v hπ0
  have hr1 : r = 1 := by
    rw [hπ] at hr
    exact_mod_cast hr.symm
  subst hr1
  induction n using Int.induction_on with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ k ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨y * π, mul_ne_zero hy hπ0, ?_⟩
    rw [v.map_mul, hyv, hπ, ← WithTop.coe_add]
    congr 1
    push_cast
    ring
  | pred k ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨y * π⁻¹, mul_ne_zero hy (inv_ne_zero hπ0), ?_⟩
    rw [v.map_mul, hyv, hri, ← WithTop.coe_add]
    congr 1
    push_cast
    ring
end GlobalTheory.ValuedPrincipal
