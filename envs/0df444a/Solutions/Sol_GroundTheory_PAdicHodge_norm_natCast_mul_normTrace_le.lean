-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_natCast_mul_normTrace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:17.719884+00:00
-- url     : https://prove2.me/submissions/0aa26b03-c1a8-47d1-a995-0a0c3261c6ed

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_norm_nextCoeff_minpoly_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module IntermediateField
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (F : Type*) [Field F] [Algebra ℚ_[p] F]
    [Algebra F (PadicAlgCl p)] [IsScalarTower ℚ_[p] F (PadicAlgCl p)] (y : PadicAlgCl p) {N : ℕ}
    (hN : (minpoly F y).natDegree ∣ N) : ‖(N : PadicAlgCl p) * normTrace F y‖ ≤ ‖y‖ := by
  have hy : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  obtain ⟨m, rfl⟩ := hN
  have hd : ((minpoly F y).natDegree : PadicAlgCl p) ≠ 0 :=
    Nat.cast_ne_zero.2 (minpoly.natDegree_pos hy).ne'
  have e : (((minpoly F y).natDegree * m : ℕ) : PadicAlgCl p) * normTrace F y =
      (m : PadicAlgCl p) * -algebraMap F (PadicAlgCl p) (minpoly F y).nextCoeff := by
    rw [normTrace, normTraceF, map_div₀, map_neg, map_natCast]
    push_cast
    field_simp
  rw [e, norm_mul, norm_neg]
  calc ‖(m : PadicAlgCl p)‖ * ‖algebraMap F (PadicAlgCl p) (minpoly F y).nextCoeff‖
      ≤ 1 * ‖y‖ := mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ m)
        (norm_nextCoeff_minpoly_le F y) (norm_nonneg _) zero_le_one
    _ = ‖y‖ := one_mul _
end GroundTheory.PAdicHodge
