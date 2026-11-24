-- Prove2me | solution 1 for GlobalTheory.one_le_abs_norm_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:23.137913+00:00
-- url     : https://prove2.me/submissions/2d14025b-09fc-4ec5-9efb-1e92df701ec1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |Algebra.norm ℚ x| := by
  have hn : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hm
    exact h0 hm
  rw [← hm, eq_intCast]
  exact_mod_cast Int.one_le_abs hm0
end GlobalTheory
