-- Prove2me | solution 1 for GlobalTheory.FiniteQuotientComap.exists_int_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:08:02.235872+00:00
-- url     : https://prove2.me/submissions/2215cd12-49f5-4cbf-a3d3-d85d9a92110b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteQuotientComap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.FiniteQuotientComap
namespace GlobalTheory.FiniteQuotientComap
theorem _root_.solution {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ b : 𝓞 E, (b : E) = (m : E) * a := by

  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R := ℤ) (Rₘ := ℚ)
    (M := nonZeroDivisors ℤ) a (Algebra.IsIntegral.isIntegral a)
  refine ⟨(m : ℤ), nonZeroDivisors.coe_ne_zero m, (⟨m • a, hm⟩ : 𝓞 E), ?_⟩
  show m • a = _
  rw [Submonoid.smul_def, zsmul_eq_mul]
end GlobalTheory.FiniteQuotientComap
