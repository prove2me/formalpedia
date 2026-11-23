-- Prove2me | solution 1 for GlobalTheory.DatumCoord.eq_of_trace_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:07.666835+00:00
-- url     : https://prove2.me/submissions/a54d6dbe-9c44-4f97-9804-b009bf226109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DatumCoord
variable {E : Type} [Field E] [NumberField E]
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.DatumCoord
namespace _root_.GlobalTheory.DatumCoord
theorem _root_.solution {c d : E}
    (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * c) = Algebra.trace ℚ E ((a : E) * d)) :
    c = d := by
  by_contra hcd
  have hne : c - d ≠ 0 := sub_ne_zero.2 hcd
  have halg : IsAlgebraic ℤ (c - d)⁻¹ :=
    IsFractionRing.isAlgebraic_iff ℤ ℚ _ |>.mpr (.of_finite ℚ _)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have key := h ⟨y • (c - d)⁻¹, hint⟩
  rw [← sub_eq_zero, ← map_sub, ← mul_sub] at key
  change Algebra.trace ℚ E (y • (c - d)⁻¹ * (c - d)) = 0 at key
  rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one,
    show (y : E) = algebraMap ℚ E y by simp, Algebra.trace_algebraMap] at key
  simp [hy, Module.finrank_pos.ne'] at key
end _root_.GlobalTheory.DatumCoord
end GlobalTheory.DatumCoord
