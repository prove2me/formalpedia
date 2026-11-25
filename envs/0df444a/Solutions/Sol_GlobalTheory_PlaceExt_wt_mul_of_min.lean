-- Prove2me | solution 1 for GlobalTheory.PlaceExt.wt_mul_of_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:15.701866+00:00
-- url     : https://prove2.me/submissions/318a7990-4ed3-4f9a-92ab-81b478a0a746

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PlaceExt
namespace GlobalTheory.PlaceExt
theorem _root_.solution {a b c : WithTop ℤ} (n : ℕ) (h : ∀ m : ℕ, ∃ p q : WithTop ℤ,
    min a ((m + n : ℕ) : ℤ) = min p ((m + n : ℕ) : ℤ) ∧
      min b ((m + n : ℕ) : ℤ) = min q ((m + n : ℕ) : ℤ) ∧
      min c (m : ℤ) = min (p + q) (m : ℤ)) : c = a + b := by
  obtain ⟨p, q, h1, h2, h3⟩ :=
    h ((a.untopD 0).natAbs + (b.untopD 0).natAbs + (c.untopD 0).natAbs + 1)
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;>
    induction c using WithTop.recTopCoe <;> induction p using WithTop.recTopCoe <;>
    induction q using WithTop.recTopCoe <;>
    simp only [WithTop.untopD_top, WithTop.untopD_coe, le_top, min_eq_right, ← WithTop.coe_min,
      WithTop.coe_inj, top_add, add_top, ← WithTop.coe_add, WithTop.top_ne_coe,
      WithTop.coe_ne_top] at h1 h2 h3 ⊢ <;> omega
end GlobalTheory.PlaceExt
