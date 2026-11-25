-- Prove2me | solution 1 for GlobalTheory.PlaceExt.wt_add_of_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:06.796341+00:00
-- url     : https://prove2.me/submissions/e01973fd-dbed-4291-8df7-6a96b47e649b

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
theorem _root_.solution {a b c : WithTop ℤ} (h : ∀ m : ℕ, ∃ p q r : WithTop ℤ,
    min a (m : ℤ) = min p (m : ℤ) ∧ min b (m : ℤ) = min q (m : ℤ) ∧
      min c (m : ℤ) = min r (m : ℤ) ∧ min p q ≤ r) : min a b ≤ c := by
  obtain ⟨p, q, r, h1, h2, h3, h4⟩ := h ((c.untopD 0).natAbs + 1)
  induction c using WithTop.recTopCoe with
  | top => exact le_top
  | coe c =>
    have hc : (c : WithTop ℤ) < ((((c.natAbs + 1 : ℕ) : ℤ)) : WithTop ℤ) := by
      rw [WithTop.coe_lt_coe]; omega
    simp only [WithTop.untopD_coe] at h1 h2 h3
    generalize ((((c.natAbs + 1 : ℕ) : ℤ)) : WithTop ℤ) = M at *
    generalize (c : WithTop ℤ) = c' at *
    grind
end GlobalTheory.PlaceExt
