-- Prove2me | solution 1 for GlobalTheory.PlaceExt.wt_eq_of_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:29:31.701728+00:00
-- url     : https://prove2.me/submissions/76cc7a16-eac3-4b30-96bb-7410dfd96aad

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
theorem _root_.solution {a p : WithTop ℤ} (h : ∀ m : ℕ, min a (m : ℤ) = min p (m : ℤ)) : a = p := by
  have h' := h ((a.untopD 0).natAbs + (p.untopD 0).natAbs + 1)
  induction a using WithTop.recTopCoe <;> induction p using WithTop.recTopCoe <;>
    simp only [WithTop.untopD_top, WithTop.untopD_coe, le_top, min_eq_right, ← WithTop.coe_min,
      WithTop.coe_inj] at h' ⊢ <;> omega
end GlobalTheory.PlaceExt
