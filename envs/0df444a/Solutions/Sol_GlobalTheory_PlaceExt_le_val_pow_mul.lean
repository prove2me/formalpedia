-- Prove2me | solution 1 for GlobalTheory.PlaceExt.le_val_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:06.006176+00:00
-- url     : https://prove2.me/submissions/5b763ae4-e0d6-469d-ad4b-8072015b8893

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
variable {L A : Type*} [Field L] [CommRing A]
namespace GlobalTheory.PlaceExt
theorem _root_.solution (u : AddValuation A (WithTop ℤ)) {t b : A} (ht : 1 ≤ u t) (hb : 0 ≤ u b)
    (m : ℕ) : ((m : ℤ) : WithTop ℤ) ≤ u (t ^ m * b) := by
  induction m with
  | zero => simpa using hb
  | succ m ih =>
    rw [pow_succ', mul_assoc, AddValuation.map_mul]
    calc (((m + 1 : ℕ) : ℤ) : WithTop ℤ) = 1 + ((m : ℤ) : WithTop ℤ) := by
          push_cast; exact add_comm _ _
      _ ≤ _ := add_le_add ht ih
end GlobalTheory.PlaceExt
