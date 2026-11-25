-- Prove2me | solution 1 for GlobalTheory.normDiscrete_exists_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:23:49.589041+00:00
-- url     : https://prove2.me/submissions/718049d5-2de7-4cd3-ac16-bceb002eab42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_ExistsCompleteDiscreteValuationRingOfIsNormDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory
variable {Ω : Type*} [Field Ω] {v : AddValuation Ω (WithTop ℤ)}
namespace GlobalTheory
theorem _root_.solution (hv : IsNormDiscrete v) (x : vRing v) (hx : x ≠ 0) :
    ∃ n : ℕ, v (x : Ω) = ((n : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hv.1 x fun h => hx (Subtype.ext h))
  have h0 : 0 ≤ v (x : Ω) := x.2
  rw [← hm] at h0 ⊢
  have h1 : 0 ≤ m := by exact_mod_cast h0
  exact ⟨m.toNat, by rw [Int.toNat_of_nonneg h1]⟩
end GlobalTheory
