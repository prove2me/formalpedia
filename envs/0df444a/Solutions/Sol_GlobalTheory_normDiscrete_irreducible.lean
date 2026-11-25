-- Prove2me | solution 1 for GlobalTheory.normDiscrete_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:12.084115+00:00
-- url     : https://prove2.me/submissions/21120aa7-d600-48cd-a975-aac921a58868

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_ExistsCompleteDiscreteValuationRingOfIsNormDiscr
import Theorems.Thm_GlobalTheory_normDiscrete_isUnit_iff

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
theorem _root_.solution {π : vRing v} (hπ : v (π : Ω) = 1) : Irreducible π := by
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · rw [normDiscrete_isUnit_iff, hπ] at h
    exact absurd h (by decide)
  · rw [normDiscrete_isUnit_iff, normDiscrete_isUnit_iff]
    have h1 : v (a : Ω) + v (b : Ω) = 1 := by
      rw [← AddValuation.map_mul, ← MulMemClass.coe_mul, ← hab, hπ]
    have ha : 0 ≤ v (a : Ω) := a.2
    have hb : 0 ≤ v (b : Ω) := b.2
    generalize v (a : Ω) = s at h1 ha ⊢
    generalize v (b : Ω) = t at h1 hb ⊢
    induction s using WithTop.recTopCoe with
    | top => simp at h1
    | coe s =>
      induction t using WithTop.recTopCoe with
      | top => simp at h1
      | coe t =>
        norm_cast at h1 ha hb ⊢
        omega
end GlobalTheory
