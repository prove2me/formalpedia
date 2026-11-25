-- Prove2me | solution 1 for GlobalTheory.normDiscrete_associated_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:10.531881+00:00
-- url     : https://prove2.me/submissions/26903156-12b9-4d08-a2df-35801d8eeb69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_ExistsCompleteDiscreteValuationRingOfIsNormDiscr
import Theorems.Thm_GlobalTheory_normDiscrete_mem_vRing_iff
import Theorems.Thm_GlobalTheory_normDiscrete_map_inv
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
theorem _root_.solution {π : vRing v} (hπ : v (π : Ω) = 1) (x : vRing v) {n : ℕ}
    (hx : v (x : Ω) = ((n : ℤ) : WithTop ℤ)) : Associated (π ^ n) x := by
  have hπ0 : (π : Ω) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hπ
    exact WithTop.top_ne_one hπ
  have hpn : v ((π : Ω) ^ n) = ((n : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_pow, hπ]
    simp
  have h1 : v ((x : Ω) * ((π : Ω) ^ n)⁻¹) = 0 := by
    rw [AddValuation.map_mul, normDiscrete_map_inv hpn, hx, ← WithTop.coe_add]
    simp
  let u : vRing v := ⟨_, (normDiscrete_mem_vRing_iff _).mpr h1.ge⟩
  have hu : IsUnit u := (normDiscrete_isUnit_iff u).mpr h1
  refine ⟨hu.unit, Subtype.ext ?_⟩
  have := pow_ne_zero n hπ0
  simp only [IsUnit.unit_spec, MulMemClass.coe_mul, SubmonoidClass.coe_pow, u]
  field_simp
end GlobalTheory
