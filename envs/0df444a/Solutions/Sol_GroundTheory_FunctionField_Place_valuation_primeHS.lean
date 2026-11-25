-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.valuation_primeHS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:23:35.452793+00:00
-- url     : https://prove2.me/submissions/2bc4a2df-791c-4641-8acd-3b11d9971e44

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Theorems.Thm_GroundTheory_FunctionField_valuation_eq_of_isEquiv
import Theorems.Thm_GroundTheory_FunctionField_Place_eq_of_le
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
attribute [local instance low] algebraExt
attribute [local instance] isScalarTower_ext
attribute [local instance] isTorsionFree_ext
variable [IsFunctionField k K] [IsFunctionField k K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] (v : Place k K)
attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure
namespace GroundTheory.FunctionField.Place
theorem _root_.solution (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    (v.primeHS q).valuation K' = (v.placeOfPrime q).valuation := by
  symm
  refine valuation_eq_of_isEquiv ?_ (v.placeOfPrime q).valuation_surjective
    (HeightOneSpectrum.valuation_surjective K' _)
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [Place.valuation_le_one_iff]
  have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
  let P : Place k K' :=
    { ring := ((v.primeHS q).valuation K').valuationSubring
      ne_top := by
        intro htop
        obtain ⟨π, hπ⟩ := (v.primeHS q).valuation_exists_uniformizer K'
        have hmem : π⁻¹ ∈ ((v.primeHS q).valuation K').valuationSubring :=
          htop ▸ ValuationSubring.mem_top _
        rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg,
          ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
        omega
      algebraMap_mem := fun c => hle ((v.placeOfPrime q).algebraMap_mem c) }
  have heq : v.placeOfPrime q = P := Place.eq_of_le hle
  constructor
  · intro hx
    exact hle hx
  · intro hx
    have hxP : x ∈ P.ring := hx
    rw [← heq] at hxP
    exact hxP
end GroundTheory.FunctionField.Place
