-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.ramificationIdx_primeOfPlace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:30:50.869985+00:00
-- url     : https://prove2.me/submissions/df0d65ef-9b25-4328-b810-ecc020e3d137

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_primeHS
import Theorems.Thm_GroundTheory_FunctionField_Place_LiesOver_valuation_algebraMap
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
import Theorems.Thm_GroundTheory_FunctionField_Place_ord_uniformizer
import Theorems.Thm_GroundTheory_FunctionField_Place_uniformizer_ne_zero
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_eq_exp_neg_ord
import Theorems.Thm_P2M_GroundTheory_FunctionField_Place_LiesOver_ramificationIdx__eq_69b785bc37b8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



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
theorem _root_.solution
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    q.1.ramificationIdx v.ring = (v.placeOfPrime q).ramificationIdx v := by
  have := q.2.1
  have := q.2.2
  have : (v.primeHS q).asIdeal.LiesOver v.heightOneSpectrum.asIdeal := q.2.2
  have hp : maximalIdeal v.ring ≠ ⊥ := IsDiscreteValuationRing.not_a_field v.ring
  have h := v.placeOfPrime_liesOver q
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal v.ring) q.1 hp,
    ← h.ramificationIdx'_eq]
  have e1 : v.valuation v.uniformizer ^ (maximalIdeal v.ring).ramificationIdx' q.1 =
      (v.primeHS q).valuation K' (algebraMap K K' v.uniformizer) :=
    HeightOneSpectrum.valuation_liesOver K' v.heightOneSpectrum (v.primeHS q) v.uniformizer
  have e2 := h.valuation_algebraMap v.uniformizer
  rw [valuation_primeHS, ← e2, v.valuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer,
    ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj] at e1
  simpa using e1
end GroundTheory.FunctionField.Place
