-- Prove2me | solution 1 for LIDT.PMF.totalVariationDistance_eq_sum_max_sub
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:45:04.661323+00:00
-- url     : https://prove2.me/submissions/58861d3b-6bee-45e8-96cb-9f3f6fe13d18

-- Generated proof for PMF.totalVariationDistance_eq_sum_max_sub.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

end LIDT

open LIDT
/-!
# PMF-weighted finite expectation identities

This module contains finite expectation identities stated directly for
Mathlib probability mass functions.  They connect `PMF.map` and
`PMF.bind` to the real-weighted finite sums used by the
low individual degree test averaging layer.

## Main declarations

* `PMF.map_apply_toReal`
* `PMF.realWeightedSum`
* `PMF.realWeightedSumLinearMap`
* `PMF.realWeightedSum_map`
* `PMF.realWeightedSum_bind`
* `PMF.map_sum_smul`
* `PMF.bind_apply_toReal`
* `PMF.bind_sum_smul`
* `PMF.sum_toReal_eq_one`
* `PMF.sum_const_smul`
* `PMF.totalVariationDistance`
* `PMF.totalVariationDistance_eq_sum_max_sub`
* `PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq`
* `PMF.sum_le_sum_add_totalVariationDistance`
* `PMF.sum_rpow_one_div_le_rpow_sum`
* `PMF.realWeightedSum_rpow_one_div_le_rpow`
* `PMF.uniformOfFintype_map_equiv`
* `PMF.uniformOfFintype_prod_apply_toReal`
* `PMF.uniformOfFintype_prod_eq_bind`
* `PMF.uniformOfFintype_sum_equiv_smul`
* `PMF.uniformOfFintype_prod_sum_smul`
* `PMF.uniformOfFintype_sum_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_equiv_snd_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_snd_smul`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators



open LIDT.PMF

theorem solution {α : Type*}
    [Fintype α] (p q : PMF α) :
    _root_.LIDT.PMF.totalVariationDistance p q =
      ∑ a : α, max 0 ((q a).toReal - (p a).toReal) := by
  classical
  have hdiff_sum :
      ∑ a : α, ((q a).toReal - (p a).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, _root_.LIDT.PMF.sum_toReal_eq_one q, _root_.LIDT.PMF.sum_toReal_eq_one p, sub_self]
  have hmax_abs :
      ∀ a : α, max 0 ((q a).toReal - (p a).toReal) =
        (((q a).toReal - (p a).toReal) + |(p a).toReal - (q a).toReal|) / 2 := by
    intro a
    by_cases hle : (q a).toReal - (p a).toReal ≤ 0
    · have hmax :
          max 0 ((q a).toReal - (p a).toReal) = 0 := max_eq_left hle
      have habs :
          |(p a).toReal - (q a).toReal| = (p a).toReal - (q a).toReal := by
        rw [abs_of_nonneg]
        linarith
      rw [hmax, habs]
      ring
    · have hnonneg : 0 ≤ (q a).toReal - (p a).toReal := le_of_not_ge hle
      have hmax :
          max 0 ((q a).toReal - (p a).toReal) =
            (q a).toReal - (p a).toReal := max_eq_right hnonneg
      have habs :
          |(p a).toReal - (q a).toReal| = (q a).toReal - (p a).toReal := by
        have hpq : (p a).toReal ≤ (q a).toReal := by linarith
        rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
        ring
      rw [hmax, habs]
      ring
  calc
    _root_.LIDT.PMF.totalVariationDistance p q =
        (1 / 2) * ∑ a : α, |(p a).toReal - (q a).toReal| := by
          rfl
    _ = (∑ a : α, ((q a).toReal - (p a).toReal) +
          ∑ a : α, |(p a).toReal - (q a).toReal|) / 2 := by
          rw [hdiff_sum]
          ring
    _ = (∑ a : α,
          (((q a).toReal - (p a).toReal) + |(p a).toReal - (q a).toReal|)) /
          2 := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a : α,
          (((q a).toReal - (p a).toReal) + |(p a).toReal - (q a).toReal|) /
            2 := by
          rw [Finset.sum_div]
    _ = ∑ a : α, max 0 ((q a).toReal - (p a).toReal) := by
          exact Finset.sum_congr rfl fun a _ => (hmax_abs a).symm
