-- Prove2me | solution 1 for LIDT.PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:47:23.317258+00:00
-- url     : https://prove2.me/submissions/52d6e24d-ae5a-4441-bd45-6b084cf995fc

-- Generated proof for PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq.
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
import Theorems.Thm_LIDT_PMF_totalVariationDistance_eq_sum_max_sub

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

theorem solution
    {α : Type*} [Fintype α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) :
    _root_.LIDT.PMF.totalVariationDistance (PMF.uniformOfFintype α) (PMF.uniformOfFinset s hs) =
      1 - (s.card : _root_.LIDT.MIPStarRE.LDT.Error) / (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error) := by
  classical
  have hs_card_ne_nat : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  have hs_card_ne : (s.card : _root_.LIDT.MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast hs_card_ne_nat
  have hα_card_ne : (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs_pos : 0 < (s.card : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact_mod_cast Nat.pos_of_ne_zero hs_card_ne_nat
  have hs_le_univ_nat : s.card ≤ Fintype.card α := by
    simpa using Finset.card_le_univ s
  have hweight_le :
      1 / (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error) ≤
        1 / (s.card : _root_.LIDT.MIPStarRE.LDT.Error) := by
    exact one_div_le_one_div_of_le hs_pos (by exact_mod_cast hs_le_univ_nat)
  have hweight_inv_le :
      (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error)⁻¹ ≤
        (s.card : _root_.LIDT.MIPStarRE.LDT.Error)⁻¹ := by
    simpa [one_div] using hweight_le
  let g : α → _root_.LIDT.MIPStarRE.LDT.Error := fun a =>
    max 0 ((PMF.uniformOfFinset s hs a).toReal - (PMF.uniformOfFintype α a).toReal)
  have hg_outside : ∀ a, a ∉ s → g a = 0 := by
    intro a ha
    simp [g, PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply, ha,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hg_inside :
      ∀ a ∈ s, g a =
        1 / (s.card : _root_.LIDT.MIPStarRE.LDT.Error) -
          1 / (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error) := by
    intro a ha
    simp [g, PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply, ha,
      ENNReal.toReal_inv, ENNReal.toReal_natCast,
      max_eq_right (sub_nonneg.mpr hweight_inv_le)]
  calc
    _root_.LIDT.PMF.totalVariationDistance (PMF.uniformOfFintype α) (PMF.uniformOfFinset s hs)
        = ∑ a : α, g a := by
          exact _root_.LIDT.PMF.totalVariationDistance_eq_sum_max_sub
            (PMF.uniformOfFintype α) (PMF.uniformOfFinset s hs)
    _ = ∑ a ∈ s, g a := by
          exact (Finset.sum_subset (Finset.subset_univ s)
            (fun a _ ha => hg_outside a ha)).symm
    _ = ∑ _a ∈ s,
          (1 / (s.card : _root_.LIDT.MIPStarRE.LDT.Error) -
            1 / (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error)) := by
          exact Finset.sum_congr rfl hg_inside
    _ = (s.card : _root_.LIDT.MIPStarRE.LDT.Error) *
          (1 / (s.card : _root_.LIDT.MIPStarRE.LDT.Error) -
            1 / (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = 1 - (s.card : _root_.LIDT.MIPStarRE.LDT.Error) /
          (Fintype.card α : _root_.LIDT.MIPStarRE.LDT.Error) := by
          field_simp [hs_card_ne, hα_card_ne]
