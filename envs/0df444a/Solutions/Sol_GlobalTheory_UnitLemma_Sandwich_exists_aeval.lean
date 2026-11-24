-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Sandwich.exists_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:21:12.562707+00:00
-- url     : https://prove2.me/submissions/35e37947-5455-4310-9941-8affed9121a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Theorems.Thm_GlobalTheory_UnitLemma_exists_basis_pow_of_separable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Sandwich
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Sandwich
theorem _root_.solution (hP : B.P.Separable) (x : B.A) : ∃ f : K.E[X], x = aeval B.g f := by
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hP
  refine ⟨∑ i, C (e.repr x i) * X ^ (i : ℕ), ?_⟩
  conv_lhs => rw [← e.sum_repr x]
  simp [map_sum, he, Algebra.smul_def]
end GlobalTheory.UnitLemma.Sandwich
