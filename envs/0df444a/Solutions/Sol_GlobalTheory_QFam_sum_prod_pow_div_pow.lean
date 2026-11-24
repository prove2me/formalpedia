-- Prove2me | solution 1 for GlobalTheory.QFam.sum_prod_pow_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:42:34.876789+00:00
-- url     : https://prove2.me/submissions/f7fa9638-6605-4314-8785-a544cb058f18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LevelOneModularFormValueGaloisTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PermutedModularFamilySumEsymmSlashInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TransportPowerSumsModularFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
theorem _root_.solution {ι S : Type} [Fintype ι] [Fintype S] (m μ : S → ℕ) (x : S → ι → ℂ)
    (ω : ℂ) :
    (∑ i, ∏ s, x s i ^ μ s) / ω ^ (∑ s, μ s * m s) = ∑ i, ∏ s, (x s i / ω ^ m s) ^ μ s := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp only [mul_comm]
end GlobalTheory.QFam
