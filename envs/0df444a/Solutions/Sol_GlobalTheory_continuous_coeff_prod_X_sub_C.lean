-- Prove2me | solution 1 for GlobalTheory.continuous_coeff_prod_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:00.765975+00:00
-- url     : https://prove2.me/submissions/20d7b948-6479-4709-86d0-974864d9b54f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsProdXSubCOfMonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMeasurableRootsEnumeration

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
open Polynomial
namespace GlobalTheory
theorem _root_.solution {ι : Type} (s : Finset ι) (n : ℕ) :
    Continuous fun r : ι → ℂ => (∏ j ∈ s, (X - C (r j))).coeff n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha, coeff_mul]
    refine continuous_finset_sum _ fun p _ => Continuous.mul ?_ (ih _)
    simp only [coeff_sub, coeff_C]
    refine continuous_const.sub ?_
    split_ifs
    · exact continuous_apply a
    · exact continuous_const
end GlobalTheory
