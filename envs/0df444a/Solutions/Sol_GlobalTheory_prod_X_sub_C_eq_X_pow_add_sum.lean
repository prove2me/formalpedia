-- Prove2me | solution 1 for GlobalTheory.prod_X_sub_C_eq_X_pow_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:48.770325+00:00
-- url     : https://prove2.me/submissions/57c3a420-e7f7-47e0-b712-fa37b4153f51

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
theorem _root_.solution {δ : ℕ} (r : Fin δ → ℂ) :
    ∏ j, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C ((∏ j, (X - C (r j))).coeff i) * X ^ (i : ℕ) := by
  have hm : (∏ j, (X - C (r j)) : ℂ[X]).Monic :=
    monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
  have hd : (∏ j, (X - C (r j)) : ℂ[X]).natDegree = δ := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have := hm.as_sum
  rw [hd, Finset.sum_range] at this
  exact this
end GlobalTheory
