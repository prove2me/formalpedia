-- Prove2me | solution 1 for GlobalTheory.exists_prod_X_sub_C_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:54.134726+00:00
-- url     : https://prove2.me/submissions/ddbb1ebd-6469-494c-b49e-27203dd91899

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsProdXSubCOfMonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMeasurableRootsEnumeration
import Theorems.Thm_GlobalTheory_MonicRootsProduct_exists_roots


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
theorem _root_.solution {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ,
      ∏ j, (X - C (r j)) = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by
  first
  | exact @_root_.GlobalTheory.MonicRootsProduct.exists_roots
  | exact _root_.GlobalTheory.MonicRootsProduct.exists_roots
  | (apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicRootsProduct.exists_roots <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicRootsProduct.exists_roots <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicRootsProduct.exists_roots ..)
end GlobalTheory
