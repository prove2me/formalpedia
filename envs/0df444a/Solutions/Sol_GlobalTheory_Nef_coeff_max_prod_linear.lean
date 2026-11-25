-- Prove2me | solution 1 for GlobalTheory.Nef.coeff_max_prod_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:28.457101+00:00
-- url     : https://prove2.me/submissions/890f1e1e-094f-494c-aad0-f4c213086ffc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinear
import Theorems.Thm_GlobalTheory_Nef_coeff_max_mul_linear
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open Polynomial
namespace GlobalTheory.Nef
theorem _root_.solution {F Γ ι : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (α β : ι → F) (s : Finset ι) :
    (∀ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) ≤ ∏ j ∈ s, max (v (α j)) (v (β j))) ∧
      ∃ i, v ((∏ j ∈ s, (C (α j) + C (β j) * X)).coeff i) = ∏ j ∈ s, max (v (α j)) (v (β j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun i => ?_, 0, by simp⟩
    by_cases h : i = 0 <;> simp [coeff_one, h]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coeff_max_mul_linear v _ _ _ _ ih.1 ih.2
end GlobalTheory.Nef
