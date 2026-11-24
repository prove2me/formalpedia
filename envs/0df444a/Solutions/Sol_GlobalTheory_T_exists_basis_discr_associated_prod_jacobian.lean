-- Prove2me | solution 1 for GlobalTheory.T.exists_basis_discr_associated_prod_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:10.880751+00:00
-- url     : https://prove2.me/submissions/6202542d-f89c-40f9-b70b-b951a8d8c25b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPoints
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
import Theorems.Thm_GlobalTheory_KeyKa_discr_jacobian_of_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (g : ℕ) (Ix : Type) [Fintype Ix] [DecidableEq Ix] (F : Fin g → (MvPowerSeries (Fin g) O)) (e : Ix → ((MvPowerSeries (Fin g) O) →ₐ[O] O)), (∀ a i, e a (F i) = 0) → (∀ a i, e a (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal O) → (∀ G, (∀ a, e a G = 0) → G ∈ Ideal.span (Set.range F)) → (∃ c : O, c ≠ 0 ∧ ∀ t : Ix → O, ∃ G, ∀ a, e a G = c * t a) → ∃ β : Ix → (MvPowerSeries (Fin g) O), (∀ G, ∃! r : Ix → O, G - ∑ a, r a • β a ∈ Ideal.span (Set.range F)) ∧ (Matrix.of fun a a' => e a (β a')).det ≠ 0 ∧ Associated ((Matrix.of fun a a' => e a (β a')).det ^ 2) (∏ a, e a (Matrix.of fun i j => MvPowerSeries.pderiv O j (F i)).det) := by
  first | exact @GlobalTheory.KeyKa.discr_jacobian_of_points | exact GlobalTheory.KeyKa.discr_jacobian_of_points | (intros; apply GlobalTheory.KeyKa.discr_jacobian_of_points <;> assumption)
end _root_.GlobalTheory.T
