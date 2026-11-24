-- Prove2me | solution 1 for GlobalTheory.EtaCard.nonempty_aut_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:53.012558+00:00
-- url     : https://prove2.me/submissions/fe706ed6-a770-433b-8261-435c86f53746

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsNullVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardLevGrpAndSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaCard
namespace GlobalTheory.EtaCard
theorem _root_.solution (O N : Type) [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O) (r : ℕ)
    (e : N ≃ₗ[O] (Fin r → O ⧸ I)) : Nonempty ((N ≃ₗ[O] N) ≃ GL (Fin r) (O ⧸ I)) := by
  have hs : Function.Surjective (algebraMap O (O ⧸ I)) := Ideal.Quotient.mk_surjective
  let e1 : (N ≃ₗ[O] N) ≃ ((Fin r → O ⧸ I) ≃ₗ[O ⧸ I] (Fin r → O ⧸ I)) :=
    { toFun := fun g => (e.symm ≪≫ₗ g ≪≫ₗ e).extendScalarsOfSurjective hs
      invFun := fun g => e ≪≫ₗ g.restrictScalars O ≪≫ₗ e.symm
      left_inv := fun g => by ext x; simp
      right_inv := fun g => by ext x; simp }
  exact ⟨e1.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.toEquiv.trans
    Matrix.GeneralLinearGroup.toLin.symm.toEquiv)⟩
end GlobalTheory.EtaCard
