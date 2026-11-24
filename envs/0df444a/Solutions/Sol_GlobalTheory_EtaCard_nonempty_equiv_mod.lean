-- Prove2me | solution 1 for GlobalTheory.EtaCard.nonempty_equiv_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:49:11.659638+00:00
-- url     : https://prove2.me/submissions/8d32ae87-040f-458b-94f2-a054b6893786

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsNullVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardLevGrpAndSpan
import Theorems.Thm_GlobalTheory_EtaCard_finrank_fibre

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
theorem _root_.solution (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)] (r : ℕ)
    (hr : Module.finrank O M = r) :
    Nonempty ((M ⧸ (I • ⊤ : Submodule O M)) ≃ₗ[O] (Fin r → O ⧸ I)) := by
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ B.equivFun.restrictScalars O⟩
end GlobalTheory.EtaCard
