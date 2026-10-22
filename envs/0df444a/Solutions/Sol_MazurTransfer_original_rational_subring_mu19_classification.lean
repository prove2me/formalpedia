-- Prove2me | solution 1 for MazurTransfer.original_rational_subring_mu19_classification
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-22T02:07:56.525583+00:00
-- url     : https://prove2.me/submissions/8a52b763-5d35-44db-87c8-9b906dfccc8d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: normalize the canonical scalar change of the same given local literal-root Hopf model to its same given arithmetic label, using the original fixed point restriction.
Named downstream consumer: the exact previously selected pi quotient map in literal mu19 coordinates, before integral norm torsor pushforward.
-/
import Definitions.Def_MazurTransfer_OriginalRationalSubringMu19ClassificationData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
import Theorems.Thm_MazurTransfer_original_rational_subring_base_change_laws
import Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_normalized_classification
noncomputable section
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13RationalSubringBaseChange MazurTransfer.Order13RationalSubringMu19Classification
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points
open scoped TensorProduct
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13RationalSubringMu19Classification
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instIsScalarTowerLocalRingOfNatNatSubtypeRatMemSubringRatLocalizedAtAlgebraicClosure_order13RationalSubringMu19Classification
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instFactPrimeOfNatNat_order13RationalSubringMu19Classification
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13RationalSubringMu19Classification
attribute [local instance] MazurTransfer.Order13RationalSubringMu19Classification.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13RationalSubringMu19Classification
namespace MazurTransfer.OriginalRationalSubringMu19ClassificationBoundary20261020
end MazurTransfer.OriginalRationalSubringMu19ClassificationBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: normalize the canonical scalar change of the SAME local
literal-root quotient to its GIVEN arithmetic label, pointwise.
Named downstream consumer: exact previously selected pi quotient map in
literal mu19 coordinates, before actual integral norm torsor pushforward.
-/

noncomputable section
namespace MazurTransfer.OriginalRationalSubringMu19ClassificationProof20261020
open Order13LocalIntegralCoefficientMaps Order13RationalSubringBaseChange
open NineteenRootsGaloisRepresentation CyclicNineteenGroupAlgebraPoints BialgebraCyclicMu19Points
open scoped TensorProduct





variable (H : Type) [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]


variable (e : WithConv (H →ₐ[R] F) ≃ Additive (Roots F))
variable (he_add : ∀ f g, e (f * g) = e f + e g)
variable (he_act : ∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (H →ₐ[R] F)),
  (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation F σ (e f))

include e he_add he_act in
theorem same_model_normalized_mu19_base_change :
    ∃ ψ : (S ⊗[R] H) ≃ₐc[S] MonoidAlgebra S Cyclic,
      ∀ f : WithConv (S ⊗[R] H →ₐ[S] F),
        literalPointEquiv ψ F f = (e (fixedBasePoint H f)).toMul := by
  letI : IsScalarTower R ℚ F := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Free R H := Module.free_of_flat_of_isLocalRing
  exact MazurTransfer.original_literal_nineteen_roots_normalized_classification
    (S ⊗[R] H)
    (baseChangeLabel 19 F (aRK := (inferInstance : Algebra R F))
      (tRQ := (inferInstance : IsScalarTower R ℚ F)) e)
    (MazurTransfer.original_rational_subring_base_change_laws.1 19 F (aRK := (inferInstance : Algebra R F))
      (tRQ := (inferInstance : IsScalarTower R ℚ F)) e he_add)
    (MazurTransfer.original_rational_subring_base_change_laws.2.1 19 F (aRK := (inferInstance : Algebra R F))
      (tRQ := (inferInstance : IsScalarTower R ℚ F)) e
      (fun σ m => rootsRepresentation F σ m) he_act)

end MazurTransfer.OriginalRationalSubringMu19ClassificationProof20261020

theorem solution : ∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] F) ≃ Additive (Roots F)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (H →ₐ[R] F)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation F σ (e f)),
∃ ψ : (S ⊗[R] H) ≃ₐc[S] MonoidAlgebra S Cyclic,
      ∀ f : WithConv (S ⊗[R] H →ₐ[S] F),
        literalPointEquiv ψ F f = (e (fixedBasePoint H f)).toMul := by
  exact MazurTransfer.OriginalRationalSubringMu19ClassificationProof20261020.same_model_normalized_mu19_base_change
#print axioms solution
