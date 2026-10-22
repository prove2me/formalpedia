-- Prove2me | solution 1 for MazurTransfer.original_literal_nineteen_roots_normalized_classification
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-22T01:50:42.972897+00:00
-- url     : https://prove2.me/submissions/ffa60a85-0f19-4be2-832a-ba4922d2d801

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the same given literal-root Hopf model over its original rational subring, normalized pointwise to its same given arithmetic root label.
Named downstream consumer: normalization of the same selected integral pi quotient arithmetic labels and norm Kummer unit conditions at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalLiteralNineteenRootsCartierDualPointsData20261020
import Definitions.Def_MazurTransfer_OriginalBialgebraCyclicMu19PointsData20261020
import Definitions.Def_MazurTransfer_OriginalCyclicCharacterConjugationData20261020
import Definitions.Def_MazurTransfer_OriginalMu19BialgebraPointLabelNormalizationData20261020
import Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_cyclic_classification
import Theorems.Thm_MazurTransfer_original_mu19_bialgebra_point_label_normalization
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.LiteralNineteenRootsCartierDualPoints
open MazurTransfer.CyclicNineteenGroupAlgebraPoints MazurTransfer.BialgebraCyclicMu19Points
local notation "K" => AlgebraicClosure ℚ
local notation "R" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instFactPrimeOfNatNat_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsCartierDualPoints
namespace MazurTransfer.OriginalLiteralNineteenRootsNormalizedClassificationBoundary20261020
end MazurTransfer.OriginalLiteralNineteenRootsNormalizedClassificationBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal mu19 form over the SAME rational-subring base,
normalized pointwise to the GIVEN arithmetic label of the SAME Hopf model.
Named downstream consumer: canonical scalar change of the actual selected
pi quotient, with its unchanged quotient restriction and Kummer maps.
-/

noncomputable section
namespace MazurTransfer.OriginalLiteralNineteenRootsNormalizedClassificationProof20261020
open NineteenRootsGaloisRepresentation BialgebraCyclicMu19Points
open CyclicNineteenGroupAlgebraPoints
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K
variable (H : Type) [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
variable (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K))
variable (he_add : ∀ f g, e (f * g) = e f + e g)
variable (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)),
  (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f))

include e he_add he_act in
theorem exists_normalized_mu19_equivalence :
    ∃ ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic,
      ∀ f : WithConv (H →ₐ[R] K), literalPointEquiv ψ K f = (e f).toMul := by
  obtain ⟨φ, hφ⟩ := MazurTransfer.original_literal_nineteen_roots_cyclic_classification
    H e he_add he_act
  exact MazurTransfer.original_mu19_bialgebra_point_label_normalization φ e he_add

end MazurTransfer.OriginalLiteralNineteenRootsNormalizedClassificationProof20261020

theorem solution : ∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
∃ ψ : H ≃ₐc[R] MonoidAlgebra R Cyclic,
      ∀ f : WithConv (H →ₐ[R] K), literalPointEquiv ψ K f = (e f).toMul := by
  exact MazurTransfer.OriginalLiteralNineteenRootsNormalizedClassificationProof20261020.exists_normalized_mu19_equivalence
#print axioms solution
