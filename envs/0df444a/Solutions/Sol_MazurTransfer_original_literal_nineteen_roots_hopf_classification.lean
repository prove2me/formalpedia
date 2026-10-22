-- Prove2me | solution 1 for MazurTransfer.original_literal_nineteen_roots_hopf_classification
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T20:29:59.133703+00:00
-- url     : https://prove2.me/submissions/400298f8-ed87-4e8d-8e4a-e986ea5c0949

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: classify a given finite-free cocommutative Hopf model with its fixed literal nineteenth-root arithmetic labels over the original rational subring, preserving the resulting Cartier dual point evaluation identity.
Named downstream consumer: explicit base transport and classification of the same selected integral pi character quotient at nineteen.
-/
import Theorems.Thm_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
import Definitions.Def_MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
import Definitions.Def_MazurTransfer_OriginalRepresentationCanonicalDistribMulActionData20261020
import Theorems.Thm_MazurTransfer_original_nineteen_roots_cyclotomic_power
import Theorems.Thm_MazurTransfer_original_finite_free_hopf_arithmetic_point_rank
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.NineteenRootsCyclotomicPower
local notation "K" => AlgebraicClosure ℚ
attribute [local instance] MazurTransfer.NineteenRootsCyclotomicPower.instFactPrimeOfNatNat_nineteenRootsCyclotomicPower
attribute [local instance] MazurTransfer.NineteenRootsCyclotomicPower.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_nineteenRootsCyclotomicPower
namespace MazurTransfer.OriginalLiteralNineteenRootsHopfClassificationBoundary20261020
end MazurTransfer.OriginalLiteralNineteenRootsHopfClassificationBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: classify a GIVEN finite-free Hopf model labelled by the
FIXED literal nineteenth roots over the rational-subring coefficient base.
Derive the rank, exponent and cyclotomic hypotheses; retain the given label.
Named downstream consumer: the SAME selected pi quotient, after explicit
base transport from Order13LocalRationalSubringEquivalence. This theorem
alone does not transport or classify the existing integral quotient witness.
-/

noncomputable section
namespace MazurTransfer.OriginalLiteralNineteenRootsHopfClassificationProof20261020
open NineteenRootsGaloisRepresentation NineteenRootsCyclotomicPower
local instance instFactPrimeOfNatNat_literalNineteenRootsHopfClassification : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsHopfClassification : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K
local instance instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsHopfClassification : DistribMulAction (K ≃ₐ[ℚ] K) (Additive (Roots K)) :=
  RepresentationCanonicalDistribMulAction.ofRepresentation (rootsRepresentation K)
variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt 19) H]
variable [Module.Finite (GaloisRep.ratLocalizedAt 19) H]
variable [Module.Free (GaloisRep.ratLocalizedAt 19) H]
variable [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt 19) H]
variable (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt 19] K) ≃ Additive (Roots K))
variable (he_add : ∀ f g, e (f * g) = e f + e g)
variable (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt 19] K)),
  (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f))

include e he_add he_act in
theorem exists_cyclotomic_bialgebra_equivalence :
    ∃ φ : H ≃ₐc[GaloisRep.ratLocalizedAt 19]
      MonoidAlgebra (GaloisRep.ratLocalizedAt 19)
        (WithConv (CartierDual (GaloisRep.ratLocalizedAt 19) H →ₐ[GaloisRep.ratLocalizedAt 19] K)),
      ∀ (ψ : WithConv (CartierDual (GaloisRep.ratLocalizedAt 19) H →ₐ[GaloisRep.ratLocalizedAt 19] K))
        (θ : CartierDual (GaloisRep.ratLocalizedAt 19) H),
        algebraMap (GaloisRep.ratLocalizedAt 19) K
          (θ (φ.symm (MonoidAlgebra.single ψ 1))) = ψ θ := by
  have he_act' : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt 19] K)),
      (∀ x : H, g x = σ (f x)) → e g = σ • e f := he_act
  have hcard : Nat.card (Additive (Roots K)) = Module.finrank (GaloisRep.ratLocalizedAt 19) H :=
    (MazurTransfer.original_finite_free_hopf_arithmetic_point_rank H K e).symm
  apply GaloisRep.exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic
    19 (by decide) H e he_add he_act' 1
    (fun m => by simpa only [pow_one] using MazurTransfer.original_nineteen_roots_cyclotomic_power.2.2.1 K m)
    (exponent K)
    (fun σ ζ hζ => MazurTransfer.original_nineteen_roots_cyclotomic_power.1 K σ ζ (by simpa only [pow_one] using hζ))
    (fun σ m => MazurTransfer.original_nineteen_roots_cyclotomic_power.2.1 K σ m) hcard

end MazurTransfer.OriginalLiteralNineteenRootsHopfClassificationProof20261020

theorem solution : ∀ (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt 19) H] [Module.Finite (GaloisRep.ratLocalizedAt 19) H] [Module.Free (GaloisRep.ratLocalizedAt 19) H] [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt 19) H] (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt 19] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt 19] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
∃ φ : H ≃ₐc[GaloisRep.ratLocalizedAt 19]
      MonoidAlgebra (GaloisRep.ratLocalizedAt 19)
        (WithConv (CartierDual (GaloisRep.ratLocalizedAt 19) H →ₐ[GaloisRep.ratLocalizedAt 19] K)),
      ∀ (ψ : WithConv (CartierDual (GaloisRep.ratLocalizedAt 19) H →ₐ[GaloisRep.ratLocalizedAt 19] K))
        (θ : CartierDual (GaloisRep.ratLocalizedAt 19) H),
        algebraMap (GaloisRep.ratLocalizedAt 19) K
          (θ (φ.symm (MonoidAlgebra.single ψ 1))) = ψ θ := by
  exact MazurTransfer.OriginalLiteralNineteenRootsHopfClassificationProof20261020.exists_cyclotomic_bialgebra_equivalence
#print axioms solution
