-- Prove2me | solution 1 for MazurTransfer.original_literal_nineteen_roots_cartier_dual_point_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-22T00:15:35.183283+00:00
-- url     : https://prove2.me/submissions/3b78ea62-6fc0-4046-80ad-9cd535da3ccc

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: retain the same given literal-root Hopf model, its original Cartier dual point convolution monoid, fixed Galois action, exponent and order nineteen, and its original chosen cyclic equivalence.
Named downstream consumer: normalized literal mu19 classification of the same selected integral pi quotient and its norm Kummer unit conditions.
-/
import Definitions.Def_MazurTransfer_OriginalLiteralNineteenRootsCartierDualPointsData20261020
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.NineteenRootsCyclotomicPower MazurTransfer.LiteralNineteenRootsCartierDualPoints
local notation "K" => AlgebraicClosure ℚ
local notation "R" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instDistribMulActionAlgEquivRatAlgebraicClosureAdditiveSubtypeUnitsMemSubgroupRoots_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instFactPrimeOfNatNat_literalNineteenRootsCartierDualPoints
attribute [local instance] MazurTransfer.LiteralNineteenRootsCartierDualPoints.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_literalNineteenRootsCartierDualPoints
namespace MazurTransfer.OriginalLiteralNineteenRootsCartierDualPointBoundary20261020
end MazurTransfer.OriginalLiteralNineteenRootsCartierDualPointBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the Cartier-dual field points of the SAME given literal-root
Hopf model have order nineteen, exponent nineteen, and trivial Galois action.
The cyclic equivalence retains the original convolution monoid definitionally.
Named downstream consumer: normalized literal-mu19 classification of the
PREVIOUSLY SELECTED actual pi quotient and its Kummer unit condition.
-/

noncomputable section
namespace MazurTransfer.OriginalLiteralNineteenRootsCartierDualPointProof20261020
open NineteenRootsGaloisRepresentation NineteenRootsCyclotomicPower



variable (H : Type) [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
variable (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K))
variable (he_add : ∀ f g, e (f * g) = e f + e g)
variable (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)),
  (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f))



include e he_add he_act in
theorem dual_points_fixed_pow_card :
    (∀ (σ : K ≃ₐ[ℚ] K) (ψ : DualPoints H) (θ : CartierDual R H), σ (ψ θ) = ψ θ) ∧
    (∀ ψ : DualPoints H, ψ ^ 19 = 1) ∧ Nat.card (DualPoints H) = 19 := by
  have hcard := MazurTransfer.original_finite_free_hopf_arithmetic_point_rank H K e
  have h := GaloisRep.cartierDual_points_of_galoisCyclotomic 19 H e he_add he_act 1
    (fun m => by simpa only [pow_one] using MazurTransfer.original_nineteen_roots_cyclotomic_power.2.2.1 K m) (exponent K)
    (fun σ ζ hζ => MazurTransfer.original_nineteen_roots_cyclotomic_power.1 K σ ζ (by simpa only [pow_one] using hζ))
    (fun σ m => MazurTransfer.original_nineteen_roots_cyclotomic_power.2.1 K σ m) hcard.symm
  exact ⟨h.1, fun ψ => by simpa only [pow_one] using h.2.1 ψ,
    h.2.2.trans (hcard.trans (roots_card K))⟩



theorem dualPointGroup_toMonoid :
    (dualPointGroup H e he_add he_act).toMonoid = (inferInstance : Monoid (DualPoints H)) := rfl





end MazurTransfer.OriginalLiteralNineteenRootsCartierDualPointProof20261020

theorem solution : (∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
(∀ (σ : K ≃ₐ[ℚ] K) (ψ : DualPoints H) (θ : CartierDual R H), σ (ψ θ) = ψ θ) ∧
    (∀ ψ : DualPoints H, ψ ^ 19 = 1) ∧ Nat.card (DualPoints H) = 19) ∧ (∀ (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H] (e : WithConv (H →ₐ[R] K) ≃ Additive (Roots K)) (he_add : ∀ f g, e (f * g) = e f + e g) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[R] K)), (∀ x : H, g x = σ (f x)) → e g = rootsRepresentation K σ (e f)),
(dualPointGroup H e he_add he_act).toMonoid = (inferInstance : Monoid (DualPoints H))) := by
  exact ⟨MazurTransfer.OriginalLiteralNineteenRootsCartierDualPointProof20261020.dual_points_fixed_pow_card, MazurTransfer.OriginalLiteralNineteenRootsCartierDualPointProof20261020.dualPointGroup_toMonoid⟩
#print axioms solution
