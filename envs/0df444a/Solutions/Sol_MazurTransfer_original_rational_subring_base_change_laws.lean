-- Prove2me | solution 1 for MazurTransfer.original_rational_subring_base_change_laws
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T21:41:13.782198+00:00
-- url     : https://prove2.me/submissions/8bd35f46-596f-4f29-b8cb-6049728cd86b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: canonical scalar base change of the given local Hopf model along the original proved coefficient equivalence, retaining the same arithmetic point label and the original Cartier dual evaluation identity.
Named downstream consumer: normalization and torsor pushforward for the same selected integral pi quotient at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalRationalSubringBaseChangeData20261020
import Theorems.Thm_MazurTransfer_original_hopf_base_change_arithmetic_points_laws
import Theorems.Thm_MazurTransfer_original_literal_nineteen_roots_hopf_classification
noncomputable section
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13LocalRationalSubringEquivalence MazurTransfer.Order13RationalSubringBaseChange MazurTransfer.NineteenRootsGaloisRepresentation
open scoped TensorProduct
local notation "F" => AlgebraicClosure ℚ
local notation "R" => LocalRing 19
local notation "S" => GaloisRep.ratLocalizedAt 19
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.instModuleZModOfNatNatAdditiveSubtypeUnitsAlgebraicClosureRatMemSubgroupRoots_order13RationalSubringBaseChange
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.localSubringTower
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.instFactPrimeOfNatNat_order13RationalSubringBaseChange
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.localSubringAlgebra
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.instIsScalarTowerLocalRingOfNatNatRatAlgebraicClosure_order13RationalSubringBaseChange
attribute [local instance] MazurTransfer.Order13RationalSubringBaseChange.instAlgebraLocalRingOfNatNatAlgebraicClosureRat_order13RationalSubringBaseChange
namespace MazurTransfer.OriginalRationalSubringBaseChangeBoundary20261020
end MazurTransfer.OriginalRationalSubringBaseChangeBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: CANONICAL scalar base change of the GIVEN local Hopf model
along the PROVED base equivalence, preserving its GIVEN arithmetic label.
Named downstream consumer: classification and torsor pushforward for the
SAME selected pi quotient at nineteen. Descent of the inverse-character
twist and integral Kummer unit conditions are separate obligations.
-/

noncomputable section
namespace MazurTransfer.OriginalRationalSubringBaseChangeProof20261020
open Order13LocalIntegralCoefficientMaps Order13LocalRationalSubringEquivalence
open scoped TensorProduct
variable (q : ℕ) [Fact q.Prime]



variable (K : Type) [CommRing K] [Algebra ℚ K]
variable [aRK : Algebra (LocalRing q) K] [tRQ : IsScalarTower (LocalRing q) ℚ K]
variable [aSK : Algebra (GaloisRep.ratLocalizedAt q) K]
variable [tSQ : IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K]



variable {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] {M : Type}
variable (e : WithConv (H →ₐ[LocalRing q] K) ≃ M)



variable [AddCommGroup M]
variable (he_add : ∀ f g, e (f * g) = e f + e g)
include he_add in
theorem baseChangeLabel_add
    (f g : WithConv (GaloisRep.ratLocalizedAt q ⊗[LocalRing q] H →ₐ[GaloisRep.ratLocalizedAt q] K)) :
    baseChangeLabel q K e (f * g) = baseChangeLabel q K e f + baseChangeLabel q K e g := by
  change e (HopfBaseChangeArithmeticPoints.restrictPoint (f * g)) = _
  rw [MazurTransfer.original_hopf_base_change_arithmetic_points_laws.2.1, he_add]
  rfl

variable (ρ : (K ≃ₐ[ℚ] K) → M → M)
variable (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[LocalRing q] K)),
  (∀ x : H, g x = σ (f x)) → e g = ρ σ (e f))
include he_act in
theorem baseChangeLabel_act (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (GaloisRep.ratLocalizedAt q ⊗[LocalRing q] H →ₐ[GaloisRep.ratLocalizedAt q] K))
    (hfg : ∀ x, g x = σ (f x)) :
    baseChangeLabel q K e g = ρ σ (baseChangeLabel q K e f) := by
  apply he_act σ
  intro x
  exact hfg (1 ⊗ₜ[LocalRing q] x)

section Nineteen

open NineteenRootsGaloisRepresentation




variable (G : Type) [CommRing G] [HopfAlgebra R G]
variable [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G]
variable (label : WithConv (G →ₐ[R] F) ≃ Additive (Roots F))
variable (hadd : ∀ f g, label (f * g) = label f + label g)
variable (hact : ∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (G →ₐ[R] F)),
  (∀ x : G, g x = σ (f x)) → label g = rootsRepresentation F σ (label f))

include label hadd hact in
theorem same_model_base_change_cyclotomic_classification :
    ∃ φ : (S ⊗[R] G) ≃ₐc[S]
      MonoidAlgebra S (WithConv (CartierDual S (S ⊗[R] G) →ₐ[S] F)),
      ∀ (ψ : WithConv (CartierDual S (S ⊗[R] G) →ₐ[S] F)) (θ : CartierDual S (S ⊗[R] G)),
        algebraMap S F (θ (φ.symm (MonoidAlgebra.single ψ 1))) = ψ θ := by
  letI : IsScalarTower R ℚ F := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Free R G := Module.free_of_flat_of_isLocalRing
  exact MazurTransfer.original_literal_nineteen_roots_hopf_classification
    (S ⊗[R] G) (baseChangeLabel 19 F (aRK := (inferInstance : Algebra R F)) (tRQ := (inferInstance : IsScalarTower R ℚ F)) label)
    (baseChangeLabel_add 19 F (aRK := (inferInstance : Algebra R F)) (tRQ := (inferInstance : IsScalarTower R ℚ F)) label hadd)
    (baseChangeLabel_act 19 F (aRK := (inferInstance : Algebra R F)) (tRQ := (inferInstance : IsScalarTower R ℚ F)) label (fun σ m => rootsRepresentation F σ m) hact)
end Nineteen

end MazurTransfer.OriginalRationalSubringBaseChangeProof20261020

theorem solution : (∀ (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [Algebra ℚ K] [aRK : Algebra (LocalRing q) K] [tRQ : IsScalarTower (LocalRing q) ℚ K] [aSK : Algebra (GaloisRep.ratLocalizedAt q) K] [tSQ : IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] {M : Type} (e : WithConv (H →ₐ[LocalRing q] K) ≃ M) [AddCommGroup M] (he_add : ∀ f g, e (f * g) = e f + e g), ∀ (f g : WithConv (GaloisRep.ratLocalizedAt q ⊗[LocalRing q] H →ₐ[GaloisRep.ratLocalizedAt q] K)),
baseChangeLabel q K e (f * g) = baseChangeLabel q K e f + baseChangeLabel q K e g) ∧ (∀ (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [Algebra ℚ K] [aRK : Algebra (LocalRing q) K] [tRQ : IsScalarTower (LocalRing q) ℚ K] [aSK : Algebra (GaloisRep.ratLocalizedAt q) K] [tSQ : IsScalarTower (GaloisRep.ratLocalizedAt q) ℚ K] {H : Type} [CommRing H] [HopfAlgebra (LocalRing q) H] {M : Type} (e : WithConv (H →ₐ[LocalRing q] K) ≃ M) [AddCommGroup M] (ρ : (K ≃ₐ[ℚ] K) → M → M) (he_act : ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[LocalRing q] K)), (∀ x : H, g x = σ (f x)) → e g = ρ σ (e f)), ∀ (σ : K ≃ₐ[ℚ] K)
    (f g : WithConv (GaloisRep.ratLocalizedAt q ⊗[LocalRing q] H →ₐ[GaloisRep.ratLocalizedAt q] K))
    (hfg : ∀ x, g x = σ (f x)),
baseChangeLabel q K e g = ρ σ (baseChangeLabel q K e f)) ∧ (∀ (G : Type) [CommRing G] [HopfAlgebra R G] [Module.Finite R G] [Module.Flat R G] [Coalgebra.IsCocomm R G] (label : WithConv (G →ₐ[R] F) ≃ Additive (Roots F)) (hadd : ∀ f g, label (f * g) = label f + label g) (hact : ∀ (σ : F ≃ₐ[ℚ] F) (f g : WithConv (G →ₐ[R] F)), (∀ x : G, g x = σ (f x)) → label g = rootsRepresentation F σ (label f)), ∃ φ : (S ⊗[R] G) ≃ₐc[S]
      MonoidAlgebra S (WithConv (CartierDual S (S ⊗[R] G) →ₐ[S] F)),
      ∀ (ψ : WithConv (CartierDual S (S ⊗[R] G) →ₐ[S] F)) (θ : CartierDual S (S ⊗[R] G)),
        algebraMap S F (θ (φ.symm (MonoidAlgebra.single ψ 1))) = ψ θ) := by
  exact ⟨MazurTransfer.OriginalRationalSubringBaseChangeProof20261020.baseChangeLabel_add, MazurTransfer.OriginalRationalSubringBaseChangeProof20261020.baseChangeLabel_act, MazurTransfer.OriginalRationalSubringBaseChangeProof20261020.same_model_base_change_cyclotomic_classification⟩
#print axioms solution
