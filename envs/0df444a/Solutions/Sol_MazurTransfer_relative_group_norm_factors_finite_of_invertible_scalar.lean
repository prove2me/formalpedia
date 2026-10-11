-- Prove2me | solution 1 for MazurTransfer.relative_group_norm_factors_finite_of_invertible_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T18:15:08.113462+00:00
-- url     : https://prove2.me/submissions/abb6a5ce-a823-4bcc-9845-57f439080c6f

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: proper relative commutative group scalar factorizations
with invertible scalar have finite factors. Named downstream consumer:
actual rational order-thirteen Picard norm endomorphisms.
Reuses checked original Anthropic FLT formal unramifiedness at exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
noncomputable section
namespace RelativeGroupFiniteNormPublicProof
private theorem finite_factor {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (G : RelativeGroupLaw R f) (hcomm : G.IsCommutative)
    (n : ℕ) (hn : IsUnit (n : R)) (φ ψ : A ⟶ A)
    (hφ : φ ≫ f = f) (hφψ : φ ≫ ψ = G.schemeNsmul n) : IsFinite φ := by
  letI : IsProper (φ ≫ f) := by rw [hφ]; infer_instance
  letI : IsProper φ := IsProper.of_comp φ f
  letI : FormallyUnramified (φ ≫ ψ) := by
    rw [hφψ]
    exact RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing G hcomm n hn
  letI : FormallyUnramified φ := FormallyUnramified.of_comp φ ψ
  letI : LocallyQuasiFinite φ :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType φ
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ
end RelativeGroupFiniteNormPublicProof

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (G : RelativeGroupLaw R f) (hcomm : G.IsCommutative)
    (n : ℕ) (hn : IsUnit (n : R))
    (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    (hφψ : φ ≫ ψ = G.schemeNsmul n) (hψφ : ψ ≫ φ = G.schemeNsmul n) :
    IsFinite φ ∧ IsFinite ψ := by
  exact ⟨RelativeGroupFiniteNormPublicProof.finite_factor f G hcomm n hn φ ψ hφ hφψ,
    RelativeGroupFiniteNormPublicProof.finite_factor f G hcomm n hn ψ φ hψ hψφ⟩

#print axioms solution
