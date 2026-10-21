-- Prove2me | solution 1 for MazurTransfer.original_positive_scalar_norm_factors_finite_flat
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T04:50:03.694998+00:00
-- url     : https://prove2.me/submissions/65b4cb29-70d0-4738-ab23-9ca780c7dca1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete positive scalar finiteness, flatness and surjectivity inputs reuse official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the same two endomorphisms factoring a positive scalar on the same abelian scheme are finite, flat, locally finitely presented and surjective over the original Noetherian base.
Named downstream consumer: the same actual nineteen integral norm maps, including over the localization at nineteen.
-/
import Theorems.Thm_MazurTransfer_original_abelian_scheme_finite_endomorphism_flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul
noncomputable section
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
namespace MazurTransfer.OriginalPositiveScalarNormFactorsFiniteFlatBoundary20261020
end MazurTransfer.OriginalPositiveScalarNormFactorsFiniteFlatBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two relative endomorphisms whose composites are the same
POSITIVE scalar on an abelian scheme are finite, flat, locally finitely
presented and surjective, including in residue characteristic dividing
the scalar. All scalar finiteness and flatness use complete exact-pin
Anthropic FLT proofs. No scalar invertibility is assumed.
Named downstream consumer: actual nineteen norm maps over Z_(19).
-/

noncomputable section
namespace MazurTransfer.OriginalPositiveScalarNormFactorsFiniteFlatProof20261020
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem scalar_norm_factors_finite_flat
    {R : Type} [CommRing R] [IsNoetherianRing R] {A : Scheme}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hcomm : L.IsCommutative) (hA : AbelianSchemePropertyBundle R f)
    (n : ℕ) (hn : 0 < n) (φ ψ : SchemeHomOver f f)
    (hφψ : φ.val ≫ ψ.val = L.schemeNsmul n)
    (hψφ : ψ.val ≫ φ.val = L.schemeNsmul n) :
    (IsFinite φ.val ∧ Flat φ.val ∧ LocallyOfFinitePresentation φ.val ∧ Surjective φ.val) ∧
    (IsFinite ψ.val ∧ Flat ψ.val ∧ LocallyOfFinitePresentation ψ.val ∧ Surjective ψ.val) := by
  letI : IsProper f := hA.proper
  letI : Smooth f := hA.smooth
  letI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  have hscalar := RelativeGroupLaw.isFinite_and_flat_schemeNsmul L hA
    (fun t x y => hcomm t x y) n hn
  letI : IsFinite (φ.val ≫ ψ.val) := by rw [hφψ]; exact hscalar.1
  letI : IsFinite (ψ.val ≫ φ.val) := by rw [hψφ]; exact hscalar.1
  haveI : IsProper (φ.val ≫ f) := by rw [φ.property]; infer_instance
  haveI : IsProper (ψ.val ≫ f) := by rw [ψ.property]; infer_instance
  letI : IsProper φ.val := IsProper.of_comp φ.val f
  letI : IsProper ψ.val := IsProper.of_comp ψ.val f
  letI : IsFinite φ.val := IsFinite.of_comp φ.val ψ.val
  letI : IsFinite ψ.val := IsFinite.of_comp ψ.val φ.val
  have hφflat := MazurTransfer.original_abelian_scheme_finite_endomorphism_flat hA φ
  have hψflat := MazurTransfer.original_abelian_scheme_finite_endomorphism_flat hA ψ
  letI : Surjective (φ.val ≫ ψ.val) := by
    rw [hφψ]
    exact RelativeGroupLaw.surjective_schemeNsmul L hcomm hA n hn
  letI : Surjective (ψ.val ≫ φ.val) := by
    rw [hψφ]
    exact RelativeGroupLaw.surjective_schemeNsmul L hcomm hA n hn
  exact ⟨⟨inferInstance, hφflat, inferInstance, Surjective.of_comp ψ.val φ.val⟩,
    ⟨inferInstance, hψflat, inferInstance, Surjective.of_comp φ.val ψ.val⟩⟩

end MazurTransfer.OriginalPositiveScalarNormFactorsFiniteFlatProof20261020

theorem solution : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {A : Scheme}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hcomm : L.IsCommutative) (hA : AbelianSchemePropertyBundle R f)
    (n : ℕ) (hn : 0 < n) (φ ψ : SchemeHomOver f f)
    (hφψ : φ.val ≫ ψ.val = L.schemeNsmul n)
    (hψφ : ψ.val ≫ φ.val = L.schemeNsmul n),
(IsFinite φ.val ∧ Flat φ.val ∧ LocallyOfFinitePresentation φ.val ∧ Surjective φ.val) ∧
    (IsFinite ψ.val ∧ Flat ψ.val ∧ LocallyOfFinitePresentation ψ.val ∧ Surjective ψ.val) := by
  exact MazurTransfer.OriginalPositiveScalarNormFactorsFiniteFlatProof20261020.scalar_norm_factors_finite_flat
#print axioms solution
