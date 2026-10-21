-- Prove2me | solution 1 for MazurTransfer.original_abelian_scheme_finite_endomorphism_flat
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T04:42:45.451983+00:00
-- url     : https://prove2.me/submissions/e103fbee-9fc1-4bba-9cf2-61d93249bf6c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The complete field and fibrewise-flatness inputs are reused from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a finite endomorphism of the same relative abelian scheme is flat over the original arbitrary commutative base, with no invertibility hypothesis.
Named downstream consumer: positive-scalar norm factors and the actual integral nineteen norm models.
-/
import Theorems.Thm_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u
/- Complete original Anthropic FLT pullback certificate, Apache-2.0, exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Design boundary: closed proof of the same fibre endomorphism pullback square. Named downstream consumer: flatness of the same finite abelian-scheme endomorphism. -/
namespace MazurTransfer.OriginalClosedFibrePullbackSupport421V220261021
lemma isPullback_schemeFibreEndo {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hh : h ≫ f = f)
    (s : S) :
    IsPullback (schemeFibreEndo f h hh s) (pullback.fst f (S.fromSpecResidueField s))
      (pullback.fst f (S.fromSpecResidueField s)) h := by
  refine IsPullback.of_right (h₁₂ := pullback.snd f (S.fromSpecResidueField s))
    (v₁₃ := S.fromSpecResidueField s) (h₂₂ := f) ?_ (schemeFibreEndo_fst f h hh s)
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip
  rw [schemeFibreEndo_snd, hh]
  exact (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip

end MazurTransfer.OriginalClosedFibrePullbackSupport421V220261021
namespace MazurTransfer.OriginalAbelianSchemeFiniteEndomorphismFlatBoundary20261020
end MazurTransfer.OriginalAbelianSchemeFiniteEndomorphismFlatBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The field and fibrewise flatness proofs are reused in full from official
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: a finite relative endomorphism of the SAME abelian
scheme is flat, including when its degree is divisible by the residue
characteristic. No scalar invertibility or unramifiedness is assumed.
Named downstream consumer: actual finite-flat nineteen norm extensions.
-/

noncomputable section
namespace MazurTransfer.OriginalAbelianSchemeFiniteEndomorphismFlatProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

theorem finite_endomorphism_flat
    {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (β : SchemeHomOver f f) [IsFinite β.val] : Flat β.val := by
  letI : Smooth f := hA.smooth
  apply AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
    f β.val β.property
  intro s
  have hs := MazurTransfer.OriginalClosedFibrePullbackSupport421V220261021.isPullback_schemeFibreEndo
    f β.val β.property s
  letI : IsFinite (schemeFibreEndo f β.val β.property s) := by
    rw [← hs.flip.isoPullback_hom_snd]
    infer_instance
  have hAs := abelianSchemePropertyBundle_fibreStr hA s
  exact AbelianSchemePropertyBundle.flat_of_isFinite _ hAs
    ⟨schemeFibreEndo f β.val β.property s, schemeFibreEndo_snd f β.val β.property s⟩

end MazurTransfer.OriginalAbelianSchemeFiniteEndomorphismFlatProof20261020

theorem solution : ∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f) (β : SchemeHomOver f f) [IsFinite β.val], Flat β.val := by
  exact MazurTransfer.OriginalAbelianSchemeFiniteEndomorphismFlatProof20261020.finite_endomorphism_flat
#print axioms solution
