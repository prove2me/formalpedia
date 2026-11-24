-- Prove2me | solution 1 for GlobalTheory.residueField_fg_trdeg_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:45.565209+00:00
-- url     : https://prove2.me/submissions/78321132-82c8-4eb2-b5b0-64026705d033

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIsOpenImmersionIsStandardSmoothOfRelativeD
import Theorems.Thm_GlobalTheory_residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_exists_isOpenImmersion_isStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : SmoothOfRelativeDimension d f) (x : X) (hx : ∀ y : X, y ⤳ x → y = x) :
    letI : Algebra K (X.residueField x) :=
      (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    (⊤ : IntermediateField K (X.residueField x)).FG ∧ Algebra.trdeg K (X.residueField x) = d := by
  obtain ⟨B, φ, j, hj, y, rfl, hjf, hφ⟩ :=
    exists_isOpenImmersion_isStandardSmoothOfRelativeDimension f d hf x
  letI : Algebra K (X.residueField (j y)) :=
    (Spec.preimage (X.fromSpecResidueField (j y) ≫ f)).hom.toAlgebra
  letI : Algebra K B := φ.hom.toAlgebra
  haveI : y.asIdeal.IsPrime := y.isPrime
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d K B := hφ
  obtain ⟨h1, h2⟩ := residueField_fg_trdeg_of_isStandardSmoothOfRelativeDimension (K := K) d
    y.asIdeal (fun q hq hqy => by
      have hs : (⟨q, hq⟩ : PrimeSpectrum B) ⤳ y := (PrimeSpectrum.le_iff_specializes _ _).mp hqy
      have := j.isOpenEmbedding.injective (hx _ (hs.map j.continuous))
      exact congrArg PrimeSpectrum.asIdeal this)
  let e : X.residueField (j y) ≅ CommRingCat.of y.asIdeal.ResidueField :=
    asIso (j.residueFieldMap y) ≪≫ Scheme.Spec.residueFieldIso B y
  have he : Spec.preimage (X.fromSpecResidueField (j y) ≫ f) ≫ e.hom =
      φ ≫ CommRingCat.ofHom (algebraMap B y.asIdeal.ResidueField) := by
    rw [← Spec.map_inj, ← cancel_epi (Spec.map (Scheme.Spec.residueFieldIso B y).inv)]
    simp only [e, Iso.trans_hom, asIso_hom, Spec.map_comp, Spec.map_preimage, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hjf]
    rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  let e' : X.residueField (j y) ≃ₐ[K] y.asIdeal.ResidueField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a => congr($(he).hom a) }
  refine ⟨IntermediateField.fg_top_iff.mpr ?_, ?_⟩
  · exact Algebra.EssFiniteType.of_surjective e'.symm.toAlgHom e'.symm.surjective
  · rw [e'.trdeg_eq, h2]
end GlobalTheory
