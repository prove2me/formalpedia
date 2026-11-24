-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothSpread.exists_finite_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:23.435394+00:00
-- url     : https://prove2.me/submissions/c0e09dc6-59bc-4b67-b0b7-6a532fd808c9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_exists_finite_smooth
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_smooth_iff_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothSpread
namespace GlobalTheory.CompanionTheory.SmoothSpread
theorem _root_.solution {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R₀ R] {Y Y₀ U : Scheme.{0}}
    {f : Y ⟶ Spec (CommRingCat.of R)} {f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)} {π : Y ⟶ Y₀}
    (hlfp : LocallyOfFinitePresentation f₀)
    (hpb : IsPullback π f f₀ (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))))
    (hf : Smooth f) [IsAffine U] (j : U ⟶ Y₀) [IsOpenImmersion j] :
    ∃ s : Set R, s.Finite ∧ ∀ (A : Subalgebra R₀ R), s ⊆ A → ∀ {W : Scheme.{0}} {p : W ⟶ U}
      {q : W ⟶ Spec (CommRingCat.of A)},
      IsPullback p q (j ≫ f₀) (Spec.map (CommRingCat.ofHom (algebraMap R₀ A))) → Smooth q := by
  let B : Type := Γ(U, ⊤)
  let e : U ≅ Spec (CommRingCat.of B) := U.isoSpec
  let α : CommRingCat.of R₀ ⟶ CommRingCat.of B := Spec.preimage (e.inv ≫ j ≫ f₀)
  have hα : Spec.map α = e.inv ≫ j ≫ f₀ := Spec.map_preimage _
  letI : Algebra R₀ B := α.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = e.inv ≫ j ≫ f₀ := hα
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) = j ≫ f₀ := by
    rw [hmap, Iso.hom_inv_id_assoc]
  have hfp : Algebra.FinitePresentation R₀ B := by
    have : LocallyOfFinitePresentation (Spec.map α) := by
      rw [hα]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation.{0})] at this
    exact this
  have hsm : Algebra.Smooth R (R ⊗[R₀] B) := by
    refine (smooth_iff_of_isPullback (j ≫ f₀) e he
      ((IsPullback.of_hasPullback j π).paste_vert hpb)).mp ?_
    infer_instance
  obtain ⟨s, hs, H⟩ := exists_finite_smooth (R₀ := R₀) (R := R) (B := B)
  refine ⟨s, hs, fun A hA W p q hW ↦ ?_⟩
  have := H A hA
  exact (smooth_iff_of_isPullback (j ≫ f₀) e he hW).mpr this
end GlobalTheory.CompanionTheory.SmoothSpread
