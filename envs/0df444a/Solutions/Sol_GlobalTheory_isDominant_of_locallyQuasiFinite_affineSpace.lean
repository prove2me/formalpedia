-- Prove2me | solution 1 for GlobalTheory.isDominant_of_locallyQuasiFinite_affineSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:10:17.351949+00:00
-- url     : https://prove2.me/submissions/6cf5f208-7fc9-4696-a1be-b832d2dcf53d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsDominantHomOfVectorOfQuasiFiniteAt
import Theorems.Thm_GlobalTheory_injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Z : Scheme.{0}} [IsIntegral Z]
    {R B : CommRingCat.{0}} [IsDomain R] [IsDomain B] {g : ℕ} (φ : R ⟶ B)
    (hφ : φ.hom.IsStandardSmoothOfRelativeDimension g) (i : Spec R ⟶ Z) [IsOpenImmersion i]
    (f : Spec B ⟶ 𝔸(Fin g; Z)) [LocallyQuasiFinite f]
    (hf : f ≫ 𝔸(Fin g; Z) ↘ Z = Spec.map φ ≫ i) : IsDominant f := by
  have hp := AffineSpace.isPullback_map (n := Fin g) i
  have : IsOpenImmersion (AffineSpace.map (Fin g) i) :=
    MorphismProperty.of_isPullback hp.flip ‹_›
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    (hp.lift f (Spec.map φ) hf ≫ (AffineSpace.SpecIso (Fin g) R).hom)
  have e : f = Spec.map ψ ≫ (AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i := by
    rw [hψ]; simp
  have e2 : CommRingCat.ofHom MvPolynomial.C ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← AffineSpace.SpecIso_inv_over, Category.assoc, Iso.hom_inv_id_assoc,
      IsPullback.lift_snd]
  have hq : LocallyQuasiFinite (Spec.map ψ) := by
    rw [e] at ‹LocallyQuasiFinite f›
    exact .of_comp _ ((AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at hq
  letI : Algebra R B := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  have hinj := injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension
    (R := R) (B := B) (g := g) { ψ.hom with commutes' := fun r => congr($e2 r) } hq
  have : IsDominant (Spec.map ψ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by rw [(RingHom.injective_iff_ker_eq_bot ψ.hom).1 hinj]; exact bot_le)⟩
  have : IsDominant (AffineSpace.map (Fin g) i) :=
    ⟨(AffineSpace.map (Fin g) i).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  rw [e]
  infer_instance
end GlobalTheory
