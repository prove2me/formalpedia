-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.local_of_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:06.338795+00:00
-- url     : https://prove2.me/submissions/57b24143-ed9e-4cd8-b943-fa5243c62dec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Theorems.Thm_GlobalTheory_DenseFibreIso_isIso_of_fibre
import Theorems.Thm_GlobalTheory_DenseFibreIso_exists_chart
import Theorems.Thm_GlobalTheory_DenseFibreIso_isPullback_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Γ' X : Scheme.{0}} (s : X ⟶ Sp R) (f : Γ' ⟶ X)
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution [IsAffineHom f] (Q : MorphismProperty Scheme.{0}) (K : Type) [Field K]
    [Algebra R K] [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (h : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
      [IsScalarTower R A B] (j : Sp A ⟶ X) (j' : Sp B ⟶ Γ') [IsOpenImmersion j],
      IsPullback (spMap (algebraMap A B)) j' j f → j ≫ s = spMap (algebraMap R A) →
      Function.Bijective
        (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B) →
      ∀ m : PrimeSpectrum (A ⊗[R] K), ∃ a : A, algebraMap A (A ⊗[R] K) a ∉ m.asIdeal ∧
        Q (spMap (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away a →+* Localization.Away a ⊗[A] B)))
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Γ')
      (f' : T' ⟶ T), IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f' := by
  obtain ⟨A, B, ψ, φ, j, j', _, ⟨y, rfl⟩, H, hj⟩ := exists_chart s f x
  let : Algebra R A := ψ.hom.toAlgebra
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra R B := (φ.hom.comp ψ.hom).toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq fun _ => rfl
  replace H : IsPullback (spMap (algebraMap A B)) j' j f := H
  replace hj : j ≫ s = spMap (algebraMap R A) := hj
  have H₁ := isPullback_tensor R A K
  obtain ⟨m, hm, -⟩ := Scheme.exists_preimage_of_isPullback H₁ y (⊥ : PrimeSpectrum K) (by
    rw [← hj, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.ext hx.symm)
  have H₂ := (isPullback_tensor A (A ⊗[R] K) B).paste_vert H
  have hi := isIso_of_fibre s f (spMap (algebraMap R K)) H₂ _ (by
    rw [Category.assoc, hj]; exact H₁.w)
  obtain ⟨a, ha, hQ⟩ := h A B j j' H hj (isIso_SpecMap_iff.1 hi) m
  refine ⟨_, _, _, _, _, (isPullback_tensor A (Localization.Away a) B).paste_vert H,
    inferInstance, ?_, hQ⟩
  have hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a, ← hm]
    exact ha
  obtain ⟨z, rfl⟩ := hy
  exact ⟨z, Scheme.Hom.comp_apply _ _ _⟩
end GlobalTheory.DenseFibreIso
