-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:12.815316+00:00
-- url     : https://prove2.me/submissions/91908948-24ac-494c-8d03-c6e308f051bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective

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
theorem _root_.solution [IsAffineHom f] (x : X) :
    ∃ (A B : CommRingCat.{0}) (ψ : CommRingCat.of R ⟶ A) (φ : A ⟶ B) (j : Spec A ⟶ X)
      (j' : Spec B ⟶ Γ'), IsOpenImmersion j ∧ x ∈ Set.range j ∧
        IsPullback (Spec.map φ) j' j f ∧ j ≫ s = Spec.map ψ := by
  obtain ⟨i, hi⟩ := X.affineOpenCover.openCover.exists_eq x
  let j := X.affineOpenCover.f i
  have : IsOpenImmersion j := X.affineOpenCover.map_prop i
  let e := (pullback j f).isoSpec
  refine ⟨_, _, Spec.preimage (j ≫ s), Spec.preimage (e.inv ≫ pullback.fst j f), j,
    e.inv ≫ pullback.snd j f, inferInstance, hi, ?_, (Spec.map_preimage _).symm⟩
  rw [Spec.map_preimage]
  exact (IsPullback.of_hasPullback j f).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)
end GlobalTheory.DenseFibreIso
