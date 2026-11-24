-- Prove2me | solution 1 for GlobalTheory.SemiAbelianDescent.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:42:56.655936+00:00
-- url     : https://prove2.me/submissions/48d62e3a-8d1d-4fa0-afdb-7d48e70f43cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeometricallyConnectedOfIsPullback

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.SemiAbelianDescent
namespace GlobalTheory.SemiAbelianDescent
theorem _root_.solution {Z : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (f : Z ⟶ Spec (CommRingCat.of Ω)) [IsIntegralHom f] [Surjective f] :
    ∃ s : Spec (CommRingCat.of Ω) ⟶ Z, s ≫ f = 𝟙 _ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have : Nonempty Z := ⟨(f.surjective (Nonempty.some inferInstance)).choose⟩
  obtain ⟨z, -, hz⟩ := (isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty
  rw [isClosed_singleton_iff_isClosedImmersion] at hz
  set g : Spec (Z.residueField z) ⟶ Spec (CommRingCat.of Ω) := Z.fromSpecResidueField z ≫ f with hg
  have : IsIntegralHom g := inferInstance
  have : IsIso (Spec.preimage g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  refine ⟨Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z, ?_⟩
  calc (Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z) ≫ f
      = Spec.map (inv (Spec.preimage g)) ≫ Spec.map (Spec.preimage g) := by
        rw [Category.assoc, Spec.map_preimage]
    _ = 𝟙 _ := by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]
end GlobalTheory.SemiAbelianDescent
