-- Prove2me | solution 1 for GlobalTheory.quasiCompact_descendsAlong_fpqc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:29.760818+00:00
-- url     : https://prove2.me/submissions/9da02f9f-8c4d-4fe6-8050-10cb8a058d3e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine ⟨fun {A X Y Z fst snd f g} h hf hfst => ?_⟩
  obtain ⟨⟨hs, -⟩, hqc⟩ := hf
  have hsnd : Surjective snd := MorphismProperty.of_isPullback h hs
  have : QuasiCompact f := hqc
  have : QuasiCompact fst := hfst
  show QuasiCompact g
  rw [quasiCompact_iff]
  intro U hU hc
  have h1 : IsCompact (fst ⁻¹' (f ⁻¹' U)) :=
    (quasiCompact_iff fst).1 ‹_› _ (hU.preimage f.continuous) ((quasiCompact_iff f).1 ‹_› U hU hc)
  have hcond : ∀ z, f (fst z) = g (snd z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have : g ⁻¹' U = snd '' (fst ⁻¹' (f ⁻¹' U)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := hsnd.surj y
      exact ⟨z, by simpa [Set.mem_preimage, hcond] using hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [Set.mem_preimage, ← hcond] using hz
  rw [this]
  exact h1.image snd.continuous
end _root_.GlobalTheory
end GlobalTheory
