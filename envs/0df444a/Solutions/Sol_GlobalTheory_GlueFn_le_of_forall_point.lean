-- Prove2me | solution 1 for GlobalTheory.GlueFn.le_of_forall_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:55.638939+00:00
-- url     : https://prove2.me/submissions/8d378c54-e171-4d82-befb-03d02eb51b96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.GlueFn
namespace GlobalTheory.GlueFn
theorem _root_.solution {X : Over (Sp ℂ)} [LocallyOfFiniteType X.hom] {O W : X.left.Opens}
    (h : ∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ x.left ⁻¹ᵁ O → ⊤ ≤ x.left ⁻¹ᵁ W) : O ≤ W := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  by_contra hne
  have hne' : ((O : Set X.left) ∩ (W : Set X.left)ᶜ).Nonempty := by
    obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 hne
    exact ⟨p, hp, hp'⟩
  obtain ⟨c, ⟨hcO, hcW⟩, hc⟩ := nonempty_inter_closedPoints hne'
    (O.isOpen.isLocallyClosed.inter W.isOpen.isClosed_compl.isLocallyClosed)
  have hc' : IsClosed {c} := hc
  let x : 𝟙_ (Over (Sp ℂ)) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom c hc') (pointOfClosedPoint_comp X.hom c hc')
  have hx : ∀ U : X.left.Opens, ⊤ ≤ x.left ⁻¹ᵁ U ↔ c ∈ U := fun U => by
    refine (top_le_preimage_iff_mem (pointOfClosedPoint X.hom c hc') U).trans ?_
    exact (pointOfClosedPoint_apply X.hom c hc' _).symm ▸ Iff.rfl
  exact hcW ((hx W).1 (h x ((hx O).2 hcO)))
end GlobalTheory.GlueFn
