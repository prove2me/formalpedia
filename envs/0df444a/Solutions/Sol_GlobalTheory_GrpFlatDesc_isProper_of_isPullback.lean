-- Prove2me | solution 1 for GlobalTheory.GrpFlatDesc.isProper_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:52.338782+00:00
-- url     : https://prove2.me/submissions/d67ab7dc-d13b-45c2-9ee1-b97cefaf3780

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescends

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GrpFlatDesc
open GrpDense MorphismProperty
variable {Z U : Scheme.{0}}
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory.GrpFlatDesc
theorem _root_.solution {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have h₁ : UniversallyClosed g :=
    of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip hj inferInstance
  have h₂ : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip hj inferInstance
  have : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
    @IsStableUnderBaseChange.inf _ _ _ _ (@IsStableUnderBaseChange.inf _ _ _ _ inferInstance inferInstance)
      inferInstance
  have : MorphismProperty.RespectsIso (C := Scheme.{0}) @UniversallyClosed := universallyClosed_respectsIso
  have h₃ : UniversallyClosed (pullback.diagonal g) :=
    of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hj
      (show UniversallyClosed (pullback.diagonal f) from inferInstance)
  have h₄ : IsSeparated g :=
    ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal g).isClosedMap.isClosed_range⟩
  exact {}
end GlobalTheory.GrpFlatDesc
