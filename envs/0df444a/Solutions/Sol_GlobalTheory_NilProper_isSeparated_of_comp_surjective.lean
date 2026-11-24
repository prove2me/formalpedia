-- Prove2me | solution 1 for GlobalTheory.NilProper.isSeparated_of_comp_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:44:34.499814+00:00
-- url     : https://prove2.me/submissions/42ccd29c-c2fc-4a42-b779-41cc9a29146a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsProperAndGeometricallyConnectedOfIsNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilProper
namespace GlobalTheory.NilProper
theorem _root_.solution {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  let m := pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 S) (by simp) (by simp)
  have hm : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have hcomm : pullback.diagonal (j ≫ f) ≫ m = j ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.diagonal_fst_assoc]
      simp
    · rw [Category.assoc, pullback.lift_snd, pullback.diagonal_snd_assoc]
      simp
  have key : m '' Set.range (pullback.diagonal (j ≫ f)) = Set.range (pullback.diagonal f) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨_, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]⟩
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [← key]
  exact m.isClosedMap _ (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range
end GlobalTheory.NilProper
