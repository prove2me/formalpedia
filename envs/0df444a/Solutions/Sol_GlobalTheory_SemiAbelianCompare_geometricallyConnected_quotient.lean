-- Prove2me | solution 1 for GlobalTheory.SemiAbelianCompare.geometricallyConnected_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:51.402781+00:00
-- url     : https://prove2.me/submissions/3a070f57-a8ac-4fb1-91d5-843e347dc42d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_SemiAbelianCompare_geometricallyConnected_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G
open GlobalTheory GlobalTheory.SemiAbelianCompare
variable {S : Scheme.{u}} {X : Type u} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {i : Semi.splitTorus S X ⟶ G} {q : G ⟶ B}
namespace GlobalTheory.SemiAbelianCompare
theorem _root_.solution [Module.Free ℤ X] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q η[B]) [hs : Surjective q.left] :
    GeometricallyConnected q.left := by
  have sq := (isPullback_torsor i q hk).map (Over.forget _)
  have : TwoUniqueSums X := by
    let b := Module.Free.chooseBasis ℤ X
    exact TwoUniqueSums.of_injective_addHom b.repr.toAddEquiv.toAddHom b.repr.injective inferInstance
  have h₁ : GeometricallyConnected ((Over.forget _).map (snd (Semi.splitTorus S X) G)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback _ _)
      (Diag.geometricallyConnected_hom S X)
  exact @geometricallyConnected_of_isPullback _ _ _ _ _ _ _ _ sq hs h₁
end GlobalTheory.SemiAbelianCompare
