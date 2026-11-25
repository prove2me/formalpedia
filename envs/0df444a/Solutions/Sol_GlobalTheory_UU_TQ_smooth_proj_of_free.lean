-- Prove2me | solution 1 for GlobalTheory.UU.TQ.smooth_proj_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:05:57.942422+00:00
-- url     : https://prove2.me/submissions/c8f01f24-5936-4f79-a610-d14f6740f67d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothProjOfFree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torsor_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torus_dim


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
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
namespace TQ
theorem _root_.solution {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G : Over S} [GrpObj G] (Q : TQ G X) : Smooth Q.q.left := by
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have := (H1.torus_dim S X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact Q.q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
end TQ
end GlobalTheory.UU
