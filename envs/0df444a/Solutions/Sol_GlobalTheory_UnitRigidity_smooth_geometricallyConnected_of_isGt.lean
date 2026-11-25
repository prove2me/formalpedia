-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:10:15.630087+00:00
-- url     : https://prove2.me/submissions/0ab2a4c3-2a35-4e46-b84c-460cd2a959a4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_UnitRigidity_geometricallyConnected_of_isPullback_of_surjective
import Theorems.Thm_GlobalTheory_UnitRigidity_isPullback_act
import Theorems.Thm_GlobalTheory_splitTorus_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitRigidity
namespace GlobalTheory.UnitRigidity
theorem _root_.solution {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G]
    (h : E.IsGt G) : Smooth G.hom ∧ GeometricallyConnected G.hom := by
  obtain ⟨D⟩ := h
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have := E.isAbelian.smooth
  have := E.isAbelian.geomConnected
  obtain ⟨-, -, -, -, h1, -, -, h2, -⟩ := (splitTorus_properties S).1 E.X
  have : Smooth (splitTorus S E.X).hom := SmoothOfRelativeDimension.smooth (Module.finrank ℤ E.X) _
  have H := (isPullback_act D.i D.q D.isKernel).map (Over.forget S)
  have a1 : Smooth (snd (splitTorus S E.X) G).left :=
    inferInstanceAs (Smooth (pullback.snd (splitTorus S E.X).hom G.hom))
  have a2 : GeometricallyConnected (snd (splitTorus S E.X) G).left :=
    inferInstanceAs (GeometricallyConnected (pullback.snd (splitTorus S E.X).hom G.hom))
  have b1 : Smooth D.q.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip ⟨⟨‹_›, ‹_›⟩, (inferInstance : QuasiCompact D.q.left)⟩ a1
  have b2 : GeometricallyConnected D.q.left :=
    @geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _ H D.q_surjective a2
  rw [← Over.w D.q]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩
end GlobalTheory.UnitRigidity
