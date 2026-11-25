-- Prove2me | solution 1 for GlobalTheory.nonempty_torusExtension_of_isGt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:56:37.755798+00:00
-- url     : https://prove2.me/submissions/fe61eb30-5da2-444c-b368-2079a890a09d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyTorusExtensionOfIsGt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (E : SplitExt (Spec (.of K)))
    (G : Over (Spec (.of K))) [GrpObj G] (h : E.IsGt G) : Nonempty (TorusExtension G) := by
  obtain ⟨d⟩ := h
  have := E.free
  have := E.finite
  have := d.q_affine
  exact ⟨
    { X := E.X
      B := E.B
      isAbelian := E.isAbelian
      q := d.q
      q_hom := d.q_hom
      q_flat := d.q_flat
      q_surjective := d.q_surjective
      q_quasiCompact := inferInstance
      i := d.i
      i_hom := d.i_hom
      isKernel := d.isKernel }⟩
end GlobalTheory
