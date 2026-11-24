-- Prove2me | solution 1 for GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:05.744032+00:00
-- url     : https://prove2.me/submissions/6347ed72-e76e-4f0f-bd43-07184b9b55bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Theorems.Thm_GlobalTheory_flat_and_surjective_of_isFinite_grpEnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S),
      Smooth f → GeometricallyConnected f → GeometricallyIntegral f) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A],
      IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left →
        Flat f.left ∧ Surjective f.left := by
  intro h K _ _ A _ hA f _ _
  have := hA.smooth
  have := h _ _ A.hom hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact flat_and_surjective_of_isFinite_grpEnd K A f
end GlobalTheory
