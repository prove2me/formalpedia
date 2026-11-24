-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.isIso_appTop_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:11.311381+00:00
-- url     : https://prove2.me/submissions/3580ae88-8898-43dc-b6fd-eeed8dcb87aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_GlobalFunctions_isIso_appTop_of_section
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isPullback_of_surjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_section


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {X S T : Scheme.{0}}
namespace GlobalTheory.GlobalFunctions
theorem _root_.solution (hI : FibreInjective) (hD : SmoothDescent) (p : X ⟶ S)
    [IsAffine S] [Smooth p] [IsProper p] [GeometricallyIntegral p] : IsIso p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  have : MorphismProperty.ContainsIdentities @Smooth.{0} := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨T, i, _, hi, _⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @Smooth
  let j : pullback (i ≫ p) (i ≫ p) ⟶ pullback p (i ≫ p) :=
    pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hj2 : j ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hj : IsPullback (pullback.fst _ _) j i (pullback.fst p (i ≫ p)) :=
    IsPullback.of_bot (by rw [hj2]; exact .of_hasPullback _ _) (pullback.lift_fst _ _ _).symm
      (.of_hasPullback _ _)
  have : Smooth j := MorphismProperty.of_isPullback hj ‹_›
  have : Surjective j := MorphismProperty.of_isPullback hj ‹_›
  have := isIso_appTop_of_section hI hD (pullback.snd p (i ≫ p)) j (pullback.diagonal (i ≫ p))
    (by rw [hj2, pullback.diagonal_snd])
  exact ProperFunctions.isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p (i ≫ p))
end GlobalTheory.GlobalFunctions
