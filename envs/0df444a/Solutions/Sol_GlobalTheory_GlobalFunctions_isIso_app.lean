-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.isIso_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:47.365636+00:00
-- url     : https://prove2.me/submissions/c249bda6-44e9-416d-898a-993295e4b835

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_GlobalFunctions_isIso_appTop_of_isAffine
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isAffine
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app_of_forall_affineOpens


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
    [Smooth p] [IsProper p] [GeometricallyIntegral p] (U : S.Opens) : IsIso (p.app U) :=
  ProperFunctions.isIso_app_of_forall_affineOpens p (fun V ↦
    have : IsAffine V.1 := V.2
    isIso_appTop_of_isAffine hI hD (p ∣_ V.1)) U
end GlobalTheory.GlobalFunctions
