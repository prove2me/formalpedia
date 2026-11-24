-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.imageUnit_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:41.040518+00:00
-- url     : https://prove2.me/submissions/fab45c1f-1324-4b26-b0a7-50b7062f698a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
variable (j : Y ⟶ X) [IsOpenImmersion j]
omit [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution (U : X.Opens) (a : Γ(X, U)ˣ) :
    imageUnit j (j ⁻¹ᵁ U) (pullU j U a) = res (Set.image_preimage_subset j U.1) a :=
  Units.ext (congrArg (fun q => q.hom a.val) (j.app_appIso_inv U))
end GlobalTheory.ExtendLineBundle
