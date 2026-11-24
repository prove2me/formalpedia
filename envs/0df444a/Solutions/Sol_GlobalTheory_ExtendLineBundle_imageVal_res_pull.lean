-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.imageVal_res_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:28.400652+00:00
-- url     : https://prove2.me/submissions/8a70dd7e-b9e0-46dd-91b0-592c6efbde26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_unitVal_res
import Theorems.Thm_GlobalTheory_ExtendLineBundle_imageUnit_pull
import Theorems.Thm_GlobalTheory_ExtendLineBundle_imageVal_res

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
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U : X.Opens} {V : Y.Opens} (hle : V ≤ j ⁻¹ᵁ U)
    (h : genericPoint X ∈ j ''ᵁ V) (a : Γ(X, U)ˣ) :
    imageVal j V (res hle (pullU j U a)) = unitVal U a :=
  (imageVal_res j hle h _).trans ((congrArg (unitVal _) (imageUnit_pull j U a)).trans
    (unitVal_res _ (j.image_mono hle h) _))
end GlobalTheory.ExtendLineBundle
