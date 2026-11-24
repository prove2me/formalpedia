-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.imageVal_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:21:18.952171+00:00
-- url     : https://prove2.me/submissions/e1efe3da-550a-4c6b-accd-ed1df710a0d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_unitVal_res
import Theorems.Thm_GlobalTheory_ExtendLineBundle_imageUnit_res

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
theorem _root_.solution {U V : Y.Opens} (hle : V ≤ U) (h : genericPoint X ∈ j ''ᵁ V)
    (a : Γ(Y, U)ˣ) : imageVal j V (res hle a) = imageVal j U a :=
  (congrArg (unitVal _) (imageUnit_res j hle a)).trans (unitVal_res _ h _)
end GlobalTheory.ExtendLineBundle
