-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.imageVal_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:14.947124+00:00
-- url     : https://prove2.me/submissions/42b6db3d-db79-468a-b3e4-a52699fb0534

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_imageVal_res_pull

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
theorem _root_.solution (M : LB X) (p q : PUnit → M.ι)
    (h : genericPoint X ∈ j ''ᵁ (LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q)) :
    imageVal j _ ((M.pull j).g p q) = unitVal _ (M.g (p ⟨⟩) (q ⟨⟩)) := by
  refine (congrArg (imageVal j _) ((Fintype.prod_unique (ι := PUnit) _).trans (zpow_one _))).trans ?_
  exact imageVal_res_pull j (U := M.U (p ⟨⟩) ⊓ M.U (q ⟨⟩)) _ h _
end GlobalTheory.ExtendLineBundle
