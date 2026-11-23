-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.unitVal_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:38.006635+00:00
-- url     : https://prove2.me/submissions/d0950cbc-7744-4cb3-a14a-78410f673a56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_val_unitVal

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
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U V : X.Opens} (hle : V ≤ U) (h : genericPoint X ∈ V) (a : Γ(X, U)ˣ) :
    unitVal V (res hle a) = unitVal U a := by
  apply Units.ext
  rw [val_unitVal h, val_unitVal (hle h)]
  exact X.presheaf.germ_res_apply (homOfLE hle) _ h a.val
end GlobalTheory.ExtendLineBundle
