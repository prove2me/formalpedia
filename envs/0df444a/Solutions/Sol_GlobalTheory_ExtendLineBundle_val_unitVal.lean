-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.val_unitVal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:16.541969+00:00
-- url     : https://prove2.me/submissions/d50b0833-cf17-4cb6-b6e6-9ad264c4de36

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
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U : X.Opens} (h : genericPoint X ∈ U) (a : Γ(X, U)ˣ) :
    (unitVal U a).val = X.presheaf.germ U _ h a.val := by
  rw [unitVal, dif_pos h]
  rfl
end GlobalTheory.ExtendLineBundle
