-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.mem_localUnits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:57.713179+00:00
-- url     : https://prove2.me/submissions/9418031b-6896-438d-a0ee-cf87577447f2

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
theorem _root_.solution {x : X} {t : X.functionFieldˣ} :
    t ∈ localUnits x ↔ t.val ∈ localSubring x ∧ t.val⁻¹ ∈ localSubring x := by
  rw [← Units.val_inv_eq_inv_val]
  rfl
end GlobalTheory.ExtendLineBundle
