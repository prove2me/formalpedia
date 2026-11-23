-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.unitVal_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:06.775+00:00
-- url     : https://prove2.me/submissions/0f876ac6-d6b3-420d-8ebd-5952b409c63d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_germ_mem
import Theorems.Thm_GlobalTheory_ExtendLineBundle_mem_localUnits
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
theorem _root_.solution {U : X.Opens} {y : X} (hy : y ∈ U) (a : Γ(X, U)ˣ) :
    unitVal U a ∈ localUnits y := by
  have hη := genericPoint_mem hy
  rw [mem_localUnits, ← Units.val_inv_eq_inv_val, ← map_inv, val_unitVal hη, val_unitVal hη]
  exact ⟨germ_mem hy _ _, germ_mem hy _ _⟩
end GlobalTheory.ExtendLineBundle
