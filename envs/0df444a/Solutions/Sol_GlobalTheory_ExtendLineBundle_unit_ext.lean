-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.unit_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:07.732459+00:00
-- url     : https://prove2.me/submissions/a5b20487-2d61-43f9-af50-dd63298da762

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
theorem _root_.solution {U : X.Opens} {a b : Γ(X, U)ˣ}
    (h : genericPoint X ∈ U → unitVal U a = unitVal U b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  have hη := genericPoint_mem hx
  have e := congrArg Units.val (h hη)
  rw [val_unitVal hη, val_unitVal hη] at e
  rw [germ_injective_of_isIntegral X _ hη e]
end GlobalTheory.ExtendLineBundle
