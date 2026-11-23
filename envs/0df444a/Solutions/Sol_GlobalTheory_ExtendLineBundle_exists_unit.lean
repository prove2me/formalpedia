-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:51.47741+00:00
-- url     : https://prove2.me/submissions/4ec09502-e363-487f-a70c-34e53926d741

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_section
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
theorem _root_.solution {U : X.Opens} {t : X.functionFieldˣ} (ht : ∀ y ∈ U, t ∈ localUnits y) :
    ∃ a : Γ(X, U)ˣ, genericPoint X ∈ U → unitVal U a = t := by
  by_cases h : genericPoint X ∈ U
  · obtain ⟨a, ha⟩ := exists_section h fun y hy => (mem_localUnits.1 (ht y hy)).1
    obtain ⟨b, hb⟩ := exists_section h fun y hy => (mem_localUnits.1 (ht y hy)).2
    have hab : a * b = 1 := germ_injective_of_isIntegral X _ h (by
      rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ t.ne_zero])
    exact ⟨Units.mkOfMulEqOne a b hab, fun _ => Units.ext ((val_unitVal h _).trans ha)⟩
  · exact ⟨1, fun h' => (h h').elim⟩
end GlobalTheory.ExtendLineBundle
