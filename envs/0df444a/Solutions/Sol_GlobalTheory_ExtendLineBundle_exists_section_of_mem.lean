-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_section_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:48.246107+00:00
-- url     : https://prove2.me/submissions/ef9224b1-cccf-431f-be96-8a8d5c28c7cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_algebraMap_germ

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
theorem _root_.solution {x : X} {t : X.functionField} (ht : t ∈ localSubring x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
      X.presheaf.germ U _ (genericPoint_mem hx) s = t := by
  obtain ⟨a, rfl⟩ := ht
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  exact ⟨U, hx, s, (algebraMap_germ hx _ s).symm⟩
end GlobalTheory.ExtendLineBundle
