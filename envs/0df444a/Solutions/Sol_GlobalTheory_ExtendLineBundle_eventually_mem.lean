-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.eventually_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:06.845868+00:00
-- url     : https://prove2.me/submissions/3dac3c63-fd77-4069-9209-8e5f9db496fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_germ_mem
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_section_of_mem

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
    ∀ᶠ y in nhds x, t ∈ localSubring y := by
  obtain ⟨U, hx, s, rfl⟩ := exists_section_of_mem ht
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact germ_mem hy _ s
end GlobalTheory.ExtendLineBundle
