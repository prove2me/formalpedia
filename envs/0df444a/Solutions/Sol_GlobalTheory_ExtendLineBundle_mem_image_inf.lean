-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.mem_image_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:25.351252+00:00
-- url     : https://prove2.me/submissions/015bce73-6fd6-47cd-8d8b-68fe14d4ccf7

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
variable (j : Y ⟶ X) [IsOpenImmersion j]
omit [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {U V : Y.Opens} {x : X} (hU : x ∈ j ''ᵁ U) (hV : x ∈ j ''ᵁ V) :
    x ∈ j ''ᵁ (U ⊓ V) := by
  obtain ⟨y, hy, rfl⟩ := hU
  exact j.apply_mem_image_iff.2 ⟨hy, j.apply_mem_image_iff.1 hV⟩
end GlobalTheory.ExtendLineBundle
