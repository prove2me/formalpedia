-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.germ_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:17.09988+00:00
-- url     : https://prove2.me/submissions/c990df0f-a927-45b5-98ac-e6906f5a2ee3

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
theorem _root_.solution {U : X.Opens} {x : X} (hx : x ∈ U) (h : genericPoint X ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U _ h s ∈ localSubring x :=
  ⟨_, algebraMap_germ hx h s⟩
end GlobalTheory.ExtendLineBundle
