-- Prove2me | solution 1 for GlobalTheory.SecAff.le_iSup_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:45.922438+00:00
-- url     : https://prove2.me/submissions/415b876e-f418-49f5-b7c6-36523ec06abe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution {κ : Type} (U : X.Opens) {W : κ → X.Opens} (hc : ⊤ ≤ ⨆ a, W a) :
    U ≤ ⨆ a, U ⊓ W a := by
  intro x hx
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (TopologicalSpace.Opens.mem_top x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hx, ha⟩
end GlobalTheory.SecAff
