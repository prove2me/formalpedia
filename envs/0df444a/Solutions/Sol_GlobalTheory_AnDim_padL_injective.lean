-- Prove2me | solution 1 for GlobalTheory.AnDim.padL_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:43.261957+00:00
-- url     : https://prove2.me/submissions/d5a87afd-9e5e-4e6c-bbb0-9cf9cbff2dd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution {k d : ℕ} (h : k ≤ d) : Function.Injective (padL k d) := by
  intro z w hzw
  funext i
  simpa [padL] using congrFun hzw (Fin.castLE h i)
end GlobalTheory.AnDim
