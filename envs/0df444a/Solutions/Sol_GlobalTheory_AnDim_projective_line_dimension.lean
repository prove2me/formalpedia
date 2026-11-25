-- Prove2me | solution 1 for GlobalTheory.AnDim.projective_line_dimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:25:39.078406+00:00
-- url     : https://prove2.me/submissions/360dd24e-69c9-44b1-8d93-82cf258c477d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_GlobalTheory_AnDim_analyticDim_empty
import Theorems.Thm_GlobalTheory_AnDim_analyticDim_univ
import Theorems.Thm_GlobalTheory_AnDim_singularLocus_univ
import Theorems.Thm_GlobalTheory_AnLogRes_isIrreducibleAnalytic_univ
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
theorem _root_.solution : IsIrreducibleAnalytic p1 Set.univ ∧ analyticDim p1 Set.univ = 1 ∧
    analyticDim p1 (singularLocus p1 Set.univ) < analyticDim p1 Set.univ := by
  refine ⟨AnLogRes.isIrreducibleAnalytic_univ p1, by simpa using analyticDim_univ p1, ?_⟩
  rw [singularLocus_univ, analyticDim_empty, analyticDim_univ]
  exact WithBot.bot_lt_coe _
end GlobalTheory.AnDim
