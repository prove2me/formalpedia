-- Prove2me | solution 1 for GlobalTheory.CMLattice.conjugate_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:22.319013+00:00
-- url     : https://prove2.me/submissions/6d978432-5735-4b8d-b179-4a69c401abbd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]
namespace GlobalTheory.CMLattice
theorem _root_.solution (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp
end GlobalTheory.CMLattice
