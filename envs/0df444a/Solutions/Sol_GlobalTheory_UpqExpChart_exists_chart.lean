-- Prove2me | solution 1 for GlobalTheory.UpqExpChart.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:45:30.928545+00:00
-- url     : https://prove2.me/submissions/21c9e851-54bf-4004-a8e6-2288fe2893f4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.UpqExpChart
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.UpqExpChart
theorem _root_.solution : ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
    (e : Matrix n n ℂ → Matrix n n ℂ) = NormedSpace.exp ∧ (0 : Matrix n n ℂ) ∈ e.source := by
  open scoped Matrix.Norms.Operator in
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ) :
        Matrix n n ℂ →L[ℂ] Matrix n n ℂ) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)
  open scoped Matrix.Norms.Operator in
  exact ⟨h.toOpenPartialHomeomorph _, rfl, h.mem_toOpenPartialHomeomorph_source⟩
end GlobalTheory.UpqExpChart
