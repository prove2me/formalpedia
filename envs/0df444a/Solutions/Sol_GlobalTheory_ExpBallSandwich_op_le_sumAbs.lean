-- Prove2me | solution 1 for GlobalTheory.ExpBallSandwich.op_le_sumAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:40:31.819076+00:00
-- url     : https://prove2.me/submissions/62c333ad-ba62-474b-91fe-61f2ee8d92a5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.ExpBallSandwich
variable {n : Type} [Fintype n] [DecidableEq n]
open scoped Matrix.Norms.Operator
namespace GlobalTheory.ExpBallSandwich
theorem _root_.solution (M : Matrix n n ℂ) : ‖M‖ ≤ sumAbs M := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : n => ∑ j, ‖M i j‖₊) ≤ ∑ i, ∑ j, ‖M i j‖₊ :=
    Finset.sup_le fun i _ => Finset.single_le_sum (f := fun l => ∑ j, ‖M l j‖₊)
          (fun l _ => by positivity) (Finset.mem_univ i)
  have h2 := NNReal.coe_le_coe.2 this
  simpa [sumAbs] using h2
end GlobalTheory.ExpBallSandwich
