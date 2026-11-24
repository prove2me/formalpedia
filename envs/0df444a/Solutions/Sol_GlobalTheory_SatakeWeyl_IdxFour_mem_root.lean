-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.IdxFour.mem_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:30.728669+00:00
-- url     : https://prove2.me/submissions/faa245f5-3805-4ab0-9a31-839a8e36c28c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
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
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.IdxFour
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.IdxFour
theorem _root_.solution {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) : g ∈ rootU σ ![0, 0, 1, 1] := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢
end GlobalTheory.SatakeWeyl.IdxFour
