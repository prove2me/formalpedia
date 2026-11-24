-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.IdxFour.mem_K_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:06.764578+00:00
-- url     : https://prove2.me/submissions/e997c6f4-0d2e-467d-ae65-26a8f660e362

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mem_KU_iff
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
theorem _root_.solution (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) :
    g ∈ KU σ 4 ↔ x ∈ intL L := by
  rw [mem_KU_iff hv, hg]
  refine ⟨fun h => by simpa [rootMat] using h 0 1, fun h i j => ?_⟩
  have h' : σ x ∈ intL L := by
    show Valued.v (σ x) ≤ 1
    rw [hv]
    exact h
  fin_cases i <;> fin_cases j <;> simp [rootMat, h, h', one_mem, zero_mem]
end GlobalTheory.SatakeWeyl.IdxFour
