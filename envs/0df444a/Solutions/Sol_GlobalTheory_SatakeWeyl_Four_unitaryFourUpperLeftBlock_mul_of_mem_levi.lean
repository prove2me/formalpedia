-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Four.unitaryFourUpperLeftBlock_mul_of_mem_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:25.163847+00:00
-- url     : https://prove2.me/submissions/75d1bde0-a465-4c5e-85f7-222bbb54934e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosets
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
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Four
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.Four
theorem _root_.solution {g : GU σ 4} (g' : GU σ 4) (hg : g ∈ leviU σ ![0, 0, 1, 1]) :
    unitaryFourUpperLeftBlock (g * g') = unitaryFourUpperLeftBlock g * unitaryFourUpperLeftBlock g' := by
  have h02 := hg 0 2 (by decide)
  have h03 := hg 0 3 (by decide)
  have h12 := hg 1 2 (by decide)
  have h13 := hg 1 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFourUpperLeftBlock, mat_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]
end GlobalTheory.SatakeWeyl.Four
