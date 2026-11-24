-- Prove2me | solution 1 for GlobalTheory.Klein.mem_intAt_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:57:06.612661+00:00
-- url     : https://prove2.me/submissions/4af27373-6969-43a2-b748-17a6891909a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
import Theorems.Thm_GlobalTheory_Klein_mem_intAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
theorem _root_.solution (ι : ℂ ≃+* ℂ_[p]) {c : ℂ} (h : c ^ 2 ∈ intAt ι) : c ∈ intAt ι := by
  rw [mem_intAt, map_pow, norm_pow] at h
  rw [mem_intAt]
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
end GlobalTheory.Klein
