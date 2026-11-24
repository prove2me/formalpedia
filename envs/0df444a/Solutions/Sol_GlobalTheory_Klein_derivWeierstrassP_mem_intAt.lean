-- Prove2me | solution 1 for GlobalTheory.Klein.derivWeierstrassP_mem_intAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:14.587724+00:00
-- url     : https://prove2.me/submissions/fa50b2c1-b373-49a8-aaae-bdf96ce96fc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
import Theorems.Thm_GlobalTheory_Klein_mem_intAt
import Theorems.Thm_GlobalTheory_Klein_mem_intAt_of_sq

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
theorem _root_.solution {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (hg : Good ι L r)
    (hz : Red ι L r z) : L.derivWeierstrassP z ∈ intAt ι := by
  obtain ⟨-, h1, h2, h3, -⟩ := hg
  obtain ⟨hz, hx⟩ := hz
  rw [← mem_intAt] at h1 h2 h3 hx
  apply mem_intAt_of_sq
  have e : L.derivWeierstrassP z ^ 2 = ((4 : ℕ) : ℂ) * (L.weierstrassP z - r) ^ 3 + 12 * r * (L.weierstrassP z - r) ^ 2
      + (12 * r ^ 2 - L.g₂) * (L.weierstrassP z - r) + (4 * r ^ 3 - L.g₂ * r - L.g₃) := by
    rw [L.derivWeierstrassP_sq z hz]; push_cast; ring
  rw [e]
  exact add_mem (add_mem (add_mem (mul_mem (natCast_mem _ 4) (pow_mem hx 3)) (mul_mem h1 (pow_mem hx 2)))
    (mul_mem h2 hx)) h3
end GlobalTheory.Klein
