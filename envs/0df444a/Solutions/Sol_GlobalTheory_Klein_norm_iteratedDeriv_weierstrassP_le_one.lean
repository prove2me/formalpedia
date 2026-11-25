-- Prove2me | solution 1 for GlobalTheory.Klein.norm_iteratedDeriv_weierstrassP_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:58:21.963851+00:00
-- url     : https://prove2.me/submissions/cd25cabb-4c0a-44c6-b608-dbcda2a5fcc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
import Theorems.Thm_GlobalTheory_Klein_apply_mem_intAt
import Theorems.Thm_GlobalTheory_Klein_exists_iteratedDeriv_eq_intFun

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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → ∀ z, Red ι L r z → ∀ k : ℕ, ‖ι (iteratedDeriv (k + 1) L.weierstrassP z)‖ ≤ 1 := by
  intro p _ ι L r hg z hz k
  obtain ⟨f, hf, hfe⟩ := exists_iteratedDeriv_eq_intFun hg k
  rw [hfe z hz.1]
  exact apply_mem_intAt hg hz hf
end GlobalTheory.Klein
