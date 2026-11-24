-- Prove2me | solution 1 for GlobalTheory.Klein.apply_mem_intAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:42.838965+00:00
-- url     : https://prove2.me/submissions/53e92c08-e25d-4641-8e1a-58fc736d4eb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
import Theorems.Thm_GlobalTheory_Klein_derivWeierstrassP_mem_intAt

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
    (hz : Red ι L r z) {f : ℂ → ℂ} (hf : f ∈ intFun ι L r) : f z ∈ intAt ι := by
  have : intFun ι L r ≤ (intAt ι).comap (Pi.evalRingHom (fun _ : ℂ => ℂ) z) := by
    refine Subring.closure_le.2 ?_
    rintro f ((rfl | rfl) | ⟨c, hc, rfl⟩)
    · exact hz.2
    · exact derivWeierstrassP_mem_intAt hg hz
    · exact hc
  exact this hf
end GlobalTheory.Klein
