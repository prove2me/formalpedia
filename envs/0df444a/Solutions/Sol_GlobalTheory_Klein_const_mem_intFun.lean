-- Prove2me | solution 1 for GlobalTheory.Klein.const_mem_intFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:18.458192+00:00
-- url     : https://prove2.me/submissions/00290870-9ecd-4388-a483-0111ffc97d94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne

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
theorem _root_.solution (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) {c : ℂ} (hc : c ∈ intAt ι) :
    (fun _ => c) ∈ intFun ι L r :=
  Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)
end GlobalTheory.Klein
