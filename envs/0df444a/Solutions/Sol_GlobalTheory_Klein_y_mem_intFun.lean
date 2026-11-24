-- Prove2me | solution 1 for GlobalTheory.Klein.y_mem_intFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:42.582242+00:00
-- url     : https://prove2.me/submissions/b4b2a1ad-59e1-4336-ad09-75c1e916d4a3

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
theorem _root_.solution (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : L.derivWeierstrassP ∈ intFun ι L r :=
  Subring.subset_closure (Or.inl (Or.inr rfl))
end GlobalTheory.Klein
