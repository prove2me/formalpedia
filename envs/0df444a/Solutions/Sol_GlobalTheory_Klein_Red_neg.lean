-- Prove2me | solution 1 for GlobalTheory.Klein.Red.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:11.808301+00:00
-- url     : https://prove2.me/submissions/5e4721cc-c40e-41c0-a19c-f0858d4831ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
namespace Red
theorem _root_.solution {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (h : Red ι L r z) : Red ι L r (-z) :=
  ⟨fun h' => h.1 (by simpa using h'), by rw [L.weierstrassP_neg]; exact h.2⟩
end Red
end GlobalTheory.Klein
